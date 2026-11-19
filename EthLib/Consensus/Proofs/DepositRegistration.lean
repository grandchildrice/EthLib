module

public import EthLib.Consensus.Transition.BuilderRequests
public import EthLib.Consensus.Proofs.Signing
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: the message authenticated by a validator deposit

A deposit signs its public key, withdrawal credentials and amount under `DOMAIN_DEPOSIT`.

Its signature uses the ordinary BLS message tag, not the proof-of-possession key tag.

The results below relate acceptance to that exact signing root and give honest signatures.

They make no claim that a verified deposit reveals its secret key.

EIP-2982, "Specification", fixes the Phase 0 deposit rules by reference.

Provenance: the `process_deposit` rule is stated in beacon-chain.md at `aa16bb4`.

[eip]: https://eips.ethereum.org/EIPS/eip-2982#specification

[source]: https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/specs/phase0/beacon-chain.md#deposits
-/

@[expose] public section

namespace EthLib.Consensus.DepositRegistration

open Base Cryptography.Bls Cryptography.Bls.Signatures Serialization.Ssz

/-- The message authenticated by a deposit, excluding the signature itself. -/
def message (data : DepositData) : DepositMessage :=
  ⟨data.pubkey, data.withdrawalCredentials, data.amount⟩

/-- The signing root checked when the deposit registers a previously unseen validator key.

The domain uses the genesis fork version and the zero genesis validators root.

It does not use the current fork version or the current validators root. -/
def signingRoot (config : Config) (data : DepositData) : Except Err Root := do
  let domain ← computeDomain config DOMAIN_DEPOSIT
  computeSigningRoot (message data) domain

/-- Every deposit message has a signing root. -/
theorem signingRoot_total (config : Config) (data : DepositData) :
    ∃ root, signingRoot config data = .ok root := by
  obtain ⟨domain, domainOk⟩ := computeDomain_total config DOMAIN_DEPOSIT
    config.GENESIS_FORK_VERSION (Vector.replicate 32 0)
  obtain ⟨root, rootOk⟩ := computeSigningRoot_total (message data) domain
  exact ⟨root, by simp only [signingRoot, domainOk, bind, Except.bind, rootOk]⟩

/-- The deposit check reads the exact signing root, with no change to its fields or domain. -/
theorem isValidDepositSignature_eq (config : Config) (checks : SignatureChecks)
    (data : DepositData) :
    isValidDepositSignature config checks data.pubkey data.withdrawalCredentials data.amount
        data.signature =
      ((signingRoot config data).mapError TransitionError.ssz).map
        (fun root => checks.verify data.pubkey (packBytes root) data.signature) := by
  obtain ⟨domain, domainOk⟩ := computeDomain_total config DOMAIN_DEPOSIT
    config.GENESIS_FORK_VERSION (Vector.replicate 32 0)
  obtain ⟨root, rootOk⟩ := computeSigningRoot_total (message data) domain
  simp only [isValidDepositSignature, isValidDepositMessageSignature, signingRoot, message,
    domainOk, liftSsz, Except.mapError, bind, Except.bind, pure, Except.pure,
    Except.map]

/-- The deposit check returns the result of the supplied check on the exact signing root. -/
theorem check_iff (config : Config) (checks : SignatureChecks) (data : DepositData)
    (result : Bool) :
    isValidDepositSignature config checks data.pubkey data.withdrawalCredentials data.amount
        data.signature = .ok result ↔
      ∃ root, signingRoot config data = .ok root ∧
        checks.verify data.pubkey (packBytes root) data.signature = result := by
  obtain ⟨root, rootOk⟩ := signingRoot_total config data
  rw [isValidDepositSignature_eq, rootOk]
  simp only [Except.mapError, Except.map, Except.ok.injEq]
  constructor
  · intro accepted
    exact ⟨root, rfl, accepted⟩
  · rintro ⟨other, same, accepted⟩
    cases same
    exact accepted

/-- Acceptance means that BLS verifies the signature on this deposit's signing root. -/
theorem accepted_iff (config : Config) (data : DepositData) :
    isValidDepositSignature config .bls data.pubkey data.withdrawalCredentials data.amount
        data.signature = .ok true ↔
      ∃ root, signingRoot config data = .ok root ∧
        verify data.pubkey (packBytes root) data.signature = true :=
  check_iff config .bls data true

/-- Changing the signature changes neither the authenticated message nor its signing root. -/
theorem signingRoot_signature (config : Config) (data : DepositData) (signature : BLSSignature) :
    signingRoot config { data with signature } = signingRoot config data := rfl

/-- Honest keys can sign every choice of withdrawal credentials and amount for registration. -/
theorem accepted_of_sign (config : Config) (sk : SecretKey)
    (withdrawalCredentials : Bytes32) (amount : Gwei) :
    ∃ signature root,
      signingRoot config ⟨skToPk sk, withdrawalCredentials, amount, signature⟩ = .ok root ∧
      sign sk (packBytes root) = .ok signature ∧
      isValidDepositSignature config .bls (skToPk sk) withdrawalCredentials amount signature =
        .ok true := by
  let data : DepositData := ⟨skToPk sk, withdrawalCredentials, amount, Vector.replicate 96 0⟩
  obtain ⟨root, rootOk⟩ := signingRoot_total config data
  obtain ⟨signature, signed, verified⟩ := verify_sign sk (packBytes root)
  have signedRoot : signingRoot config
      ⟨skToPk sk, withdrawalCredentials, amount, signature⟩ = .ok root := rootOk
  exact ⟨signature, root, signedRoot, signed,
    (accepted_iff config ⟨skToPk sk, withdrawalCredentials, amount, signature⟩).mpr
      ⟨root, signedRoot, verified⟩⟩

/-- A deposit message has no variable-size count to overflow its commitment word. -/
theorem message_commitmentSized (data : DepositData) :
    CommitmentSized (SszType.desc DepositMessage) (SszType.toValue (message data)) := by
  refine .container fun pair member => ?_
  simp [SszType.desc, SszType.toValue, SszFields.descs, SszFields.toValues] at member
  repeat' rcases member with rfl | member
  all_goals first | exact .byteVector _ _ | exact .uint _ _

/-- Signing data has only two fixed-width fields. -/
private theorem signingData_commitmentSized (data : SigningData) :
    CommitmentSized (SszType.desc SigningData) (SszType.toValue data) := by
  refine .container fun pair member => ?_
  simp [SszType.desc, SszType.toValue, SszFields.descs, SszFields.toValues] at member
  repeat' rcases member with rfl | member
  all_goals exact .byteVector _ _

/-- Equal deposit signing roots bind the key, credentials and amount, or expose a SHA-256 collision.

The signatures themselves are excluded from the authenticated message. -/
theorem signingRoot_binding {config : Config} {first second : DepositData} {root : Root}
    (firstRoot : signingRoot config first = .ok root)
    (secondRoot : signingRoot config second = .ok root) :
    message first = message second ∨ ∃ left right : Bytes, MessageCollision left right := by
  obtain ⟨domain, domainOk⟩ := computeDomain_total config DOMAIN_DEPOSIT
    config.GENESIS_FORK_VERSION (Vector.replicate 32 0)
  obtain ⟨firstObject, firstOk⟩ := SszType.hashTreeRoot_total (message first)
  obtain ⟨secondObject, secondOk⟩ := SszType.hashTreeRoot_total (message second)
  simp only [signingRoot, domainOk, computeSigningRoot, firstOk, secondOk, bind,
    Except.bind] at firstRoot secondRoot
  rcases SszType.hashTreeRoot_binding (signingData_commitmentSized _)
      (signingData_commitmentSized _) firstRoot secondRoot with same | collision
  · have sameObject := congrArg SigningData.objectRoot same
    change firstObject = secondObject at sameObject
    rw [← sameObject] at secondOk
    rcases SszType.hashTreeRoot_binding (message_commitmentSized first)
        (message_commitmentSized second) firstOk secondOk with same | collision
    · exact .inl same
    · obtain ⟨_, _, _, _, left, right, _, _, _, collides⟩ := collision
      exact .inr ⟨left, right, collides⟩
  · obtain ⟨_, _, _, _, left, right, _, _, _, collides⟩ := collision
    exact .inr ⟨left, right, collides⟩

/-- Deposits for distinct public keys have distinct signing roots, or SHA-256 collides. -/
theorem collision_of_signingRoot_eq_of_pubkey_ne {config : Config}
    {first second : DepositData} {root : Root} (different : first.pubkey ≠ second.pubkey)
    (firstRoot : signingRoot config first = .ok root)
    (secondRoot : signingRoot config second = .ok root) :
    ∃ left right : Bytes, MessageCollision left right := by
  rcases signingRoot_binding firstRoot secondRoot with same | collision
  · exact (different (congrArg DepositMessage.pubkey same)).elim
  · exact collision

/-- A deposit and a message of another domain type share a signing root only if SHA-256 collides.

This covers sync-committee messages without assuming that distinct domains imply distinct hashes.
-/
theorem collision_of_signingRoot_eq_of_domain_ne {α : Type} [SszType α]
    [LawfulSszType α] {config : Config} {data : DepositData} {object : α}
    {domainType : DomainType} {version : Version} {genesis : Root} {domain : Domain}
    {root : Root} (different : DOMAIN_DEPOSIT ≠ domainType)
    (domainOk : computeDomain config domainType version genesis = .ok domain)
    (depositRoot : signingRoot config data = .ok root)
    (otherRoot : computeSigningRoot object domain = .ok root) :
    ∃ left right : Bytes, MessageCollision left right := by
  obtain ⟨depositDomain, depositDomainOk⟩ := computeDomain_total config DOMAIN_DEPOSIT
    config.GENESIS_FORK_VERSION (Vector.replicate 32 0)
  obtain ⟨depositObject, depositObjectOk⟩ := SszType.hashTreeRoot_total (message data)
  obtain ⟨otherObject, otherObjectOk⟩ := SszType.hashTreeRoot_total object
  simp only [signingRoot, depositDomainOk, computeSigningRoot, depositObjectOk, bind,
    Except.bind] at depositRoot
  simp only [computeSigningRoot, otherObjectOk, bind, Except.bind] at otherRoot
  rcases SszType.hashTreeRoot_binding (signingData_commitmentSized _)
      (signingData_commitmentSized _) depositRoot otherRoot with same | collision
  · have sameDomain := congrArg SigningData.domain same
    exact (computeDomain_ne different depositDomainOk domainOk sameDomain).elim
  · obtain ⟨_, _, _, _, left, right, _, _, _, collides⟩ := collision
    exact ⟨left, right, collides⟩

end EthLib.Consensus.DepositRegistration
