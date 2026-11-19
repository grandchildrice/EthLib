module

public import EthLib.Consensus.Proofs.DepositSecurity
public import EthLib.Cryptography.Proofs.Bls.Security.PopExtract
public import EthLib.Cryptography.Proofs.Bls.Security.PopRefinement

/-!
# Proofs: extracting the honest share from aggregates of deposit-registered keys

The extraction uses each key's accepted deposit signature, not a BLS key-tag proof of possession.

The hash of each other key's deposit signing root must be a known nonzero multiple of the challenge.

Under that condition, its deposit signature gives its share of an aggregate on the challenge.

Subtracting those shares and dividing by the honest key's multiplicity extracts its share.

This proves the algebraic step only.

No game here justifies programming those registration-message hashes adaptively.

That programming needs to account for queries on the signed credentials, amount and public key.

The single-key bound of `DepositSecurity` does not supply that missing coupling.
-/

@[expose] public section

namespace EthLib.Consensus.DepositRegistration

open Base Cryptography.Bls Cryptography.Bls.Security
open scoped Classical

namespace Aggregate

/-- An accepted registration with an oracle hash gives the pairing equation on its exact key. -/
theorem isDh_of_registration {config : Config} {data : DepositData} {key : G1Sub} {hash : G2Sub}
    (decoded : decodeKey (packBytes data.pubkey) = some key)
    (accepted : isValidDepositSignature config (Forgery.oracleChecks
      ({ config, data } : Forgery.Claim).message hash) data.pubkey data.withdrawalCredentials
        data.amount data.signature = .ok true) :
    blsScheme.isDh key hash ((decodeSignature (packBytes data.signature)).getD 0) = true := by
  obtain ⟨root, rooted, checked⟩ := (check_iff config _ data true).mp accepted
  have message : ({ config, data } : Forgery.Claim).message = packBytes root := by
    simp only [Forgery.Claim.message, rooted]
  simp only [Forgery.oracleChecks, message, decide_true, Bool.true_and] at checked
  obtain ⟨other, same, paired⟩ := exists_decodeKey_isDh_of_byteVerify checked
  rw [decoded, Option.some.injEq] at same
  subst other
  exact paired

/-- Encoding every subgroup key and decoding it gives the original key list. -/
private theorem mapM_decodeKey_encode (keys : List G1Sub) :
    (keys.map G1Sub.encode).mapM decodeKey = some keys := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp [decodeKey_encode, ih]

/-- Byte aggregate verification gives the pairing equation on the original subgroup keys. -/
theorem isDh_sum_of_byteFastAggregateVerify {keys : List G1Sub} {signature : ByteArray}
    {hash : G2Sub}
    (accepted : byteFastAggregateVerify (keys.map G1Sub.encode).toArray signature hash = true) :
    blsScheme.isDh keys.sum hash ((decodeSignature signature).getD 0) = true := by
  obtain ⟨other, decoded, paired⟩ := isDh_of_byteFastAggregateVerify accepted
  simp only [mapM_decodeKey_encode, Option.some.injEq] at decoded
  subst other
  exact paired

/-- The original deposit signatures supply the other shares of a valid aggregate.

Each key uses one fixed retained registration, with its original signed credentials and amount.

The registration hash is programmed at that signing root under the ordinary BLS message tag.

This condition is a hypothesis of the algebraic step, not an assumption of hash independence.

The honest multiplicity must be nonzero in the scalar field. -/
theorem extractAggregate_eq_of_registrations (config : Config) (secret : Scalar)
    (challenge : G2Sub) (registrations : G1Sub → DepositData) (scalars : G1Sub → Scalar)
    (keys : List G1Sub) (signature : ByteArray)
    (decoded : ∀ key ∈ keys,
      decodeKey (packBytes (registrations key).pubkey) = some key)
    (accepted : ∀ key ∈ keys, key ≠ secret • g1 → scalars key ≠ 0 ∧
      isValidDepositSignature config (Forgery.oracleChecks
        ({ config, data := registrations key } : Forgery.Claim).message
          (scalars key • challenge)) (registrations key).pubkey
            (registrations key).withdrawalCredentials (registrations key).amount
              (registrations key).signature = .ok true)
    (count : (keys.count (secret • g1) : Scalar) ≠ 0)
    (aggregate : byteFastAggregateVerify (keys.map G1Sub.encode).toArray signature challenge =
      true) :
    Pop.extractAggregate (secret • g1) scalars
        (keys.map fun key => (key,
          (decodeSignature (packBytes (registrations key).signature)).getD 0))
        ((decodeSignature signature).getD 0) = secret • challenge := by
  have projected : ((keys.map fun key =>
      (key, (decodeSignature (packBytes (registrations key).signature)).getD 0)).map
      Prod.fst) = keys := by
    rw [List.map_map]
    exact List.map_id keys
  have sameCount : @List.count G1Sub instBEqOfDecidableEq (secret • g1) keys =
      keys.count (secret • g1) := by
    simp only [List.count_eq_countP]
    apply List.countP_congr
    intro key _
    simp only [beq_iff_eq]
  apply Pop.extractAggregate_eq (F := Scalar) (scheme := blsScheme) blsScheme_sound
    (a := secret) (Z := challenge)
  · intro pair member
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
    exact G1Sub.exists_eq_smul_g1 key
  · intro pair member different
    obtain ⟨key, keyMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨nonzero, checked⟩ := accepted key keyMember different
    exact ⟨nonzero, isDh_of_registration (decoded key keyMember) checked⟩
  · rw [projected, show blsScheme.g₁ = g1 from rfl, sameCount]
    exact count
  · rw [projected]
    exact isDh_sum_of_byteFastAggregateVerify (keys := keys) (signature := signature) aggregate

end Aggregate

end EthLib.Consensus.DepositRegistration
