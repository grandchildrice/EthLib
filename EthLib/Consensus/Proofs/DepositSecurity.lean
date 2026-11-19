module

public import EthLib.Consensus.Proofs.DepositRegistry
public import EthLib.Cryptography.Proofs.Bls.Security.Refinement

/-!
# Proofs: a forged registration signature under an honest validator key

The adversary chooses the configuration, withdrawal credentials, amount and signature.

The key it tries to register is the honest key that the game gives it.

It may ask for hashes and signatures, but cannot win on a signing root submitted to signing.

The root uses the deposit message and `DOMAIN_DEPOSIT`, as the real registration check does.

Only BLS's hash to `G2` is a random oracle here, and SSZ still uses the concrete SHA-256.

This is a single-key bound, not the bound for an aggregate of adaptively registered keys.

In particular, it does not replace the key-tag oracle of the BLS proof-of-possession game.

The game includes scalar zero, whose key validation always fails.
-/

@[expose] public section

namespace EthLib.Consensus.DepositRegistration

open Base Cryptography.Bls Cryptography.Bls.Security
open OracleComp OracleSpec ENNReal
open scoped Classical

/-- An accepted real deposit gives decoded subgroup elements and their exact pairing equation. -/
theorem accepted_isDh {config : Config} {data : DepositData}
    (accepted : isValidDepositSignature config .bls data.pubkey data.withdrawalCredentials
      data.amount data.signature = .ok true) :
    ∃ root key,
      signingRoot config data = .ok root ∧ decodeKey (packBytes data.pubkey) = some key ∧
        blsScheme.isDh key (hashPoint (packBytes root))
          ((decodeSignature (packBytes data.signature)).getD 0) = true := by
  obtain ⟨root, rooted, verified⟩ := (accepted_iff config data).mp accepted
  rw [← byteVerify_hashPoint] at verified
  obtain ⟨key, decoded, paired⟩ := exists_decodeKey_isDh_of_byteVerify verified
  exact ⟨root, key, rooted, decoded, paired⟩

/-- Every key in a registered state has its own accepted deposit and subgroup equation.

The message includes the original credentials and amount of that key's registration. -/
theorem Registered.isDh {preset : Preset} {fork : Fork} {config : Config}
    {state : BeaconState preset fork} (registered : Registered config state)
    {index : Nat} {validator : Validator}
    (found : state.validators.data[index]? = some validator) :
    ∃ data root key, data.pubkey = validator.pubkey ∧
      signingRoot config data = .ok root ∧ decodeKey (packBytes validator.pubkey) = some key ∧
        blsScheme.isDh key (hashPoint (packBytes root))
          ((decodeSignature (packBytes data.signature)).getD 0) = true := by
  obtain ⟨data, same, accepted⟩ := registered index validator found
  obtain ⟨root, key, rooted, decoded, paired⟩ := accepted_isDh accepted
  exact ⟨data, root, key, same, rooted, same ▸ decoded, paired⟩

namespace Forgery

/-- The registration attempt: a chain configuration and the complete deposit data. -/
structure Claim where
  config : Config
  data : DepositData

/-- The signing root of the attempt, as bytes.

Every typed deposit has a root, so the error branch is unreachable. -/
def Claim.message (claim : Claim) : ByteArray :=
  match signingRoot claim.config claim.data with
  | .ok root => packBytes root
  | .error _ => .empty

/-- The attempt read as one BLS message and one signature, with the original signature bytes. -/
def Claim.toSignature (claim : Claim) : ByteArray × ByteArray :=
  (claim.message, packBytes claim.data.signature)

/-- An adversary that tries to register the honest key with a new signed deposit message. -/
structure Adversary where
  main : ByteArray → OracleComp (Security.Spec ByteArray ByteArray) Claim

/-- A one-message check with the oracle's hash in place of BLS's hash to `G2`.

It rejects other messages and does not offer aggregate verification. -/
noncomputable def oracleChecks (message : ByteArray) (hash : G2Sub) : SignatureChecks where
  verify key input signature :=
    decide (input = message) && byteVerify (packBytes key) (packBytes signature) hash
  fastAggregateVerify _ _ _ := false

/-- With the real hash, the deposit check in the game is exactly the real BLS check. -/
theorem oracleChecks_hashPoint (claim : Claim) :
    isValidDepositSignature claim.config
        (oracleChecks claim.message (hashPoint claim.message)) claim.data.pubkey
        claim.data.withdrawalCredentials claim.data.amount claim.data.signature =
      isValidDepositSignature claim.config .bls claim.data.pubkey
        claim.data.withdrawalCredentials claim.data.amount claim.data.signature := by
  obtain ⟨root, rooted⟩ := signingRoot_total claim.config claim.data
  have message : claim.message = packBytes root := by simp only [Claim.message, rooted]
  rw [isValidDepositSignature_eq, isValidDepositSignature_eq, rooted]
  simp only [Except.mapError, Except.map, oracleChecks, message, decide_true, Bool.true_and,
    byteVerify_hashPoint, SignatureChecks.bls]

/-- The attempt wins with the honest key, a fresh signing root and an accepted deposit check. -/
noncomputable def wins (key : G1Sub) (signed : List ByteArray) (claim : Claim)
    (hash : G2Sub) : Bool :=
  decide (packBytes claim.data.pubkey = G1Sub.encode key) &&
    decide (claim.message ∉ signed) &&
    decide (isValidDepositSignature claim.config (oracleChecks claim.message hash)
      claim.data.pubkey claim.data.withdrawalCredentials claim.data.amount claim.data.signature =
        .ok true)

/-- With the real BLS hash, a win is exactly a fresh accepted deposit under the honest key.

The statement concerns real registration checks and does not replace SHA-256 by a random oracle. -/
theorem wins_hashPoint_iff (key : G1Sub) (signed : List ByteArray) (claim : Claim) :
    wins key signed claim (hashPoint claim.message) = true ↔
      packBytes claim.data.pubkey = G1Sub.encode key ∧ claim.message ∉ signed ∧
        isValidDepositSignature claim.config .bls claim.data.pubkey
          claim.data.withdrawalCredentials claim.data.amount claim.data.signature = .ok true := by
  simp only [wins, oracleChecks_hashPoint, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- A win passes the underlying BLS byte check under the same key and hash. -/
theorem byteWins_of_wins {key : G1Sub} {signed : List ByteArray} {claim : Claim}
    {hash : G2Sub} (win : wins key signed claim hash = true) :
    decide (claim.message ∉ signed) &&
      byteVerify (G1Sub.encode key) claim.toSignature.2 hash = true := by
  simp only [wins, Bool.and_eq_true, decide_eq_true_eq] at win
  obtain ⟨⟨same, fresh⟩, accepted⟩ := win
  obtain ⟨root, rooted, verified⟩ :=
    (check_iff claim.config (oracleChecks claim.message hash) claim.data true).mp accepted
  have message : claim.message = packBytes root := by simp only [Claim.message, rooted]
  simp only [oracleChecks, ← message, decide_true, Bool.true_and] at verified
  rw [same] at verified
  change decide (claim.message ∉ signed) &&
    byteVerify (G1Sub.encode key) (packBytes claim.data.signature) hash = true
  rw [show decide (claim.message ∉ signed) = true from decide_eq_true fresh, Bool.true_and]
  exact verified

/-- The run retains the full claim, then makes the verification's one hash call. -/
noncomputable def runAt (main : ByteArray → OracleComp (Security.Spec ByteArray ByteArray) Claim)
    (secret : Scalar) : ProbComp ((Claim × G2Sub) × Security.State Scalar ByteArray) :=
  (simulateQ (Security.impl g2 secret) (do
    let claim ← simulateQ encodingImpl (main (G1Sub.encode (secret • g1)))
    let hash ← query (spec := Security.Spec ByteArray G2Sub) (.inr (.inl claim.message))
    return (claim, hash))).run Security.State.init

/-- The deposit forger read as a forger of BLS signatures on byte strings. -/
def Adversary.toBls (adversary : Adversary) : Security.ByteAdversary where
  main key := Claim.toSignature <$> adversary.main key

/-- The single-key registration game, with a uniformly sampled secret scalar. -/
noncomputable def experiment (adversary : Adversary) :
    ProbComp (Bool × Security.State Scalar ByteArray) := do
  let secret ← $ᵗ Scalar
  (fun (outcome : (Claim × G2Sub) × Security.State Scalar ByteArray) =>
    (wins (secret • g1) outcome.2.signed outcome.1.1 outcome.1.2, outcome.2)) <$>
    runAt adversary.main secret

/-- The probability of registering the honest key with a signature on a fresh signing root. -/
noncomputable def advantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let outcome ← experiment adversary}[outcome.1 = true]

/-- Every run uses at most this many BLS hash calls, including signing and final verification. -/
def HashCallBound (adversary : Adversary) (bound : Nat) : Prop :=
  ∀ outcome ∈ support (experiment adversary), outcome.2.calls ≤ bound

/-- Reading the output as a BLS forgery retains the exact original hash-call state. -/
theorem runAt_toBls (adversary : Adversary) (secret : Scalar) :
    (fun (outcome : (Claim × G2Sub) × Security.State Scalar ByteArray) =>
      (decide (outcome.1.1.message ∉ outcome.2.signed) &&
        byteVerify (G1Sub.encode (secret • g1)) outcome.1.1.toSignature.2 outcome.1.2,
        outcome.2)) <$> runAt adversary.main secret =
      byteExperimentAt adversary.toBls secret := by
  simp only [runAt, byteExperimentAt, byteMain, Adversary.toBls, simulateQ_map, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
    bind_map_left, bind_assoc, pure_bind, Claim.toSignature]

/-- A successful registration forgery is no more likely than the corresponding BLS forgery. -/
theorem advantage_le_byteForgeAdvantage (adversary : Adversary) :
    advantage adversary ≤ byteForgeAdvantage adversary.toBls := by
  unfold advantage experiment byteForgeAdvantage byteExperiment
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  apply MeasureTheory.lintegral_mono
  intro secret
  dsimp only
  rw [← runAt_toBls]
  simp only [Functor.map_map]
  exact prEvent_mono _ _ _ fun outcome win => byteWins_of_wins win

/-- The registration game and its BLS reading count exactly the same hash calls. -/
theorem snd_map_experiment (adversary : Adversary) :
    Prod.snd <$> experiment adversary = Prod.snd <$> byteExperiment adversary.toBls := by
  unfold experiment byteExperiment
  simp only [← runAt_toBls, map_bind, Functor.map_map]

/-- The registration forger and the corresponding BLS forger have the same call bound. -/
theorem hashCallBound_iff (adversary : Adversary) (bound : Nat) :
    HashCallBound adversary bound ↔ ByteHashCallBound adversary.toBls bound :=
  forall_mem_support_snd_iff (snd_map_experiment adversary) fun state => state.calls ≤ bound

/-- A fresh deposit signature under one honest key reduces to the named co-CDH solver.

The bound counts BLS hash calls, including signing and the final verification.

Freshness is by signing-root bytes, so a hash collision can make distinct deposit data nonfresh.

This does not bound a forgery under a sum of adversarially registered keys. -/
theorem advantage_le_coCdhAdvantage (adversary : Adversary) {bound : Nat}
    (positive : 0 < bound) (budget : HashCallBound adversary bound) :
    advantage adversary ≤ bound * coCdhAdvantage Scalar g1 g2
      (Security.reduction (F := Scalar) g2 adversary.toBls.toGroup bound) :=
  (advantage_le_byteForgeAdvantage adversary).trans
    (byteForgeAdvantage_le_coCdhAdvantage_of_byteHashCallBound adversary.toBls positive
      ((hashCallBound_iff adversary bound).mp budget))

/-- The registration game with a uniformly sampled nonzero scalar, as real secret keys require. -/
noncomputable def nonzeroExperiment (adversary : Adversary) :
    ProbComp (Bool × Security.State Scalar ByteArray) := do
  let secret ← $ᵗ NonzeroScalar
  (fun (outcome : (Claim × G2Sub) × Security.State Scalar ByteArray) =>
    (wins (secret.val • g1) outcome.2.signed outcome.1.1 outcome.1.2, outcome.2)) <$>
    runAt adversary.main secret.val

/-- The probability of a registration forgery under a nonzero honest secret scalar. -/
noncomputable def nonzeroAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let outcome ← nonzeroExperiment adversary}[outcome.1 = true]

/-- Restricting the key to a nonzero scalar keeps the reduction to the BLS byte game. -/
theorem nonzeroAdvantage_le_byteForgeAdvantage (adversary : Adversary) :
    nonzeroAdvantage adversary ≤ nonzeroByteForgeAdvantage adversary.toBls := by
  unfold nonzeroAdvantage nonzeroExperiment nonzeroByteForgeAdvantage nonzeroByteExperiment
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  apply MeasureTheory.lintegral_mono
  intro secret
  dsimp only
  rw [← runAt_toBls]
  simp only [Functor.map_map]
  exact prEvent_mono _ _ _ fun outcome win => byteWins_of_wins win

/-- A real nonzero key's fresh deposit signature satisfies the nonzero-key co-CDH bound.

The factor `r / (r - 1)` accounts for excluding scalar zero from the honest-key distribution.

The hash-call bound covers every run of the original scalar-sampling game. -/
theorem nonzeroAdvantage_le_coCdhAdvantage (adversary : Adversary) {bound : Nat}
    (positive : 0 < bound) (budget : HashCallBound adversary bound) :
    nonzeroAdvantage adversary ≤
      (Fr.modulus : ℝ≥0∞) / ((Fr.modulus - 1 : Nat) : ℝ≥0∞) *
        (bound * coCdhAdvantage Scalar g1 g2
          (Security.reduction (F := Scalar) g2 adversary.toBls.toGroup bound)) :=
  (nonzeroAdvantage_le_byteForgeAdvantage adversary).trans
    (Security.nonzeroByteForgeAdvantage_le_coCdhAdvantage adversary.toBls positive
      ((hashCallBound_iff adversary bound).mp budget))

end Forgery

end EthLib.Consensus.DepositRegistration
