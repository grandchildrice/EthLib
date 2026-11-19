module

public import EthLib.Consensus.Proofs.DepositAggregate

/-!
# Proofs: adaptive programming of the shared BLS message oracle

The message oracle has one byte-string cache for ordinary messages and deposit signing roots.

A fixed role mask chooses which roots use the co-CDH challenge as their hash basis.

The mask is not a parser for deposit data or a second key-tag oracle.

The coupling below holds for every mask and for arbitrary adaptive oracle computations.

Signing a masked root is an explicit bad event, including when its hash was queried earlier.

A later probability bound still has to choose masks and account for this event and zero scalars.

No lower bound on the probability of a suitable mask is asserted here.
-/

@[expose] public section

namespace EthLib.Consensus.DepositRegistration.Adaptive

open Base Cryptography.Bls Cryptography.Bls.Security
open OracleComp OracleSpec ENNReal
open scoped Classical

/-- One immutable programming decision for each ordinary BLS message byte string. -/
abbrev Mask := ByteArray → Bool

/-- A cached scalar uses the challenge basis exactly on the masked roots. -/
noncomputable def answer (base challenge : G2Sub) (mask : Mask) (input : ByteArray)
    (scalar : Scalar) : G2Sub :=
  scalar • if mask input then challenge else base

/-- A single ordinary-message cache, including repeated queries and later registration checks. -/
noncomputable def hash (base challenge : G2Sub) (mask : Mask) (input : ByteArray) :
    StateT (Security.State Scalar ByteArray) ProbComp G2Sub := fun state =>
  match lookup input state.table with
  | some (_, scalar) =>
    pure (answer base challenge mask input scalar, { state with calls := state.calls + 1 })
  | none =>
    (fun scalar => (answer base challenge mask input scalar,
      { state with table := state.table ++ [(input, scalar)], calls := state.calls + 1 })) <$>
      ($ᵗ Scalar)

/-- Masking does not change the real oracle when both bases are the ordinary generator. -/
theorem hash_real (mask : Mask) (input : ByteArray) :
    hash g2 g2 mask input = Security.hash g2 input := by
  funext state
  unfold hash Security.hash answer
  cases lookup input state.table <;> simp

/-- Divide the cached scalar of each masked root by the challenge's nonzero scalar. -/
noncomputable def scaleTable (mask : Mask) (scale : Scalar)
    (table : List (ByteArray × Scalar)) : List (ByteArray × Scalar) :=
  table.map fun entry => (entry.1, if mask entry.1 then entry.2 * scale else entry.2)

/-- Scaling retains the exact lookup position, with a root-dependent scalar change. -/
theorem lookup_scaleTable (mask : Mask) (scale : Scalar) (input : ByteArray)
    (table : List (ByteArray × Scalar)) :
    lookup input (scaleTable mask scale table) =
      (lookup input table).map fun entry =>
        (entry.1, if mask input then entry.2 * scale else entry.2) := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨message, scalar⟩ := entry
    simp only [scaleTable, List.map_cons] at ih ⊢
    simp only [lookup]
    by_cases same : message = input
    · subst message
      simp
    · simp [same, ih, Option.map_map, Function.comp_def]

/-- Read real states through the simulator's coordinates, keeping signing history and calls. -/
noncomputable def projectState (mask : Mask) (challengeScalar : Scalar)
    (state : Security.State Scalar ByteArray) : Security.State Scalar ByteArray :=
  { state with table := scaleTable mask challengeScalar⁻¹ state.table }

/-- A one-query distributional coupling, including roots queried before their deposit is known. -/
theorem prEvent_hash_projectState (mask : Mask) {challengeScalar : Scalar}
    (nonzero : challengeScalar ≠ 0) (input : ByteArray)
    (state : Security.State Scalar ByteArray)
    (event : G2Sub × Security.State Scalar ByteArray → Prop) :
    Pr{let result ← Security.hash g2 input state}[
        event (result.1, projectState mask challengeScalar result.2)] =
      Pr{let result ← (hash g2 (challengeScalar • g2) mask input
        (projectState mask challengeScalar state))}[event result] := by
  have looked : lookup input (projectState mask challengeScalar state).table =
      (lookup input state.table).map fun entry =>
        (entry.1, if mask input then entry.2 * challengeScalar⁻¹ else entry.2) :=
    lookup_scaleTable mask challengeScalar⁻¹ input state.table
  unfold Security.hash hash
  cases found : lookup input state.table with
  | some entry =>
    rw [found, Option.map_some] at looked
    rw [looked]
    obtain ⟨position, scalar⟩ := entry
    dsimp only
    by_cases role : mask input = true
    · simp [answer, role, projectState, smul_smul, nonzero]
    · simp [answer, role, projectState]
  | none =>
    rw [found, Option.map_none] at looked
    rw [looked]
    dsimp only
    rw [prEvent_map, prEvent_map]
    by_cases role : mask input = true
    · conv_rhs => rw [← SampleableType.prEvent_uniformSample_equiv
        (Equiv.mulRight₀ challengeScalar⁻¹ (inv_ne_zero nonzero))]
      refine prEvent_congr _ _ _ fun scalar => ?_
      simp [projectState, scaleTable, answer, role, smul_smul, nonzero]
    · refine prEvent_congr _ _ _ fun scalar => ?_
      simp [projectState, scaleTable, answer, role]

/-- The scalar already retained for this root, or zero when no query has installed it. -/
noncomputable def scalarAt (input : ByteArray) (state : Security.State Scalar ByteArray) : Scalar :=
  ((lookup input state.table).getD (0, 0)).2

/-- The simulator can sign roots on the ordinary basis using the supplied `a • g2`.

A masked signing request returns zero; the coupling charges that request to `Bad`. -/
noncomputable def signature (publicPoint : G2Sub) (mask : Mask) (input : ByteArray)
    (state : Security.State Scalar ByteArray) : G2Sub :=
  if mask input then 0 else scalarAt input state • publicPoint

/-- The shared-cache signing simulation counts its hash and retains the original message. -/
noncomputable def sign (base publicPoint challenge : G2Sub) (mask : Mask) (input : ByteArray) :
    StateT (Security.State Scalar ByteArray) ProbComp G2Sub := fun state =>
  (fun result => (signature publicPoint mask input result.2,
    { result.2 with signed := result.2.signed ++ [input] })) <$>
      hash base challenge mask input state

/-- Coins, ordinary hashes and signatures all use the same cache and immutable role mask. -/
noncomputable def impl (base publicPoint challenge : G2Sub) (mask : Mask) :
    QueryImpl (Security.Spec ByteArray G2Sub)
      (StateT (Security.State Scalar ByteArray) ProbComp)
  | .inl count => fun state =>
    (·, state) <$> (query (spec := unifSpec) count : ProbComp (Fin (count + 1)))
  | .inr (.inl input) => hash base challenge mask input
  | .inr (.inr input) => sign base publicPoint challenge mask input

/-- A signing request used a root whose hash is programmed on the challenge basis. -/
def Bad (mask : Mask) (state : Security.State Scalar ByteArray) : Prop :=
  ∃ input ∈ state.signed, mask input = true

/-- Once a masked root was signed, every later adaptive query keeps that fact. -/
theorem preservesInv_bad (mask : Mask) (secret : Scalar) :
    QueryImpl.PreservesInv (Security.impl (M := ByteArray) g2 secret) (Bad mask) := by
  intro query state bad result reached
  obtain ⟨_, signed, _⟩ := grows_of_mem_support_impl reached
  obtain ⟨input, member, role⟩ := bad
  exact ⟨input, signed member, role⟩

/-- Every adaptive query couples until the explicitly retained masked-signing event. -/
theorem dominatedUntilBad (mask : Mask) (secret : Scalar) {challengeScalar : Scalar}
    (nonzero : challengeScalar ≠ 0) :
    QueryImpl.DominatedUntilBad (Security.impl (M := ByteArray) g2 secret)
      (impl g2 (secret • g2) (challengeScalar • g2) mask)
      (projectState mask challengeScalar) (fun _ => True) (Bad mask) := by
  intro query state _ _ event
  rcases query with count | input | input
  · change Pr{let result ← (·, state) <$> _}[_] ≤
      Pr{let result ← (·, projectState mask challengeScalar state) <$> _}[_]
    rw [prEvent_map, prEvent_map]
    exact prEvent_mono _ _ _ fun _ accepted => accepted.1
  · change Pr{let result ← Security.hash g2 input state}[_] ≤
      Pr{let result ← (hash g2 (challengeScalar • g2) mask input
        (projectState mask challengeScalar state))}[_]
    exact (prEvent_mono _ _ _ fun _ accepted => accepted.1).trans
      (prEvent_hash_projectState mask nonzero input state event).le
  · change Pr{let result ← (fun result => (secret • result.1,
        { result.2 with signed := result.2.signed ++ [input] })) <$>
        Security.hash g2 input state}[_] ≤
      Pr{let result ← (fun result => (signature (secret • g2) mask input result.2,
        { result.2 with signed := result.2.signed ++ [input] })) <$>
        hash g2 (challengeScalar • g2) mask input
          (projectState mask challengeScalar state)}[_]
    rw [prEvent_map, prEvent_map]
    have coupled := prEvent_hash_projectState mask nonzero input state fun result =>
      event (signature (secret • g2) mask input result.2,
        { result.2 with signed := result.2.signed ++ [input] })
    refine le_trans ?_ coupled.le
    refine prEvent_mono_of_support _ _ _ fun result reached ⟨accepted, good⟩ => ?_
    obtain ⟨⟨position, scalar, found, answerEq⟩, _⟩ := mem_support_hash reached
    have role : mask input = false := by
      cases selected : mask input with
      | false => rfl
      | true => exact (good ⟨input, by simp, selected⟩).elim
    have sameSignature : signature (secret • g2) mask input
        (projectState mask challengeScalar result.2) = secret • result.1 := by
      simp only [signature, role, Bool.false_eq_true, ↓reduceIte, scalarAt, projectState,
        lookup_scaleTable, found, Option.map_some, Option.getD_some]
      rw [answerEq, smul_smul, smul_smul, mul_comm]
    rw [sameSignature]
    exact accepted

/-- The coupling covers an arbitrary finite adaptive oracle computation, including verification.

The final state has the same total hash calls and the same exact signing-request history.

No registration-message classifier or independent proof-of-possession hash is used. -/
theorem prEvent_run_projectState_le {α : Type} (mask : Mask) (secret : Scalar)
    {challengeScalar : Scalar} (nonzero : challengeScalar ≠ 0)
    (computation : OracleComp (Security.Spec ByteArray G2Sub) α)
    (state : Security.State Scalar ByteArray)
    (event : α × Security.State Scalar ByteArray → Prop) :
    Pr{let result ← (simulateQ (Security.impl g2 secret) computation).run state}[
        event (result.1, projectState mask challengeScalar result.2) ∧ ¬Bad mask result.2] ≤
      Pr{let result ← (simulateQ
        (impl g2 (secret • g2) (challengeScalar • g2) mask) computation).run
          (projectState mask challengeScalar state)}[event result] :=
  (dominatedUntilBad mask secret nonzero).prEvent_simulateQ_run_map_and_not_bad_le
    (fun _ _ _ _ _ => trivial) (preservesInv_bad mask secret) computation state trivial event

/-- Rescaling a cache keeps every original hash-call count. -/
theorem projectState_calls (mask : Mask) (scalar : Scalar)
    (state : Security.State Scalar ByteArray) :
    (projectState mask scalar state).calls = state.calls := rfl

/-- Rescaling a cache keeps every original signing request, in its original order. -/
theorem projectState_signed (mask : Mask) (scalar : Scalar)
    (state : Security.State Scalar ByteArray) :
    (projectState mask scalar state).signed = state.signed := rfl

/-- The scalar at a masked root is divided by the challenge scalar, without moving the root. -/
theorem scalarAt_projectState (mask : Mask) (scalar : Scalar) (input : ByteArray)
    (state : Security.State Scalar ByteArray) :
    scalarAt input (projectState mask scalar state) =
      if mask input then scalarAt input state * scalar⁻¹ else scalarAt input state := by
  simp only [scalarAt, projectState, lookup_scaleTable]
  cases lookup input state.table with
  | none => simp
  | some entry => cases mask input <;> rfl

/-- Read one answer from the shared cache, rather than from a separate registration oracle. -/
noncomputable def cachedHash (base challenge : G2Sub) (mask : Mask)
    (state : Security.State Scalar ByteArray) (input : ByteArray) : G2Sub :=
  answer base challenge mask input (scalarAt input state)

/-- A query installs its answer once, counts even repeats, and changes no signing history. -/
theorem mem_support_hash {base challenge : G2Sub} {mask : Mask} {input : ByteArray}
    {state : Security.State Scalar ByteArray} {result : G2Sub × Security.State Scalar ByteArray}
    (reached : result ∈ support (hash base challenge mask input state)) :
    (∃ position scalar, lookup input result.2.table = some (position, scalar) ∧
      result.1 = answer base challenge mask input scalar) ∧
      (result.2.table = state.table ∨ ∃ entry, result.2.table = state.table ++ [entry]) ∧
      result.2.signed = state.signed ∧ result.2.calls = state.calls + 1 := by
  unfold hash at reached
  split at reached
  · next position scalar found =>
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact ⟨⟨position, scalar, found, rfl⟩, .inl rfl, rfl, rfl⟩
  · next fresh =>
    simp only [support_map, Set.mem_image] at reached
    obtain ⟨scalar, _, rfl⟩ := reached
    exact ⟨⟨_, scalar, lookup_append_of_none fresh scalar, rfl⟩, .inr ⟨_, rfl⟩, rfl, rfl⟩

/-- The cache's answer is exactly the answer actually returned by this query. -/
theorem cachedHash_of_mem_support_hash {base challenge : G2Sub} {mask : Mask} {input : ByteArray}
    {state : Security.State Scalar ByteArray} {result : G2Sub × Security.State Scalar ByteArray}
    (reached : result ∈ support (hash base challenge mask input state)) :
    cachedHash base challenge mask result.2 input = result.1 := by
  obtain ⟨⟨_, scalar, found, returned⟩, _⟩ := mem_support_hash reached
  simp only [cachedHash, scalarAt, found, Option.getD_some]
  exact returned.symm

/-- Every later query keeps an installed root's original coefficient and lookup position. -/
theorem preservesInv_lookup (base publicPoint challenge : G2Sub) (mask : Mask)
    (input : ByteArray) (position : Nat) (scalar : Scalar) :
    QueryImpl.PreservesInv (impl base publicPoint challenge mask)
      (fun state => lookup input state.table = some (position, scalar)) := by
  intro query state found result reached
  have stable {state' : Security.State Scalar ByteArray}
      (table : state'.table = state.table ∨ ∃ entry, state'.table = state.table ++ [entry]) :
      lookup input state'.table = some (position, scalar) := by
    rcases table with same | ⟨entry, appended⟩
    · simpa only [same] using found
    · rw [appended]
      exact lookup_append_of_some [entry] found
  rcases query with count | message | message
  · change result ∈ support ((·, state) <$> _) at reached
    simp only [support_map, Set.mem_image] at reached
    obtain ⟨_, _, rfl⟩ := reached
    exact found
  · exact stable (mem_support_hash reached).2.1
  · change result ∈ support ((fun result : G2Sub × Security.State Scalar ByteArray =>
        (signature publicPoint mask message result.2,
        { result.2 with signed := result.2.signed ++ [message] })) <$>
        hash base challenge mask message state) at reached
    simp only [support_map, Set.mem_image] at reached
    obtain ⟨hashed, reached, rfl⟩ := reached
    exact stable (mem_support_hash reached).2.1

/-- Adaptive computation, including later deposit disclosure, retains an earlier answer. -/
theorem cachedHash_after_adaptive {α : Type} (base publicPoint challenge : G2Sub) (mask : Mask)
    (input : ByteArray) {state : Security.State Scalar ByteArray}
    {hashed : G2Sub × Security.State Scalar ByteArray}
    (queried : hashed ∈ support (hash base challenge mask input state))
    (computation : OracleComp (Security.Spec ByteArray G2Sub) α)
    {result : α × Security.State Scalar ByteArray}
    (reached : result ∈ support ((simulateQ (impl base publicPoint challenge mask)
      computation).run hashed.2)) :
    cachedHash base challenge mask result.2 input = hashed.1 := by
  obtain ⟨⟨position, scalar, found, returned⟩, _⟩ := mem_support_hash queried
  have retained := simulateQ_run_preservesInv (impl base publicPoint challenge mask)
    (fun state => lookup input state.table = some (position, scalar))
    (preservesInv_lookup base publicPoint challenge mask input position scalar)
    computation hashed.2 found result reached
  simp only [cachedHash, scalarAt, retained, Option.getD_some]
  exact returned.symm

/-- All ordinary cached hash values are unchanged by the distributional projection. -/
theorem cachedHash_projectState (mask : Mask) {scalar : Scalar} (nonzero : scalar ≠ 0)
    (state : Security.State Scalar ByteArray) (input : ByteArray) :
    cachedHash g2 (scalar • g2) mask (projectState mask scalar state) input =
      scalarAt input state • g2 := by
  simp only [cachedHash, answer, scalarAt_projectState]
  cases mask input <;> simp [smul_smul, nonzero]

/-- A candidate aggregate and the retained deposit of each key it uses.

Each retained deposit has its original credentials and amount.

The adversary chooses that full context independently for each key.

Repeated committee keys use their one retained registration, as an actual validator registry does.
-/
structure Output where
  keys : List G1Sub
  registrations : G1Sub → DepositData
  message : ByteArray
  signature : ByteArray

/-- The exact registration root with the retained deposit's complete signed context. -/
def Output.registrationRoot (output : Output) (config : Config) (key : G1Sub) : ByteArray :=
  ({ config, data := output.registrations key } : Forgery.Claim).message

/-- Overlap with a signed root of another domain exposes a concrete SHA-256 collision.

This applies to individual roots in an observed adaptive signing transcript.

It assumes neither global hash injectivity nor a parser for opaque hash-oracle queries. -/
theorem Output.collision_of_registrationRoot_eq_of_domain_ne {α : Type}
    [Serialization.Ssz.SszType α] [Serialization.Ssz.LawfulSszType α]
    (output : Output) {config : Config} {key : G1Sub} {object : α}
    {domainType : DomainType} {version : Version} {genesis : Root} {domain : Domain}
    {root : Root} (different : DOMAIN_DEPOSIT ≠ domainType)
    (domainOk : computeDomain config domainType version genesis = .ok domain)
    (rootOk : computeSigningRoot object domain = .ok root)
    (overlap : output.registrationRoot config key = packBytes root) :
    ∃ left right : Serialization.Ssz.Bytes, Serialization.Ssz.MessageCollision left right := by
  obtain ⟨registration, registrationOk⟩ := signingRoot_total config (output.registrations key)
  simp only [Output.registrationRoot, Forgery.Claim.message, registrationOk] at overlap
  have sameRoot : registration = root := Base.packBytes_injective overlap
  subst registration
  exact collision_of_signingRoot_eq_of_domain_ne different domainOk registrationOk rootOk

/-- An aggregate adversary using one ordinary message-hash oracle and one signing oracle. -/
structure Adversary where
  main : G1Sub → OracleComp (Security.Spec ByteArray G2Sub) Output

/-- Verification queries the target and every retained registration through that same oracle.

These queries count even when the adversary has already queried their roots. -/
noncomputable def run (config : Config) (adversary : Adversary) (key : G1Sub) :
    OracleComp (Security.Spec ByteArray G2Sub) Output := do
  let output ← adversary.main key
  let _ ← query (spec := Security.Spec ByteArray G2Sub) (.inr (.inl output.message))
  let _ ← output.keys.mapM fun key =>
    query (spec := Security.Spec ByteArray G2Sub)
      (.inr (.inl (output.registrationRoot config key)))
  return output

/-- Actual deposit-signature and byte aggregate checks using the supplied ordinary hash answers.

The honest key's multiplicity is required to be nonzero in the scalar field. -/
noncomputable def Verified (config : Config) (honest : G1Sub) (output : Output)
    (oracleHash : ByteArray → G2Sub) : Prop :=
  (∀ key ∈ output.keys,
    decodeKey (packBytes (output.registrations key).pubkey) = some key ∧
      isValidDepositSignature config
        (Forgery.oracleChecks (output.registrationRoot config key)
          (oracleHash (output.registrationRoot config key))) (output.registrations key).pubkey
            (output.registrations key).withdrawalCredentials (output.registrations key).amount
              (output.registrations key).signature = .ok true) ∧
    (output.keys.count honest : Scalar) ≠ 0 ∧
    byteFastAggregateVerify (output.keys.map G1Sub.encode).toArray output.signature
      (oracleHash output.message) = true

/-- The hash-role and scalar event on which the simulator can extract the honest contribution.

It asks only for roles and nonzero retained coefficients, not pointwise programmed hash equations.

The same byte root always has the same role, including queries made before a deposit is disclosed.
-/
def Ready (config : Config) (mask : Mask) (honest : G1Sub) (output : Output)
    (state : Security.State Scalar ByteArray) : Prop :=
  mask output.message = true ∧ scalarAt output.message state ≠ 0 ∧
    ∀ key ∈ output.keys, key ≠ honest →
      mask (output.registrationRoot config key) = true ∧
        scalarAt (output.registrationRoot config key) state ≠ 0

/-- The role event and absence of masked signing imply freshness of the aggregate message. -/
theorem fresh_of_ready_not_bad {config : Config} {mask : Mask} {honest : G1Sub}
    {output : Output} {state : Security.State Scalar ByteArray}
    (ready : Ready config mask honest output state) (good : ¬Bad mask state) :
    output.message ∉ state.signed := by
  intro signed
  exact good ⟨output.message, signed, ready.1⟩

/-- The roles needed by extraction can coexist with the original signing-request history. -/
def RolesFit (config : Config) (mask : Mask) (honest : G1Sub) (output : Output)
    (signed : List ByteArray) : Prop :=
  mask output.message = true ∧
    (∀ key ∈ output.keys, key ≠ honest → mask (output.registrationRoot config key) = true) ∧
    ∀ input ∈ signed, mask input = false

/-- A compatible role mask exists exactly when no required challenge root was signed.

The witness is chosen after a fixed transcript only to establish feasibility.

This is not a causal mask-selection algorithm or a probability bound for selecting one. -/
theorem exists_rolesFit_iff (config : Config) (honest : G1Sub) (output : Output)
    (signed : List ByteArray) :
    (∃ mask, RolesFit config mask honest output signed) ↔
      output.message ∉ signed ∧
        ∀ key ∈ output.keys, key ≠ honest → output.registrationRoot config key ∉ signed := by
  constructor
  · rintro ⟨mask, target, registrations, signing⟩
    constructor
    · intro signedTarget
      exact Bool.noConfusion (target.symm.trans (signing output.message signedTarget))
    · intro key member different signedRegistration
      exact Bool.noConfusion ((registrations key member different).symm.trans
        (signing _ signedRegistration))
  · rintro ⟨fresh, separate⟩
    let mask : Mask := fun input => decide (input = output.message ∨
      ∃ key ∈ output.keys, key ≠ honest ∧ input = output.registrationRoot config key)
    refine ⟨mask, ?_, ?_, ?_⟩
    · exact decide_eq_true (Or.inl rfl)
    · intro key member different
      exact decide_eq_true (Or.inr ⟨key, member, different, rfl⟩)
    · intro input signedInput
      apply decide_eq_false
      rintro (rfl | ⟨key, member, different, rfl⟩)
      · exact fresh signedInput
      · exact separate key member different signedInput

/-- With the real BLS hash, every accepted registration is a genuine signature witness. -/
theorem Verified.registrationWitnesses {config : Config} {honest : G1Sub} {output : Output}
    (verified : Verified config honest output hashPoint) :
    ∀ key ∈ output.keys, HasWitness config (output.registrations key).pubkey := by
  intro key member
  have accepted := (verified.1 key member).2
  change isValidDepositSignature config
    (Forgery.oracleChecks ({ config, data := output.registrations key } : Forgery.Claim).message
      (hashPoint ({ config, data := output.registrations key } : Forgery.Claim).message))
    (output.registrations key).pubkey (output.registrations key).withdrawalCredentials
      (output.registrations key).amount (output.registrations key).signature = .ok true at accepted
  rw [Forgery.oracleChecks_hashPoint
    ({ config, data := output.registrations key } : Forgery.Claim)] at accepted
  exact ⟨output.registrations key, rfl, accepted⟩

/-- Read all extraction coefficients from the simulator's one retained ordinary-message cache. -/
noncomputable def extract (config : Config) (honest : G1Sub) (output : Output)
    (state : Security.State Scalar ByteArray) : G2Sub :=
  let target := scalarAt output.message state
  target⁻¹ • Pop.extractAggregate honest
    (fun key => scalarAt (output.registrationRoot config key) state * target⁻¹)
    (output.keys.map fun key => (key,
      (decodeSignature (packBytes (output.registrations key).signature)).getD 0))
    ((decodeSignature output.signature).getD 0)

/-- Accepted deposits and cache roles imply extraction without hash-equation premises. -/
theorem extract_eq_of_verified_ready (config : Config) (mask : Mask) (secret : Scalar)
    (challenge : G2Sub) (output : Output) (state : Security.State Scalar ByteArray)
    (verified : Verified config (secret • g1) output (cachedHash g2 challenge mask state))
    (ready : Ready config mask (secret • g1) output state) :
    extract config (secret • g1) output state = secret • challenge := by
  obtain ⟨registrations, count, aggregate⟩ := verified
  obtain ⟨targetRole, targetNonzero, otherRoles⟩ := ready
  let target := scalarAt output.message state
  have targetHash : cachedHash g2 challenge mask state output.message = target • challenge := by
    simp only [cachedHash, answer, targetRole, ↓reduceIte, target]
  have extracted := Aggregate.extractAggregate_eq_of_registrations config secret
    (cachedHash g2 challenge mask state output.message) output.registrations
    (fun key => scalarAt (output.registrationRoot config key) state * target⁻¹)
    output.keys output.signature (fun key member => (registrations key member).1) ?_ count aggregate
  · change target⁻¹ • _ = secret • challenge
    rw [extracted, targetHash, smul_smul, smul_smul]
    calc
      (target⁻¹ * secret * target) • challenge =
          (secret * (target⁻¹ * target)) • challenge := by congr 1; ring
      _ = secret • challenge := by simp [target, targetNonzero]
  · intro key member different
    obtain ⟨role, nonzero⟩ := otherRoles key member different
    refine ⟨mul_ne_zero nonzero (inv_ne_zero targetNonzero), ?_⟩
    have hashRelation :
        (scalarAt (output.registrationRoot config key) state * target⁻¹) •
            cachedHash g2 challenge mask state output.message =
          cachedHash g2 challenge mask state (output.registrationRoot config key) := by
      rw [targetHash]
      simp only [cachedHash, answer, role, ↓reduceIte, smul_smul, mul_assoc]
      simp [target, targetNonzero]
    rw [hashRelation]
    exact (registrations key member).2

/-- The causal shared-oracle simulator, with no access to the honest secret or challenge scalar. -/
noncomputable def solverAt (config : Config) (mask : Mask) (adversary : Adversary)
    (honest : G1Sub) (publicPoint challenge : G2Sub) : ProbComp G2Sub := do
  let result ← (simulateQ (impl g2 publicPoint challenge mask)
    (run config adversary honest)).run Security.State.init
  return extract config honest result.1 result.2

/-- A genuine adaptive aggregate coupling for the actual retained deposit checks.

The left event uses the real shared ordinary-message oracle, not a separate key-tag oracle.

The probability loss from selecting a suitable role mask is deliberately left in the event.

Accounting for masks, zero coefficients, signing overlaps and the honest-key distribution remains.
-/
theorem prEvent_verified_ready_le_solver (config : Config) (mask : Mask) (adversary : Adversary)
    (secret : Scalar) {challengeScalar : Scalar} (nonzero : challengeScalar ≠ 0) :
    Pr{let result ← (simulateQ (Security.impl g2 secret)
        (run config adversary (secret • g1))).run Security.State.init}[
      Verified config (secret • g1) result.1 (fun input => scalarAt input result.2 • g2) ∧
        Ready config mask (secret • g1) result.1
          (projectState mask challengeScalar result.2) ∧ ¬Bad mask result.2] ≤
      Pr{let guess ← solverAt config mask adversary (secret • g1) (secret • g2)
          (challengeScalar • g2)}[guess = secret • (challengeScalar • g2)] := by
  let event : Output × Security.State Scalar ByteArray → Prop := fun result =>
    Verified config (secret • g1) result.1 (cachedHash g2 (challengeScalar • g2) mask result.2) ∧
      Ready config mask (secret • g1) result.1 result.2
  have coupled := prEvent_run_projectState_le mask secret nonzero
    (run config adversary (secret • g1)) Security.State.init event
  have sameHash (state : Security.State Scalar ByteArray) :
      cachedHash g2 (challengeScalar • g2) mask (projectState mask challengeScalar state) =
        (fun input => scalarAt input state • g2) := by
    funext input
    exact cachedHash_projectState mask nonzero state input
  have sameEvent :
      (fun result : Output × Security.State Scalar ByteArray =>
        event (result.1, projectState mask challengeScalar result.2) ∧ ¬Bad mask result.2) =
      (fun result => Verified config (secret • g1) result.1
        (fun input => scalarAt input result.2 • g2) ∧
          Ready config mask (secret • g1) result.1
            (projectState mask challengeScalar result.2) ∧ ¬Bad mask result.2) := by
    funext result
    simp only [event, sameHash, and_assoc]
  rw [sameEvent] at coupled
  refine coupled.trans ?_
  unfold solverAt
  rw [bind_pure_comp, prEvent_map]
  change _ ≤ Pr{let result ← (simulateQ
    (impl g2 (secret • g2) (challengeScalar • g2) mask)
      (run config adversary (secret • g1))).run Security.State.init}[_]
  exact prEvent_mono _ _ _ fun result accepted =>
    extract_eq_of_verified_ready config mask secret (challengeScalar • g2) result.1 result.2
      accepted.1 accepted.2

end EthLib.Consensus.DepositRegistration.Adaptive
