module

public import EthLib.Consensus.Proofs.DepositRegistration
public import EthLib.Consensus.Proofs.Transition.Operations

/-!
# Proofs: validator keys retain their deposit-signature witnesses

A new validator key comes with an accepted deposit signature for that exact key.

A top-up of an existing key need not have a valid signature, and does not replace its witness.

The results follow the registration paths before Electra and from Electra.

They also cover finite lists of block deposits and of pending deposits.

They do not assert knowledge of a secret key or an aggregate-signature security bound.
-/

@[expose] public section

namespace EthLib.Consensus.DepositRegistration

open Base Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config}
  {state after : BeaconState preset fork}

/-- A deposit with an accepted BLS signature for this exact public key. -/
def HasWitness (config : Config) (pubkey : BLSPubkey) : Prop :=
  ∃ data : DepositData, data.pubkey = pubkey ∧
    isValidDepositSignature config .bls data.pubkey data.withdrawalCredentials data.amount
      data.signature = .ok true

/-- Each key in the current registry has a deposit-signature witness.

The witness records the credentials and amount that were signed at registration.

They need not equal the validator's later credentials, balance or effective balance. -/
def Registered (config : Config) (state : BeaconState preset fork) : Prop :=
  ∀ (index : Nat) (validator : Validator), state.validators.data[index]? = some validator →
    HasWitness config validator.pubkey

/-- An empty registry needs no witnesses. -/
theorem registered_of_empty (empty : state.validators.data = #[]) : Registered config state := by
  intro index validator found
  simp [empty] at found

/-- An unchanged registry keeps all witnesses. -/
theorem Registered.of_validators_eq (registered : Registered config state)
    (same : after.validators = state.validators) : Registered config after := by
  intro index validator found
  rw [same] at found
  exact registered index validator found

/-- Adding a validator with an accepted deposit keeps the witnesses of all existing keys. -/
theorem Registered.addValidatorToRegistry (registered : Registered config state)
    {data : DepositData} {credited : Gwei}
    (accepted : isValidDepositSignature config .bls data.pubkey data.withdrawalCredentials
      data.amount data.signature = .ok true)
    (added : addValidatorToRegistry state data.pubkey data.withdrawalCredentials credited =
      .ok after) : Registered config after := by
  intro index validator found
  rcases addValidatorToRegistry_validator added found with old | fresh
  · exact registered index validator old
  · subst validator
    exact ⟨data, rfl, accepted⟩

/-- Crediting a pending deposit keeps registration witnesses, including on unsigned top-ups. -/
theorem Registered.applyPendingDeposit (registered : Registered config state)
    {deposit : PendingDeposit}
    (computed : applyPendingDeposit config .bls state deposit = .ok after) :
    Registered config after := by
  unfold Consensus.applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact registered
    simp only [bind_ok_iff] at computed
    obtain ⟨valid, checked, computed⟩ := computed
    cases valid with
    | false =>
      cases computed
      exact registered
    | true =>
      exact registered.addValidatorToRegistry
        (data := ⟨deposit.pubkey, deposit.withdrawalCredentials, deposit.amount,
          deposit.signature⟩) checked computed
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, increased⟩ := computed
    exact registered.of_validators_eq (increaseBalance_validators increased)

/-- Queuing a pending deposit does not change any registration witness. -/
theorem Registered.addPendingDeposit (registered : Registered config state)
    {electra : .pectra ≤ fork} {deposit : PendingDeposit}
    (queued : addPendingDeposit state electra deposit = .ok after) : Registered config after := by
  obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
  exact registered

/-- The Electra registration path keeps witnesses, with the signed amount before zero credit.

A newly registered validator starts at zero balance, but its witness retains the deposited amount.
-/
theorem Registered.applyDepositElectra (registered : Registered config state)
    {electra : .pectra ≤ fork} {data : DepositData}
    (computed : applyDepositElectra config .bls state electra data.pubkey
      data.withdrawalCredentials data.amount data.signature = .ok after) :
    Registered config after := by
  unfold Consensus.applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨valid, checked, computed⟩ := computed
    cases valid with
    | false =>
      cases computed
      exact registered
    | true =>
      change (do
        let middle ← Consensus.addValidatorToRegistry state data.pubkey
          data.withdrawalCredentials 0
        liftAccessor (Consensus.addPendingDeposit middle electra
          ⟨data.pubkey, data.withdrawalCredentials, data.amount, data.signature,
            GENESIS_SLOT⟩)) = .ok after at computed
      simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨middle, added, queued⟩ := computed
      exact (registered.addValidatorToRegistry checked added).addPendingDeposit queued
  · exact registered.addPendingDeposit (liftAccessor_ok.mp computed)

/-- Applying a block deposit keeps the signature witness of every registered key. -/
theorem Registered.applyDeposit (registered : Registered config state) {data : DepositData}
    (computed : applyDeposit config .bls state data.pubkey data.withdrawalCredentials data.amount
      data.signature = .ok after) : Registered config after := by
  unfold Consensus.applyDeposit at computed
  split at computed
  · exact registered.applyDepositElectra computed
  · exact registered.applyPendingDeposit computed

/-- A finite sequence of pending deposits keeps the original registration witnesses. -/
theorem Registered.foldlM_applyPendingDeposit (registered : Registered config state)
    {deposits : List PendingDeposit}
    (computed : deposits.foldlM (Consensus.applyPendingDeposit config .bls) state = .ok after) :
    Registered config after := by
  induction deposits generalizing state with
  | nil =>
    cases computed
    exact registered
  | cons deposit rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨next, step, computed⟩ := computed
    exact ih (registered.applyPendingDeposit step) computed

/-- A finite sequence of block deposits keeps the original registration witnesses. -/
theorem Registered.foldlM_applyDeposit (registered : Registered config state)
    {deposits : List DepositData}
    (computed : deposits.foldlM (fun state data => Consensus.applyDeposit config .bls state
      data.pubkey data.withdrawalCredentials data.amount data.signature) state = .ok after) :
    Registered config after := by
  induction deposits generalizing state with
  | nil =>
    cases computed
    exact registered
  | cons data rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨next, step, computed⟩ := computed
    exact ih (registered.applyDeposit step) computed

/-- A block deposit that passes its Merkle proof also keeps every registration witness. -/
theorem Registered.processDeposit (registered : Registered config state)
    {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config .bls before state deposit = .ok after) :
    Registered config after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  have prior : Registered config { state with eth1DepositIndex := fun _ => next } := registered
  exact prior.applyDeposit applied

/-- Every key after a finite sequence of accepted block deposits keeps a registration witness.

The result also covers invalid signatures on known-key top-ups, which need no fresh witness. -/
theorem Registered.foldlM_processDeposit (registered : Registered config state)
    {before : fork < .hegota} {deposits : List Deposit}
    (computed : deposits.foldlM (Consensus.processDeposit config .bls before) state = .ok after) :
    Registered config after := by
  induction deposits generalizing state with
  | nil =>
    cases computed
    exact registered
  | cons deposit rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨next, step, computed⟩ := computed
    exact ih (registered.processDeposit step) computed

/-- Starting from an empty registry, every registered key has an accepted deposit signature.

The trace runs the actual block-deposit transition, including each deposit's Merkle proof. -/
theorem registered_of_processDeposits_from_empty {before : fork < .hegota}
    {deposits : List Deposit} (empty : state.validators.data = #[])
    (computed : deposits.foldlM (processDeposit config .bls before) state = .ok after) :
    Registered config after :=
  (registered_of_empty empty).foldlM_processDeposit computed

end EthLib.Consensus.DepositRegistration
