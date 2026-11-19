module

public import EthLib.Networking.Proofs.Quic.Tls.Handshake

/-!
# Proofs: authentication along initialized libp2p QUIC handshakes

A trace retains the exact input state, incoming bytes and returned step of each accepted call.

Its initial state comes from `clientStart` or `serverStart`, with one fixed configuration.

The client also keeps the peer ID that it dialled fixed throughout the trace.

The results connect completion to CertificateVerify and Finished checks in that trace.

These checks are the authentication block of [RFC 8446 §§4.4.3 and 4.4.4][authentication].

They establish the order and inputs of the checks, without asserting signature unforgeability.

The caller still reassembles CRYPTO data and supplies fresh secret ephemeral keys.

[authentication]: https://www.rfc-editor.org/rfc/rfc8446#section-4.4
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls.Handshake

open EthLib.Base

/-- One accepted invocation, retaining its original state, complete input and exact output. -/
structure Observation where
  before : State
  input : FlightMessage
  result : Step

/-- A client's accepted calls, starting with its actual initialization result. -/
inductive ClientTrace (config : Config) (expected : ByteArray) :
    List Observation → State → Prop where
  | start {step : Step} (accepted : clientStart config = .ok step) :
      ClientTrace config expected [] step.state
  | next {observations : List Observation} {before : State} {input : FlightMessage}
      {result : Step} (prior : ClientTrace config expected observations before)
      (accepted : clientStep config expected before input = .ok result) :
      ClientTrace config expected (observations ++ [⟨before, input, result⟩]) result.state

/-- A server's accepted calls, starting with its actual initialization result. -/
inductive ServerTrace (config : Config) : List Observation → State → Prop where
  | start {state : State} (accepted : serverStart config = .ok state) :
      ServerTrace config [] state
  | next {observations : List Observation} {before : State} {input : FlightMessage}
      {result : Step} (prior : ServerTrace config observations before)
      (accepted : serverStep config before input = .ok result) :
      ServerTrace config (observations ++ [⟨before, input, result⟩]) result.state

private theorem receive_fields (state : State) (input : FlightMessage) (after : State)
    (accepted : receive state input = .ok after) :
    after.phase = state.phase ∧ after.peerChain = state.peerChain := by
  simp only [receive, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨_, _, rfl⟩ := accepted
  exact ⟨rfl, rfl⟩

private theorem emit_fields (state : State) (level : Level) (message : Message)
    (after : State) (output : FlightMessage)
    (accepted : emit state level message = .ok (after, output)) :
    after.phase = state.phase ∧ after.peerChain = state.peerChain := by
  simp only [emit, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at accepted
  obtain ⟨_, _, _, _, rfl, _⟩ := accepted
  exact ⟨rfl, rfl⟩

private theorem serverBoundary_fields (state after : State)
    (accepted : serverBoundary state = .ok after) :
    after.phase = state.phase ∧ after.peerChain = state.peerChain := by
  simp only [serverBoundary, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨_, _, _, _, rfl⟩ := accepted
  exact ⟨rfl, rfl⟩

private theorem sendCertificateVerify_fields (config : Config) (server : Bool)
    (offered : List Wire.CodePoint) (state after : State) (output : FlightMessage)
    (accepted : sendCertificateVerify config server offered state = .ok (after, output)) :
    after.phase = state.phase ∧ after.peerChain = state.peerChain := by
  simp only [sendCertificateVerify, bind_ok_iff] at accepted
  obtain ⟨_, _, _, _, emitted⟩ := accepted
  exact emit_fields _ _ _ _ _ emitted

private theorem sendFinished_fields (server : Bool) (state after : State)
    (output : FlightMessage)
    (accepted : sendFinished server state = .ok (after, output)) :
    after.phase = state.phase ∧ after.peerChain = state.peerChain := by
  simp only [sendFinished, bind_ok_iff] at accepted
  obtain ⟨_, _, _, _, emitted⟩ := accepted
  exact emit_fields _ _ _ _ _ emitted

private theorem complete_fields (config : Config) (expected : Option ByteArray) (state : State)
    (output : List FlightMessage) (step : Step)
    (accepted : complete config expected state output = .ok step) :
    step.state.phase = .complete ∧ step.state.peerChain = state.peerChain ∧
      ∀ result, step.completion = some result → result.peerChain = state.peerChain := by
  simp only [complete, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨_, _, _, _, _, _, rfl⟩ := accepted
  exact ⟨rfl, rfl, fun _ h => by cases Option.some.inj h; rfl⟩

private theorem clientStart_phase (config : Config) (step : Step)
    (accepted : clientStart config = .ok step) : step.state.phase = .serverHello := by
  simp only [clientStart, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨_, _, _, _, _, emitted, rfl⟩ := accepted
  exact (emit_fields _ _ _ _ _ emitted).1

private theorem serverStart_phase (config : Config) (state : State)
    (accepted : serverStart config = .ok state) : state.phase = .clientHello := by
  simp only [serverStart, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨_, _, _, _, rfl⟩ := accepted
  rfl

private theorem clientRetry_phase (config : Config) (state : State) (hello : ClientHello)
    (server : ServerHello) (input : FlightMessage) (step : Step)
    (accepted : clientRetry config state hello server input = .ok step) :
    step.state.phase = state.phase := by
  simp only [clientRetry, bind_ok_iff] at accepted
  obtain ⟨_, _, _, _, group, _, cookie, _, _, _, accepted⟩ := accepted
  cases group <;>
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  all_goals
    aesop (add safe forward [receive_fields, emit_fields])

private theorem clientServerHello_phase (config : Config) (state : State)
    (server : ServerHello) (input : FlightMessage) (step : Step)
    (accepted : clientServerHello config state server input = .ok step) :
    step.state.phase = state.phase ∨ step.state.phase = .encryptedExtensions := by
  simp only [clientServerHello, bind_ok_iff, pure, Except.pure] at accepted
  aesop (config := { maxRuleApplicationDepth := 100 })
    (add norm simp [bind_ok_iff, pure, Except.pure, Except.ok.injEq])
    (add safe forward clientRetry_phase)

private theorem clientEncryptedExtensions_phase (state : State) (extensions : List Extension)
    (input : FlightMessage) (step : Step)
    (accepted : clientEncryptedExtensions state extensions input = .ok step) :
    step.state.phase = .certificateRequest := by
  simp only [clientEncryptedExtensions, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  rfl

private theorem clientCertificateRequest_phase (config : Config) (state : State)
    (request : CertificateRequest) (input : FlightMessage) (step : Step)
    (accepted : clientCertificateRequest config state request input = .ok step) :
    step.state.phase = .serverCertificate := by
  simp only [clientCertificateRequest, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  rfl

private theorem clientFinished_fields (config : Config) (expected : ByteArray) (state : State)
    (value : ByteArray) (input : FlightMessage) (step : Step)
    (accepted : clientFinished config expected state value input = .ok step) :
    step.state.phase = .complete ∧ step.state.peerChain = state.peerChain ∧
      ∀ result, step.completion = some result → result.peerChain = state.peerChain := by
  simp only [clientFinished, bind_ok_iff] at accepted
  rcases accepted with ⟨_, _, _, received, _, boundary, _, _, _, _,
    _, certificate, _, signature, _, finished, accepted⟩
  have final := complete_fields _ _ _ _ _ accepted
  have r := receive_fields _ _ _ received
  have b := serverBoundary_fields _ _ boundary
  have c := emit_fields _ _ _ _ _ certificate
  have v := sendCertificateVerify_fields _ _ _ _ _ _ signature
  have f := sendFinished_fields _ _ _ _ finished
  exact ⟨final.1, final.2.1.trans (f.2.trans (v.2.trans (c.2.trans (b.2.trans r.2)))),
    fun result h => (final.2.2 result h).trans
      (f.2.trans (v.2.trans (c.2.trans (b.2.trans r.2))))⟩

private theorem clientFinished_checked (config : Config) (expected : ByteArray) (state : State)
    (value : ByteArray) (input : FlightMessage) (step : Step)
    (accepted : clientFinished config expected state value input = .ok step) :
    checkFinished true state value = .ok () := by
  simp only [clientFinished, bind_ok_iff] at accepted
  obtain ⟨checked, valid, _⟩ := accepted
  cases checked
  exact valid

private theorem serverFlight_phase (config : Config) (state : State) (hello : ClientHello)
    (suite group : Wire.CodePoint) (share : KeyShareEntry) (step : Step)
    (accepted : serverFlight config state hello suite group share = .ok step) :
    step.state.phase = .clientCertificate := by
  simp only [serverFlight, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  rfl

private theorem serverClientHello_phase (config : Config) (state : State) (hello : ClientHello)
    (input : FlightMessage) (step : Step)
    (accepted : serverClientHello config state hello input = .ok step) :
    step.state.phase = state.phase ∨ step.state.phase = .clientCertificate := by
  simp only [serverClientHello, bind_ok_iff, pure, Except.pure] at accepted
  aesop (config := { maxRuleApplicationDepth := 100 })
    (add norm simp [bind_ok_iff, pure, Except.pure, Except.ok.injEq])
    (add safe forward [serverFlight_phase, receive_fields, emit_fields])

private theorem clientStep_finished_origin (config : Config) (expected : ByteArray)
    (state : State) (input : FlightMessage) (step : Step)
    (accepted : clientStep config expected state input = .ok step)
    (phase : step.state.phase = .serverFinished) :
    state.phase = .serverCertificateVerify ∧ ∃ algorithm signature,
      readMessage .handshake input = .ok (.certificateVerify algorithm signature) ∧
      step.state.peerChain = state.peerChain := by
  simp only [clientStep] at accepted
  aesop (config := { maxRuleApplicationDepth := 100 })
    (add norm simp [bind_ok_iff, pure, Except.pure, Except.ok.injEq])
    (add safe forward [clientServerHello_phase, clientEncryptedExtensions_phase,
      clientCertificateRequest_phase, clientFinished_fields, receive_fields])

private theorem serverStep_finished_origin (config : Config) (state : State)
    (input : FlightMessage) (step : Step)
    (accepted : serverStep config state input = .ok step)
    (phase : step.state.phase = .clientFinished) :
    state.phase = .clientCertificateVerify ∧ ∃ algorithm signature,
      readMessage .handshake input = .ok (.certificateVerify algorithm signature) ∧
      step.state.peerChain = state.peerChain := by
  simp only [serverStep] at accepted
  aesop (config := { maxRuleApplicationDepth := 100 })
    (add norm simp [bind_ok_iff, pure, Except.pure, Except.ok.injEq])
    (add safe forward [serverClientHello_phase, complete_fields, receive_fields])

private theorem clientStep_completion_origin (config : Config) (expected : ByteArray)
    (state : State) (input : FlightMessage) (step : Step) (result : Completion)
    (accepted : clientStep config expected state input = .ok step)
    (completed : step.completion = some result) :
    state.phase = .serverFinished ∧ result.peerChain = state.peerChain ∧ ∃ value,
      readMessage .handshake input = .ok (.finished value) ∧
      checkFinished true state value = .ok () := by
  obtain ⟨final, output, boundary⟩ :=
    clientStep_complete config expected state input step result accepted completed
  have phase := (complete_fields _ _ _ _ _ boundary).1
  simp only [clientStep] at accepted
  aesop (config := { maxRuleApplicationDepth := 100 })
    (add norm simp [bind_ok_iff, pure, Except.pure, Except.ok.injEq])
    (add safe forward [clientServerHello_phase, clientEncryptedExtensions_phase,
      clientCertificateRequest_phase, clientFinished_fields, clientFinished_checked])

private theorem serverStep_completion_origin (config : Config) (state : State)
    (input : FlightMessage) (step : Step) (result : Completion)
    (accepted : serverStep config state input = .ok step)
    (completed : step.completion = some result) :
    state.phase = .clientFinished ∧ result.peerChain = state.peerChain ∧ ∃ value,
      readMessage .handshake input = .ok (.finished value) ∧
      checkFinished false state value = .ok () := by
  obtain ⟨final, output, boundary⟩ :=
    serverStep_complete config state input step result accepted completed
  have phase := (complete_fields _ _ _ _ _ boundary).1
  simp only [serverStep] at accepted
  aesop (config := { maxRuleApplicationDepth := 100 })
    (add norm simp [bind_ok_iff, pure, Except.pure, Except.ok.injEq])
    (add safe forward [serverClientHello_phase, receive_fields, complete_fields])

/-- A retained client call verified the server's signature on its exact saved transcript. -/
def ClientCertificateObserved (config : Config) (expected : ByteArray)
    (observations : List Observation) (chain : List ByteArray) : Prop :=
  ∃ observation ∈ observations, observation.before.peerChain = chain ∧
    observation.before.phase = .serverCertificateVerify ∧ ∃ algorithm signature,
      readMessage .handshake observation.input =
        .ok (.certificateVerify algorithm signature) ∧
      clientStep config expected observation.before observation.input = .ok observation.result

/-- A retained server call verified the client's signature on its exact saved transcript. -/
def ServerCertificateObserved (config : Config) (observations : List Observation)
    (chain : List ByteArray) : Prop :=
  ∃ observation ∈ observations, observation.before.peerChain = chain ∧
    observation.before.phase = .clientCertificateVerify ∧ ∃ algorithm signature,
      readMessage .handshake observation.input =
        .ok (.certificateVerify algorithm signature) ∧
      serverStep config observation.before observation.input = .ok observation.result

/-- A client waiting for Finished reached it by checking CertificateVerify in the same trace. -/
theorem ClientTrace.certificate_verify {config : Config} {expected : ByteArray}
    {observations : List Observation} {state : State}
    (trace : ClientTrace config expected observations state)
    (phase : state.phase = .serverFinished) :
    ClientCertificateObserved config expected observations state.peerChain := by
  cases trace with
  | start accepted =>
    have initial := clientStart_phase _ _ accepted
    rw [initial] at phase
    cases phase
  | @next observations before input result _ accepted =>
    obtain ⟨atCertificateVerify, algorithm, signature, parsed, sameChain⟩ :=
      clientStep_finished_origin _ _ _ _ _ accepted phase
    exact ⟨⟨before, input, result⟩, by simp, sameChain.symm, atCertificateVerify,
      algorithm, signature, parsed, accepted⟩

/-- A server waiting for Finished reached it by checking CertificateVerify in the same trace. -/
theorem ServerTrace.certificate_verify {config : Config} {observations : List Observation}
    {state : State} (trace : ServerTrace config observations state)
    (phase : state.phase = .clientFinished) :
    ServerCertificateObserved config observations state.peerChain := by
  cases trace with
  | start accepted =>
    have initial := serverStart_phase _ _ accepted
    rw [initial] at phase
    cases phase
  | @next observations before input result _ accepted =>
    obtain ⟨atCertificateVerify, algorithm, signature, parsed, sameChain⟩ :=
      serverStep_finished_origin _ _ _ _ accepted phase
    exact ⟨⟨before, input, result⟩, by simp, sameChain.symm, atCertificateVerify,
      algorithm, signature, parsed, accepted⟩

/-- A client's observed CertificateVerify used an allowed scheme and the authenticated chain. -/
theorem ClientCertificateObserved.signature {config : Config} {expected : ByteArray}
    {observations : List Observation} {chain : List ByteArray}
    (observed : ClientCertificateObserved config expected observations chain) :
    ∃ observation ∈ observations, ∃ algorithm signature peer,
      observation.before.peerChain = chain ∧
      readMessage .handshake observation.input =
        .ok (.certificateVerify algorithm signature) ∧
      algorithm ∈ config.policy.signatureSchemes ∧ algorithm.val = 0x0403 ∧
      authenticate config (some expected) chain = .ok peer ∧
      Libp2p.Tls.verifyP256 peer.certificate.spki
        (certificateVerifyInput true observation.before.transcript.hash) signature = true := by
  obtain ⟨observation, member, chain, phase, algorithm, signature, parsed, accepted⟩ := observed
  obtain ⟨_, _, _, _, _, allowed, implemented, peer, authenticated, verified⟩ :=
    clientStep_certificateVerify _ _ _ _ _ _ _ phase parsed accepted
  exact ⟨observation, member, algorithm, signature, peer, chain, parsed, allowed, implemented,
    chain ▸ authenticated, verified⟩

/-- A server's observed CertificateVerify used an allowed scheme and the authenticated chain. -/
theorem ServerCertificateObserved.signature {config : Config} {observations : List Observation}
    {chain : List ByteArray}
    (observed : ServerCertificateObserved config observations chain) :
    ∃ observation ∈ observations, ∃ algorithm signature peer,
      observation.before.peerChain = chain ∧
      readMessage .handshake observation.input =
        .ok (.certificateVerify algorithm signature) ∧
      algorithm ∈ config.policy.signatureSchemes ∧ algorithm.val = 0x0403 ∧
      authenticate config none chain = .ok peer ∧
      Libp2p.Tls.verifyP256 peer.certificate.spki
        (certificateVerifyInput false observation.before.transcript.hash) signature = true := by
  obtain ⟨observation, member, chain, phase, algorithm, signature, parsed, accepted⟩ := observed
  obtain ⟨_, _, _, _, _, allowed, implemented, peer, authenticated, verified⟩ :=
    serverStep_certificateVerify _ _ _ _ _ _ phase parsed accepted
  exact ⟨observation, member, algorithm, signature, peer, chain, parsed, allowed, implemented,
    chain ▸ authenticated, verified⟩

/-- Completing a client checks Finished after the same chain's CertificateVerify in its trace. -/
theorem ClientTrace.completion_authenticated {config : Config} {expected : ByteArray}
    {observations : List Observation} {state : State} {input : FlightMessage} {step : Step}
    {result : Completion} (trace : ClientTrace config expected observations state)
    (accepted : clientStep config expected state input = .ok step)
    (completed : step.completion = some result) :
    ClientCertificateObserved config expected observations result.peerChain ∧
      ∃ value, readMessage .handshake input = .ok (.finished value) ∧
        checkFinished true state value = .ok () := by
  obtain ⟨phase, chain, finished⟩ :=
    clientStep_completion_origin _ _ _ _ _ _ accepted completed
  rw [chain]
  exact ⟨trace.certificate_verify phase, finished⟩

/-- Completing a server checks Finished after the same chain's CertificateVerify in its trace. -/
theorem ServerTrace.completion_authenticated {config : Config}
    {observations : List Observation} {state : State} {input : FlightMessage} {step : Step}
    {result : Completion} (trace : ServerTrace config observations state)
    (accepted : serverStep config state input = .ok step)
    (completed : step.completion = some result) :
    ServerCertificateObserved config observations result.peerChain ∧
      ∃ value, readMessage .handshake input = .ok (.finished value) ∧
        checkFinished false state value = .ok () := by
  obtain ⟨phase, chain, finished⟩ :=
    serverStep_completion_origin _ _ _ _ _ accepted completed
  rw [chain]
  exact ⟨trace.certificate_verify phase, finished⟩

/-- A client cannot complete a trace containing no CertificateVerify message. -/
theorem ClientTrace.no_completion_without_certificateVerify {config : Config}
    {expected : ByteArray} {observations : List Observation} {state : State}
    {input : FlightMessage} {step : Step} {result : Completion}
    (trace : ClientTrace config expected observations state)
    (absent : ∀ observation ∈ observations, ∀ algorithm signature,
      readMessage .handshake observation.input ≠
        .ok (.certificateVerify algorithm signature))
    (completed : step.completion = some result) :
    clientStep config expected state input ≠ .ok step := by
  intro accepted
  obtain ⟨observed, _⟩ := trace.completion_authenticated accepted completed
  obtain ⟨observation, member, _, _, algorithm, signature, parsed, _⟩ := observed
  exact absent observation member algorithm signature parsed

/-- A server cannot complete a trace containing no CertificateVerify message. -/
theorem ServerTrace.no_completion_without_certificateVerify {config : Config}
    {observations : List Observation} {state : State} {input : FlightMessage}
    {step : Step} {result : Completion} (trace : ServerTrace config observations state)
    (absent : ∀ observation ∈ observations, ∀ algorithm signature,
      readMessage .handshake observation.input ≠
        .ok (.certificateVerify algorithm signature))
    (completed : step.completion = some result) : serverStep config state input ≠ .ok step := by
  intro accepted
  obtain ⟨observed, _⟩ := trace.completion_authenticated accepted completed
  obtain ⟨observation, member, _, _, algorithm, signature, parsed, _⟩ := observed
  exact absent observation member algorithm signature parsed

/-- A client rejects Finished where it still requires the server's CertificateVerify. -/
theorem clientStep_finished_before_certificateVerify (config : Config) (expected : ByteArray)
    (state : State) (input : FlightMessage) (value : ByteArray)
    (phase : state.phase = .serverCertificateVerify)
    (message : readMessage .handshake input = .ok (.finished value)) :
    clientStep config expected state input = .error .unexpectedMessage := by
  simp [clientStep, phase, message, bind, Except.bind]
  rfl

/-- A server rejects Finished where it still requires the client's CertificateVerify. -/
theorem serverStep_finished_before_certificateVerify (config : Config) (state : State)
    (input : FlightMessage) (value : ByteArray)
    (phase : state.phase = .clientCertificateVerify)
    (message : readMessage .handshake input = .ok (.finished value)) :
    serverStep config state input = .error .unexpectedMessage := by
  simp [serverStep, phase, message, bind, Except.bind]
  rfl

end EthLib.Networking.Quic.Tls.Handshake
