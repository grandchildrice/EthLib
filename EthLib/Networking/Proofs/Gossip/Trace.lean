module

public import EthLib.Networking.Proofs.Gossip.Membership
public import EthLib.Networking.Proofs.Gossip.Heartbeat
public import EthLib.Networking.Proofs.Gossip.Cache

/-!
# Proofs: the seen cache across mixed gossipsub operations

The events below call the router's receive, heartbeat, join, leave and publish operations.

They keep one parameter set and one message ID function throughout a trace.

Client choices, peer standing and validation may change at every event.

An unexpired seen entry survives every event, including a heartbeat.

Forwarding and delivery record the ID, and a new publish does so even without a recipient.

That entry prevents forwarding and delivery of its ID until its original expiry.

The result holds across any finite mixture of events, until the entry's lifetime ends.

IWANT answers are separate from forwarding and are not suppressed by this result.

The source is [gossipsub v1.0, "Message Cache" and "Message Processing"][gossip].

[gossip]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-cache
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Trace

open EthLib.Networking.Gossip

/-- An input to one of the router's operations, with its client choices. -/
inductive Action where
  | receive (backoffMs pruneBackoffMs : Nat) (standing : PeerId → Standing)
      (validate : Message → ValidationResult) (source : PeerId) (rpc : Rpc)
  | heartbeat (choices : ClientChoices) (select : Select) (rank : Rank)
      (standing : PeerId → Standing)
  | join (select : Select) (standing : PeerId → Standing) (topic : String)
  | leave (choices : ClientChoices) (topic : String)
  | publish (choices : ClientChoices) (select : Select) (standing : PeerId → Standing)
      (message : Message)

/-- One router input at a time measured in milliseconds. -/
structure Event where
  time : Nat
  action : Action

/-- Execute the named operation with the trace's original parameters and message ID function. -/
def Event.step (p : GossipsubParameters) (msgId : Message → MessageId) (event : Event)
    (state : RouterState) : RouterState × Out :=
  match event.action with
  | .receive backoff pruneBackoff standing validate source rpc =>
    receiveRpc p backoff pruneBackoff standing msgId validate event.time source rpc state
  | .heartbeat choices select rank standing =>
    heartbeat p choices select rank standing event.time state
  | .join select standing topic => join p select standing event.time topic state
  | .leave choices topic => leave choices event.time topic state
  | .publish choices select standing message =>
    publish p choices select standing msgId event.time message state

/-- The state after executing each event, in list order. -/
def run (p : GossipsubParameters) (msgId : Message → MessageId) (state : RouterState)
    (events : List Event) : RouterState :=
  events.foldl (fun state event => (event.step p msgId state).1) state

/-- An output forwards or delivers at least one message of this ID.

Answers to IWANT requests are not forwarding and are not counted. -/
def Emits (msgId : Message → MessageId) (id : MessageId) (output : Out) : Prop :=
  ∃ message, msgId message = id ∧
    ((∃ peer, (peer, message) ∈ output.forward) ∨ message ∈ output.delivered)

/-- Choosing the peers of a publish leaves the seen cache intact. -/
private theorem publishPeers_seen (p : GossipsubParameters) (choices : ClientChoices)
    (select : Select) (standing : PeerId → Standing) (now : Nat) (topic : String)
    (state : RouterState) :
    (publishPeers p choices select standing now topic state).1.seen = state.seen := by
  unfold publishPeers
  split
  · rfl
  · split <;> rfl

/-- A heartbeat keeps exactly those seen entries whose lifetime has not ended. -/
theorem heartbeat_seen_iff (p : GossipsubParameters) (choices : ClientChoices)
    (select : Select) (rank : Rank) (standing : PeerId → Standing) (now : Nat)
    (state : RouterState) (id : MessageId) (inserted : Nat) :
    (id, inserted) ∈ (heartbeat p choices select rank standing now state).1.seen.entries ↔
      (id, inserted) ∈ state.seen.entries ∧ now < inserted + p.seen_ttl * 1000 := by
  simp [heartbeat, SeenCache.expire]

/-- At the lifetime boundary and afterwards, a heartbeat removes the original entry. -/
theorem heartbeat_seen_expired (p : GossipsubParameters) (choices : ClientChoices)
    (select : Select) (rank : Rank) (standing : PeerId → Standing) (now : Nat)
    (state : RouterState) (id : MessageId) (inserted : Nat)
    (expired : inserted + p.seen_ttl * 1000 ≤ now) :
    (id, inserted) ∉ (heartbeat p choices select rank standing now state).1.seen.entries := by
  rw [heartbeat_seen_iff]
  omega

/-- Every operation retains an entry that has not expired at the time of that operation. -/
theorem step_seen (p : GossipsubParameters) (msgId : Message → MessageId)
    (event : Event) (state : RouterState) (id : MessageId) (inserted : Nat)
    (present : (id, inserted) ∈ state.seen.entries)
    (live : event.time < inserted + p.seen_ttl * 1000) :
    (id, inserted) ∈ (event.step p msgId state).1.seen.entries := by
  rcases event with ⟨now, action⟩
  cases action with
  | receive backoff pruneBackoff standing validate source rpc =>
    exact Router.receiveRpc_seen p backoff pruneBackoff standing msgId validate now source rpc
      state (id, inserted) present
  | heartbeat choices select rank standing =>
    exact (heartbeat_seen_iff p choices select rank standing now state id inserted).2
      ⟨present, live⟩
  | join select standing topic =>
    simp only [Event.step, join]
    split <;> exact present
  | leave choices topic =>
    simp only [Event.step, leave]
    split <;> exact present
  | publish choices select standing message =>
    simp only [Event.step, publish]
    split
    · exact present
    · rw [publishPeers_seen]
      exact List.mem_cons_of_mem _ present

/-- A new publish records its message ID even when it has no peer to forward to. -/
theorem publish_seen (p : GossipsubParameters) (msgId : Message → MessageId)
    (choices : ClientChoices) (select : Select) (standing : PeerId → Standing)
    (now : Nat) (message : Message) (state : RouterState)
    (fresh : state.seen.contains now (p.seen_ttl * 1000) (msgId message) = false) :
    (msgId message, now) ∈
      (publish p choices select standing msgId now message state).1.seen.entries := by
  simp only [publish, fresh, Bool.false_eq_true, ↓reduceIte]
  rw [publishPeers_seen]
  exact List.mem_cons_self

/-- Every forwarded or delivered ID is recorded at the time of its emitting event. -/
theorem step_emits_seen (p : GossipsubParameters) (msgId : Message → MessageId)
    (event : Event) (state : RouterState) (id : MessageId)
    (emitted : Emits msgId id (event.step p msgId state).2) :
    (id, event.time) ∈ (event.step p msgId state).1.seen.entries := by
  rcases event with ⟨now, action⟩
  cases action with
  | receive backoff pruneBackoff standing validate source rpc =>
    rcases emitted with ⟨message, rfl, forwarded | delivered⟩
    · obtain ⟨peer, sent⟩ := forwarded
      exact Router.receiveRpc_forward_seen p backoff pruneBackoff standing msgId validate now
        source rpc state (Or.inl sent)
    · exact Router.receiveRpc_forward_seen p backoff pruneBackoff standing msgId validate now
        source rpc state (q := default) (Or.inr delivered)
  | heartbeat choices select rank standing =>
    simp [Event.step, heartbeat, Emits] at emitted
  | join select standing topic =>
    by_cases joined : topic ∈ state.topics <;>
      simp [Event.step, join, joined, Emits] at emitted
  | leave choices topic =>
    by_cases joined : topic ∈ state.topics <;>
      simp [Event.step, leave, joined, Emits] at emitted
  | publish choices select standing original =>
    rcases emitted with ⟨message, rfl, forwarded | delivered⟩
    · obtain ⟨peer, sent⟩ := forwarded
      have same := Membership.publish_forward_message p choices select standing msgId now
        state sent
      subst message
      by_cases seen : state.seen.contains now (p.seen_ttl * 1000) (msgId original) = true
      · simp [Event.step, publish, seen] at sent
      · exact publish_seen p msgId choices select standing now original state
          (by simpa using seen)
    · simp only [Event.step, publish] at delivered
      split at delivered <;> simp at delivered

/-- An operation does not forward or deliver an ID whose seen entry is still live. -/
theorem step_seen_skip (p : GossipsubParameters) (msgId : Message → MessageId)
    (event : Event) (state : RouterState) (id : MessageId) (inserted : Nat)
    (present : (id, inserted) ∈ state.seen.entries)
    (live : event.time < inserted + p.seen_ttl * 1000) :
    ¬ Emits msgId id (event.step p msgId state).2 := by
  rcases event with ⟨now, action⟩
  intro emitted
  cases action with
  | receive backoff pruneBackoff standing validate source rpc =>
    rcases emitted with ⟨message, same, forwarded | delivered⟩
    · obtain ⟨peer, sent⟩ := forwarded
      exact (Router.receiveRpc_seen_skip p backoff pruneBackoff standing msgId validate now source
        rpc state present live same).1 sent
    · exact (Router.receiveRpc_seen_skip p backoff pruneBackoff standing msgId validate now source
        rpc state (q := default) present live same).2 delivered
  | heartbeat choices select rank standing =>
    simp [Event.step, heartbeat, Emits] at emitted
  | join select standing topic =>
    by_cases joined : topic ∈ state.topics <;>
      simp [Event.step, join, joined, Emits] at emitted
  | leave choices topic =>
    by_cases joined : topic ∈ state.topics <;>
      simp [Event.step, leave, joined, Emits] at emitted
  | publish choices select standing original =>
    rcases emitted with ⟨message, same, forwarded | delivered⟩
    · obtain ⟨peer, sent⟩ := forwarded
      have equal := Membership.publish_forward_message p choices select standing msgId now
        state sent
      subst message
      have seen : state.seen.contains now (p.seen_ttl * 1000) (msgId original) = true := by
        simp only [SeenCache.contains, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨(id, inserted), present, same.symm, live⟩
      simp [Event.step, publish, seen] at sent
    · simp only [Event.step, publish] at delivered
      split at delivered <;> simp at delivered

/-- A finite mixed trace keeps an entry when every event precedes its expiry. -/
theorem run_seen (p : GossipsubParameters) (msgId : Message → MessageId)
    (events : List Event) (state : RouterState) (id : MessageId) (inserted : Nat)
    (present : (id, inserted) ∈ state.seen.entries)
    (live : ∀ event ∈ events, event.time < inserted + p.seen_ttl * 1000) :
    (id, inserted) ∈ (run p msgId state events).seen.entries := by
  induction events generalizing state with
  | nil => exact present
  | cons event events ih =>
    exact ih (event.step p msgId state).1
      (step_seen p msgId event state id inserted present (live event (by simp)))
      (fun e he => live e (by simp [he]))

/-- Nondecreasing event times keep every intermediate event before the final time. -/
private theorem time_le_last {events : List Event} {last : Event}
    (ordered : (events ++ [last]).Pairwise (fun a b => a.time ≤ b.time))
    (event : Event) (member : event ∈ events) : event.time ≤ last.time :=
  ordered.rel_of_mem_append member (by simp)

/-- Once an event emits an ID, a later event cannot emit it before the lifetime ends.

Every intermediate operation is executed, including heartbeat expiry.

The timestamps of the intermediate and final events are nondecreasing.

The initial state and every client choice are otherwise arbitrary. -/
theorem emits_once (p : GossipsubParameters) (msgId : Message → MessageId)
    (first last : Event) (between : List Event) (state : RouterState) (id : MessageId)
    (emitted : Emits msgId id (first.step p msgId state).2)
    (ordered : (first :: between ++ [last]).Pairwise (fun a b => a.time ≤ b.time))
    (live : last.time < first.time + p.seen_ttl * 1000) :
    ¬ Emits msgId id
      (last.step p msgId (run p msgId (first.step p msgId state).1 between)).2 := by
  have recorded := step_emits_seen p msgId first state id emitted
  have preserved := run_seen p msgId between (first.step p msgId state).1 id first.time recorded
    (fun event member => Nat.lt_of_le_of_lt
      (time_le_last ordered.tail event member) live)
  exact step_seen_skip p msgId last _ id first.time preserved live

/-- A new publish prevents every later forwarding or delivery of its ID until its expiry.

This also holds when the initial publish has no recipient.

Intermediate events may include heartbeat, topic membership, publishing and received RPCs. -/
theorem publish_once (p : GossipsubParameters) (msgId : Message → MessageId)
    (choices : ClientChoices) (select : Select) (standing : PeerId → Standing)
    (now : Nat) (message : Message) (state : RouterState) (between : List Event) (last : Event)
    (fresh : state.seen.contains now (p.seen_ttl * 1000) (msgId message) = false)
    (ordered : (between ++ [last]).Pairwise (fun a b => a.time ≤ b.time))
    (live : last.time < now + p.seen_ttl * 1000) :
    ¬ Emits msgId (msgId message)
      (last.step p msgId
        (run p msgId (publish p choices select standing msgId now message state).1 between)).2 := by
  have recorded := publish_seen p msgId choices select standing now message state fresh
  have preserved := run_seen p msgId between _ (msgId message) now recorded
    (fun event member => Nat.lt_of_le_of_lt (time_le_last ordered event member) live)
  exact step_seen_skip p msgId last _ (msgId message) now preserved live

end EthLib.Networking.Proofs.Gossip.Trace
