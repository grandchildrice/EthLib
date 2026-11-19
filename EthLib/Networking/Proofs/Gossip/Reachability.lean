module

public import EthLib.Networking.Proofs.Gossip.Trace

/-!
# Proofs: reachable gossipsub mesh and fanout uniqueness

A router state is well formed when:

- The peerTopics table has at most one entry for each peer.
- Each entry of the fanout lists its peers once.
- Each mesh lists its peers once.

The rules of gossipsub v1.0 keep the mesh and the fanout of a topic as sets of peers.

The actual receive, heartbeat, join, leave and publish operations preserve this invariant.

The selector is lawful at each heartbeat, join and publish event.

Receive and leave events need no selection assumption.

`Trace.run` composes the actual operations over any finite list of events.

From the actual empty router state, every mesh and fanout then lists each peer at most once.

Client choices, standing, validation and event times may vary at every step.

The parameters and message ID function are fixed throughout a trace, as in `Trace.run`.

This uniqueness result needs no monotonicity assumption on event times.

The sources are [gossipsub v1.0, "Peering State" and "Fanout Maintenance"][gossip].

[gossip]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#peering-state
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Reachability

open EthLib.Networking.Gossip

/-- A router state is well formed when each of its lists of peers holds a peer once.

The topics of the peers name each peer once, and each mesh and fanout entry lists its peers once. -/
def WellFormed (s : RouterState) : Prop :=
  (s.peerTopics.map Prod.fst).Nodup ∧
    (∀ entry ∈ s.fanout, entry.2.Nodup) ∧
    (∀ t, (peersOf s.mesh t).Nodup)

/-- If each entry lists distinct peers, each lookup lists distinct peers. -/
private theorem peersOf_nodup_of_entries {m : List (String × List PeerId)}
    (h : ∀ entry ∈ m, entry.2.Nodup) (t : String) : (peersOf m t).Nodup := by
  unfold peersOf
  induction m with
  | nil => simp
  | cons entry m ih =>
    obtain ⟨topic, peers⟩ := entry
    by_cases hne : topic = t
    · subst topic
      simp only [List.lookup_cons]
      have hb : (t == t) = true := by simp
      simp only [hb]
      simpa using h (t, peers) (by simp)
    · have hb : (t == topic) = false := by
        simpa using Ne.symm hne
      simp only [List.lookup_cons, hb]
      exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

/-- A map whose entries list their peers once gives a lookup that lists no peer twice. -/
theorem fanout_nodup_of_entries {m : List (String × List PeerId)}
    (h : ∀ entry ∈ m, entry.2.Nodup) (t : String) : (peersOf m t).Nodup :=
  peersOf_nodup_of_entries h t

/-- The peers that announced a topic are distinct when `peerTopics` has distinct keys.

The peers of a topic are the keys of the topics of the peers that announced it. -/
theorem topicPeers_nodup {s : RouterState} (h : (s.peerTopics.map Prod.fst).Nodup) (t : String) :
    (topicPeers s t).Nodup := by
  unfold topicPeers
  refine List.Sublist.nodup (List.Sublist.map _ ?_) h
  exact List.filter_sublist

/-- A subscription change keeps the topics of the peers naming each peer once.

The changed peer comes first, and the other peers keep their entry. -/
theorem applySubscription_nodup {peerTopics : List (PeerId × List String)} {src : PeerId}
    (sub : SubOpts) (h : (peerTopics.map Prod.fst).Nodup) :
    (applySubscription src peerTopics sub).map Prod.fst |>.Nodup := by
  unfold applySubscription
  rw [List.map_cons]
  apply List.nodup_cons.2
  constructor
  · intro hin
    obtain ⟨entry, hentry, he⟩ := List.mem_map.mp hin
    have hne : entry.1 ≠ src := by
      simpa using (List.mem_filter.mp hentry).2
    exact hne he
  · exact List.Sublist.nodup (List.Sublist.map Prod.fst List.filter_sublist) h


/-- A fold preserves a projection when every step preserves it. -/
private theorem foldl_project {A B C : Type} (l : List A) (f : B → A → B) (get : B → C)
    (h : ∀ b a, get (f b a) = get b) (b : B) : get (l.foldl f b) = get b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => exact (ih (f b a)).trans (h b a)

/-- Processing one message keeps the peer table and fanout. -/
private theorem receiveMessage_tables (p : GossipsubParameters)
    (msgId : Message → MessageId) (validate : Message → ValidationResult) (now : Nat)
    (s : RouterState) (out : Out) (m : Message) :
    ((receiveMessage p msgId validate now (s, out) m).1.peerTopics,
      (receiveMessage p msgId validate now (s, out) m).1.fanout) =
      (s.peerTopics, s.fanout) := by
  simp only [receiveMessage]
  split
  · rfl
  · cases validate m <;> rfl

/-- Processing one GRAFT keeps the peer table and fanout. -/
private theorem receiveGraft_tables (p : GossipsubParameters) (backoffMs now : Nat)
    (src : PeerId) (s : RouterState) (out : Out) (g : Graft) :
    ((receiveGraft p backoffMs now src (s, out) g).1.peerTopics,
      (receiveGraft p backoffMs now src (s, out) g).1.fanout) =
      (s.peerTopics, s.fanout) := by
  simp only [receiveGraft]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl

/-- Processing one PRUNE keeps the peer table and fanout. -/
private theorem receivePrune_tables (pruneBackoffMs now : Nat) (src : PeerId)
    (s : RouterState) (q : Prune) :
    ((receivePrune pruneBackoffMs now src s q).peerTopics,
      (receivePrune pruneBackoffMs now src s q).fanout) = (s.peerTopics, s.fanout) := by
  by_cases ht : q.topicId ∉ s.topics <;> simp [receivePrune, ht]

/-- An RPC preserves distinct peer-table keys and peers in every mesh and fanout entry. -/
theorem receiveRpc_wellFormed (p : GossipsubParameters) (backoffMs pruneBackoffMs : Nat)
    (standing : PeerId → Standing) (msgId : Message → MessageId)
    (validate : Message → ValidationResult) (now : Nat) (src : PeerId) (rpc : Rpc)
    (s : RouterState) (hs : WellFormed s) :
    WellFormed (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1 := by
  by_cases gray : (standing src).belowGraylist = true ∧ src ∉ s.explicit
  · rw [Router.receiveRpc_graylist p backoffMs pruneBackoffMs standing msgId validate now src
      rpc s gray.1 gray.2]
    exact hs
  · let s1 : RouterState :=
      { s with peerTopics := rpc.subscriptions.foldl (applySubscription src) s.peerTopics }
    let a1 := rpc.publish.foldl (receiveMessage p msgId validate now) (s1, {})
    let a2 := rpc.control.graft.foldl (receiveGraft p backoffMs now src) a1
    let s3 := rpc.control.prune.foldl (receivePrune pruneBackoffMs now src) a2.1
    -- After subscriptions, message and control processing keep both tables.
    have hm : (a1.1.peerTopics, a1.1.fanout) = (s1.peerTopics, s1.fanout) :=
      foldl_project rpc.publish (receiveMessage p msgId validate now)
        (fun a : RouterState × Out => (a.1.peerTopics, a.1.fanout))
        (fun a m => receiveMessage_tables p msgId validate now a.1 a.2 m) (s1, {})
    have hg : (a2.1.peerTopics, a2.1.fanout) = (a1.1.peerTopics, a1.1.fanout) :=
      foldl_project rpc.control.graft (receiveGraft p backoffMs now src)
        (fun a : RouterState × Out => (a.1.peerTopics, a.1.fanout))
        (fun a g => receiveGraft_tables p backoffMs now src a.1 a.2 g) a1
    have hp : (s3.peerTopics, s3.fanout) = (a2.1.peerTopics, a2.1.fanout) :=
      foldl_project rpc.control.prune (receivePrune pruneBackoffMs now src)
        (fun state : RouterState => (state.peerTopics, state.fanout))
        (fun state q => receivePrune_tables pruneBackoffMs now src state q) a2.1
    have tables := hp.trans (hg.trans hm)
    -- Each subscription removes the old key before placing its replacement first.
    have keys : ((rpc.subscriptions.foldl (applySubscription src) s.peerTopics).map
        Prod.fst).Nodup :=
      Router.foldl_inv rpc.subscriptions (fun table => (table.map Prod.fst).Nodup)
        (applySubscription src) (fun table sub _ h => applySubscription_nodup sub h) hs.1
    have result :
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1 = s3 := by
      simp only [receiveRpc, gray, ite_false]
      split <;> rfl
    have peerTopics_eq : s3.peerTopics = s1.peerTopics := congrArg Prod.fst tables
    have fanout_eq : s3.fanout = s1.fanout := congrArg Prod.snd tables
    refine ⟨?_, ?_, Router.receiveRpc_mesh_nodup p backoffMs pruneBackoffMs standing msgId
      validate now src rpc s hs.2.2⟩
    · rw [result, peerTopics_eq]
      exact keys
    · rw [result, fanout_eq]
      exact hs.2.1

/-- Replacing an entry keeps every stored list free of duplicate peers. -/
private theorem setPeers_entries_nodup (m : List (String × List PeerId)) (topic : String)
    (peers : List PeerId) (hm : ∀ entry ∈ m, entry.2.Nodup) (hp : peers.Nodup) :
    ∀ entry ∈ setPeers m topic peers, entry.2.Nodup := by
  intro entry he
  simp only [setPeers, List.mem_cons] at he
  rcases he with rfl | he
  · exact hp
  · exact hm entry (List.mem_filter.mp he).1

/-- Joining a topic preserves the peer-list invariant under lawful selection. -/
theorem join_wellFormed (p : GossipsubParameters) (sel : Select)
    (standing : PeerId → Standing) (now : Nat) (topic : String) (s : RouterState)
    (hsel : sel.Lawful) (hs : WellFormed s) :
    WellFormed (join p sel standing now topic s).1 := by
  refine ⟨?_, ?_, Membership.join_mesh_nodup p sel standing now topic s hsel
    (fanout_nodup_of_entries hs.2.1 topic) (topicPeers_nodup hs.1 topic) hs.2.2⟩
  · simp only [join]
    split <;> exact hs.1
  · simp only [join]
    split
    · exact hs.2.1
    · intro entry he
      exact hs.2.1 entry (List.mem_filter.mp he).1

/-- Leaving a topic preserves the peer-list invariant without selection assumptions. -/
theorem leave_wellFormed (choices : ClientChoices) (now : Nat) (topic : String)
    (s : RouterState) (hs : WellFormed s) :
    WellFormed (leave choices now topic s).1 := by
  refine ⟨?_, ?_, Membership.leave_mesh_nodup choices now topic s hs.2.2⟩
  · simp only [leave]
    split <;> exact hs.1
  · simp only [leave]
    split <;> exact hs.2.1

/-- Choosing publish peers preserves the invariant under lawful selection. -/
private theorem publishPeers_wellFormed (p : GossipsubParameters) (choices : ClientChoices)
    (sel : Select) (standing : PeerId → Standing) (now : Nat) (topic : String)
    (s : RouterState) (hsel : sel.Lawful) (hs : WellFormed s) :
    WellFormed (publishPeers p choices sel standing now topic s).1 := by
  simp only [publishPeers]
  split
  · exact hs
  · split
    · exact hs
    · refine ⟨hs.1, ?_, hs.2.2⟩
      apply setPeers_entries_nodup _ _ _ hs.2.1
      cases hfan : peersOf s.fanout topic with
      | nil =>
        exact (hsel _ _).1.nodup ((topicPeers_nodup hs.1 topic).filter _)
      | cons peer peers =>
        simpa only [hfan] using fanout_nodup_of_entries hs.2.1 topic

/-- Publishing preserves the invariant under lawful selection. -/
theorem publish_wellFormed (p : GossipsubParameters) (choices : ClientChoices)
    (sel : Select) (standing : PeerId → Standing) (msgId : Message → MessageId)
    (now : Nat) (message : Message) (s : RouterState) (hsel : sel.Lawful)
    (hs : WellFormed s) :
    WellFormed (publish p choices sel standing msgId now message s).1 := by
  simp only [publish]
  split
  · exact hs
  · exact publishPeers_wellFormed p choices sel standing now message.topic _ hsel hs

/-- Fanout maintenance keeps every stored list free of duplicate peers. -/
private theorem fanoutAfter_entries_nodup (p : GossipsubParameters) (sel : Select)
    (standing : PeerId → Standing) (now : Nat) (s : RouterState) (hsel : sel.Lawful)
    (hs : ∀ entry ∈ s.fanout, entry.2.Nodup) :
    ∀ entry ∈ fanoutAfter p sel standing now s, entry.2.Nodup := by
  intro entry he
  simp only [fanoutAfter, List.mem_filterMap] at he
  obtain ⟨⟨topic, peers⟩, hmem, hout⟩ := he
  by_cases expired : lastPublished s topic + p.fanout_ttl * 1000 < now
  · simp only [expired, ↓reduceIte] at hout
    contradiction
  · simp only [expired, ↓reduceIte] at hout
    let kept := peers.filter fun q => !(standing q).belowPublish
    have hkept : kept.Nodup := (hs (topic, peers) hmem).filter _
    by_cases small : kept.length < p.D
    · dsimp only [kept] at small
      simp only [small, ↓reduceIte] at hout
      have heq := Option.some.inj hout
      rw [← heq]
      rw [List.nodup_append]
      refine ⟨hkept, (hsel _ _).1.nodup (EthLib.Base.nodup_eraseDups _), ?_⟩
      -- A top-up candidate cannot also be one of the retained peers.
      intro a ha b hb hab
      subst hab
      have candidate := (hsel _ _).1.subset hb
      have eligible := (List.mem_filter.mp (List.mem_eraseDups.mp candidate)).2
      simp [ha] at eligible
    · dsimp only [kept] at small
      simp only [small, ↓reduceIte] at hout
      have heq := Option.some.inj hout
      rw [← heq]
      exact hkept

/-- A heartbeat preserves the invariant under lawful selection. -/
theorem heartbeat_wellFormed (p : GossipsubParameters) (choices : ClientChoices)
    (sel : Select) (rank : Rank) (standing : PeerId → Standing) (now : Nat)
    (s : RouterState) (hsel : sel.Lawful) (hs : WellFormed s) :
    WellFormed (heartbeat p choices sel rank standing now s).1 := by
  exact ⟨hs.1, fanoutAfter_entries_nodup p sel standing now s hsel hs.2.1,
    Heartbeat.heartbeat_mesh_nodup p choices sel rank standing now s hsel⟩

/-- Only heartbeat, join and publish events constrain their peer selector. -/
def LawfulSelections (event : Trace.Event) : Prop :=
  match event.action with
  | .receive .. => True
  | .heartbeat _ sel _ _ => sel.Lawful
  | .join sel _ _ => sel.Lawful
  | .leave .. => True
  | .publish _ sel _ _ => sel.Lawful

/-- Every router event preserves the invariant under its own selection condition. -/
theorem step_wellFormed (p : GossipsubParameters) (msgId : Message → MessageId)
    (event : Trace.Event) (s : RouterState) (hs : WellFormed s)
    (hsel : LawfulSelections event) : WellFormed (event.step p msgId s).1 := by
  rcases event with ⟨now, action⟩
  cases action with
  | receive backoff pruneBackoff standing validate source rpc =>
    exact receiveRpc_wellFormed p backoff pruneBackoff standing msgId validate now source rpc s hs
  | heartbeat choices sel rank standing =>
    exact heartbeat_wellFormed p choices sel rank standing now s hsel hs
  | join sel standing topic =>
    exact join_wellFormed p sel standing now topic s hsel hs
  | leave choices topic =>
    exact leave_wellFormed choices now topic s hs
  | publish choices sel standing message =>
    exact publish_wellFormed p choices sel standing msgId now message s hsel hs

/-- Every finite mixed trace preserves the invariant from its original state. -/
theorem run_wellFormed (p : GossipsubParameters) (msgId : Message → MessageId)
    (s : RouterState) (events : List Trace.Event) (hs : WellFormed s)
    (hsel : ∀ event ∈ events, LawfulSelections event) :
    WellFormed (Trace.run p msgId s events) := by
  exact Router.foldl_inv events WellFormed _
    (fun state event he hstate => step_wellFormed p msgId event state hstate (hsel event he)) hs

/-- The actual empty router state satisfies every component of the invariant. -/
theorem empty_wellFormed : WellFormed ({} : RouterState) := by
  simp [WellFormed, peersOf]

/-- Every mesh reachable from the empty state lists each peer at most once. -/
theorem run_empty_mesh_nodup (p : GossipsubParameters) (msgId : Message → MessageId)
    (events : List Trace.Event) (hsel : ∀ event ∈ events, LawfulSelections event) (topic : String) :
    (peersOf (Trace.run p msgId ({} : RouterState) events).mesh topic).Nodup :=
  (run_wellFormed p msgId {} events empty_wellFormed hsel).2.2 topic

/-- Every fanout reachable from the empty state lists each peer at most once. -/
theorem run_empty_fanout_nodup (p : GossipsubParameters) (msgId : Message → MessageId)
    (events : List Trace.Event) (hsel : ∀ event ∈ events, LawfulSelections event) (topic : String) :
    (peersOf (Trace.run p msgId ({} : RouterState) events).fanout topic).Nodup :=
  fanout_nodup_of_entries
    (run_wellFormed p msgId {} events empty_wellFormed hsel).2.1 topic

end EthLib.Networking.Proofs.Gossip.Reachability
