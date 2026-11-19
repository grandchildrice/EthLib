module

public import EthLib.Networking.Proofs.Gossip.Trace

/-!
# Proofs: helper lemmas for well-formed router states

A router state is well formed when:

- The peerTopics table has at most one entry for each peer.
- Each entry of the fanout lists its peers once.
- Each mesh lists its peers once.

The rules of gossipsub v1.0 keep the mesh and the fanout of a topic as sets of peers.

This module supplies the invariant and the universal helper lemmas.

The full reachable-state result is still pending.

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

end EthLib.Networking.Proofs.Gossip.Reachability
