module

public import EthLib.Networking.Proofs.Gossip.Heartbeat
public import EthLib.Networking.Proofs.Gossip.Membership

/-!
# Proofs: the lists of peers along the steps of the gossipsub router

A run is a list of steps, each a received RPC, a join, a leave, a publish or a heartbeat.

Each join, publish and heartbeat of the run uses a lawful choice.

- Such a run keeps three properties of the state.
  No mesh holds a peer twice, and no fanout holds a peer twice.
  The topics of the peers list each peer at most once.
- So in each state that a run reaches, the peers that announced each topic appear once each.
- A run from a router with no mesh, no fanout and no topics of peers reaches only such states.
- So a join with a lawful choice from such a state keeps every mesh free of a repeated peer.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Steps

open EthLib.Networking.Gossip

open EthLib.Networking.Proofs.Gossip

/-- One step of the gossipsub router, as a map of its state, with any arguments.

A join, a publish and a heartbeat use a lawful choice. -/
inductive RouterStep : (RouterState → RouterState) → Prop where
  /-- A received RPC. -/
  | receive (p : GossipsubParameters) (backoffMs pruneBackoffMs : Nat)
      (standing : PeerId → Standing) (msgId : Message → MessageId)
      (validate : Message → ValidationResult) (now : Nat) (src : PeerId) (rpc : Rpc) :
      RouterStep fun r => (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc
        r).1
  /-- A join of a topic. -/
  | join (p : GossipsubParameters) (sel : Select) (standing : PeerId → Standing) (now : Nat)
      (topic : String) (hsel : sel.Lawful) :
      RouterStep fun r => (EthLib.Networking.Gossip.join p sel standing now topic r).1
  /-- A leave of a topic. -/
  | leave (c : ClientChoices) (now : Nat) (topic : String) :
      RouterStep fun r => (EthLib.Networking.Gossip.leave c now topic r).1
  /-- A publish of a message. -/
  | publish (p : GossipsubParameters) (c : ClientChoices) (sel : Select)
      (standing : PeerId → Standing) (msgId : Message → MessageId) (now : Nat) (m : Message)
      (hsel : sel.Lawful) :
      RouterStep fun r => (EthLib.Networking.Gossip.publish p c sel standing msgId now m r).1
  /-- A heartbeat. -/
  | heartbeat (p : GossipsubParameters) (c : ClientChoices) (sel : Select) (rank : Rank)
      (standing : PeerId → Standing) (now : Nat) (hsel : sel.Lawful) :
      RouterStep fun r => (EthLib.Networking.Gossip.heartbeat p c sel rank standing now r).1

/-- One step keeps each mesh and each fanout free of a repeated peer.

It also keeps each peer listed at most once among the topics of the peers. -/
private theorem step_nodup {f : RouterState → RouterState} (hf : RouterStep f) {r : RouterState}
    (h : (∀ t, (peersOf r.mesh t).Nodup) ∧ (∀ t, (peersOf r.fanout t).Nodup) ∧
      (r.peerTopics.map (·.1)).Nodup) :
    (∀ t, (peersOf (f r).mesh t).Nodup) ∧ (∀ t, (peersOf (f r).fanout t).Nodup) ∧
      ((f r).peerTopics.map (·.1)).Nodup := by
  obtain ⟨hm, hn, hk⟩ := h
  cases hf with
  | receive p b pb st mi v now src rpc =>
    dsimp only
    refine ⟨Router.receiveRpc_mesh_nodup p b pb st mi v now src rpc r hm, ?_,
      Router.receiveRpc_peerTopics_nodup p b pb st mi v now src rpc r hk⟩
    rw [Router.receiveRpc_fanout]
    exact hn
  | join p sel st now topic hsel =>
    dsimp only
    refine ⟨Membership.join_mesh_nodup p sel st now topic r hsel (hn topic)
      (Router.topicPeers_nodup hk topic) hm, Membership.join_fanout_nodup p sel st now topic r hn,
      ?_⟩
    rw [Membership.join_peerTopics]
    exact hk
  | leave c now topic =>
    dsimp only
    refine ⟨Membership.leave_mesh_nodup c now topic r hm, ?_, ?_⟩
    · rw [Membership.leave_fanout]
      exact hn
    · rw [Membership.leave_peerTopics]
      exact hk
  | publish p c sel st mi now m hsel =>
    dsimp only
    refine ⟨?_, Membership.publish_fanout_nodup p c sel st mi now r hsel
      (Router.topicPeers_nodup hk m.topic) hn, ?_⟩
    · rw [Membership.publish_mesh]
      exact hm
    · rw [Membership.publish_peerTopics]
      exact hk
  | heartbeat p c sel rank st now hsel =>
    dsimp only
    exact ⟨Heartbeat.heartbeat_mesh_nodup p c sel rank st now r hsel,
      Heartbeat.heartbeat_fanout_nodup p c sel rank st now r hsel hn, hk⟩

/-- Along a run, no mesh and no fanout holds a peer twice.

The topics of the peers list each peer at most once.

So the peers that announced each topic appear once each.

Each step of the run must be a step of the router.

The run needs a start where no mesh and no fanout holds a peer twice.

The topics of the peers at the start must list each peer at most once. -/
theorem steps_nodup (steps : List (RouterState → RouterState))
    (hsteps : ∀ f ∈ steps, RouterStep f) {s0 s : RouterState}
    (hm : ∀ t, (peersOf s0.mesh t).Nodup) (hf : ∀ t, (peersOf s0.fanout t).Nodup)
    (hk : (s0.peerTopics.map (·.1)).Nodup) (hs : s = steps.foldl (fun r f => f r) s0) :
    (∀ t, (peersOf s.mesh t).Nodup) ∧ (∀ t, (peersOf s.fanout t).Nodup) ∧
      (s.peerTopics.map (·.1)).Nodup ∧ ∀ t, (topicPeers s t).Nodup := by
  have H := Router.foldl_inv steps (fun r : RouterState => (∀ t, (peersOf r.mesh t).Nodup) ∧
    (∀ t, (peersOf r.fanout t).Nodup) ∧ (r.peerTopics.map (·.1)).Nodup) (fun r f => f r)
    (fun r f hf' hr => step_nodup (hsteps f hf') hr) ⟨hm, hf, hk⟩
  rw [← hs] at H
  exact ⟨H.1, H.2.1, H.2.2, Router.topicPeers_nodup H.2.2⟩

/-- A run from a router with no mesh, no fanout and no topics of peers repeats no peer in a list.

That holds of each mesh, each fanout and the topics of the peers.

It also holds of the peers that announced each topic.

Each step of the run must be a step of the router. -/
theorem steps_nodup_of_empty (steps : List (RouterState → RouterState))
    (hsteps : ∀ f ∈ steps, RouterStep f) {s0 s : RouterState} (hm : s0.mesh = [])
    (hf : s0.fanout = []) (hk : s0.peerTopics = []) (hs : s = steps.foldl (fun r f => f r) s0) :
    (∀ t, (peersOf s.mesh t).Nodup) ∧ (∀ t, (peersOf s.fanout t).Nodup) ∧
      (s.peerTopics.map (·.1)).Nodup ∧ ∀ t, (topicPeers s t).Nodup :=
  steps_nodup steps hsteps (fun t => by simp [peersOf, hm]) (fun t => by simp [peersOf, hf])
    (by simp [hk]) hs

/-- A join after a run from a router with no mesh, no fanout and no topics of peers repeats no peer.

That holds of each mesh after the join.

It is the result above for the run followed by one join.

Each step of the run must be a step of the router, and the join needs a lawful choice. -/
theorem steps_join_mesh_nodup (steps : List (RouterState → RouterState))
    (hsteps : ∀ f ∈ steps, RouterStep f) {s0 s : RouterState} (hm : s0.mesh = [])
    (hf : s0.fanout = []) (hk : s0.peerTopics = []) (hs : s = steps.foldl (fun r f => f r) s0)
    (p : GossipsubParameters) (sel : Select) (hsel : sel.Lawful) (standing : PeerId → Standing)
    (now : Nat) (topic t : String) :
    (peersOf (join p sel standing now topic s).1.mesh t).Nodup := by
  have hj : ∀ f ∈ steps ++ [fun r => (join p sel standing now topic r).1], RouterStep f := by
    intro f hf'
    rcases List.mem_append.1 hf' with h | h
    · exact hsteps f h
    · rw [List.mem_singleton.1 h]
      exact RouterStep.join p sel standing now topic hsel
  refine (steps_nodup_of_empty (s := (join p sel standing now topic s).1) _ hj hm hf hk ?_).1 t
  rw [List.foldl_append, ← hs] <;> rfl

end EthLib.Networking.Proofs.Gossip.Steps
