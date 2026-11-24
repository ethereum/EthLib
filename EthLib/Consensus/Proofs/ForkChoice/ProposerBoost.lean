module

public import EthLib.Consensus.Proofs.ForkChoice.Ghost

/-!
# Proofs: the proposer boost makes its block the head

Take a store before Gloas whose boost goes to a viable block.

A vote conflicts with that block when it is neither in its chain nor in its subtree.

Suppose that the conflicting votes weigh less than the score of the boost.

Then the head of the store descends from the boosted block.

The boost is Buterin's [mitigation of balancing attacks][mitigation], "Proposed solution", step 3.

[mitigation]: https://notes.ethereum.org/@vbuterin/lmd_ghost_mitigation
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.ForkChoice

variable {preset : Preset} {fork : Fork} {config : Config} {state : BeaconState preset fork}

namespace Store

variable {store : Store preset fork}

variable (store) in
open scoped Classical in
/-- The stake of the latest votes that conflict with a block.

Such a vote is neither in the chain of the block nor in its subtree.

A validator counts when it is active and not slashed in the given state.

Its stake is its effective balance, and an equivocator has no vote. -/
noncomputable def stakeAgainst (lower : store.ParentsBelow) (state : BeaconState preset fork)
    (root : Root) : ℕ :=
  stake (balanceAt state)
    (conflicting (blockTree lower) (voters state) (store.latestVote ·.toUInt64) (some root))

/-- No vote conflicts with a block when each latest message is in its chain or in its subtree.

That is asked only of the validators that do not equivocate. -/
theorem stakeAgainst_eq_zero {lower : store.ParentsBelow} {root : Root}
    (aligned : ∀ index message, store.latestMessages[index]? = some message →
      store.equivocatingIndices.contains index = false →
      (blockTree lower).Ancestor (some message.root) (some root) ∨
        (blockTree lower).Ancestor (some root) (some message.root)) :
    store.stakeAgainst lower state root = 0 := by
  classical
  unfold stakeAgainst conflicting
  rw [Finset.filter_false_of_mem fun i _ => ?_, stake_empty]
  rintro ⟨m, vote, notChain, notSubtree⟩
  -- The vote is the root of the latest message of a validator that does not equivocate.
  simp only [latestVote] at vote
  split at vote
  · cases vote
  rename_i honest
  obtain ⟨message, latest, rfl⟩ := Option.map_eq_some_iff.mp vote
  rcases aligned _ message latest (Bool.eq_false_iff.mpr honest) with chain | subtree
  · exact notChain chain
  · exact notSubtree subtree

variable (lower : store.ParentsBelow)

/-- Before Gloas, the boost keeps the head in the subtree of a viable boosted block.

The conflicting votes must weigh less than the score of the boost.

Each known block must sit at a later slot than its known parent.

The validators that count, their stakes and the score come from the justified state. -/
theorem ancestor_getHead_of_boost {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    {root : Root} {score : Gwei} (before : fork < .glamsterdam)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (viable : ⟨root, .pending⟩ ∈ nodes)
    (boosted : store.proposerBoostRoot = root) (nonzero : root ≠ Vector.replicate 32 0)
    (proposerScore : store.getProposerScore config = .ok score)
    (light : store.stakeAgainst lower state root < score.toNat)
    (found : store.getHead config = .ok head) :
    (blockTree lower).Ancestor (some root) (some head.root) := by
  -- The model boosts the block, with the proposer score as the stake of the boost.
  have boostedRoot : store.boostedRoot = some (some root) := by
    simp [boostedRoot, boosted, nonzero]
  have scoreEq : store.boostScore config = score.toNat := by
    simp [boostScore, boosted, nonzero, proposerScore]
  have belowJustified := (filterNodeTree_ancestor (lower := lower) before tree _ viable).1
  have inView : some root ∈ (view lower nodes).blocks := by
    simp only [view, View.mem_ofBlocks, List.mem_toFinset, List.mem_map]
    exact ⟨_, ⟨_, viable, rfl⟩, .refl _⟩
  -- At each fork on the way, the child towards the block holds at least the score of the boost.
  --
  -- Every other child holds only conflicting votes.
  --
  -- So the model head descends from the block, and the store head is the model head.
  have model := ancestor_ghost_withBoost (V := voters state) (w := balanceAt state) rootValue
    inView belowJustified light
  rwa [← boostedRoot, ← scoreEq, getHead_eq_ghost_withBoost lower before justifiedState tree
    found] at model

/-- Before Gloas, the boost makes a viable boosted block the head when no block builds on it.

Each known block must sit at a later slot than its known parent.

The validators that count, their stakes and the score come from the justified state. -/
theorem getHead_eq_of_boost {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    {root : Root} {score : Gwei} (before : fork < .glamsterdam)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (viable : ⟨root, .pending⟩ ∈ nodes)
    (boosted : store.proposerBoostRoot = root) (nonzero : root ≠ Vector.replicate 32 0)
    (proposerScore : store.getProposerScore config = .ok score)
    -- The conflicting votes must weigh less than the score of the boost.
    (light : store.stakeAgainst lower state root < score.toNat)
    -- No block of the store builds on the boosted block, viable or not.
    (leaf : ∀ (child : Root) (block : BeaconBlock preset fork), store.blocks[child]? = some block →
      block.parentRoot ≠ root)
    (found : store.getHead config = .ok head) :
    head = ⟨root, .pending⟩ := by
  have above := ancestor_getHead_of_boost lower before justifiedState tree viable boosted nonzero
    proposerScore light found
  -- The head descends from the block, and the block has no child, so the head is the block.
  have sameRoot : some head.root = some root := by
    obtain ⟨n, step⟩ := above
    cases n with
    | zero => exact step
    | succ n =>
      have strict : (blockTree lower).Ancestor (some root) (some head.root) := ⟨n + 1, step⟩
      by_contra hne
      obtain ⟨c, hc, -⟩ := strict.exists_child (Ne.symm hne)
      rcases c with _ | child
      · exact hc.1 rfl
      · obtain ⟨block, childFound, parent⟩ := blockTree_isChild_iff.mp hc
        exact leaf child block childFound parent
  have headPending := getHead_pending before found
  obtain ⟨headRoot, status⟩ := head
  simp only [Option.some.injEq] at sameRoot headPending
  rw [sameRoot, headPending]

end Store

end EthLib.Consensus
