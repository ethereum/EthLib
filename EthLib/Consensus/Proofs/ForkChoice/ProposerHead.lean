module

public import EthLib.Base.Except
public import EthLib.Consensus.ForkChoice.ProposerHead

/-!
# Proofs: the head on which a proposer builds

The proposer builds on the head or on its parent, and on nothing else.

It skips the head only when the head is weak.

It never answers while the head still holds the boost.

From Gloas the choice fails as not yet specified.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

/-- From Fulu the shuffling test always lets a re-org happen. -/
theorem shufflingAllowsReorg_of_fulu {slot : Slot} (fulu : .fusaka ≤ fork) :
    shufflingAllowsReorg preset fork slot = .ok true := by
  simp [shufflingAllowsReorg, fulu, pure, Except.pure]

/-- Before Fulu a re-org waits for a slot that does not start an epoch. -/
theorem shufflingAllowsReorg_of_lt {slot : Slot} (before : fork < .fusaka)
    (positive : preset.SLOTS_PER_EPOCH ≠ 0) :
    shufflingAllowsReorg preset fork slot = .ok (slot % preset.SLOTS_PER_EPOCH ≠ 0) := by
  have later : ¬ .fusaka ≤ fork := Nat.not_le_of_lt before
  simp [shufflingAllowsReorg, isShufflingStable, later, positive, pure, Except.pure]

namespace Store

variable {config : Config} {store : Store preset fork}

/-- From Gloas the choice of the proposer is not yet specified here, so it fails. -/
theorem getProposerHead_of_gloas {headNode : ForkChoiceNode} {slot : Slot}
    (gloas : .glamsterdam ≤ fork) :
    store.getProposerHead config headNode slot = .error (.forkNotYetSpecified fork) := by
  simp [getProposerHead, gloas, throw, throwThe, MonadExceptOf.throw]

/-- The proposer builds on the head, or on the parent of its block.

It builds on the parent only when the head is weak. -/
theorem getProposerHead_ok {headNode chosen : ForkChoiceNode} {slot : Slot}
    (found : store.getProposerHead config headNode slot = .ok chosen) :
    chosen = headNode ∨
      ∃ block, store.blocks[headNode.root]? = some block ∧
        chosen = ⟨block.parentRoot, .pending⟩ ∧
        store.isHeadWeak config headNode.root = .ok true := by
  by_cases gloas : .glamsterdam ≤ fork
  · rw [getProposerHead_of_gloas gloas] at found
    cases found
  simp only [getProposerHead, gloas, ↓reduceIte, bind_ok_iff] at found
  obtain ⟨headBlock, headFound, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, found⟩ := found
  split at found
  · simp [throw, throwThe, MonadExceptOf.throw] at found
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at found
  obtain ⟨weak, weakFound, _, _, _, _, found⟩ := found
  have block : store.blocks[headNode.root]? = some headBlock := by
    unfold block at headFound
    split at headFound <;> simp_all [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
  split at found
  · rename_i reorg
    exact .inr ⟨headBlock, block, found.symm, by rw [weakFound, show weak = true by simp_all]⟩
  · split at found
    · rename_i reorg
      exact .inr ⟨headBlock, block, found.symm, by rw [weakFound, show weak = true by simp_all]⟩
    · exact .inl found.symm

/-- The proposer gets no answer while the head still holds the boost. -/
theorem getProposerHead_boosted {headNode chosen : ForkChoiceNode} {slot : Slot}
    (boosted : store.proposerBoostRoot = headNode.root) :
    store.getProposerHead config headNode slot ≠ .ok chosen := by
  intro found
  by_cases gloas : .glamsterdam ≤ fork
  · rw [getProposerHead_of_gloas gloas] at found
    cases found
  simp only [getProposerHead, gloas, ↓reduceIte, bind_ok_iff] at found
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, found⟩ := found
  simp [boosted, throw, throwThe, MonadExceptOf.throw] at found

end Store

end EthLib.Consensus
