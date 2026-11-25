module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements

/-!
# Proofs: the coverage of a walk of roots

The fast confirmation rule confirms a block through a walk of roots that ends at that block.

The walk starts after a start block and lists its roots oldest first.

Honest heads cover a root over a span of times when each up-to-date honest head descends from it.

Coverage of the whole walk follows from coverage of the start and a step for each member.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Coverage of a walk, from the coverage of its start and a step for each member. -/
theorem Execution.walk_covers {first last : ℕ} {P : Prop} {start : Root} (members : List Root)
    (parentOf : Root → Root)
    -- The walk starts after a start block and lists its roots oldest first.
    --
    -- Each member's parent is the member before it.
    --
    -- The first member's parent is the start.
    (parents : ∀ i (h : i < members.length), parentOf members[i] =
      if _ : i = 0 then start else members[i - 1]'(by omega))
    (startCovers : HonestHeadsCover (e := e) start first (last + 1))
    -- The step covers a member up to one more time, from its parent's coverage up to that time.
    --
    -- It may also read the coverage of every member before that time.
    --
    -- The step may fail with an alternative `P` instead.
    --
    -- The result then holds `P`.
    (step : ∀ T, T ≤ last → (∀ m ∈ members, HonestHeadsCover (e := e) m first T) →
      ∀ m ∈ members, HonestHeadsCover (e := e) (parentOf m) first (T + 1) →
        HonestHeadsCover (e := e) m first (T + 1) ∨ P) :
    (∀ m ∈ members, HonestHeadsCover (e := e) m first (last + 1)) ∨ P := by
  by_cases alternative : P
  · exact Or.inr alternative
  refine Or.inl ?_
  -- Every member is covered up to each time up to `last + 1`, by induction on the time.
  have upTo : ∀ T, T ≤ last + 1 → ∀ m ∈ members, HonestHeadsCover (e := e) m first T := by
    intro T
    induction T with
    | zero =>
      -- No time lies before 0.
      intro _ m _ earlier _ below
      exact absurd below (Nat.not_lt_zero _)
    | succ T ih =>
      intro within
      have before := ih (Nat.le_of_succ_le within)
      -- At this time, each member is covered, by induction on its position.
      have atIndex : ∀ i (h : i < members.length),
          HonestHeadsCover (e := e) members[i] first (T + 1) := by
        intro i
        induction i using Nat.strong_induction_on with
        | _ i ihIndex =>
        intro h
        have parentCovers : HonestHeadsCover (e := e) (parentOf members[i]) first (T + 1) := by
          rw [parents i h]
          split
          · exact honestHeadsCover_mono startCovers le_rfl within
          · exact ihIndex (i - 1) (by omega) (by omega)
        exact (step T (by omega) before members[i] (List.getElem_mem h) parentCovers).resolve_right
          alternative
      intro m mem
      obtain ⟨i, h, rfl⟩ := List.getElem_of_mem mem
      exact atIndex i h
  exact upTo (last + 1) le_rfl

end EthLib.Consensus.Models.Network
