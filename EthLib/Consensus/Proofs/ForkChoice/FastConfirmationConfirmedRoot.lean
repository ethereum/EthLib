module

public import EthLib.Consensus.Proofs.ForkChoice.AncestorRoots
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation

/-!
# Proofs: how the fast confirmation rule chooses the confirmed block

The fast confirmation of a slot stores a confirmed block.

This file states where that block comes from, without the long definition of the rule.

The rule first picks a block to start from, in one of three ways.

- It keeps the block stored before.
  That block is then in the chain of the head.
  At the first slot of an epoch its chain also passes `isConfirmedChainSafe`.
- It falls back to the finalized block.
- At the first slot of an epoch it takes the observed justified block.
  That checkpoint is then the unrealized justification of the head.

The rule then stores that block, or a later block of the chain of the head.

A later block is one of the roots that `getAncestorRoots` walks from the start to the head.

That block and each root before it in the walk pass `isOneConfirmed`.

The votes are those of the state of the observed justified checkpoint.

So a property of the confirmed block holds after a fast confirmation in four steps.

Three of them give it to each block that the rule can start from.

The fourth keeps it along a walk of blocks that the rule confirms.

The theorems do not record every check of the rule.

For the start they keep four checks.

- The block stored before is in the chain of the head.
- At the first slot of an epoch, that block passes `isConfirmedChainSafe`.
- The observed justified block is taken only at the first slot of an epoch.
- The observed justified checkpoint is then the unrealized justification of the head.

They leave out the other checks on the start, which compare the epochs and the slots of the blocks.

For the walks they keep `isOneConfirmed` only.

They leave out the check that the head of the slot before holds each block of the first walk.

They leave out the checks that a voting source or an unrealized justification is recent.

They leave out `willNoConflictingCheckpointBeJustified` and `willCurrentTargetBeJustified`.

Those two are about the justification of the target of the current epoch.

No theorem here states that a confirmed block stays in the chain of the head.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The last check of a step of the walks of the rule: the block is one-confirmed, or it stops.

A step that goes on takes the block as its state.

A step that stops keeps its state.

The votes are those of the source of balances. -/
private theorem of_oneConfirmedStep {head root state : Root}
    {source : Except ForkChoiceError (BeaconState preset fork)} {step : ForInStep Root}
    (stepped : (do
      let balanceSource ← source
      let tally ← source.map store.tallyVotes
      if !(← store.isOneConfirmed config head balanceSource tally root) then
        pure (ForInStep.done state)
      else pure (ForInStep.yield root)) = .ok step) :
    step = .done state ∨ step = .yield root ∧ ∃ balanceSource, source = .ok balanceSource ∧
      store.isOneConfirmed config head balanceSource (store.tallyVotes balanceSource) root =
        .ok true := by
  simp only [bind_ok_iff] at stepped
  obtain ⟨balanceSource, sourced, tally, tallied, verdict, checked, stepped⟩ := stepped
  rw [sourced] at tallied
  simp only [Except.map, Except.ok.injEq] at tallied
  subst tallied
  cases verdict <;> simp only [Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true,
    ite_false, pure, Except.pure, Except.ok.injEq] at stepped
  · exact Or.inl stepped.symm
  · exact Or.inr ⟨stepped.symm, balanceSource, sourced, checked⟩

/-- The latest confirmed descendant is the start, or a one-confirmed root of the walk to the head.

Each root of the walk before it is one-confirmed too.

The walk is `getAncestorRoots`, from the start to the head, with the oldest root first.

The votes are those of the state of the observed justified checkpoint.

The theorem does not record the other checks of the two walks of the rule. -/
theorem findLatestConfirmedDescendant_eq_or {fcr : FastConfirmationStore}
    {head start root : Root}
    (found : store.findLatestConfirmedDescendant config fcr head start = .ok root) :
    root = start ∨ ∃ balanceSource chain later,
      store.checkpointState fcr.currentEpochObservedJustifiedCheckpoint = .ok balanceSource ∧
      store.getAncestorRoots head start = .ok (chain ++ root :: later) ∧
      ∀ member ∈ chain ++ [root], store.isOneConfirmed config head balanceSource
        (store.tallyVotes balanceSource) member = .ok true := by
  unfold findLatestConfirmedDescendant at found
  rw [bind_ok_iff] at found
  obtain ⟨currentEpoch, -, found⟩ := found
  rw [bind_ok_iff] at found
  obtain ⟨currentSlot, -, found⟩ := found
  rw [bind_ok_iff] at found
  obtain ⟨isEpochStart, -, found⟩ := found
  -- The rest of the rule is three parts: the previous epoch, the current epoch, the result.
  extract_lets arith recent source tally confirmedRoot finish current previous at found
  let good (root : Root) : Prop := ∃ state, source = .ok state ∧
    store.isOneConfirmed config head state (store.tallyVotes state) root = .ok true
  -- Each one-confirmed root names the source of balances, and the source is one state.
  suffices reached : root = start ∨ ∃ chain later,
      store.getAncestorRoots head start = .ok (chain ++ root :: later) ∧
      ∀ member ∈ chain ++ [root], good member by
    refine reached.imp id ?_
    rintro ⟨chain, later, walked, allGood⟩
    obtain ⟨balanceSource, sourced, -⟩ := allGood root (by simp)
    refine ⟨balanceSource, chain, later, sourced, walked, ?_⟩
    intro member isMember
    obtain ⟨other, otherSourced, confirmed⟩ := allGood member isMember
    obtain rfl : balanceSource = other := Except.ok.inj (sourced.symm.trans otherSourced)
    exact confirmed
  -- The checks before the first walk only decide whether it runs.
  have reach : ∃ previousEpochOk, previous previousEpochOk = .ok root := by
    clear_value previous
    repeat' first
      | split at found
      | (rw [bind_ok_iff] at found; obtain ⟨_, -, found⟩ := found)
    all_goals exact ⟨_, found⟩
  clear found
  obtain ⟨previousEpochOk, found⟩ := reach
  -- The first walk ends at the start, or at a root with a one-confirmed walk up to it.
  have first : ∃ mid, (mid = start ∨ ∃ chain later,
      store.getAncestorRoots head start = .ok (chain ++ mid :: later) ∧
      ∀ member ∈ chain ++ [mid], good member) ∧ current () mid = .ok root := by
    simp only [previous] at found
    split at found
    · rw [bind_ok_iff] at found
      obtain ⟨walk, walked, found⟩ := found
      rw [bind_ok_iff] at found
      obtain ⟨mid, looped, found⟩ := found
      refine ⟨mid, ?_, found⟩
      refine (forIn_ok_last_kept (kept := good) ?_ ?_ looped).imp id ?_
      · intro x s s' stepped
        rw [bind_ok_iff] at stepped
        obtain ⟨_, -, stepped⟩ := stepped
        split at stepped
        · simp [pure, Except.pure] at stepped
        · rw [bind_ok_iff] at stepped
          obtain ⟨_, -, stepped⟩ := stepped
          split at stepped
          · simp [pure, Except.pure] at stepped
          · rcases of_oneConfirmedStep stepped with stopped | ⟨went, confirmed⟩
            · simp at stopped
            · exact ⟨ForInStep.yield.inj went, confirmed⟩
      · intro x s s' stepped
        rw [bind_ok_iff] at stepped
        obtain ⟨_, -, stepped⟩ := stepped
        split at stepped
        · simpa [pure, Except.pure] using stepped.symm
        · rw [bind_ok_iff] at stepped
          obtain ⟨_, -, stepped⟩ := stepped
          split at stepped
          · simpa [pure, Except.pure] using stepped.symm
          · rcases of_oneConfirmedStep stepped with stopped | ⟨went, -⟩
            · exact ForInStep.done.inj stopped
            · simp at went
      · rintro ⟨chain, later, split, allGood⟩
        exact ⟨chain, later, split ▸ walked, allGood⟩
    · exact ⟨start, Or.inl rfl, found⟩
  clear found
  obtain ⟨mid, firstChain, found⟩ := first
  simp -zeta only [current] at found
  extract_lets tentative currentBody at found
  -- The check before the second walk only decides whether it runs.
  have reach : ∃ currentEpochOk, currentBody currentEpochOk = .ok root := by
    clear_value currentBody
    repeat' first
      | split at found
      | (rw [bind_ok_iff] at found; obtain ⟨_, -, found⟩ := found)
    all_goals exact ⟨_, found⟩
  clear found
  obtain ⟨currentEpochOk, found⟩ := reach
  simp -zeta only [currentBody] at found
  split at found
  · rw [bind_ok_iff] at found
    obtain ⟨walk, walked, found⟩ := found
    rw [bind_ok_iff] at found
    obtain ⟨last, looped, found⟩ := found
    -- The second walk starts where the first ended, and ends in the same two ways.
    have second := forIn_ok_last_kept (kept := good) (by
      intro x s s' stepped
      simp only [bind_ok_iff] at stepped
      obtain ⟨_, -, _, -, stepped⟩ := stepped
      split at stepped
      · rw [bind_ok_iff] at stepped
        obtain ⟨_, -, stepped⟩ := stepped
        split at stepped
        · simp [pure, Except.pure] at stepped
        · rcases of_oneConfirmedStep stepped with stopped | ⟨went, confirmed⟩
          · simp at stopped
          · exact ⟨ForInStep.yield.inj went, confirmed⟩
      · rcases of_oneConfirmedStep stepped with stopped | ⟨went, confirmed⟩
        · simp at stopped
        · exact ⟨ForInStep.yield.inj went, confirmed⟩) (by
      intro x s s' stepped
      simp only [bind_ok_iff] at stepped
      obtain ⟨_, -, _, -, stepped⟩ := stepped
      split at stepped
      · rw [bind_ok_iff] at stepped
        obtain ⟨_, -, stepped⟩ := stepped
        split at stepped
        · simpa [pure, Except.pure] using stepped.symm
        · rcases of_oneConfirmedStep stepped with stopped | ⟨went, -⟩
          · exact ForInStep.done.inj stopped
          · simp at went
      · rcases of_oneConfirmedStep stepped with stopped | ⟨went, -⟩
        · exact ForInStep.done.inj stopped
        · simp at went) looped
    extract_lets tentativeRoot accepted acceptBody at found
    rw [bind_ok_iff] at found
    obtain ⟨_, -, found⟩ := found
    -- The last checks only decide whether the rule accepts the end of the second walk.
    have reach : ∃ accept, acceptBody accept = .ok root := by
      clear_value acceptBody
      repeat' first
        | split at found
        | (rw [bind_ok_iff] at found; obtain ⟨_, -, found⟩ := found)
      all_goals exact ⟨_, found⟩
    clear found
    obtain ⟨accept, found⟩ := reach
    have ends : root = last ∨ root = mid := by
      simp only [acceptBody, finish] at found
      split at found
      · exact Or.inl (by simpa [pure, Except.pure, tentativeRoot, accepted] using found.symm)
      · exact Or.inr (by simpa [pure, Except.pure] using found.symm)
    rcases ends with rfl | rfl
    · rcases second with same | ⟨chain, later, split, allGood⟩
      · exact same ▸ firstChain
      · subst split
        rcases firstChain with rfl | ⟨earlier, between, firstWalked, earlierGood⟩
        · exact Or.inr ⟨chain, later, walked, allGood⟩
        · -- The second walk is the rest of the first, so the two join into one walk.
          have rest := getAncestorRoots_of_append firstWalked
          obtain rfl : between = chain ++ root :: later :=
            Except.ok.inj (rest.symm.trans walked)
          refine Or.inr ⟨earlier ++ mid :: chain, later, by simpa using firstWalked, ?_⟩
          intro member isMember
          rw [show earlier ++ mid :: chain ++ [root] = (earlier ++ [mid]) ++ (chain ++ [root]) by
            simp] at isMember
          exact (List.mem_append.mp isMember).elim (earlierGood member) (allGood member)
    · exact firstChain
  · have ends : root = mid := by simpa [finish, pure, Except.pure] using found.symm
    exact ends ▸ firstChain

/-- The latest confirmed block is a block to start from, or its latest confirmed descendant.

The rule starts from the stored block, the finalized block or the observed justified block.

It keeps the stored block only when that block is in the chain of the head.

At the first slot of an epoch, the stored block must also pass `isConfirmedChainSafe`.

It takes the observed justified block only at the first slot of an epoch.

The observed justified checkpoint is then the unrealized justification of the head.

The theorem does not record the checks of the rule on the epochs and the slots of the blocks. -/
theorem getLatestConfirmed_eq_or {fcr : FastConfirmationStore} {head root : Root}
    (latest : store.getLatestConfirmed config fcr head = .ok root) :
    ∃ slot start, store.getCurrentSlot config = .ok slot ∧
      (start = fcr.confirmedRoot ∧
          store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
          (isStartSlotAtEpoch preset slot = .ok true →
            store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true) ∨
        start = store.finalizedCheckpoint.root ∨
        start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧
          isStartSlotAtEpoch preset slot = .ok true ∧
          store.unrealizedJustification head =
            .ok fcr.currentEpochObservedJustifiedCheckpoint) ∧
      (root = start ∨ store.findLatestConfirmedDescendant config fcr head start = .ok root) := by
  unfold getLatestConfirmed at latest
  rw [bind_ok_iff] at latest
  obtain ⟨currentEpoch, -, latest⟩ := latest
  rw [bind_ok_iff] at latest
  obtain ⟨slot, slotFound, latest⟩ := latest
  refine ⟨slot, ?_⟩
  -- The rest of the rule is three parts: the reset, the observed block, the descendant.
  extract_lets arith confirmedRoot observed finish observedRoot afterReset finalizedRoot
    resetBody at latest
  let kept : Prop := store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
    (isStartSlotAtEpoch preset slot = .ok true →
      store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true)
  -- The rule keeps the stored block only when the checks of the reset pass.
  have reset : ∃ reset, (reset = false → kept) ∧ resetBody reset = .ok root := by
    clear_value resetBody
    rw [bind_ok_iff] at latest
    obtain ⟨_, -, latest⟩ := latest
    rw [bind_ok_iff] at latest
    obtain ⟨_, -, latest⟩ := latest
    split at latest
    · exact ⟨true, by simp, latest⟩
    · rw [bind_ok_iff] at latest
      obtain ⟨onChain, ancestry, latest⟩ := latest
      split at latest
      · exact ⟨true, by simp, latest⟩
      · rename_i isOnChain
        obtain rfl : onChain = true := by simpa using isOnChain
        rw [bind_ok_iff] at latest
        obtain ⟨atStart, startChecked, latest⟩ := latest
        split at latest
        · rw [bind_ok_iff] at latest
          obtain ⟨safe, chainChecked, latest⟩ := latest
          refine ⟨!safe, fun notReset => ⟨ancestry, fun _ => ?_⟩, latest⟩
          obtain rfl : safe = true := by simpa using notReset
          exact chainChecked
        · rename_i notStart
          refine ⟨false, fun _ => ⟨ancestry, fun isStart => ?_⟩, latest⟩
          exact absurd (Except.ok.inj (startChecked.symm.trans isStart)) notStart
  clear latest
  obtain ⟨reset, keeps, latest⟩ := reset
  have base : ∃ base, (base = fcr.confirmedRoot ∧ kept ∨
      base = store.finalizedCheckpoint.root) ∧ afterReset () base = .ok root := by
    cases reset
    · exact ⟨fcr.confirmedRoot, Or.inl ⟨rfl, keeps rfl⟩, latest⟩
    · exact ⟨store.finalizedCheckpoint.root, Or.inr rfl, latest⟩
  clear latest keeps
  obtain ⟨base, baseCase, latest⟩ := base
  -- The observed justified block replaces that block only when its four checks pass.
  have start : ∃ start, (start = fcr.confirmedRoot ∧ kept ∨
      start = store.finalizedCheckpoint.root ∨
      start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧
        isStartSlotAtEpoch preset slot = .ok true ∧
        store.unrealizedJustification head =
          .ok fcr.currentEpochObservedJustifiedCheckpoint) ∧ finish () start = .ok root := by
    clear_value finish
    simp only [afterReset, bind_ok_iff] at latest
    obtain ⟨atStart, startChecked, _, -, _, -, justified, justification, _, -, latest⟩ := latest
    split at latest
    · rename_i replaced
      refine ⟨observedRoot, Or.inr (Or.inr ⟨rfl, ?_, ?_⟩), latest⟩
      · exact replaced.1 ▸ startChecked
      · exact justification.trans (congrArg Except.ok replaced.2.2.1.symm)
    · exact ⟨base, baseCase.imp id Or.inl, latest⟩
  clear latest
  obtain ⟨start, startCase, latest⟩ := start
  refine ⟨start, slotFound, startCase, ?_⟩
  simp only [finish, bind_ok_iff] at latest
  obtain ⟨_, -, _, -, latest⟩ := latest
  split at latest
  · exact Or.inr latest
  · exact Or.inl (Except.ok.inj latest).symm

/-- The fast confirmation of a slot stores a block to start from, or a confirmed block after it.

The rule starts from the block stored before, the finalized block or the observed justified block.

It keeps the block stored before only when that block is in the chain of the head of the store.

At the first slot of an epoch, that block must also pass `isConfirmedChainSafe`.

It takes the observed justified block only at the first slot of an epoch.

A later block is a root of the walk from the start to the head.

That block and each root before it in the walk are one-confirmed.

The observed justified checkpoint is that of the store after the call, as the rule reads it.

The theorem does not record the other checks of the rule. -/
theorem onFastConfirmation_confirmedRoot {fcr after : FastConfirmationStore}
    (confirmed : store.onFastConfirmation config fcr = .ok after) :
    ∃ head slot start, store.getHead config = .ok head ∧
      store.getCurrentSlot config = .ok slot ∧
      (start = fcr.confirmedRoot ∧
          store.isAncestor ⟨head.root, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
          (isStartSlotAtEpoch preset slot = .ok true →
            store.isConfirmedChainSafe config after head.root fcr.confirmedRoot = .ok true) ∨
        start = store.finalizedCheckpoint.root ∨
        start = after.currentEpochObservedJustifiedCheckpoint.root ∧
          isStartSlotAtEpoch preset slot = .ok true ∧
          store.unrealizedJustification head.root =
            .ok after.currentEpochObservedJustifiedCheckpoint) ∧
      (after.confirmedRoot = start ∨ ∃ balanceSource chain later,
        store.checkpointState after.currentEpochObservedJustifiedCheckpoint = .ok balanceSource ∧
        store.getAncestorRoots head.root start = .ok (chain ++ after.confirmedRoot :: later) ∧
        ∀ member ∈ chain ++ [after.confirmedRoot], store.isOneConfirmed config head.root
          balanceSource (store.tallyVotes balanceSource) member = .ok true) := by
  unfold onFastConfirmation at confirmed
  simp only [bind_ok_iff] at confirmed
  obtain ⟨head, found, updated, update, root, latest, confirmed⟩ := confirmed
  simp only [pure, Except.pure, Except.ok.injEq] at confirmed
  subst confirmed
  obtain ⟨slot, start, slotFound, startCase, rootCase⟩ := getLatestConfirmed_eq_or latest
  -- The update of the tracked variables keeps the block stored before.
  rw [updateFastConfirmationVariables_confirmedRoot update] at startCase
  -- No check here reads the confirmed block of its store, so the store after the call serves.
  refine ⟨head, slot, start, found, slotFound, startCase, ?_⟩
  rcases rootCase with same | later
  · exact Or.inl same
  · exact findLatestConfirmedDescendant_eq_or later

end Store

end EthLib.Consensus
