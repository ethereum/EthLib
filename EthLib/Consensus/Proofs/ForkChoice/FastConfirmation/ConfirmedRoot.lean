module

public import EthLib.Consensus.Proofs.ForkChoice.AncestorRoots
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic

/-!
# Root selection and checkpoint-check soundness of the fast confirmation rule

A successful call records its selected start and the checkpoint tests along its walk.

Each operation has one walk, shared by its root-selection and checkpoint-check interfaces.

This result does not establish safety in an execution or in another store.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The checkpoint tests passed by a block confirmed after the selected start.

The start satisfies the lower freshness bound `currentEpoch ≤ startEpoch + 1`.

This bound permits future start epochs.

For a current-epoch root after a non-current start, the target-justification Boolean test passes.

A non-current root has a recent voting source, either its own or the previous-slot head's.

In the latter case the ancestry Boolean test also passes.

Away from an epoch boundary, the applicable no-conflict Boolean test passes.

The applicable unrealized justification is recent.

These are successful checks, not conclusions of actual justification or execution safety. -/
def Checked (store : Store preset fork) (config : Config) (fcr : FastConfirmationStore)
    (head start root : Root) : Prop :=
  ∃ epoch slot rootEpoch startEpoch,
    store.getCurrentStoreEpoch config = .ok epoch ∧ store.getCurrentSlot config = .ok slot ∧
    store.getBlockEpoch root = .ok rootEpoch ∧ store.getBlockEpoch start = .ok startEpoch ∧
    epoch.toNat ≤ startEpoch.toNat + 1 ∧
    ((startEpoch.toNat + 1 = epoch.toNat ∧ rootEpoch ≠ epoch ∧
      (∃ source, store.getVotingSource config fcr.previousSlotHead = .ok source ∧
          epoch.toNat ≤ source.epoch.toNat + 2 ∧
          store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨root, .pending⟩ = .ok true) ∧
      (isStartSlotAtEpoch preset slot = .ok false →
        store.willNoConflictingCheckpointBeJustified config head = .ok true ∧
        ∃ tip justification, (tip = head ∨ tip = fcr.previousSlotHead) ∧
          store.unrealizedJustification tip = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1)) ∨
      ((isStartSlotAtEpoch preset slot = .ok false →
        ∃ justification, store.unrealizedJustification head = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1) ∧
      (rootEpoch = epoch → startEpoch ≠ epoch →
        store.willCurrentTargetBeJustified config head = .ok true) ∧
      (rootEpoch ≠ epoch →
        (∃ source, store.getVotingSource config root = .ok source ∧
          epoch.toNat ≤ source.epoch.toNat + 2) ∧
        (isStartSlotAtEpoch preset slot = .ok false →
          store.willNoConflictingCheckpointBeJustified config head = .ok true))))

/-- Reading a later root of a walk cannot decrease the block epoch. -/
private theorem walk_epoch_le {head start root : Root} {roots : List Root}
    {startEpoch rootEpoch : Epoch}
    (walked : store.getAncestorRoots head start = .ok roots) (member : root ∈ roots)
    (startOk : store.getBlockEpoch start = .ok startEpoch)
    (rootOk : store.getBlockEpoch root = .ok rootEpoch) : startEpoch ≤ rootEpoch := by
  obtain ⟨b, t, bOk, tOk, lt⟩ := slot_lt_of_mem_getAncestorRoots walked (by simp) member
  simp [getBlockEpoch, bOk, tOk, bind, Except.bind, pure, Except.pure] at startOk rootOk
  subst startEpoch
  subst rootEpoch
  exact UInt64.le_iff_toNat_le.mpr (by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp lt)))

/-- A loop over an increasing walk records a target check whenever it crosses the start epoch. -/
private theorem target_checked_loop {head start init out : Root} {roots : List Root}
    {body : Root → Root → Except ForkChoiceError (ForInStep Root)}
    (walked : store.getAncestorRoots head start = .ok roots)
    (initial : ∀ se ie, store.getBlockEpoch start = .ok se →
      store.getBlockEpoch init = .ok ie → se ≤ ie ∧
        (se ≠ ie → store.willCurrentTargetBeJustified config head = .ok true))
    (step : ∀ x s r, body x s = .ok r →
      r = .done s ∨ r = .yield x ∧
        ∃ se, store.getBlockEpoch s = .ok se ∧
          ∀ xe, store.getBlockEpoch x = .ok xe →
            (se < xe → store.willCurrentTargetBeJustified config head = .ok true))
    (looped : forIn roots init body = .ok out) :
    ∀ se oe, store.getBlockEpoch start = .ok se → store.getBlockEpoch out = .ok oe →
      se ≤ oe ∧ (se ≠ oe → store.willCurrentTargetBeJustified config head = .ok true) := by
  apply forIn_ok_invariant (fun _ s => ∀ se ie, store.getBlockEpoch start = .ok se →
    store.getBlockEpoch s = .ok ie → se ≤ ie ∧
      (se ≠ ie → store.willCurrentTargetBeJustified config head = .ok true))
    _ initial ?_ ?_ (fun _ h => h) looped
  · intro read x rest s s' split holds stepped
    rcases step x s _ stepped with stopped | ⟨went, ie, oldOk, crossed⟩
    · cases stopped
    obtain rfl := ForInStep.yield.inj went
    intro se xe startOk xOk
    have le := walk_epoch_le walked (split ▸ (by simp)) startOk xOk
    refine ⟨le, ?_⟩
    intro different
    -- A successful step reads the old state epoch before it can yield.
    by_cases checked : store.willCurrentTargetBeJustified config head = .ok true
    · exact checked
    have old := holds se ie startOk oldOk
    have same : se = ie := Classical.byContradiction (fun different => checked (old.2 different))
    subst ie
    exact crossed xe xOk (UInt64.lt_iff_toNat_lt.mpr (by
      have := UInt64.le_iff_toNat_le.mp le
      have := mt UInt64.toNat_inj.mp different
      omega))
  · intro read x rest s s' split holds stepped
    rcases step x s _ stepped with stopped | ⟨went, crossed⟩
    · exact ForInStep.done.inj stopped ▸ holds
    · cases went

/-- The descendant walk retains one-confirmed roots and its conditional checkpoint checks. -/
private theorem findLatestConfirmedDescendant_walk {fcr : FastConfirmationStore}
    {head start root : Root}
    (found : store.findLatestConfirmedDescendant config fcr head start = .ok root) :
    root = start ∨
      (∃ balanceSource chain later,
        store.checkpointState fcr.currentEpochObservedJustifiedCheckpoint = .ok balanceSource ∧
        store.getAncestorRoots head start = .ok (chain ++ root :: later) ∧
        ∀ member ∈ chain ++ [root], store.isOneConfirmed config head balanceSource
          (store.tallyVotes balanceSource) member = .ok true) ∧
      ((∀ epoch startEpoch, store.getCurrentStoreEpoch config = .ok epoch →
        store.getBlockEpoch start = .ok startEpoch → epoch.toNat ≤ startEpoch.toNat + 1) →
        store.Checked config fcr head start root) := by
  unfold findLatestConfirmedDescendant at found
  rw [bind_ok_iff] at found
  obtain ⟨epoch, epochOk, found⟩ := found
  rw [bind_ok_iff] at found
  obtain ⟨slot, slotOk, found⟩ := found
  rw [bind_ok_iff] at found
  obtain ⟨atStart, atStartOk, found⟩ := found
  extract_lets arith recentCheck source tally confirmedRoot finish current previous at found
  let good (root : Root) : Prop := ∃ state, source = .ok state ∧
    store.isOneConfirmed config head state (store.tallyVotes state) root = .ok true
  let chainTo (root : Root) : Prop := root = start ∨ ∃ chain later,
    store.getAncestorRoots head start = .ok (chain ++ root :: later) ∧
    ∀ member ∈ chain ++ [root], good member
  suffices result : chainTo root ∧
      ((∀ epoch startEpoch, store.getCurrentStoreEpoch config = .ok epoch →
        store.getBlockEpoch start = .ok startEpoch → epoch.toNat ≤ startEpoch.toNat + 1) →
        root = start ∨ store.Checked config fcr head start root) by
    rcases result.1 with same | ⟨chain, later, walked, allGood⟩
    · exact Or.inl same
    · by_cases same : root = start
      · exact Or.inl same
      refine Or.inr ⟨?_, fun recent => (result.2 recent).resolve_left same⟩
      obtain ⟨balanceSource, sourced, _⟩ := allGood root (by simp)
      refine ⟨balanceSource, chain, later, sourced, walked, ?_⟩
      intro member isMember
      obtain ⟨other, otherSourced, confirmed⟩ := allGood member isMember
      obtain rfl : balanceSource = other := Except.ok.inj (sourced.symm.trans otherSourced)
      exact confirmed
  have oneStep {x s : Root} {r : ForInStep Root}
      (stepped : (do
        if !(← store.isOneConfirmed config head (← source) (← tally) x) then
          return ForInStep.done s
        return ForInStep.yield x) = .ok r) :
      r = .done s ∨ r = .yield x ∧ good x := by
    simp only [bind_ok_iff] at stepped
    obtain ⟨state, stateOk, votes, votesOk, confirmed, confirmedOk, stepped⟩ := stepped
    change source.map store.tallyVotes = .ok votes at votesOk
    rw [stateOk] at votesOk
    simp only [Except.map, Except.ok.injEq] at votesOk
    subst votes
    cases confirmed <;>
      simp only [Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq] at stepped
    · exact Or.inl stepped.symm
    · exact Or.inr ⟨stepped.symm, state, stateOk, confirmedOk⟩
  have notStart (h : isStartSlotAtEpoch preset slot = .ok false) : atStart = false :=
    Except.ok.inj (atStartOk.symm.trans h)
  have recentNat {e : Epoch} {gap : UInt64}
      (checked : recentCheck e gap = .ok true) : epoch.toNat ≤ e.toNat + gap.toNat := by
    simp only [recentCheck, arith, bind_ok_iff] at checked
    obtain ⟨sum, sumOk, checked⟩ := checked
    have sumValue := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
    have le : epoch ≤ sum := by simpa [pure, Except.pure] using checked.symm
    have := UInt64.le_iff_toNat_le.mp le
    omega
  let previousChecks (mid : Root) : Prop :=
    ∃ se, store.getBlockEpoch start = .ok se ∧
      (mid = start ∨ ∃ me source, store.getBlockEpoch mid = .ok me ∧
        se.toNat + 1 = epoch.toNat ∧ me ≠ epoch ∧
        store.getVotingSource config fcr.previousSlotHead = .ok source ∧
        epoch.toNat ≤ source.epoch.toNat + 2 ∧
        store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨mid, .pending⟩ = .ok true ∧
        (isStartSlotAtEpoch preset slot = .ok false →
          store.willNoConflictingCheckpointBeJustified config head = .ok true ∧
          ∃ tip justification, (tip = head ∨ tip = fcr.previousSlotHead) ∧
            store.unrealizedJustification tip = .ok justification ∧
            epoch.toNat ≤ justification.epoch.toNat + 1))
  -- The gates of the first walk supply checks shared by every root that it accepts.
  have reach : ∃ previousEpochOk se, store.getBlockEpoch start = .ok se ∧
      (previousEpochOk = true →
        se.toNat + 1 = epoch.toNat ∧
        ∃ votingSource, store.getVotingSource config fcr.previousSlotHead = .ok votingSource ∧
          epoch.toNat ≤ votingSource.epoch.toNat + 2 ∧
          (isStartSlotAtEpoch preset slot = .ok false →
            store.willNoConflictingCheckpointBeJustified config head = .ok true ∧
            ∃ tip justification, (tip = head ∨ tip = fcr.previousSlotHead) ∧
              store.unrealizedJustification tip = .ok justification ∧
              epoch.toNat ≤ justification.epoch.toNat + 1)) ∧
      previous previousEpochOk = .ok root := by
    clear_value previous
    simp only [bind_ok_iff] at found
    obtain ⟨se, seOk, sum, sumOk, found⟩ := found
    have sumValue := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
    split at found
    · exact ⟨false, se, seOk, by simp, found⟩
    · rename_i same
      have seValue : se.toNat + 1 = epoch.toNat := by
        have equal : sum = epoch := by simpa using same
        subst sum
        simpa using sumValue.symm
      simp only [bind_ok_iff] at found
      obtain ⟨votingSource, votingOk, sourceRecent, sourceRecentOk, found⟩ := found
      split at found
      · exact ⟨false, se, seOk, by simp, found⟩
      · rename_i sourcePass
        have sourceBound : epoch.toNat ≤ votingSource.epoch.toNat + 2 :=
          recentNat (by have pass : sourceRecent = true := by simpa using sourcePass
                        exact pass ▸ sourceRecentOk)
        split at found
        · rename_i firstSlot
          refine ⟨true, se, seOk, fun _ => ⟨seValue, votingSource, votingOk, sourceBound, ?_⟩,
            found⟩
          intro h
          have := notStart h
          simp_all
        · simp only [bind_ok_iff] at found
          obtain ⟨noConflict, noConflictOk, found⟩ := found
          split at found
          · exact ⟨false, se, seOk, by simp, found⟩
          · rename_i noConflictPass
            have noConflictOk : store.willNoConflictingCheckpointBeJustified config head =
                .ok true := by
              have pass : noConflict = true := by simpa using noConflictPass
              exact pass ▸ noConflictOk
            simp only [bind_ok_iff] at found
            obtain ⟨justification, justificationOk, justificationRecent, justificationRecentOk,
              found⟩ := found
            split at found
            · rename_i justificationPass
              refine ⟨true, se, seOk, fun _ => ⟨seValue, votingSource, votingOk, sourceBound,
                fun _ => ⟨noConflictOk, fcr.previousSlotHead, justification, Or.inr rfl,
                  justificationOk, ?_⟩⟩, found⟩
              exact recentNat (justificationPass ▸ justificationRecentOk)
            · simp only [bind_ok_iff] at found
              obtain ⟨headJustification, headJustificationOk, headRecent, headRecentOk, found⟩ :=
                found
              refine ⟨headRecent, se, seOk, fun passed => ⟨seValue, votingSource, votingOk,
                sourceBound, fun _ => ⟨noConflictOk, head, headJustification, Or.inl rfl,
                  headJustificationOk, ?_⟩⟩, found⟩
              exact recentNat (passed ▸ headRecentOk)
  clear found
  obtain ⟨previousEpochOk, se, seOk, previousOk, found⟩ := reach
  -- Each accepted root adds its own epoch and ancestry checks to those shared checks.
  have first : ∃ mid, previousChecks mid ∧ chainTo mid ∧ current () mid = .ok root := by
    simp only [previous] at found
    split at found
    · rename_i passed
      obtain ⟨seValue, votingSource, votingOk, sourceBound, boundary⟩ := previousOk passed
      rw [bind_ok_iff] at found
      obtain ⟨walk, walked, found⟩ := found
      rw [bind_ok_iff] at found
      obtain ⟨mid, looped, found⟩ := found
      have accepted := forIn_ok_last_kept (kept := fun x => good x ∧ ∃ me,
          store.getBlockEpoch x = .ok me ∧ me ≠ epoch ∧
          store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨x, .pending⟩ = .ok true) (by
        intro x s r stepped
        rw [bind_ok_iff] at stepped
        obtain ⟨me, meOk, stepped⟩ := stepped
        split at stepped
        · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
        · rename_i different
          rw [bind_ok_iff] at stepped
          obtain ⟨onChain, onChainOk, stepped⟩ := stepped
          split at stepped
          · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
          · rename_i onChainPass
            exact (oneStep stepped).imp id (fun h =>
              ⟨h.1, h.2, me, meOk, different, by simp_all⟩)) looped
      rcases accepted with same | ⟨before, after, split, all⟩
      · exact ⟨mid, ⟨se, seOk, Or.inl same⟩, Or.inl same, found⟩
      · obtain ⟨_, me, meOk, different, ancestry⟩ := all mid (by simp)
        exact ⟨mid, ⟨se, seOk, Or.inr ⟨me, votingSource, meOk, seValue, different,
          votingOk, sourceBound, ancestry, boundary⟩⟩,
          Or.inr ⟨before, after, split ▸ walked, fun x hx => (all x hx).1⟩, found⟩
    · exact ⟨start, ⟨se, seOk, Or.inl rfl⟩, Or.inl rfl, found⟩
  clear found
  obtain ⟨mid, firstChecks, firstChain, found⟩ := first
  have firstResult (recent : ∀ epoch startEpoch,
      store.getCurrentStoreEpoch config = .ok epoch →
      store.getBlockEpoch start = .ok startEpoch → epoch.toNat ≤ startEpoch.toNat + 1) :
      mid = start ∨ store.Checked config fcr head start mid := by
    obtain ⟨se, seOk, same | ⟨me, source, meOk, seValue, different, sourceOk,
      sourceBound, ancestry, boundary⟩⟩ := firstChecks
    · exact Or.inl same
    · exact Or.inr ⟨epoch, slot, me, se, epochOk, slotOk, meOk, seOk,
        recent epoch se epochOk seOk, Or.inl ⟨seValue, different,
          ⟨source, sourceOk, sourceBound, ancestry⟩, boundary⟩⟩
  simp -zeta only [current] at found
  extract_lets tentative currentBody at found
  have reach : ∃ currentEpochOk,
      (currentEpochOk = true → isStartSlotAtEpoch preset slot = .ok false →
        ∃ justification, store.unrealizedJustification head = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1) ∧
      currentBody currentEpochOk = .ok root := by
    clear_value currentBody
    split at found
    · rename_i firstSlot
      refine ⟨true, fun _ h => ?_, found⟩
      have := notStart h
      simp_all
    · simp only [bind_ok_iff] at found
      obtain ⟨justification, justificationOk, verdict, verdictOk, found⟩ := found
      exact ⟨verdict, fun h _ => ⟨justification, justificationOk,
        recentNat (h ▸ verdictOk)⟩, found⟩
  clear found
  obtain ⟨currentEpochOk, currentChecks, found⟩ := reach
  simp -zeta only [currentBody] at found
  split at found
  · rename_i passed
    rw [bind_ok_iff] at found
    obtain ⟨walk, walked, found⟩ := found
    rw [bind_ok_iff] at found
    obtain ⟨last, looped, found⟩ := found
    extract_lets tentativeRoot accepted acceptBody at found
    change store.getBlockEpoch last >>= _ = .ok root at found
    rw [bind_ok_iff] at found
    obtain ⟨lastEpoch, lastEpochOk, found⟩ := found
    -- Rejection restores the first walk's result, not the tentative result of the second walk.
    have acceptedResult : root = mid ∨ root = last ∧
        (lastEpoch ≠ epoch →
          (∃ source, store.getVotingSource config last = .ok source ∧
            epoch.toNat ≤ source.epoch.toNat + 2) ∧
          (isStartSlotAtEpoch preset slot = .ok false →
            store.willNoConflictingCheckpointBeJustified config head = .ok true)) := by
      have finishResult {accept : Bool} (ended : acceptBody accept = .ok root) :
          (accept = true ∧ root = last) ∨ (accept = false ∧ root = mid) := by
        simp only [acceptBody, finish] at ended
        split at ended
        · exact Or.inl ⟨by assumption, by simpa [pure, Except.pure, tentativeRoot, accepted]
            using ended.symm⟩
        · rename_i notAccepted
          have rejected : accept = false := Bool.eq_false_iff.mpr notAccepted
          exact Or.inr ⟨rejected, by simpa [pure, Except.pure] using ended.symm⟩
      split at found
      · rename_i isCurrent
        simp only [pure, Except.pure, bind, Except.bind] at found
        rcases finishResult (accept := true) found with ⟨_, same⟩ | ⟨bad, _⟩
        · exact Or.inr ⟨same, fun h => False.elim (h isCurrent)⟩
        · cases bad
      · rw [bind_ok_iff] at found
        obtain ⟨votingSource, votingOk, found⟩ := found
        rw [bind_ok_iff] at found
        obtain ⟨sourceRecent, sourceRecentOk, found⟩ := found
        split at found
        · simp only [pure, Except.pure, bind, Except.bind] at found
          rcases finishResult (accept := false) found with ⟨bad, _⟩ | ⟨_, same⟩
          · cases bad
          · exact Or.inl same
        · rename_i recentPass
          have pass : sourceRecent = true := by simpa using recentPass
          have bound := recentNat (pass ▸ sourceRecentOk)
          split at found
          · rename_i firstSlot
            simp only [pure, Except.pure, bind, Except.bind] at found
            rcases finishResult (accept := true) found with ⟨_, same⟩ | ⟨bad, _⟩
            · refine Or.inr ⟨same, fun _ => ⟨⟨votingSource, votingOk, bound⟩, ?_⟩⟩
              intro h
              have := notStart h
              simp_all
            · cases bad
          · rw [bind_ok_iff] at found
            obtain ⟨accept, acceptOk, found⟩ := found
            rcases finishResult found with ⟨rfl, same⟩ | ⟨_, same⟩
            · exact Or.inr ⟨same, fun _ => ⟨⟨votingSource, votingOk, bound⟩,
                fun _ => acceptOk⟩⟩
            · exact Or.inl same
    have step : ∀ x s r, (do
        if (← store.getBlockEpoch x) > (← store.getBlockEpoch s) then
          if !(← store.willCurrentTargetBeJustified config head) then
            return ForInStep.done s
        if !(← store.isOneConfirmed config head (← source) (← tally) x) then
          return ForInStep.done s
        return ForInStep.yield x) = .ok r →
        r = ForInStep.done s ∨ r = .yield x ∧ good x ∧
          ∃ se, store.getBlockEpoch s = .ok se ∧
            ∀ xe, store.getBlockEpoch x = .ok xe →
              (se < xe → store.willCurrentTargetBeJustified config head = .ok true) := by
        intro x s r stepped
        simp only [bind_ok_iff] at stepped
        obtain ⟨xe, xeOk, se, oldOk, stepped⟩ := stepped
        split at stepped
        · rename_i crosses
          rw [bind_ok_iff] at stepped
          obtain ⟨check, checkOk, stepped⟩ := stepped
          split at stepped
          · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
          · rename_i checkPass
            exact (oneStep stepped).imp id (fun h =>
              ⟨h.1, h.2, se, oldOk, fun _ _ _ => by simp_all⟩)
        · rename_i noCross
          refine (oneStep stepped).imp id (fun h => ⟨h.1, h.2, se, oldOk, ?_⟩)
          intro other otherOk lt
          obtain rfl : xe = other := Except.ok.inj (xeOk.symm.trans otherOk)
          exact absurd lt noCross
    have second := forIn_ok_last_kept (kept := good) (fun x s r h =>
      (step x s r h).imp id (fun h => ⟨h.1, h.2.1⟩)) looped
    have target := target_checked_loop (config := config) walked (by
      intro me ie meOk ieOk
      have same : me = ie := Except.ok.inj (meOk.symm.trans ieOk)
      subst ie
      exact ⟨UInt64.le_refl _, by simp⟩) (fun x s r h =>
        (step x s r h).imp id (fun h => ⟨h.1, h.2.2⟩)) looped
    rcases acceptedResult with rfl | ⟨rfl, acceptedChecks⟩
    · exact ⟨firstChain, firstResult⟩
    · refine ⟨?_, ?_⟩
      · rcases second with same | ⟨chain, later, split, allGood⟩
        · exact same ▸ firstChain
        · subst split
          rcases firstChain with rfl | ⟨earlier, between, firstWalked, earlierGood⟩
          · exact Or.inr ⟨chain, later, walked, allGood⟩
          · have rest := getAncestorRoots_of_append firstWalked
            obtain rfl : between = chain ++ root :: later :=
              Except.ok.inj (rest.symm.trans walked)
            refine Or.inr ⟨earlier ++ mid :: chain, later, by simpa using firstWalked, ?_⟩
            intro member isMember
            rw [show earlier ++ mid :: chain ++ [root] =
              (earlier ++ [mid]) ++ (chain ++ [root]) by simp] at isMember
            exact (List.mem_append.mp isMember).elim (earlierGood member) (allGood member)
      · intro recent
        obtain ⟨se, seOk, firstCases⟩ := firstChecks
        have startToMid : ∃ me, store.getBlockEpoch mid = .ok me := by
          rcases firstCases with rfl | ⟨me, source, meOk, rest⟩
          · exact ⟨se, seOk⟩
          · exact ⟨me, meOk⟩
        obtain ⟨me, meOk⟩ := startToMid
        have lastTarget := target me lastEpoch meOk lastEpochOk
        refine Or.inr ⟨epoch, slot, lastEpoch, se, epochOk, slotOk, lastEpochOk, seOk,
          recent epoch se epochOk seOk, Or.inr ⟨currentChecks passed, ?_, acceptedChecks⟩⟩
        intro lastCurrent startDifferent
        have midDifferent : me ≠ lastEpoch := by
          intro same
          subst me
          rcases firstCases with same | ⟨_, _, midOk, seValue, midNotCurrent, _⟩
          · subst mid
            have := Except.ok.inj (seOk.symm.trans meOk)
            exact startDifferent (this.trans lastCurrent)
          · have := Except.ok.inj (midOk.symm.trans meOk)
            exact midNotCurrent (this.trans lastCurrent)
        exact lastTarget.2 midDifferent
  · have same : root = mid := by simpa [finish, pure, Except.pure] using found.symm
    exact same ▸ ⟨firstChain, firstResult⟩

/-- The descendant search records the applicable checkpoint checks for its selected start. -/
theorem findLatestConfirmedDescendant_checked {fcr : FastConfirmationStore}
    {head start root : Root}
    (recent : ∀ epoch startEpoch, store.getCurrentStoreEpoch config = .ok epoch →
      store.getBlockEpoch start = .ok startEpoch → epoch.toNat ≤ startEpoch.toNat + 1)
    (found : store.findLatestConfirmedDescendant config fcr head start = .ok root) :
    root = start ∨ store.Checked config fcr head start root := by
  exact (findLatestConfirmedDescendant_walk found).imp id (fun h => h.2 recent)

/-- The descendant is the start or the end of a one-confirmed walk from that start. -/
theorem findLatestConfirmedDescendant_eq_or {fcr : FastConfirmationStore}
    {head start root : Root}
    (found : store.findLatestConfirmedDescendant config fcr head start = .ok root) :
    root = start ∨ ∃ balanceSource chain later,
      store.checkpointState fcr.currentEpochObservedJustifiedCheckpoint = .ok balanceSource ∧
      store.getAncestorRoots head start = .ok (chain ++ root :: later) ∧
      ∀ member ∈ chain ++ [root], store.isOneConfirmed config head balanceSource
        (store.tallyVotes balanceSource) member = .ok true := by
  exact (findLatestConfirmedDescendant_walk found).imp id And.left

/-- The selected start carries the reset and replacement checks of the actual call.

Keeping the stored root requires the lower freshness bound, which permits future epochs.

The ancestry and applicable chain-safety Boolean checks must also pass.

Otherwise the base is the finalized root.

Replacing the base requires the epoch-boundary and preceding-epoch checks to pass.

The unrealized-justification and strictly-later-slot checks must also pass.

The returned root is that start or passes its applicable checkpoint checks. -/
private theorem getLatestConfirmed_walk {fcr : FastConfirmationStore} {head root : Root}
    (latest : store.getLatestConfirmed config fcr head = .ok root) :
    ∃ slot start, store.getCurrentSlot config = .ok slot ∧
      (∃ base,
        (base = fcr.confirmedRoot ∧
            ((∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
                store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
                epoch.toNat ≤ blockEpoch.toNat + 1) ∧
              store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
              (isStartSlotAtEpoch preset slot = .ok true →
                store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true)) ∨
          base = store.finalizedCheckpoint.root ∧
            ¬((∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
                store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
                epoch.toNat ≤ blockEpoch.toNat + 1) ∧
              store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
              (isStartSlotAtEpoch preset slot = .ok true →
                store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true))) ∧
        (start = base ∧
            ¬(isStartSlotAtEpoch preset slot = .ok true ∧
              (∃ observedBlock epoch,
                store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
                store.getCurrentStoreEpoch config = .ok epoch ∧
                Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
              store.unrealizedJustification head =
                .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
              ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
                store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
                baseBlock.slot < observedBlock.slot) ∨
          start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧
            isStartSlotAtEpoch preset slot = .ok true ∧
            (∃ observedBlock epoch,
              store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
              store.getCurrentStoreEpoch config = .ok epoch ∧
              Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
            store.unrealizedJustification head =
              .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
            ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
              store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
              baseBlock.slot < observedBlock.slot)) ∧
      (root = start ∨ store.Checked config fcr head start root ∧
        store.findLatestConfirmedDescendant config fcr head start = .ok root ∧
        ∃ balanceSource chain later,
          store.checkpointState fcr.currentEpochObservedJustifiedCheckpoint = .ok balanceSource ∧
          store.getAncestorRoots head start = .ok (chain ++ root :: later) ∧
          ∀ member ∈ chain ++ [root], store.isOneConfirmed config head balanceSource
            (store.tallyVotes balanceSource) member = .ok true) := by
  unfold getLatestConfirmed at latest
  rw [bind_ok_iff] at latest
  obtain ⟨currentEpoch, epochFound, latest⟩ := latest
  rw [bind_ok_iff] at latest
  obtain ⟨slot, slotFound, latest⟩ := latest
  refine ⟨slot, ?_⟩
  extract_lets arith confirmedRoot observed finish observedRoot afterReset finalizedRoot
    resetBody at latest
  -- The three checks that keep the block stored before.
  let kept : Prop :=
    (∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
      store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
      epoch.toNat ≤ blockEpoch.toNat + 1) ∧
    store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
    (isStartSlotAtEpoch preset slot = .ok true →
      store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true)
  -- Keep the reset decision paired with the continuation that consumes it.
  have reset : ∃ reset, (reset = false → kept) ∧ (reset = true → ¬kept) ∧
      resetBody reset = .ok root := by
    clear_value resetBody
    rw [bind_ok_iff] at latest
    obtain ⟨blockEpoch, blockEpochOk, latest⟩ := latest
    rw [bind_ok_iff] at latest
    obtain ⟨sum, sumOk, latest⟩ := latest
    have sumValue := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
    simp only [UInt64.toNat_one] at sumValue
    -- The epoch check of `kept` is the negation of the staleness test of the rule.
    have epochCheck : (∃ epoch be, store.getCurrentStoreEpoch config = .ok epoch ∧
        store.getBlockEpoch fcr.confirmedRoot = .ok be ∧ epoch.toNat ≤ be.toNat + 1) ↔
        ¬sum < currentEpoch := by
      constructor
      · rintro ⟨epoch, be, epochOk, beOk, le⟩ stale
        obtain rfl : currentEpoch = epoch := Except.ok.inj (epochFound.symm.trans epochOk)
        obtain rfl : blockEpoch = be := Except.ok.inj (blockEpochOk.symm.trans beOk)
        have := UInt64.lt_iff_toNat_lt.mp stale
        omega
      · intro fresh
        have := UInt64.not_lt.mp fresh
        refine ⟨currentEpoch, blockEpoch, epochFound, blockEpochOk, ?_⟩
        have := UInt64.le_iff_toNat_le.mp this
        omega
    split at latest
    · rename_i stale
      exact ⟨true, by simp, fun _ held => epochCheck.mp held.1 stale, latest⟩
    · rename_i fresh
      rw [bind_ok_iff] at latest
      obtain ⟨onChain, ancestry, latest⟩ := latest
      split at latest
      · rename_i offChain
        refine ⟨true, by simp, fun _ held => ?_, latest⟩
        have same := Except.ok.inj (ancestry.symm.trans held.2.1)
        simp [same] at offChain
      · rename_i isOnChain
        obtain rfl : onChain = true := by simpa using isOnChain
        rw [bind_ok_iff] at latest
        obtain ⟨atStart, startChecked, latest⟩ := latest
        split at latest
        · rename_i startTrue
          obtain rfl : atStart = true := by simpa using startTrue
          rw [bind_ok_iff] at latest
          obtain ⟨safe, chainChecked, latest⟩ := latest
          refine ⟨!safe, fun notReset => ⟨epochCheck.mpr fresh, ancestry, fun _ => ?_⟩,
            fun isReset held => ?_, latest⟩
          · obtain rfl : safe = true := by simpa using notReset
            exact chainChecked
          · have same := Except.ok.inj (chainChecked.symm.trans (held.2.2 startChecked))
            simp [same] at isReset
        · rename_i notStart
          refine ⟨false, fun _ => ⟨epochCheck.mpr fresh, ancestry, fun isStart => ?_⟩,
            by simp, latest⟩
          exact absurd (Except.ok.inj (startChecked.symm.trans isStart)) (by simpa using notStart)
  clear latest
  obtain ⟨reset, keeps, drops, latest⟩ := reset
  have base : ∃ base, (base = fcr.confirmedRoot ∧ kept ∨
      base = store.finalizedCheckpoint.root ∧ ¬kept) ∧ afterReset () base = .ok root := by
    cases reset
    · exact ⟨fcr.confirmedRoot, Or.inl ⟨rfl, keeps rfl⟩, latest⟩
    · exact ⟨store.finalizedCheckpoint.root, Or.inr ⟨rfl, drops rfl⟩, latest⟩
  clear latest keeps drops
  obtain ⟨base, baseCase, latest⟩ := base
  -- The observed checkpoint replaces this base exactly when all four replacement checks pass.
  let over : Prop :=
    isStartSlotAtEpoch preset slot = .ok true ∧
    (∃ observedBlock epoch,
      store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
      store.getCurrentStoreEpoch config = .ok epoch ∧
      Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
    store.unrealizedJustification head = .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
    ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
      store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
      baseBlock.slot < observedBlock.slot
  have start : ∃ start, (start = base ∧ ¬over ∨
      start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧ over) ∧
      finish () start = .ok root := by
    clear_value finish
    simp only [afterReset, bind_ok_iff] at latest
    obtain ⟨atStart, startChecked, observedBlock, observedFound, observedEpoch, epochAdded,
      justified, justification, baseBlock, baseFound, latest⟩ := latest
    split at latest
    · rename_i replaced
      refine ⟨observedRoot, Or.inr ⟨rfl, replaced.1 ▸ startChecked,
        ⟨observedBlock, currentEpoch, observedFound, epochFound,
          replaced.2.1 ▸ mapError_ok_iff.mp epochAdded⟩,
        justification.trans (congrArg Except.ok replaced.2.2.1.symm),
        baseBlock, observedBlock, baseFound, observedFound, replaced.2.2.2⟩, latest⟩
    · rename_i kept'
      refine ⟨base, Or.inl ⟨rfl, ?_⟩, latest⟩
      rintro ⟨isStart, ⟨ob, epoch, obFound, epochOk, added⟩, headJustified, bb, ob', bbFound,
        ob'Found, lower'⟩
      apply kept'
      obtain rfl : atStart = true := Except.ok.inj (startChecked.symm.trans isStart)
      obtain rfl : ob = observedBlock := Except.ok.inj (obFound.symm.trans observedFound)
      obtain rfl : ob' = ob := Except.ok.inj (ob'Found.symm.trans obFound)
      obtain rfl : bb = baseBlock := Except.ok.inj (bbFound.symm.trans baseFound)
      obtain rfl : epoch = currentEpoch := Except.ok.inj (epochOk.symm.trans epochFound)
      have sameEpoch : observedEpoch = epoch :=
        Except.ok.inj ((mapError_ok_iff.mp epochAdded).symm.trans added)
      have sameJustified : justified = fcr.currentEpochObservedJustifiedCheckpoint :=
        Except.ok.inj (justification.symm.trans headJustified)
      exact ⟨rfl, sameEpoch, sameJustified.symm, lower'⟩
  clear latest
  obtain ⟨start, startCase, latest⟩ := start
  refine ⟨start, slotFound, ⟨base, baseCase, startCase⟩, ?_⟩
  simp only [finish, bind_ok_iff] at latest
  obtain ⟨startEpoch, startOk, sum, sumOk, latest⟩ := latest
  split at latest
  · rename_i recentStart
    have recent : ∀ epoch se, store.getCurrentStoreEpoch config = .ok epoch →
        store.getBlockEpoch start = .ok se → epoch.toNat ≤ se.toNat + 1 := by
      intro epoch se epochOk seOk
      obtain rfl : currentEpoch = epoch := Except.ok.inj (epochFound.symm.trans epochOk)
      obtain rfl : startEpoch = se := Except.ok.inj (startOk.symm.trans seOk)
      have value := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
      have le := UInt64.le_iff_toNat_le.mp recentStart
      simp only [UInt64.toNat_one] at value
      omega
    rcases findLatestConfirmedDescendant_walk latest with same | ⟨chain, checked⟩
    · exact Or.inl same
    · exact Or.inr ⟨checked recent, latest, chain⟩
  · exact Or.inl (Except.ok.inj latest).symm

/-- The selected start retains its reset, replacement and descendant checkpoint checks. -/
theorem getLatestConfirmed_checked_start {fcr : FastConfirmationStore} {head root : Root}
    (latest : store.getLatestConfirmed config fcr head = .ok root) :
    ∃ slot start, store.getCurrentSlot config = .ok slot ∧
      (∃ base,
        (base = fcr.confirmedRoot ∧
            ((∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
                store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
                epoch.toNat ≤ blockEpoch.toNat + 1) ∧
              store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
              (isStartSlotAtEpoch preset slot = .ok true →
                store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true)) ∨
          base = store.finalizedCheckpoint.root ∧
            ¬((∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
                store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
                epoch.toNat ≤ blockEpoch.toNat + 1) ∧
              store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
              (isStartSlotAtEpoch preset slot = .ok true →
                store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true))) ∧
        (start = base ∧
            ¬(isStartSlotAtEpoch preset slot = .ok true ∧
              (∃ observedBlock epoch,
                store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
                store.getCurrentStoreEpoch config = .ok epoch ∧
                Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
              store.unrealizedJustification head =
                .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
              ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
                store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
                baseBlock.slot < observedBlock.slot) ∨
          start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧
            isStartSlotAtEpoch preset slot = .ok true ∧
            (∃ observedBlock epoch,
              store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
              store.getCurrentStoreEpoch config = .ok epoch ∧
              Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
            store.unrealizedJustification head =
              .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
            ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
              store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
              baseBlock.slot < observedBlock.slot)) ∧
      (root = start ∨ store.Checked config fcr head start root ∧
        store.findLatestConfirmedDescendant config fcr head start = .ok root) := by
  obtain ⟨slot, start, slotOk, startCase, result⟩ := getLatestConfirmed_walk latest
  exact ⟨slot, start, slotOk, startCase,
    result.imp id (fun h => ⟨h.1, h.2.1⟩)⟩

/-- The latest confirmed block is a selected start or its latest confirmed descendant. -/
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
          (∃ observedBlock epoch,
            store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
            store.getCurrentStoreEpoch config = .ok epoch ∧
            Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
          store.unrealizedJustification head =
            .ok fcr.currentEpochObservedJustifiedCheckpoint) ∧
      (root = start ∨ store.findLatestConfirmedDescendant config fcr head start = .ok root) := by
  obtain ⟨slot, start, slotOk, ⟨base, baseCase, startCase⟩, result⟩ :=
    getLatestConfirmed_walk latest
  refine ⟨slot, start, slotOk, ?_, result.imp id (fun h => h.2.1)⟩
  rcases startCase with ⟨rfl, _⟩ | ⟨same, boundary, observed, justified, _⟩
  · rcases baseCase with ⟨same, _, ancestry, safe⟩ | ⟨same, _⟩
    · exact Or.inl ⟨same, ancestry, safe⟩
    · exact Or.inr (Or.inl same)
  · exact Or.inr (Or.inr ⟨same, boundary, observed, justified⟩)

/-- The checkpoint update records the epoch boundary tests of the same slot. -/
private theorem updateFastConfirmationVariables_checkpoints
    {fcr after : FastConfirmationStore} {head : Root}
    (updated : store.updateFastConfirmationVariables config fcr head = .ok after) :
    ∃ slot, store.getCurrentSlot config = .ok slot ∧
      (∀ next, addChecked slot 1 = .ok next →
        isStartSlotAtEpoch preset next = .ok true →
        after.previousEpochGreatestUnrealizedCheckpoint = store.unrealizedJustifiedCheckpoint) ∧
      (∀ next, addChecked slot 1 = .ok next →
        isStartSlotAtEpoch preset next = .ok false →
        after.previousEpochGreatestUnrealizedCheckpoint =
          fcr.previousEpochGreatestUnrealizedCheckpoint) ∧
      (isStartSlotAtEpoch preset slot = .ok true →
        after.currentEpochObservedJustifiedCheckpoint =
          after.previousEpochGreatestUnrealizedCheckpoint ∧
        after.previousEpochObservedJustifiedCheckpoint =
          fcr.currentEpochObservedJustifiedCheckpoint) ∧
      (isStartSlotAtEpoch preset slot = .ok false →
        after.currentEpochObservedJustifiedCheckpoint =
          fcr.currentEpochObservedJustifiedCheckpoint ∧
        after.previousEpochObservedJustifiedCheckpoint =
          fcr.previousEpochObservedJustifiedCheckpoint) := by
  unfold updateFastConfirmationVariables at updated
  simp only [bind_ok_iff] at updated
  obtain ⟨slot, slotOk, next, nextOk, nextStart, nextStartOk, updated⟩ := updated
  have nextOk := mapError_ok_iff.mp nextOk
  refine ⟨slot, slotOk, ?_⟩
  split at updated <;> simp only [bind_ok_iff] at updated <;>
    obtain ⟨atStart, atStartOk, updated⟩ := updated <;> split at updated <;>
    simp only [pure, Except.pure, Except.ok.injEq] at updated <;> subst updated <;>
    simp_all

/-- A successful call records its selected start, tracked heads and checkpoint-field updates.

Its stored root is that start or a distinct root of its one-confirmed walk passing `Checked`.

The checkpoint tests read the previous-slot head in the store after the call.

Success is the only premise; execution safety is neither assumed nor concluded. -/
theorem onFastConfirmation_checked {fcr after : FastConfirmationStore}
    (confirmed : store.onFastConfirmation config fcr = .ok after) :
    ∃ head slot start, store.getHead config = .ok head ∧
      store.getCurrentSlot config = .ok slot ∧
      after.previousSlotHead = fcr.currentSlotHead ∧
      after.currentSlotHead = head.root ∧
      (∀ next, addChecked slot 1 = .ok next →
        isStartSlotAtEpoch preset next = .ok true →
        after.previousEpochGreatestUnrealizedCheckpoint = store.unrealizedJustifiedCheckpoint) ∧
      (∀ next, addChecked slot 1 = .ok next →
        isStartSlotAtEpoch preset next = .ok false →
        after.previousEpochGreatestUnrealizedCheckpoint =
          fcr.previousEpochGreatestUnrealizedCheckpoint) ∧
      (isStartSlotAtEpoch preset slot = .ok true →
        after.currentEpochObservedJustifiedCheckpoint =
          after.previousEpochGreatestUnrealizedCheckpoint ∧
        after.previousEpochObservedJustifiedCheckpoint =
          fcr.currentEpochObservedJustifiedCheckpoint) ∧
      (isStartSlotAtEpoch preset slot = .ok false →
        after.currentEpochObservedJustifiedCheckpoint =
          fcr.currentEpochObservedJustifiedCheckpoint ∧
        after.previousEpochObservedJustifiedCheckpoint =
          fcr.previousEpochObservedJustifiedCheckpoint) ∧
      (∃ base,
        (base = fcr.confirmedRoot ∧
            ((∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
                store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
                epoch.toNat ≤ blockEpoch.toNat + 1) ∧
              store.isAncestor ⟨head.root, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ =
                .ok true ∧
              (isStartSlotAtEpoch preset slot = .ok true →
                store.isConfirmedChainSafe config after head.root
                  fcr.confirmedRoot = .ok true)) ∨
          base = store.finalizedCheckpoint.root ∧
            ¬((∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
                 store.getBlockEpoch fcr.confirmedRoot = .ok blockEpoch ∧
                 epoch.toNat ≤ blockEpoch.toNat + 1) ∧
               store.isAncestor ⟨head.root, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ =
                 .ok true ∧
               (isStartSlotAtEpoch preset slot = .ok true →
                 store.isConfirmedChainSafe config after head.root
                   fcr.confirmedRoot = .ok true))) ∧
        (start = base ∧
            ¬(isStartSlotAtEpoch preset slot = .ok true ∧
               (∃ observedBlock epoch,
                 store.block after.currentEpochObservedJustifiedCheckpoint.root =
                   .ok observedBlock ∧
                 store.getCurrentStoreEpoch config = .ok epoch ∧
                 Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
               store.unrealizedJustification head.root =
                 .ok after.currentEpochObservedJustifiedCheckpoint ∧
               ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
                 store.block after.currentEpochObservedJustifiedCheckpoint.root =
                   .ok observedBlock ∧
                 baseBlock.slot < observedBlock.slot) ∨
          start = after.currentEpochObservedJustifiedCheckpoint.root ∧
            (isStartSlotAtEpoch preset slot = .ok true ∧
              (∃ observedBlock epoch,
                store.block after.currentEpochObservedJustifiedCheckpoint.root =
                  .ok observedBlock ∧
                store.getCurrentStoreEpoch config = .ok epoch ∧
                Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
              store.unrealizedJustification head.root =
                .ok after.currentEpochObservedJustifiedCheckpoint ∧
              ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
                store.block after.currentEpochObservedJustifiedCheckpoint.root =
                  .ok observedBlock ∧
                baseBlock.slot < observedBlock.slot))) ∧
      (after.confirmedRoot = start ∨
        after.confirmedRoot ≠ start ∧
        store.Checked config after head.root start after.confirmedRoot ∧
        ∃ balanceSource chain later,
          store.checkpointState after.currentEpochObservedJustifiedCheckpoint =
            .ok balanceSource ∧
          store.getAncestorRoots head.root start = .ok (chain ++ after.confirmedRoot :: later) ∧
          ∀ member ∈ chain ++ [after.confirmedRoot], store.isOneConfirmed config head.root
            balanceSource (store.tallyVotes balanceSource) member = .ok true) := by
  unfold onFastConfirmation at confirmed
  simp only [bind_ok_iff] at confirmed
  obtain ⟨head, headOk, updated, updateOk, root, latest, confirmed⟩ := confirmed
  simp only [pure, Except.pure, Except.ok.injEq] at confirmed
  subst confirmed
  obtain ⟨slot, start, slotOk, startCase, result⟩ :=
    getLatestConfirmed_walk latest
  obtain ⟨previousHead, currentHead⟩ :=
    Prod.mk.inj (updateFastConfirmationVariables_heads updateOk)
  obtain ⟨updateSlot, updateSlotOk, checkpoints⟩ :=
    updateFastConfirmationVariables_checkpoints updateOk
  have sameSlot : updateSlot = slot := Except.ok.inj (updateSlotOk.symm.trans slotOk)
  subst updateSlot
  rw [updateFastConfirmationVariables_confirmedRoot updateOk] at startCase
  refine ⟨head, slot, start, headOk, slotOk, previousHead, currentHead,
    checkpoints.1, checkpoints.2.1, checkpoints.2.2.1, checkpoints.2.2.2, startCase, ?_⟩
  rcases result with same | ⟨checked, _, walk⟩
  · exact Or.inl same
  · obtain ⟨balanceSource, chain, later, sourceOk, walked, confirmedAll⟩ := walk
    refine Or.inr ⟨fun same => ?_, checked, balanceSource, chain, later, sourceOk, walked,
      confirmedAll⟩
    obtain ⟨b, t, bOk, tOk, lt⟩ := slot_lt_of_mem_getAncestorRoots walked (by simp)
      (List.mem_append_right _ (List.mem_cons_self ..))
    rw [← same] at tOk
    obtain rfl : b = t := Except.ok.inj (bOk.symm.trans tOk)
    exact UInt64.lt_irrefl _ lt

/-- The stored root is a selected start or the end of its one-confirmed walk. -/
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
          (∃ observedBlock epoch,
            store.block after.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
            store.getCurrentStoreEpoch config = .ok epoch ∧
            Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
          store.unrealizedJustification head.root =
            .ok after.currentEpochObservedJustifiedCheckpoint) ∧
      (after.confirmedRoot = start ∨ ∃ balanceSource chain later,
        store.checkpointState after.currentEpochObservedJustifiedCheckpoint = .ok balanceSource ∧
        store.getAncestorRoots head.root start = .ok (chain ++ after.confirmedRoot :: later) ∧
        ∀ member ∈ chain ++ [after.confirmedRoot], store.isOneConfirmed config head.root
          balanceSource (store.tallyVotes balanceSource) member = .ok true) := by
  obtain ⟨head, slot, start, headOk, slotOk, _, _, _, _, _, _,
    ⟨base, baseCase, startCase⟩, result⟩ := onFastConfirmation_checked confirmed
  refine ⟨head, slot, start, headOk, slotOk, ?_, result.imp id (fun h => h.2.2)⟩
  rcases startCase with ⟨rfl, _⟩ | ⟨same, boundary, observed, justified, _⟩
  · rcases baseCase with ⟨same, _, ancestry, safe⟩ | ⟨same, _⟩
    · exact Or.inl ⟨same, ancestry, safe⟩
    · exact Or.inr (Or.inl same)
  · exact Or.inr (Or.inr ⟨same, boundary, observed, justified⟩)

end Store

end EthLib.Consensus
