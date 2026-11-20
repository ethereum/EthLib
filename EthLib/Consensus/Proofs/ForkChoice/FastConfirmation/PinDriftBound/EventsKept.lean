module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.Transition.EpochReads
import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ownership
import Mathlib.Algebra.Order.Floor.Div

@[expose] public section

namespace EthLib.Consensus.Models.Network

open DirectSafety.Apriori.Internal (recordBalance_single)

section

/-! Which validator fields persist through transitions and their recorded events. -/

namespace PinDrift.Internal

open Base Uint64 Models DirectSafety

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- What a chain of steps keeps of the registry, at any forks.

Assigned exits stay, and a slash stays.

The withdrawable epoch of a key with an exit set only rises, and only for a slashed key. -/
structure Kept {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) :
    Prop where
  life : RegistryLifecycle s t
  slashed : SlashedPersistence s t
  withdrawable : WithdrawableKept s t

/-- Two steps keep what one keeps.

The exit of the first comes from its lifecycle, and the slash of the second from its persistence. -/
private theorem Kept.trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : PinDrift.Internal.Kept s t) (two : PinDrift.Internal.Kept t u)
      : PinDrift.Internal.Kept s u where
  life := one.life.trans two.life
  slashed := one.slashed.trans two.slashed
  withdrawable i v w found read far := by
    obtain ⟨m, mFound, step⟩ := one.life.validators i v found
    have mFar : m.exitEpoch ≠ FAR_FUTURE_EPOCH := by rw [step.exitEpoch far]; exact far
    obtain ⟨le1, moved1⟩ := one.withdrawable i v m found mFound far
    obtain ⟨le2, moved2⟩ := two.withdrawable i m w mFound read mFar
    refine ⟨UInt64.le_trans le1 le2, ?_⟩
    rcases moved2 with flag | same
    · exact .inl flag
    · rcases moved1 with flag | same1
      · obtain ⟨w', read', marked⟩ := two.slashed i m mFound flag
        rw [read, Option.some.injEq] at read'
        subst read'
        exact .inl marked
      · exact .inr (same.trans same1)

/-- A state with the same validators keeps everything. -/
private theorem Kept.of_data {f g : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    (same : t.validators.data = s.validators.data) : PinDrift.Internal.Kept s t where
  life := .of_data same
  slashed := .of_data same
  withdrawable i v w found read _ := by
    rw [same, found, Option.some.injEq] at read
    subst read
    exact ⟨UInt64.le_refl _, .inr rfl⟩

/-- A step that keeps the lifecycle, the slashes and each withdrawable epoch keeps everything. -/
private theorem Kept.of_withdrawable {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (life : RegistryLifecycle s t) (slashed : SlashedPersistence s t)
    (same : ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v →
      ∃ w, t.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch) :
    PinDrift.Internal.Kept s t where
  life := life
  slashed := slashed
  withdrawable i v w found read _ := by
    obtain ⟨w', read', equal⟩ := same i v found
    rw [read, Option.some.injEq] at read'
    subst read'
    exact ⟨UInt64.le_of_eq equal.symm, .inr equal⟩

/-- The pending deposits keep every validator of the registry before them as it was. -/
private theorem pendingDeposits_entries {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} (ok : processPendingDeposits config checks s electra = .ok t)
    (i : ℕ) (v : Validator) (found : s.validators.data[i]? = some v) :
    t.validators.data[i]? = some v := by
  obtain ⟨_, _, applied, _, next, _, _, _, _, _, _, _, _, appliedOk, rfl⟩ :=
    processPendingDeposits_applied ok
  have kept := foldlM_ok_invariant
    (fun u : BeaconState preset fork => u.validators.data[i]? = some v)
    (fun u deposit u' previous step => by
      rcases applyPendingDeposit_cases step with rfl | ⟨index, raised⟩ | ⟨_, added⟩
      · exact previous
      · rw [increaseBalance_validators raised]
        exact previous
      · have inside := (Array.getElem?_eq_some_iff.mp previous).1
        rw [addValidatorToRegistry_validators_eq_push added, Array.getElem?_push]
        simp only [Nat.ne_of_lt inside, ↓reduceIte]
        exact previous)
    found appliedOk
  exact kept

/-- The update of the effective balances keeps the withdrawable epoch of each validator. -/
private theorem effectiveUpdates_withdrawable {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i : ℕ) (v : Validator)
    (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch := by
  unfold processEffectiveBalanceUpdates at ok
  refine foldlM_ok_invariant (fun u : BeaconState preset fork =>
    ∃ w, u.validators.data[i]? = some w ∧ w.withdrawableEpoch = v.withdrawableEpoch)
    (fun u j u' previous step => ?_) ⟨v, found, rfl⟩ ok
  obtain ⟨w, read, equal⟩ := previous
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨validator, validatorOk, balance, _, next, _, set⟩ := step
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  by_cases same : i = j
  · subst same
    rw [getValidatorAt_eq_ok_iff.mp validatorOk, Option.some.injEq] at read
    subst read
    exact ⟨{ validator with effectiveBalance := next },
      by simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set], equal⟩
  · refine ⟨w, ?_, equal⟩
    simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set, Ne.symm same,
      same] using read

/-- From Electra, every stage of an epoch keeps the registry. -/
private theorem kept_stage {fork : Fork} {k : EpochStage} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (edge : EpochStage.Edge config checks k s t) : PinDrift.Internal.Kept
      s t := by
  cases k
  case registry =>
    simp only [EpochStage.Edge] at edge
    exact ⟨registryLifecycle_processRegistryUpdates edge,
      .of_frame (frame_processRegistryUpdates edge).toFrame,
      withdrawableKept_processRegistryUpdates electra edge⟩
  case pendingDeposits =>
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact PinDrift.Internal.Kept.of_withdrawable (registryLifecycle_processPendingDeposits edge)
      (.of_frame (frame_processPendingDeposits edge).toFrame)
      fun i v found => ⟨v, pendingDeposits_entries edge i v found, rfl⟩
  case effectiveBalances =>
    simp only [EpochStage.Edge] at edge
    exact PinDrift.Internal.Kept.of_withdrawable (registryLifecycle_processEffectiveBalanceUpdates
      edge)
      (.of_frame (frame_processEffectiveBalanceUpdates edge).toFrame)
      (effectiveUpdates_withdrawable edge)
  all_goals exact PinDrift.Internal.Kept.of_data (congrArg (·.data) (edge.validators_eq ⟨nofun,
    nofun, nofun⟩))

/-- From Electra, a whole epoch transition keeps the registry. -/
private theorem kept_processEpoch {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processEpoch config checks s = .ok t) : PinDrift.Internal.Kept
      s t :=
  (processEpoch_trace ok).transport (fun a b => PinDrift.Internal.Kept a b) (fun _ =>
    PinDrift.Internal.Kept.of_data rfl)
    (fun one two => one.trans two)
    (fun _ _ _ _ computed => kept_stage electra (EpochStage.action_cases.mp computed))

/-- From Electra, a slot of a run keeps the registry. -/
private theorem kept_slot {u w : ForkedBeaconState preset} (electra : .pectra ≤ u.fork)
    (ok : advanceSlotAcross config checks u = .ok w) : PinDrift.Internal.Kept u.state w.state := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, afterEq⟩ := advanceSlot_ok slotOk
  have cachedKept : PinDrift.Internal.Kept u.state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact PinDrift.Internal.Kept.of_data rfl
  have epochKept : PinDrift.Internal.Kept cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact kept_processEpoch electra epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ PinDrift.Internal.Kept.of_data rfl
  have advancedKept : PinDrift.Internal.Kept u.state advanced := by
    rw [afterEq]
    exact cachedKept.trans (epochKept.trans (PinDrift.Internal.Kept.of_data rfl))
  exact (processUpgrades_induction (forked := ⟨u.fork, advanced⟩)
    (property := fun z => .pectra ≤ z.fork ∧ PinDrift.Internal.Kept u.state z.state)
    (fun {_ post} held more => ⟨Nat.le_trans held.1 (Nat.le_of_lt post.property),
      held.2.trans (PinDrift.Internal.Kept.of_data (upgradeNext_validators_of_electra held.1
        more))⟩)
    ⟨electra, advancedKept⟩ upgrades).2

/-- From Fulu and before Gloas, a block keeps the registry. -/
private theorem kept_block {fork : Fork} {a t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, a⟩ = false}
    {ok : applySignedBlock config checks engine a signed true = .ok t}
    (fulu : .fusaka ≤ fork) (early : fork < .glamsterdam) (matched : BalancesMatch a) :
    PinDrift.Internal.Kept a t := by
  have processed := (applySignedBlock_ok ok).2.1
  have frame := frame_processBlock processed
  refine ⟨registryLifecycle_processBlock processed, .of_frame frame, ?_⟩
  exact Run.withdrawableKept_of_same_epoch (Run.nil.snoc (Step.block engine signed due ok)) early
    fulu (by simp only [getCurrentEpoch, frame.slot]) matched

/-- From Fulu and before Gloas, a run keeps the registry. -/
theorem kept_run {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (fulu : .fusaka ≤ x.fork) (tail : Run config checks x y) (early : y.fork < .glamsterdam) :
    PinDrift.Internal.Kept x.state y.state := by
  induction tail with
  | nil => exact PinDrift.Internal.Kept.of_data rfl
  | @snoc middle last pre step ih =>
    have earlyMiddle : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have fuluMiddle : .fusaka ≤ middle.fork :=
      Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
    refine (ih earlyMiddle).trans ?_
    cases step with
    | slot ok =>
      exact kept_slot (Nat.le_trans (by decide) fuluMiddle) ok
    | block engine signed due ok =>
      exact kept_block (engine := engine) (signed := signed) (due := due) (ok := ok)
        fuluMiddle early
        (run_justified_separated (shared.append pre) genesis).1.balancesMatch

/-- A replay step keeps the registry and the slot, and records no deposit event. -/
private structure Grew {f : Fork} (p q : BalanceReplay preset f) : Prop where
  kept : PinDrift.Internal.Kept p.1 q.1
  slot : q.1.slot = p.1.slot
  size : q.1.validators.data.size = p.1.validators.data.size
  events : ∀ e ∈ q.2, e ∈ p.2 ∨ e.source ≠ .deposits

/-- A replay step that does nothing grows the replay. -/
private theorem Grew.refl {f : Fork} (p : BalanceReplay preset f) : Grew p p :=
  ⟨PinDrift.Internal.Kept.of_data rfl, rfl, rfl, fun _ member => .inl member⟩

/-- Two growing replay steps in a row grow the replay. -/
private theorem Grew.trans {f : Fork} {p q r : BalanceReplay preset f} (one : Grew p q)
    (two : Grew q r) : Grew p r where
  kept := one.kept.trans two.kept
  slot := two.slot.trans one.slot
  size := two.size.trans one.size
  events e member := by
    rcases two.events e member with old | other
    · exact one.events e old
    · exact .inr other

/-- A replay event either came from the input log or has the source of the appended events. -/
theorem mem_or_source_of_append {source : BalanceSource}
    {pre post : List (BalanceEvent preset)} {added e : BalanceEvent preset}
    (events : post = pre ++ [added]) (same : added.source = source)
    (member : e ∈ post) : e ∈ pre ∨ e.source = source := by
  rw [events] at member
  rcases List.mem_append.mp member with old | added
  · exact .inl old
  · exact .inr ((congrArg BalanceEvent.source (List.mem_singleton.mp added)).trans same)

/-- A carried pass changes the state by its action and records nothing. -/
theorem carryBalance_cases {f : Fork}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {p q : BalanceReplay preset f} (ok : carryBalance action p = .ok q) :
    action p.1 = .ok q.1 ∧ q.2 = p.2 := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨after, computed, rfl⟩ := ok
  exact ⟨computed, rfl⟩

/-- A replay of reward and penalty deltas keeps the registry and records no deposit. -/
private theorem replayDeltas_grew {f : Fork} {source : BalanceSource}
    {deltas : Array Gwei × Array Gwei} {p q : BalanceReplay preset f}
    (notDeposit : source ≠ .deposits) (ok : replayDeltas source deltas p = .ok q) : Grew p q := by
  unfold replayDeltas at ok
  refine foldlM_ok_invariant (fun r => Grew p r) (fun r i r' previous step => ?_) (Grew.refl p) ok
  refine previous.trans ?_
  simp only [bind_ok_iff] at step
  obtain ⟨index, _, raised, raisedOk, loweredOk⟩ := step
  obtain ⟨_, _, _, raisedAction, raisedEvents⟩ := recordBalance_single raisedOk
  obtain ⟨_, _, _, loweredAction, loweredEvents⟩ := recordBalance_single loweredOk
  have raisedAction := liftAccessor_ok.mp raisedAction
  have loweredAction := liftAccessor_ok.mp loweredAction
  have first : Grew r raised :=
    ⟨PinDrift.Internal.Kept.of_data (congrArg (·.data) (increaseBalance_validators raisedAction)),
      (frame_increaseBalance raisedAction).toFrame.slot,
      congrArg Array.size (congrArg (·.data) (increaseBalance_validators raisedAction)),
      fun e member => by
        rcases PinDrift.Internal.mem_or_source_of_append raisedEvents rfl member with old | new
        · exact .inl old
        · refine .inr ?_
          rw [new]
          exact (show BalanceSource.rewards ≠ .deposits by decide)⟩
  have second : Grew raised r' :=
    ⟨PinDrift.Internal.Kept.of_data (congrArg (·.data) (decreaseBalance_validators loweredAction)),
      (frame_decreaseBalance loweredAction).toFrame.slot,
      congrArg Array.size (congrArg (·.data) (decreaseBalance_validators loweredAction)),
      fun e member => by
        rcases PinDrift.Internal.mem_or_source_of_append loweredEvents rfl member with old | new
        · exact .inl old
        · exact .inr (by rw [new]; exact notDeposit)⟩
  exact first.trans second

/-- The replay of the rewards and penalties keeps the registry and records no deposit. -/
private theorem replayRewards_grew {f : Fork} {p q : BalanceReplay preset f}
    (ok : replayRewards (config := config) p = .ok q) : Grew p q := by
  unfold replayRewards at ok
  split at ok
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact Grew.refl _
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · obtain ⟨middle, middleOk, lastOk⟩ := bind_ok_iff.mp ok
      have first : Grew p middle := foldlM_ok_invariant (fun r => Grew p r)
        (fun _ _ _ previous step => previous.trans (replayDeltas_grew (by decide) step))
        (Grew.refl p) middleOk
      exact first.trans (replayDeltas_grew (by decide) lastOk)
    · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
      obtain ⟨one, oneOk, ok⟩ := bind_ok_iff.mp ok
      obtain ⟨two, twoOk, lastOk⟩ := bind_ok_iff.mp ok
      have middle : Grew one two := foldlM_ok_invariant (fun r => Grew one r)
        (fun _ _ _ previous step => previous.trans (replayDeltas_grew (by decide) step))
        (Grew.refl one) twoOk
      exact ((replayDeltas_grew (by decide) oneOk).trans middle).trans
        (replayDeltas_grew (by decide) lastOk)

/-- From Electra, each stage of an epoch before the pending deposits keeps the registry. -/
private theorem replay_stage {f : Fork} (electra : .pectra ≤ f) {k : EpochStage}
    (member : k ∈ [EpochStage.justification, .inactivity, .rewards, .registry, .slashings,
      .eth1Reset]) {p q : BalanceReplay preset f}
    (ok : epochReplayAction (config := config) (checks := checks) k p = .ok q) : Grew p q := by
  have sizeOf : ∀ {k' : EpochStage} (e : EpochStage.Edge config checks k' p.1 q.1),
      (k' ≠ .registry ∧ k' ≠ .pendingDeposits ∧ k' ≠ .effectiveBalances) →
        q.1.validators.data.size = p.1.validators.data.size := fun e other =>
    congrArg Array.size (congrArg (·.data) (e.validators_eq other))
  have ofEdge (edge : EpochStage.Edge config checks k p.1 q.1) (same : q.2 = p.2)
      (size : q.1.validators.data.size = p.1.validators.data.size) : Grew p q :=
    ⟨kept_stage electra edge, edge.slot_eq, size, fun e member => .inl (same ▸ member)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [epochReplayAction] at ok
    obtain ⟨action, same⟩ := PinDrift.Internal.carryBalance_cases ok
    exact ofEdge action same (sizeOf (k' := .justification) action ⟨nofun, nofun, nofun⟩)
  · simp only [epochReplayAction] at ok
    split at ok
    · obtain ⟨action, same⟩ := PinDrift.Internal.carryBalance_cases ok
      rename_i h
      have edge : EpochStage.Edge config checks .inactivity p.1 q.1 := by
        simp only [EpochStage.Edge, h, ↓reduceDIte]; exact action
      exact ofEdge edge same (sizeOf edge ⟨nofun, nofun, nofun⟩)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact Grew.refl _
  · simp only [epochReplayAction] at ok
    exact replayRewards_grew ok
  · simp only [epochReplayAction] at ok
    obtain ⟨action, same⟩ := PinDrift.Internal.carryBalance_cases ok
    exact ofEdge action same (sameSizes_processRegistryUpdates (config := config)
      (by simpa only [EpochStage.Edge] using action)).1
  · simp only [epochReplayAction] at ok
    obtain ⟨_, _, _, action, events⟩ := recordBalance_single ok
    have edge : EpochStage.Edge config checks .slashings p.1 q.1 := action
    exact ⟨kept_stage electra edge, edge.slot_eq, sizeOf edge ⟨nofun, nofun, nofun⟩,
      fun e member => by
        rcases PinDrift.Internal.mem_or_source_of_append events rfl member with old | new
        · exact .inl old
        · refine .inr ?_
          rw [new]
          exact (show BalanceSource.slashings ≠ .deposits by decide)⟩
  · simp only [epochReplayAction] at ok
    split at ok
    · obtain ⟨action, same⟩ := PinDrift.Internal.carryBalance_cases ok
      rename_i h
      have edge : EpochStage.Edge config checks .eth1Reset p.1 q.1 := by
        simp only [EpochStage.Edge, h, ↓reduceDIte]; exact action
      exact ofEdge edge same (sizeOf edge ⟨nofun, nofun, nofun⟩)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact Grew.refl _

/-- A later state has the exit and withdrawable epochs of an earlier one at its indices. -/
def ExitsStay {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) : Prop :=
  ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v →
    ∃ w, t.validators.data[i]? = some w ∧ w.exitEpoch = v.exitEpoch ∧
      w.withdrawableEpoch = v.withdrawableEpoch

/-- Two states in a row that keep the exits and withdrawable epochs keep them together. -/
private theorem ExitsStay.trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : PinDrift.Internal.ExitsStay s t) (two :
      PinDrift.Internal.ExitsStay t u) : PinDrift.Internal.ExitsStay s u :=
  fun i v found => by
    obtain ⟨m, mFound, exit, wd⟩ := one i v found
    obtain ⟨w, wFound, exit', wd'⟩ := two i m mFound
    exact ⟨w, wFound, exit'.trans exit, wd'.trans wd⟩

/-- A state with the same validators has the same exits. -/
private theorem ExitsStay.of_data {f g : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    (same : t.validators.data = s.validators.data) : PinDrift.Internal.ExitsStay s t :=
  fun i v found => ⟨v, by rw [same]; exact found, rfl, rfl⟩

/-- The state at the input of a slot step's pending deposits, for a deposit event of the step.

It keeps the registry of the step's start, at its epoch and with at most its size.

The step's end state has the exit and withdrawable epochs of that input.

A step with a deposit event ends in a later epoch. -/
theorem Step.deposit_input {u w : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks u = .ok w) (fulu : .fusaka ≤ u.fork)
    (early : w.fork < .glamsterdam) {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks u w).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source = .deposits →
      PinDrift.Internal.Kept u.state e.before.state ∧
      e.before.state.validators.data.size ≤ u.state.validators.data.size ∧
      getCurrentEpoch e.before.state = getCurrentEpoch u.state ∧
      PinDrift.Internal.ExitsStay e.before.state w.state ∧
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch w.state).toNat := by
  intro e member source
  have electraU : .pectra ≤ u.fork := Nat.le_trans (by decide) fulu
  obtain ⟨advanced, cached, crossings, advanceOk, upgrades, cachedOk, crossingOk, branch⟩ :=
    Step.balanceEvents_slot ok early replayed
  have noCrossings : crossings = [] :=
    DirectSafety.Apriori.Internal.upgradeBalanceReplay_electra_nil
      (u := ⟨u.fork, advanced⟩) electraU crossingOk
  rcases branch with ⟨_, eventsEq⟩ | ⟨middle, updated, recorded, recordOk, updatedOk,
      validatorsEq, _, eventsEq, next, nextNat, nextSlot, nextMod, -⟩
  · rw [eventsEq, noCrossings] at member
    cases member
  rw [eventsEq, noCrossings, List.append_nil] at member
  have cachedKept : PinDrift.Internal.Kept u.state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact PinDrift.Internal.Kept.of_data rfl
  have cachedSlot : cached.slot = u.state.slot := (frame_processSlot cachedOk).slot
  have trace := epochBalanceReplay_trace recordOk
  change EpochTrace _ ([EpochStage.justification, .inactivity, .rewards, .registry, .slashings,
    .eth1Reset] ++ [.pendingDeposits, .pendingConsolidations]) _ _ at trace
  obtain ⟨six, head, rest⟩ := EpochTrace.append_iff.mp trace
  have grew : Grew (cached, []) six := head.transport (fun p q => Grew p q) Grew.refl Grew.trans
    (fun _ member _ _ computed => replay_stage electraU member computed)
  cases rest with
  | cons first rest =>
    cases rest with
    | cons second rest =>
      cases rest
      simp only [epochReplayAction, electraU, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at first second
      obtain ⟨deposited, depositOk, rfl⟩ := first
      obtain ⟨consolidated, consolidatedOk, same⟩ := second
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rcases List.mem_append.mp member with old | last
      · rcases List.mem_append.mp old with old | added
        · rcases grew.events e old with listed | other
          · cases listed
          · exact absurd source other
        · rw [List.mem_singleton.mp added]
          have cachedSize : cached.validators.data.size = u.state.validators.data.size := by
            obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
            rfl
          have same : getCurrentEpoch six.1 = getCurrentEpoch u.state := by
            simp only [getCurrentEpoch, grew.slot, cachedSlot]
          have deposits : PinDrift.Internal.ExitsStay six.1 deposited := fun i v found =>
            ⟨v, pendingDeposits_entries depositOk i v found, rfl, rfl⟩
          have consolidations : PinDrift.Internal.ExitsStay deposited consolidated :=
            PinDrift.Internal.ExitsStay.of_data (congrArg (·.data)
              (processPendingConsolidations_fields consolidatedOk).1)
          have updates : PinDrift.Internal.ExitsStay consolidated updated := fun i v found => by
            obtain ⟨balance, owned⟩ := processEffectiveBalanceUpdates_owned updatedOk found
            obtain ⟨_, read, -⟩ :=
              processEffectiveBalanceUpdates_effectiveBalance_eq updatedOk found owned
            exact ⟨_, read, rfl, rfl⟩
          have upgraded : PinDrift.Internal.ExitsStay updated w.state :=
            PinDrift.Internal.ExitsStay.of_data
            ((processUpgrades_validators_of_electra (s := ⟨u.fork, advanced⟩) electraU early
              upgrades).trans (congrArg (·.data) validatorsEq))
          have crossed : (getCurrentEpoch u.state).toNat < (getCurrentEpoch w.state).toNat := by
            rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat,
              (processUpgrades_slot upgrades).trans nextSlot,
              nextSlot_epoch_of_boundary nextNat nextMod]
            omega
          exact ⟨cachedKept.trans grew.kept, (grew.size.trans cachedSize).le, same,
            deposits.trans (consolidations.trans (updates.trans upgraded)), crossed⟩
      · rw [List.mem_singleton.mp last] at source
        cases source

/-- Every deposit event of a slot step of the run starts at a state that keeps the registry.

A slot step records a deposit event only for the pending deposits of its epoch pass.

So the event starts at the input of that pass.

That input is the state after the first six stages of the epoch.

They are justification, inactivity, rewards, registry updates, slashings and the eth1 reset.

The steps of the run before the slot keep the registry, and so does each of those stages.

Block deposits are not covered.

From Electra they credit no existing key.

The registry at the event's start has at most the size of the one at the slot step's start.

A slashed key at the slot step's start is slashed at the event's start, and their epochs agree. -/
theorem Run.events_kept {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam)
    {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w)
    (contained : tail.Contains (Step.slot ok))
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks u w).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source = .deposits →
      RegistryLifecycle x.state e.before.state ∧
      WithdrawableKept x.state e.before.state ∧
      getCurrentEpoch e.before.state ≤ getCurrentEpoch y.state ∧
      e.before.state.validators.data.size ≤ u.state.validators.data.size ∧
      SlashedPersistence u.state e.before.state ∧
      getCurrentEpoch e.before.state = getCurrentEpoch u.state := by
  intro e member source
  obtain ⟨pre, post, rfl⟩ := Run.contains_split tail (Step.slot ok) contained
  have stepFork := (Step.slot ok : Step config checks u w).chainStep.fork_le
  have earlyW : w.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have earlyU : u.fork < .glamsterdam := Nat.lt_of_le_of_lt stepFork earlyW
  have fuluU : .fusaka ≤ u.fork := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
  have run : PinDrift.Internal.Kept x.state u.state := PinDrift.Internal.kept_run shared genesis
    fulu pre earlyU
  have epochLe : getCurrentEpoch u.state ≤ getCurrentEpoch y.state :=
    currentEpoch_le_of_chainSteps
      (Relation.ReflTransGen.head (Step.slot ok : Step config checks u w).chainStep
        post.chainSteps)
  obtain ⟨kept, size, same, -, -⟩ := PinDrift.Internal.Step.deposit_input ok fuluU earlyW replayed e
    member source
  have total := run.trans kept
  exact ⟨total.life, total.withdrawable, same ▸ epochLe, size, kept.slashed, same⟩

end PinDrift.Internal

end

end EthLib.Consensus.Models.Network
