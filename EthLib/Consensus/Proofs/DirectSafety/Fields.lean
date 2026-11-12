module

public import EthLib.Consensus.Proofs.DirectSafety.Provenance
public import EthLib.Consensus.Proofs.DirectSafety.Hashes
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.FfgJustification
public import Mathlib.Tactic.FinCases

/-!
# Concrete justification calls and checkpoint fields

Every call below is at an epoch boundary of the supplied run, on the state that processSlot returns.

The witnesses describe executions of the four bit rules, not an abstract finality relation.

Gasper §4 describes justification and finalization: https://arxiv.org/abs/2003.03052v3.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

private theorem append_slot_tail {g x y a : ForkedBeaconState preset}
    (pre : Run config checks g x) (step : Step config checks x y)
    (post : Run config checks y a) :
    pre.append ((Run.nil.snoc step).append post) = (pre.snoc step).append post := by
  induction post with
  | nil => rfl
  | snoc post next ih => exact congrArg (fun run => run.snoc next) ih

/-- The indices that the justification test of an epoch counts for its target.

From Altair they are the unslashed validators with the timely target flag.

Before Altair they are the unslashed attesters of the matching target attestations. -/
def targetIndices {fork : Fork} (state : BeaconState preset fork) (epoch : Epoch) :
    Except TransitionError (List ValidatorIndex) := do
  if altair : .altair ≤ fork then
    liftAccessor (getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX epoch)
  else
    let pending ← getMatchingTargetAttestations state (Nat.lt_of_not_le altair) epoch
    liftAccessor (getUnslashedAttestingIndices state pending)

/-- A slot step of the run that ends an epoch, with the justification step that it runs.

`cached` is the state after caching the slot, and `weighed` the state after justification. -/
structure EpochCall {g a : ForkedBeaconState preset} (run : Run config checks g a) where
  before : ForkedBeaconState preset
  after : ForkedBeaconState preset
  advanced : advanceSlotAcross config checks before = .ok after
  member : run.Contains (.slot advanced)
  boundary : (before.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0
  cached : BeaconState preset before.fork
  weighed : BeaconState preset before.fork
  cachedOk : processSlot before.state = .ok cached
  weighedOk : processJustificationAndFinalization cached = .ok weighed
  later : GENESIS_EPOCH + 1 < getCurrentEpoch cached

/-- An epoch call splits the run at its slot step.

Caching the slot is a frame, and keeps the registry and the balances. -/
theorem EpochCall.selected_prefix {g a : ForkedBeaconState preset}
    {run : Run config checks g a} (call : EpochCall run) :
    ∃ (pre : Run config checks g call.before) (post : Run config checks call.after a),
      run = (pre.snoc (.slot call.advanced)).append post ∧
      Frame call.before.state call.cached ∧
      call.cached.validators = call.before.state.validators ∧
      call.cached.balances = call.before.state.balances := by
  obtain ⟨pre, post, same⟩ := run.contains_split (.slot call.advanced) call.member
  refine ⟨pre, post, same, frame_processSlot call.cachedOk, ?_⟩
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok call.cachedOk
  rw [cachedEq]
  exact ⟨rfl, rfl⟩

/-- The test of justification succeeds at a state for the attesting indices.

It states only that the pure test succeeds, with the balance reads and checked arithmetic.

It does not say that the test ran, or where. -/
def JustificationPasses {fork : Fork} (state : BeaconState preset fork)
    (indices : List ValidatorIndex) : Prop :=
  ∃ total part threshold weighted : Gwei,
    getTotalActiveBalance state = .ok total ∧ getTotalBalance state indices = .ok part ∧
    Uint64.mulChecked total 2 = .ok threshold ∧ Uint64.mulChecked part 3 = .ok weighted ∧
    threshold ≤ weighted

/-- A test that passes gives the counted keys two thirds of the active stake.

The keys of the registry are distinct, and the active stake is above one and a half increments.

The bound on the indices comes from the successful balance reads. -/
private theorem JustificationPasses.stake_le {fork : Fork} {state : BeaconState preset fork}
    {indices : List ValidatorIndex} (passes : JustificationPasses state indices)
    (unique : PubkeysDistinct state)
    (floor : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * Models.stake (effectiveWeight state) (activeKeys state)) :
    2 * Models.stake (effectiveWeight state) (activeKeys state) ≤
      3 * Models.stake (effectiveWeight state) (keysAt state indices) := by
  obtain ⟨_, _, _, _, totalOk, partOk, thresholdOk, weightedOk, passes⟩ := passes
  have active := getTotalActiveBalance_ok totalOk
  have activeWeight := keys_weight state _ unique (getTotalBalance_ok_iff_stake.mp active).1
  have partWeight := keys_weight state _ unique (getTotalBalance_ok_iff_stake.mp partOk).1
  simp only [activeKeys, activeWeight] at floor ⊢
  simp only [partWeight]
  exact (justificationTest_iff_stake active partOk thresholdOk weightedOk floor).mp passes

/-- A justification test that passed in an epoch call, for its previous or its current epoch.

The target is the checkpoint of that epoch, with the root that the state records for it. -/
structure QuorumCall {g a : ForkedBeaconState preset} (run : Run config checks g a)
    extends EpochCall run where
  current : Bool
  target : Checkpoint
  targetEpoch : target.epoch =
    if current then getCurrentEpoch cached else getPreviousEpoch cached
  targetRoot : getBlockRoot cached target.epoch = .ok target.root
  indices : List ValidatorIndex
  counted : targetIndices cached target.epoch = .ok indices
  passes : JustificationPasses cached indices

/-- The justified checkpoint that the counted votes name as their source. -/
def QuorumCall.source {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : QuorumCall run) : Checkpoint :=
  if call.current then call.cached.currentJustifiedCheckpoint
    else call.cached.previousJustifiedCheckpoint

/-- The keys of the validators that the test counted. -/
noncomputable def QuorumCall.voters {g a : ForkedBeaconState preset}
    {run : Run config checks g a} (call : QuorumCall run) : Finset BLSPubkey :=
  keysAt call.cached call.indices

/-- At each end of an epoch of the run, the active stake is above one and a half increments.

Below that, a test can pass with no vote, since a total balance is at least one increment. -/
def EnoughStake {g a : ForkedBeaconState preset} (run : Run config checks g a) : Prop :=
  ∀ call : EpochCall run, 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
    2 * Models.stake (effectiveWeight call.cached) (activeKeys call.cached)

/-- A chain of quorum calls of the run that justifies `checkpoint` from genesis.

Each call takes the target of the call before it as its source. -/
structure JustificationHistory {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (checkpoint : Checkpoint) where
  calls : List (QuorumCall run)
  nonempty : calls ≠ []
  start : ∀ c, calls.head? = some c → c.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩
  finish : ∀ c, calls.getLast? = some c → c.target = checkpoint
  consecutive : ∀ i left right, calls[i]? = some left → calls[i + 1]? = some right →
    left.target = right.source

private def EpochCall.extend {g x a : ForkedBeaconState preset}
    {pre : Run config checks g x} (call : EpochCall pre) (tail : Run config checks x a) :
    EpochCall (pre.append tail) :=
  { call with member := (pre.contains_append tail _).mpr (.inl call.member) }

private def QuorumCall.extend {g x a : ForkedBeaconState preset}
    {pre : Run config checks g x} (call : QuorumCall pre) (tail : Run config checks x a) :
    QuorumCall (pre.append tail) :=
  { call with toEpochCall := call.toEpochCall.extend tail }

private def JustificationHistory.extend {g x a : ForkedBeaconState preset}
    {pre : Run config checks g x} {c : Checkpoint} (history : JustificationHistory pre c)
    (tail : Run config checks x a) : JustificationHistory (pre.append tail) c where
  calls := history.calls.map (fun call => call.extend tail)
  nonempty := by simpa using history.nonempty
  start := by
    intro call found
    simp only [List.head?_map, Option.map_eq_some_iff] at found
    obtain ⟨old, first, rfl⟩ := found
    exact history.start old first
  finish := by
    intro call found
    simp only [List.getLast?_map, Option.map_eq_some_iff] at found
    obtain ⟨old, last, rfl⟩ := found
    exact history.finish old last
  consecutive := by
    intro i left right one two
    simp only [List.getElem?_map, Option.map_eq_some_iff] at one two
    obtain ⟨oldLeft, one, rfl⟩ := one
    obtain ⟨oldRight, two, rfl⟩ := two
    exact history.consecutive i oldLeft oldRight one two

-- Append the new call to the source history, or start at the genesis checkpoint.
private theorem history_of_call {g a : ForkedBeaconState preset}
    {run : Run config checks g a} (call : QuorumCall run)
    (source : call.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      Nonempty (JustificationHistory run call.source)) :
    Nonempty (JustificationHistory run call.target) := by
  rcases source with initial | history
  · refine ⟨⟨[call], by simp, ?_, ?_, ?_⟩⟩
    · intro c found
      simpa using (Option.some.inj found ▸ initial)
    · intro c found
      simpa using (Option.some.inj found ▸ (rfl : call.target = call.target))
    · intro i left right one two
      simp at two
  · obtain ⟨history⟩ := history
    refine ⟨⟨history.calls ++ [call], by simp, ?_, ?_, ?_⟩⟩
    · intro c first
      have eq : (history.calls ++ [call]).head? = history.calls.head? := by
        cases h : history.calls with
        | nil => exact False.elim (history.nonempty h)
        | cons x xs => rfl
      exact history.start c (eq ▸ first)
    · intro c last
      simpa using (show call = c from by simpa using last) ▸
        (rfl : call.target = call.target)
    · intro i left right one two
      by_cases lt : i + 1 < history.calls.length
      · exact history.consecutive i left right
          (by simpa [List.getElem?_append, show i < history.calls.length by omega] using one)
          (by simpa [List.getElem?_append, lt] using two)
      · have bound := (List.getElem?_eq_some_iff.mp one).1
        have nextBound := (List.getElem?_eq_some_iff.mp two).1
        simp only [List.length_append, List.length_singleton] at bound nextBound
        have lastIndex : i + 1 = history.calls.length := by omega
        have rightEq : right = call := by
          simpa [List.getElem?_append, lastIndex] using two.symm
        subst right
        apply history.finish left
        rw [List.getLast?_eq_getElem?]
        have small : i < history.calls.length := by omega
        have indexEq : history.calls.length - 1 = i := by omega
        simpa [List.getElem?_append, small, indexEq] using one

/-- The four rules by which justification finalizes a checkpoint, read from the bits of a call. -/
def FinalizationRule {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : EpochCall run) (checkpoint : Checkpoint) : Prop :=
  let bits := call.weighed.justificationBits.bits
  let e := (getCurrentEpoch call.cached).toNat
  (checkpoint = call.cached.previousJustifiedCheckpoint ∧
    ((bits[1] = true ∧ bits[2] = true ∧ bits[3] = true ∧ checkpoint.epoch.toNat + 3 = e) ∨
      (bits[1] = true ∧ bits[2] = true ∧ checkpoint.epoch.toNat + 2 = e))) ∨
  (checkpoint = call.cached.currentJustifiedCheckpoint ∧
    ((bits[0] = true ∧ bits[1] = true ∧ bits[2] = true ∧ checkpoint.epoch.toNat + 2 = e) ∨
      (bits[0] = true ∧ bits[1] = true ∧ checkpoint.epoch.toNat + 1 = e)))

/-- The keys that a test of the run counts hold two thirds of the active stake at its state.

The keys stay distinct along the run, so each counts once.

The run starts at a genesis built from deposits.

Its active stake is above one and a half increments at each end of an epoch. -/
theorem quorum_count {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g)
    (enough : EnoughStake run) (call : QuorumCall run) :
    2 * Models.stake (effectiveWeight call.cached) (activeKeys call.cached) ≤
      3 * Models.stake (effectiveWeight call.cached) call.voters := by
  obtain ⟨pre, _, _, _, validators, _⟩ := call.toEpochCall.selected_prefix
  have unique : PubkeysDistinct call.cached := by
    simpa [PubkeysDistinct, validatorKeys, validators] using
      pre.unique (genesis_unique genesis)
  exact call.passes.stake_le unique (enough call.toEpochCall)

/-- At the state of an epoch call, the pending attestations and target flags hold votes of the run.

The run starts at a genesis built from deposits, and the preset meets the parameters. -/
theorem cached_participation {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (call : EpochCall run) :
    ParticipationBacked run call.cached := by
  obtain ⟨pre, post, same, _⟩ := call.selected_prefix
  let tail := (Run.nil.snoc (.slot call.advanced)).append post
  have backed := inherited_participation pre tail parameters genesis
  have eqRun : pre.append tail = run :=
    (append_slot_tail pre (.slot call.advanced) post).trans same.symm
  rw [eqRun] at backed
  exact ⟨backed.1.of_processSlot call.cachedOk,
    backed.2.of_processSlot (by have := parameters.slots; omega)
      (by have := parameters.roots; omega) call.cachedOk⟩

/-- Each key counted for a link accepted a vote of the run for that link.

The caller shows that a vote at a validator index is accepted under the key of the validator. -/
private theorem counted_accepted {g a : ForkedBeaconState preset} (run : Run config checks g a)
    {fork : Fork} {state : BeaconState preset fork} (backed : ParticipationBacked run state)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch state) (current : Bool) (target : Checkpoint)
    (targetEpoch : target.epoch =
      if current then getCurrentEpoch state else getPreviousEpoch state)
    (targetRoot : getBlockRoot state target.epoch = .ok target.root)
    {indices : List ValidatorIndex} (counted : targetIndices state target.epoch = .ok indices)
    (accept : ∀ (index : ValidatorIndex) (data : AttestationData) (validator : Validator),
      state.validators.data[index.toNat]? = some validator → (index, data) ∈ run.votes →
        run.Accepted validator.pubkey data) :
    ∀ key ∈ keysAt state indices, ∃ data, run.Accepted key data ∧
      data.source = (if current then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint) ∧ data.target = target := by
  have late := UInt64.not_le.mpr later
  intro key member
  simp only [keysAt, List.mem_toFinset, List.mem_filterMap] at member
  obtain ⟨index, inside, found⟩ := member
  obtain ⟨validator, validatorFound, keyEq⟩ := Option.map_eq_some_iff.mp found
  have voted : ∃ vote, LinkVote state current index.toNat vote ∧ vote ∈ run.votes := by
    rw [targetEpoch] at counted
    unfold targetIndices at counted
    split at counted
    · exact (backed.2.attester ‹_› late current (liftAccessor_ok.mp counted) inside).2
    · simp only [bind_ok_iff, liftAccessor_ok] at counted
      obtain ⟨pending, matching, indicesOk⟩ := counted
      obtain ⟨_, data, link, cast⟩ := backed.1.attester (Nat.lt_of_not_le ‹_›)
        (fun first => False.elim (late first)) current matching indicesOk inside
      exact ⟨(index, data), link, cast⟩
  obtain ⟨vote, link, cast⟩ := voted
  obtain ⟨position, epoch, source, root⟩ := link
  have indexEq : vote.1 = index := UInt64.toNat_inj.mp position
  refine ⟨vote.2, ?_, source, ?_⟩
  · rw [← keyEq]
    exact accept index vote.2 validator validatorFound (by simpa [← indexEq] using cast)
  · have epochEq := epoch.trans targetEpoch.symm
    have rootEq : vote.2.target.root = target.root := by
      rw [epochEq, targetRoot, Except.ok.injEq] at root
      exact root.symm
    cases h₁ : vote.2.target
    cases h₂ : target
    simp_all

/-- Each key that a test counts has a vote of the run with the source and target of the test.

The run starts at a genesis built from deposits, and the preset meets the parameters. -/
theorem quorum_attestations {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (call : QuorumCall run) :
    ∀ key ∈ call.voters, ∃ data, run.Accepted key data ∧
      data.source = call.source ∧ data.target = call.target := by
  obtain ⟨pre, post, same, _, validators, _⟩ := call.toEpochCall.selected_prefix
  refine counted_accepted run (cached_participation run parameters genesis call.toEpochCall)
    call.later call.current call.target call.targetEpoch call.targetRoot call.counted ?_
  intro index data validator found voted
  -- The validator keeps its key from the cached state to the end of the run.
  have atBefore : call.before.state.validators.data[index.toNat]? = some validator := by
    simpa [validators] using found
  let tail := (Run.nil.snoc (.slot call.advanced)).append post
  obtain ⟨last, atLast, keyLast⟩ := tail.key_preserved index.toNat validator atBefore
  rw [← keyLast]
  exact selected_vote_key run index data last atLast voted

private theorem call_balances {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : EpochCall run) :
    ∃ (previous current : List ValidatorIndex) (total pb cb : Gwei),
      targetIndices call.cached (getPreviousEpoch call.cached) = .ok previous ∧
      targetIndices call.cached (getCurrentEpoch call.cached) = .ok current ∧
      getTotalActiveBalance call.cached = .ok total ∧
      getTotalBalance call.cached previous = .ok pb ∧
      getTotalBalance call.cached current = .ok cb ∧
      weighJustificationAndFinalization call.cached total pb cb = .ok call.weighed := by
  have ok := call.weighedOk
  have late := UInt64.not_le.mpr call.later
  unfold processJustificationAndFinalization at ok
  split at ok
  · rename_i altair
    simp only [processJustificationAndFinalizationAltair, ite_eq_right late,
      bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      pb, pbOk, cb, cbOk, weighed⟩ := ok
    exact ⟨previous, current, total, pb, cb,
      by simpa [targetIndices, altair, liftAccessor_ok] using previousOk,
      by simpa [targetIndices, altair, liftAccessor_ok] using currentOk,
      totalOk, pbOk, cbOk, weighed⟩
  · rename_i notAltair
    simp only [bind_ok_iff, liftAccessor_ok, getAttestingBalance] at ok
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      pb, ⟨pi, piOk, pbOk⟩, cb, ⟨ci, ciOk, cbOk⟩, weighed⟩ := ok
    refine ⟨pi, ci, total, pb, cb, ?_, ?_, totalOk, pbOk, cbOk, weighed⟩
    · simp [targetIndices, notAltair, bind_ok_iff, liftAccessor_ok]
      exact ⟨_, previousOk, piOk⟩
    · simp [targetIndices, notAltair, bind_ok_iff, liftAccessor_ok]
      exact ⟨_, currentOk, ciOk⟩

private theorem call_bits {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : EpochCall run) (i : Fin 4) (set : call.weighed.justificationBits.bits[i] = true) :
    (∃ quorum : QuorumCall run,
      quorum.target.epoch.toNat + i.val = (getCurrentEpoch call.cached).toNat) ∨
      ∃ j : Fin 4, j.val + 1 = i.val ∧ call.cached.justificationBits.bits[j] = true := by
  obtain ⟨previous, current, total, pb, cb, previousOk, currentOk, totalOk, pbOk, cbOk,
    weighed⟩ := call_balances call
  obtain ⟨threshold, pw, cw, thresholdOk, pwOk, cwOk, zero, one, two, _⟩ :=
    weighJustificationAndFinalization_bits weighed
  have make (now : Bool) (root : Root)
      (rootOk : getBlockRoot call.cached
        (if now then getCurrentEpoch call.cached else getPreviousEpoch call.cached) = .ok root)
      (passes : threshold ≤ if now then cw else pw) :
      ∃ quorum : QuorumCall run,
        quorum.target.epoch =
          (if now then getCurrentEpoch call.cached else getPreviousEpoch call.cached) := by
    refine ⟨{ toEpochCall := call
              current := now
              target := ⟨_, root⟩
              targetEpoch := rfl
              targetRoot := rootOk
              indices := if now then current else previous
              counted := ?_
              passes := ⟨total, if now then cb else pb, threshold, if now then cw else pw,
                totalOk, ?_, thresholdOk, ?_, passes⟩ }, rfl⟩
    · cases now <;> assumption
    · cases now <;> assumption
    · cases now <;> assumption
  fin_cases i
  · obtain ⟨passes, root, rootOk, _⟩ := zero set
    obtain ⟨quorum, epoch⟩ := make true root rootOk passes
    exact .inl ⟨quorum, by simp [epoch]⟩
  · rcases one set with ⟨passes, root, rootOk⟩ | old
    · obtain ⟨quorum, epoch⟩ := make false root rootOk passes
      have previousEpoch := getPreviousEpoch_toNat call.cached
      have late := UInt64.lt_iff_toNat_lt.mp call.later
      simp only [GENESIS_EPOCH, UInt64.reduceAdd, UInt64.reduceToNat] at late
      exact .inl ⟨quorum, by simp only [epoch, Bool.false_eq_true, ↓reduceIte]; omega⟩
    · exact .inr ⟨0, rfl, old⟩
  · exact .inr ⟨1, rfl, two ▸ set⟩
  · right
    refine ⟨2, rfl, ?_⟩
    simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at weighed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, eq⟩ := weighed
    rw [← eq] at set
    simpa [shiftJustificationBits] using set

private theorem call_new_bits {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : EpochCall run) :
    (call.weighed.justificationBits.bits[0] = true →
      ∃ quorum : QuorumCall run,
        quorum.source = call.cached.currentJustifiedCheckpoint ∧
        quorum.target = call.weighed.currentJustifiedCheckpoint ∧
        quorum.target.epoch = getCurrentEpoch call.cached) ∧
    (call.weighed.justificationBits.bits[1] = true →
      (∃ quorum : QuorumCall run,
        quorum.source = call.cached.previousJustifiedCheckpoint ∧
        quorum.target.epoch = getPreviousEpoch call.cached) ∨
      call.cached.justificationBits.bits[0] = true) := by
  obtain ⟨previous, current, total, pb, cb, previousOk, currentOk, totalOk, pbOk, cbOk,
    weighed⟩ := call_balances call
  obtain ⟨threshold, pw, cw, thresholdOk, pwOk, cwOk, zero, one, _⟩ :=
    weighJustificationAndFinalization_bits weighed
  constructor
  · intro set
    obtain ⟨passes, root, rootOk, target⟩ := zero set
    refine ⟨{ toEpochCall := call
              current := true
              target := ⟨getCurrentEpoch call.cached, root⟩
              targetEpoch := rfl
              targetRoot := rootOk
              indices := current
              counted := currentOk
              passes := ⟨total, cb, threshold, cw, totalOk, cbOk, thresholdOk, cwOk, passes⟩ },
      rfl, target.symm, rfl⟩
  · intro set
    rcases one set with ⟨passes, root, rootOk⟩ | old
    · refine .inl ⟨{ toEpochCall := call
                     current := false
                     target := ⟨getPreviousEpoch call.cached, root⟩
                     targetEpoch := rfl
                     targetRoot := rootOk
                     indices := previous
                     counted := previousOk
                     passes := ⟨total, pb, threshold, pw, totalOk, pbOk, thresholdOk, pwOk,
                       passes⟩ }, rfl, rfl⟩
    · exact .inr old

private theorem upgrades_bits {first last : ForkedBeaconState preset}
    (ok : processUpgrades config checks first = .ok last) :
    last.state.slot = first.state.slot ∧
      last.state.justificationBits = first.state.justificationBits := by
  apply processUpgrades_induction (property := fun s =>
    s.state.slot = first.state.slot ∧ s.state.justificationBits = first.state.justificationBits)
    ?_ ⟨rfl, rfl⟩ ok
  intro pre post ih next
  have frame := upgradeFrame_upgradeNext next
  exact ⟨frame.slot.trans ih.1, frame.justificationBits.trans ih.2⟩

private theorem run_bits {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g)
    (i : Fin 4) (set : a.state.justificationBits.bits[i] = true) :
    ∃ quorum : QuorumCall run,
      quorum.target.epoch.toNat + i.val + 1 = (getCurrentEpoch a.state).toNat := by
  -- Between epoch calls, each bit refers to the epoch one position further back.
  induction run generalizing i with
  | nil =>
    obtain ⟨_, _, _, ok⟩ := genesis
    have bits := (initializeBeaconStateFromEth1_finality ok).1
    simp [bits] at set
  | @snoc before after pre step ih =>
    have old (bits : after.state.justificationBits = before.state.justificationBits)
        (epoch : (getCurrentEpoch after.state).toNat =
          (getCurrentEpoch before.state).toNat) :
        ∃ quorum : QuorumCall (pre.snoc step),
          quorum.target.epoch.toNat + i.val + 1 = (getCurrentEpoch after.state).toNat := by
      obtain ⟨quorum, eq⟩ := ih i (by simpa [bits] using set)
      exact ⟨quorum.extend (Run.nil.snoc step), eq.trans epoch.symm⟩
    cases step with
    | block engine signed due ok =>
      have frame := frame_processBlock (applySignedBlock_ok ok).2.1
      exact old frame.justificationBits (by simp [getCurrentEpoch_toNat, frame.slot])
    | slot ok =>
      have across := ok
      simp only [advanceSlotAcross, bind_ok_iff] at across
      obtain ⟨advanced, advancedOk, upgraded⟩ := across
      have upgrade := upgrades_bits upgraded
      obtain ⟨next, cached, epoched, sum, cachedOk, epochOk, advancedEq⟩ :=
        advanceSlot_ok advancedOk
      have cachedFrame := frame_processSlot cachedOk
      have epochedSet : epoched.justificationBits.bits[i] = true := by
        simpa [upgrade.2, advancedEq] using set
      have endEpoch : (getCurrentEpoch after.state).toNat =
          next.toNat / preset.SLOTS_PER_EPOCH.toNat := by
        simp [getCurrentEpoch_toNat, upgrade.1, advancedEq]
      unfold epochIfLast at epochOk
      split at epochOk
      · rename_i boundary
        obtain ⟨weighed, weighedOk, frame⟩ := processEpoch_frame epochOk
        have weighedSet : weighed.justificationBits.bits[i] = true := by
          simpa [frame.justificationBits] using epochedSet
        have epochs := nextSlot_epoch_of_boundary sum boundary
        by_cases early : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1
        · have eq := processJustificationAndFinalization_early_eq early weighedOk
          have oldSet : before.state.justificationBits.bits[i] = true := by
            simpa [eq, cachedFrame.justificationBits] using weighedSet
          obtain ⟨quorum, target⟩ := ih i oldSet
          have late := quorum.later
          have beforeEpoch : (getCurrentEpoch before.state).toNat ≤ 1 := by
            have := UInt64.le_iff_toNat_le.mp early
            simpa [getCurrentEpoch_toNat, cachedFrame.slot, GENESIS_EPOCH] using this
          have targetLate : 1 ≤ quorum.target.epoch.toNat := by
            have := UInt64.lt_iff_toNat_lt.mp late
            have prev := getPreviousEpoch_toNat quorum.cached
            rw [quorum.targetEpoch]
            split <;> simp_all [GENESIS_EPOCH] <;> omega
          omega
        · let call : EpochCall (pre.snoc (.slot ok)) :=
            { before := before, after := after, advanced := ok,
              member := .last pre (.slot ok), boundary := by
                have natural := congrArg UInt64.toNat boundary
                simpa [UInt64.toNat_mod, sum] using natural,
              cached := cached, weighed := weighed, cachedOk := cachedOk,
              weighedOk := weighedOk, later := UInt64.not_le.mp early }
          rcases call_bits call i weighedSet with ⟨quorum, target⟩ | ⟨j, shift, oldSet⟩
          · refine ⟨quorum, ?_⟩
            have cacheEpoch : (getCurrentEpoch cached).toNat =
                before.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
              simp [getCurrentEpoch_toNat, cachedFrame.slot]
            change quorum.target.epoch.toNat + i.val = (getCurrentEpoch cached).toNat at target
            omega
          · obtain ⟨quorum, target⟩ := ih j
              (by simpa [call, cachedFrame.justificationBits] using oldSet)
            refine ⟨quorum.extend (Run.nil.snoc (.slot ok)), ?_⟩
            simp only [getCurrentEpoch_toNat] at target
            change quorum.target.epoch.toNat + i.val + 1 = _
            omega
      · have eq : epoched = cached := Except.ok.inj epochOk.symm
        apply old
        · simpa [advancedEq, eq] using upgrade.2.trans
            (show advanced.justificationBits = before.state.justificationBits by
              simpa [advancedEq, eq] using cachedFrame.justificationBits)
        · rw [endEpoch, getCurrentEpoch_toNat]
          exact nextSlot_epoch_of_inside sum ‹_›

/-- A set bit identifies a successful test on this run, not merely an epoch number. -/
private theorem justification_bit_call {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (call : EpochCall run) (i : Fin 4) (set : call.weighed.justificationBits.bits[i] = true) :
    ∃ witness : QuorumCall run,
      witness.target.epoch.toNat + i.val = (getCurrentEpoch call.cached).toNat := by
  rcases call_bits call i set with direct | ⟨j, shift, oldSet⟩
  · exact direct
  · obtain ⟨pre, post, same, frame, _⟩ := call.selected_prefix
    obtain ⟨quorum, target⟩ := run_bits pre genesis j
      (by simpa [frame.justificationBits] using oldSet)
    let tail := (Run.nil.snoc (.slot call.advanced)).append post
    have eqRun : pre.append tail = run :=
      (append_slot_tail pre (.slot call.advanced) post).trans same.symm
    have result : ∃ witness : QuorumCall (pre.append tail),
        witness.target.epoch.toNat + i.val = (getCurrentEpoch call.cached).toNat := by
      refine ⟨quorum.extend tail, ?_⟩
      have cachedEpoch : (getCurrentEpoch call.cached).toNat =
          (getCurrentEpoch call.before.state).toNat := by
        simp [getCurrentEpoch_toNat, frame.slot]
      change quorum.target.epoch.toNat + i.val = _
      omega
    exact Eq.mp (congrArg (fun r => ∃ witness : QuorumCall r,
      witness.target.epoch.toNat + i.val = (getCurrentEpoch call.cached).toNat) eqRun) result

private theorem call_current {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : EpochCall run) :
    call.weighed.currentJustifiedCheckpoint = call.cached.currentJustifiedCheckpoint ∨
      ∃ quorum : QuorumCall run,
        quorum.target = call.weighed.currentJustifiedCheckpoint ∧
        (quorum.source = call.cached.previousJustifiedCheckpoint ∨
          quorum.source = call.cached.currentJustifiedCheckpoint) := by
  have make (previous current : List ValidatorIndex) (total pb cb : Gwei)
      (previousOk : targetIndices call.cached (getPreviousEpoch call.cached) = .ok previous)
      (currentOk : targetIndices call.cached (getCurrentEpoch call.cached) = .ok current)
      (totalOk : getTotalActiveBalance call.cached = .ok total)
      (pbOk : getTotalBalance call.cached previous = .ok pb)
      (cbOk : getTotalBalance call.cached current = .ok cb)
      (weighed : weighJustificationAndFinalization call.cached total pb cb =
        .ok call.weighed) :
      call.weighed.currentJustifiedCheckpoint = call.cached.currentJustifiedCheckpoint ∨
        ∃ quorum : QuorumCall run,
          quorum.target = call.weighed.currentJustifiedCheckpoint ∧
          (quorum.source = call.cached.previousJustifiedCheckpoint ∨
            quorum.source = call.cached.currentJustifiedCheckpoint) := by
    rcases weighJustificationAndFinalization_currentJustified weighed with ⟨same, _⟩ |
      ⟨now, threshold, weighted, thresholdOk, weightedOk, passes, epoch, root⟩
    · exact .inl same
    · right
      refine ⟨{ toEpochCall := call
                current := now
                target := call.weighed.currentJustifiedCheckpoint
                targetEpoch := epoch
                targetRoot := root
                indices := if now then current else previous
                counted := ?_
                passes := ⟨total, if now then cb else pb, threshold, weighted,
                  totalOk, ?_, thresholdOk, weightedOk, passes⟩ }, rfl, ?_⟩
      · rw [epoch]; cases now <;> assumption
      · cases now <;> assumption
      · cases now <;> simp [QuorumCall.source]
  obtain ⟨previous, current, total, pb, cb, previousOk, currentOk, totalOk, pbOk, cbOk,
    weighed⟩ := call_balances call
  exact make previous current total pb cb previousOk currentOk totalOk pbOk cbOk weighed

private theorem upgrades_justified {first last : ForkedBeaconState preset}
    (ok : processUpgrades config checks first = .ok last) :
    last.state.previousJustifiedCheckpoint = first.state.previousJustifiedCheckpoint ∧
      last.state.currentJustifiedCheckpoint = first.state.currentJustifiedCheckpoint := by
  apply processUpgrades_induction (property := fun s =>
    s.state.previousJustifiedCheckpoint = first.state.previousJustifiedCheckpoint ∧
      s.state.currentJustifiedCheckpoint = first.state.currentJustifiedCheckpoint)
    ?_ ⟨rfl, rfl⟩ ok
  intro pre post ih next
  have frame := upgradeFrame_upgradeNext next
  exact ⟨frame.previousJustified.trans ih.1, frame.currentJustified.trans ih.2⟩

private theorem run_zero {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g)
    (set : a.state.justificationBits.bits[0] = true) :
    ∃ quorum : QuorumCall run,
      quorum.source = a.state.previousJustifiedCheckpoint ∧
      quorum.target = a.state.currentJustifiedCheckpoint ∧
      quorum.target.epoch.toNat + 1 = (getCurrentEpoch a.state).toNat := by
  -- Bit zero retains the current-target call and its source after checkpoint rotation.
  induction run with
  | nil =>
    obtain ⟨_, _, _, ok⟩ := genesis
    simp [(initializeBeaconStateFromEth1_finality ok).1] at set
  | @snoc before after pre step ih =>
    have old (bits : after.state.justificationBits = before.state.justificationBits)
        (previous : after.state.previousJustifiedCheckpoint =
          before.state.previousJustifiedCheckpoint)
        (current : after.state.currentJustifiedCheckpoint = before.state.currentJustifiedCheckpoint)
        (epoch : (getCurrentEpoch after.state).toNat = (getCurrentEpoch before.state).toNat) :
        ∃ quorum : QuorumCall (pre.snoc step),
          quorum.source = after.state.previousJustifiedCheckpoint ∧
          quorum.target = after.state.currentJustifiedCheckpoint ∧
          quorum.target.epoch.toNat + 1 = (getCurrentEpoch after.state).toNat := by
      obtain ⟨quorum, source, target, date⟩ := ih (by simpa [bits] using set)
      exact ⟨quorum.extend (Run.nil.snoc step), source.trans previous.symm,
        target.trans current.symm, date.trans epoch.symm⟩
    cases step with
    | block engine signed due ok =>
      have frame := frame_processBlock (applySignedBlock_ok ok).2.1
      exact old frame.justificationBits frame.previousJustified frame.currentJustified
        (by simp [getCurrentEpoch_toNat, frame.slot])
    | slot ok =>
      have across := ok
      simp only [advanceSlotAcross, bind_ok_iff] at across
      obtain ⟨advanced, advancedOk, upgraded⟩ := across
      have upgrade := upgrades_bits upgraded
      have fields := upgrades_justified upgraded
      obtain ⟨next, cached, epoched, sum, cachedOk, epochOk, advancedEq⟩ :=
        advanceSlot_ok advancedOk
      have cachedFrame := frame_processSlot cachedOk
      have epochedSet : epoched.justificationBits.bits[0] = true := by
        simpa [upgrade.2, advancedEq] using set
      have endEpoch : (getCurrentEpoch after.state).toNat =
          next.toNat / preset.SLOTS_PER_EPOCH.toNat := by
        simp [getCurrentEpoch_toNat, upgrade.1, advancedEq]
      unfold epochIfLast at epochOk
      split at epochOk
      · rename_i boundary
        obtain ⟨weighed, weighedOk, frame⟩ := processEpoch_frame epochOk
        have weighedSet : weighed.justificationBits.bits[0] = true := by
          simpa [frame.justificationBits] using epochedSet
        have epochs := nextSlot_epoch_of_boundary sum boundary
        by_cases early : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1
        · have eq := processJustificationAndFinalization_early_eq early weighedOk
          obtain ⟨quorum, date⟩ := run_bits pre genesis 0
            (by simpa [eq, cachedFrame.justificationBits] using weighedSet)
          have earlyNat : (getCurrentEpoch before.state).toNat ≤ 1 := by
            simpa [getCurrentEpoch_toNat, cachedFrame.slot, GENESIS_EPOCH] using
              UInt64.le_iff_toNat_le.mp early
          have late := UInt64.lt_iff_toNat_lt.mp quorum.later
          have prev := getPreviousEpoch_toNat quorum.cached
          have target := congrArg UInt64.toNat quorum.targetEpoch
          simp only [GENESIS_EPOCH, UInt64.reduceAdd, UInt64.reduceToNat] at late
          split at target <;> simp only [Fin.val_zero] at date <;> omega
        · let call : EpochCall (pre.snoc (.slot ok)) :=
            { before := before, after := after, advanced := ok,
              member := .last pre (.slot ok), boundary := by
                have natural := congrArg UInt64.toNat boundary
                simpa [UInt64.toNat_mod, sum] using natural,
              cached := cached, weighed := weighed, cachedOk := cachedOk,
              weighedOk := weighedOk, later := UInt64.not_le.mp early }
          obtain ⟨quorum, source, target, date⟩ := (call_new_bits call).1 weighedSet
          obtain ⟨_, _, _, _, _, _, _, _, _, _, weighing⟩ := call_balances call
          have previous := (weighJustificationAndFinalization_checkpoints weighing).1
          refine ⟨quorum, ?_, ?_, ?_⟩
          · exact source.trans (previous.symm.trans
              (frame.previousJustified.symm.trans (by simpa [advancedEq] using fields.1.symm)))
          · exact target.trans (frame.currentJustified.symm.trans
              (by simpa [advancedEq] using fields.2.symm))
          · have dateNat := congrArg UInt64.toNat date
            change quorum.target.epoch.toNat = (getCurrentEpoch cached).toNat at dateNat
            simp only [getCurrentEpoch_toNat, cachedFrame.slot] at dateNat
            omega
      · have eq : epoched = cached := Except.ok.inj epochOk.symm
        apply old
        · exact upgrade.2.trans (by simpa [advancedEq, eq] using cachedFrame.justificationBits)
        · exact fields.1.trans (by simpa [advancedEq, eq] using cachedFrame.previousJustified)
        · exact fields.2.trans (by simpa [advancedEq, eq] using cachedFrame.currentJustified)
        · rw [endEpoch, getCurrentEpoch_toNat]
          exact nextSlot_epoch_of_inside sum ‹_›

/-- A justified field of the last state is the genesis checkpoint, or has a justification history.

The history is a chain of quorum calls of the run.

The run starts at a genesis built from deposits. -/
theorem justified_fields {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) (c : Checkpoint)
    (field : c = a.state.previousJustifiedCheckpoint ∨ c = a.state.currentJustifiedCheckpoint) :
    c = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨ Nonempty (JustificationHistory run c) := by
  induction run generalizing c with
  | nil =>
    obtain ⟨_, _, _, ok⟩ := genesis
    have fields := initializeBeaconStateFromEth1_checkpoints ok
    exact .inl (field.elim (fun h => h.trans fields.2.1) (fun h => h.trans fields.2.2))
  | @snoc before after pre step ih =>
    have old (c : Checkpoint)
        (field : c = before.state.previousJustifiedCheckpoint ∨
          c = before.state.currentJustifiedCheckpoint) :
        c = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
          Nonempty (JustificationHistory (pre.snoc step) c) := by
      rcases ih c field with initial | history
      · exact .inl initial
      · obtain ⟨history⟩ := history
        exact .inr ⟨history.extend (Run.nil.snoc step)⟩
    cases step with
    | block engine signed due ok =>
      have frame := frame_processBlock (applySignedBlock_ok ok).2.1
      exact old c (field.elim (fun h => .inl (h.trans frame.previousJustified))
        (fun h => .inr (h.trans frame.currentJustified)))
    | slot ok =>
      have across := ok
      simp only [advanceSlotAcross, bind_ok_iff] at across
      obtain ⟨advanced, advancedOk, upgraded⟩ := across
      have upgrade := upgrades_justified upgraded
      obtain ⟨next, cached, epoched, sum, cachedOk, epochOk, advancedEq⟩ :=
        advanceSlot_ok advancedOk
      have cachedFrame := frame_processSlot cachedOk
      have epochedField : c = epoched.previousJustifiedCheckpoint ∨
          c = epoched.currentJustifiedCheckpoint := by
        simpa [advancedEq] using field.elim
          (fun h => Or.inl (h.trans upgrade.1)) (fun h => Or.inr (h.trans upgrade.2))
      have fromCached (c : Checkpoint)
          (field : c = cached.previousJustifiedCheckpoint ∨
            c = cached.currentJustifiedCheckpoint) :
          c = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
            Nonempty (JustificationHistory (pre.snoc (.slot ok)) c) :=
        old c (field.elim (fun h => .inl (h.trans cachedFrame.previousJustified))
          (fun h => .inr (h.trans cachedFrame.currentJustified)))
      unfold epochIfLast at epochOk
      split at epochOk
      · rename_i boundary
        obtain ⟨weighed, weighedOk, frame⟩ := processEpoch_frame epochOk
        have weighedField : c = weighed.previousJustifiedCheckpoint ∨
            c = weighed.currentJustifiedCheckpoint := epochedField.elim
          (fun h => .inl (h.trans frame.previousJustified))
          (fun h => .inr (h.trans frame.currentJustified))
        by_cases early : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1
        · have eq := processJustificationAndFinalization_early_eq early weighedOk
          exact fromCached c (eq ▸ weighedField)
        · let call : EpochCall (pre.snoc (.slot ok)) :=
            { before := before, after := after, advanced := ok,
              member := .last pre (.slot ok), boundary := by
                have natural := congrArg UInt64.toNat boundary
                simpa [UInt64.toNat_mod, sum] using natural,
              cached := cached, weighed := weighed, cachedOk := cachedOk,
              weighedOk := weighedOk, later := UInt64.not_le.mp early }
          rcases weighedField with previous | current
          · rcases processJustificationAndFinalization_ok weighedOk with eq |
              ⟨_, _, _, weighing⟩
            · exact fromCached c (.inl (eq ▸ previous))
            · exact fromCached c (.inr
                (previous.trans (weighJustificationAndFinalization_checkpoints weighing).1))
          · rcases call_current call with same | ⟨quorum, target, source⟩
            · exact fromCached c (.inr (current.trans same))
            · have history := history_of_call quorum (fromCached quorum.source source)
              exact .inr ((target.trans current.symm) ▸ history)
      · have eq : epoched = cached := Except.ok.inj epochOk.symm
        exact fromCached c (eq ▸ epochedField)

private theorem quorum_source_history {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) (call : QuorumCall run) :
    call.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      Nonempty (JustificationHistory run call.source) := by
  obtain ⟨pre, post, same, frame, _⟩ := call.toEpochCall.selected_prefix
  have field : call.source = call.before.state.previousJustifiedCheckpoint ∨
      call.source = call.before.state.currentJustifiedCheckpoint := by
    unfold QuorumCall.source
    cases call.current
    · exact .inl frame.previousJustified
    · exact .inr frame.currentJustified
  rcases justified_fields pre genesis call.source field with initial | history
  · exact .inl initial
  · obtain ⟨history⟩ := history
    let tail := (Run.nil.snoc (.slot call.advanced)).append post
    have eqRun : pre.append tail = run :=
      (append_slot_tail pre (.slot call.advanced) post).trans same.symm
    have result : Nonempty (JustificationHistory (pre.append tail) call.source) :=
      ⟨history.extend tail⟩
    exact .inr (Eq.mp (congrArg (fun r => Nonempty (JustificationHistory r call.source))
      eqRun) result)

private theorem justification_split {fork : Fork} {state after : BeaconState preset fork}
    (ok : processJustificationAndFinalization state = .ok after) :
    (getCurrentEpoch state ≤ GENESIS_EPOCH + 1 ∧ after = state) ∨
      GENESIS_EPOCH + 1 < getCurrentEpoch state ∧
      ∃ total previous current,
        weighJustificationAndFinalization state total previous current = .ok after := by
  unfold processJustificationAndFinalization at ok
  split at ok
  · unfold processJustificationAndFinalizationAltair at ok
    split at ok
    · exact .inl ⟨‹_›, Except.ok.inj ok.symm⟩
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, total, _, previous, _, current, _, weighed⟩ := ok
      exact .inr ⟨UInt64.not_le.mp ‹_›, total, previous, current, weighed⟩
  · split at ok
    · exact .inl ⟨‹_›, Except.ok.inj ok.symm⟩
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, total, _, previous, _, current, _, weighed⟩ := ok
      exact .inr ⟨UInt64.not_le.mp ‹_›, total, previous, current, weighed⟩

private theorem weighed_rule {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : EpochCall run) :
    call.weighed.finalizedCheckpoint = call.cached.finalizedCheckpoint ∨
      FinalizationRule call call.weighed.finalizedCheckpoint := by
  rcases justification_split call.weighedOk with ⟨early, _⟩ | ⟨_, total, previous, current, ok⟩
  · exact False.elim ((UInt64.not_le.mpr call.later) early)
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure,
    Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, b₃, h₃, b₂, h₂, c₂, hc₂, c₁, hc₁, eq⟩ := ok
  unfold FinalizationRule
  rw [← eq]
  dsimp only
  split
  · rename_i yes
    right
    right
    refine ⟨rfl, ?_⟩
    simp only [Bool.or_eq_true] at yes
    rcases yes with yes | yes
    · rw [yes] at hc₂
      have rule := finalizes_eq_true hc₂
      simp only [Bool.and_eq_true, UInt64.reduceToNat] at rule
      exact .inl ⟨rule.1.1.1, rule.1.1.2, rule.1.2, rule.2⟩
    · rw [yes] at hc₁
      have rule := finalizes_eq_true hc₁
      simp only [Bool.and_eq_true, UInt64.reduceToNat] at rule
      exact .inr ⟨rule.1.1, rule.1.2, rule.2⟩
  · split
    · rename_i yes
      right
      left
      refine ⟨rfl, ?_⟩
      simp only [Bool.or_eq_true] at yes
      rcases yes with yes | yes
      · rw [yes] at h₃
        have rule := finalizes_eq_true h₃
        simp only [Bool.and_eq_true, UInt64.reduceToNat] at rule
        exact .inl ⟨rule.1.1.1, rule.1.1.2, rule.1.2, rule.2⟩
      · rw [yes] at h₂
        have rule := finalizes_eq_true h₂
        simp only [Bool.and_eq_true, UInt64.reduceToNat] at rule
        exact .inr ⟨rule.1.1, rule.1.2, rule.2⟩
    · exact .inl rfl

private theorem upgrades_finalized {first last : ForkedBeaconState preset}
    (ok : processUpgrades config checks first = .ok last) :
    last.state.finalizedCheckpoint = first.state.finalizedCheckpoint := by
  apply processUpgrades_induction (property := fun s =>
    s.state.finalizedCheckpoint = first.state.finalizedCheckpoint) ?_ rfl ok
  intro pre post ih next
  exact (upgradeFrame_upgradeNext next).finalized.trans ih

/-- The finalized field of the last state is the genesis checkpoint, or an epoch call set it.

That call met a finalization rule for it.

The run starts at a genesis built from deposits. -/
theorem finalized_field {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) :
    a.state.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      ∃ call : EpochCall run, call.weighed.finalizedCheckpoint = a.state.finalizedCheckpoint ∧
        FinalizationRule call a.state.finalizedCheckpoint := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, ok⟩ := genesis
    exact .inl (initializeBeaconStateFromEth1_finality ok).2
  | @snoc before after pre step ih =>
    have keep (same : after.state.finalizedCheckpoint = before.state.finalizedCheckpoint) :
        after.state.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
          ∃ call : EpochCall (pre.snoc step),
            call.weighed.finalizedCheckpoint = after.state.finalizedCheckpoint ∧
              FinalizationRule call after.state.finalizedCheckpoint := by
      rcases ih with initial | ⟨call, eq, rule⟩
      · exact .inl (same.trans initial)
      · exact .inr ⟨call.extend (Run.nil.snoc step), eq.trans same.symm, same ▸ rule⟩
    cases step with
    | block engine signed due ok =>
      exact keep (frame_processBlock (applySignedBlock_ok ok).2.1).finalized
    | slot ok =>
      have across := ok
      simp only [advanceSlotAcross, bind_ok_iff] at across
      obtain ⟨advanced, advancedOk, upgraded⟩ := across
      have upgrade := upgrades_finalized upgraded
      obtain ⟨next, cached, epoched, sum, cachedOk, epochOk, advancedEq⟩ :=
        advanceSlot_ok advancedOk
      have cachedFrame := frame_processSlot cachedOk
      unfold epochIfLast at epochOk
      split at epochOk
      · rename_i boundary
        obtain ⟨weighed, weighedOk, frame⟩ := processEpoch_frame epochOk
        have lastEq : after.state.finalizedCheckpoint = weighed.finalizedCheckpoint := by
          simpa [advancedEq] using upgrade.trans
            (show advanced.finalizedCheckpoint = weighed.finalizedCheckpoint by
              rw [advancedEq]; exact frame.finalized)
        rcases justification_split weighedOk with ⟨_, eq⟩ | ⟨late, _⟩
        · exact keep (lastEq.trans (eq ▸ cachedFrame.finalized))
        · let call : EpochCall (pre.snoc (.slot ok)) :=
            { before := before, after := after, advanced := ok,
              member := .last pre (.slot ok), boundary := by
                have natural := congrArg UInt64.toNat boundary
                simpa [UInt64.toNat_mod, sum] using natural,
              cached := cached, weighed := weighed, cachedOk := cachedOk,
              weighedOk := weighedOk, later := late }
          rcases weighed_rule call with same | rule
          · exact keep (lastEq.trans (same.trans cachedFrame.finalized))
          · exact .inr ⟨call, lastEq.symm, lastEq ▸ rule⟩
      · have eq : epoched = cached := Except.ok.inj epochOk.symm
        apply keep
        exact upgrade.trans (by simpa [advancedEq, eq] using cachedFrame.finalized)

/-- A finalization rule for a checkpoint gives a quorum call from it, one or two epochs ahead.

The checkpoint is the genesis checkpoint, or has a justification history.

With a target two epochs ahead, a checkpoint of the epoch between them has a history too.

The run starts at a genesis built from deposits. -/
theorem finalization_rule_quorums {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) (call : EpochCall run)
    (c : Checkpoint) (rule : FinalizationRule call c) :
    ∃ outgoing : QuorumCall run, outgoing.source = c ∧
      (outgoing.target.epoch.toNat = c.epoch.toNat + 1 ∨
        outgoing.target.epoch.toNat = c.epoch.toNat + 2) ∧
      (c = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        Nonempty (JustificationHistory run c)) ∧
      (outgoing.target.epoch.toNat = c.epoch.toNat + 2 →
        ∃ middle : Checkpoint, middle.epoch.toNat = c.epoch.toNat + 1 ∧
          Nonempty (JustificationHistory run middle)) := by
  have middle (i : Fin 4) (set : call.weighed.justificationBits.bits[i] = true)
      (date : c.epoch.toNat + 1 + i.val = (getCurrentEpoch call.cached).toNat) :
      ∃ middle : Checkpoint, middle.epoch.toNat = c.epoch.toNat + 1 ∧
        Nonempty (JustificationHistory run middle) := by
    obtain ⟨quorum, epoch⟩ := justification_bit_call run genesis call i set
    exact ⟨quorum.target, by omega,
      history_of_call quorum (quorum_source_history run genesis quorum)⟩
  have finish (outgoing : QuorumCall run) (source : outgoing.source = c)
      (gap : outgoing.target.epoch.toNat = c.epoch.toNat + 1 ∨
        outgoing.target.epoch.toNat = c.epoch.toNat + 2)
      (mid : outgoing.target.epoch.toNat = c.epoch.toNat + 2 →
        ∃ middle : Checkpoint, middle.epoch.toNat = c.epoch.toNat + 1 ∧
          Nonempty (JustificationHistory run middle)) :
      ∃ outgoing : QuorumCall run, outgoing.source = c ∧
        (outgoing.target.epoch.toNat = c.epoch.toNat + 1 ∨
          outgoing.target.epoch.toNat = c.epoch.toNat + 2) ∧
        (c = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
          Nonempty (JustificationHistory run c)) ∧
        (outgoing.target.epoch.toNat = c.epoch.toNat + 2 →
          ∃ middle : Checkpoint, middle.epoch.toNat = c.epoch.toNat + 1 ∧
            Nonempty (JustificationHistory run middle)) := by
    exact ⟨outgoing, source, gap,
      source ▸ quorum_source_history run genesis outgoing, mid⟩
  have previous (set : call.weighed.justificationBits.bits[1] = true) :
      ∃ outgoing : QuorumCall run,
        outgoing.source = call.cached.previousJustifiedCheckpoint ∧
        outgoing.target.epoch.toNat + 1 = (getCurrentEpoch call.cached).toNat := by
    -- Bit one is either a fresh previous-target quorum or the retained current-target call.
    rcases (call_new_bits call).2 set with ⟨quorum, source, epoch⟩ | old
    · have prev := getPreviousEpoch_toNat call.cached
      have late := UInt64.lt_iff_toNat_lt.mp call.later
      simp only [GENESIS_EPOCH, UInt64.reduceAdd, UInt64.reduceToNat] at late
      exact ⟨quorum, source, by rw [epoch]; omega⟩
    · obtain ⟨pre, post, same, frame, _⟩ := call.selected_prefix
      obtain ⟨quorum, source, _, date⟩ := run_zero pre genesis
        (by simpa [frame.justificationBits] using old)
      let tail := (Run.nil.snoc (.slot call.advanced)).append post
      have eqRun : pre.append tail = run :=
        (append_slot_tail pre (.slot call.advanced) post).trans same.symm
      have result : ∃ outgoing : QuorumCall (pre.append tail),
          outgoing.source = call.cached.previousJustifiedCheckpoint ∧
          outgoing.target.epoch.toNat + 1 = (getCurrentEpoch call.cached).toNat := by
        refine ⟨quorum.extend tail, source.trans frame.previousJustified.symm, ?_⟩
        change quorum.target.epoch.toNat + 1 = _
        simpa [getCurrentEpoch_toNat, frame.slot] using date
      exact Eq.mp (congrArg (fun r => ∃ outgoing : QuorumCall r,
        outgoing.source = call.cached.previousJustifiedCheckpoint ∧
        outgoing.target.epoch.toNat + 1 = (getCurrentEpoch call.cached).toNat) eqRun) result
  rcases rule with ⟨source, three | two⟩ | ⟨source, two | one⟩
  · obtain ⟨outgoing, start, date⟩ := previous three.1
    exact finish outgoing (start.trans source.symm) (.inr (by omega))
      (fun _ => middle 2 three.2.1 (by omega))
  · obtain ⟨outgoing, start, date⟩ := previous two.1
    exact finish outgoing (start.trans source.symm) (.inl (by omega))
      (fun gap => False.elim (by omega))
  · obtain ⟨outgoing, start, _, date⟩ := (call_new_bits call).1 two.1
    have dateNat := congrArg UInt64.toNat date
    exact finish outgoing (start.trans source.symm) (.inr (by omega))
      (fun _ => middle 1 two.2.1 (by omega))
  · obtain ⟨outgoing, start, _, date⟩ := (call_new_bits call).1 one.1
    have dateNat := congrArg UInt64.toNat date
    exact finish outgoing (start.trans source.symm) (.inl (by omega))
      (fun gap => False.elim (by omega))

/-- The finalized field of the last state is the genesis checkpoint, or has a justification history.

The run starts at a genesis built from deposits. -/
theorem finalized_history {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) :
    a.state.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      Nonempty (JustificationHistory run a.state.finalizedCheckpoint) := by
  rcases finalized_field run genesis with initial | ⟨call, _, rule⟩
  · exact Or.inl initial
  · obtain ⟨_, _, _, history, _⟩ :=
      finalization_rule_quorums run genesis call _ rule
    exact history

private theorem call_target_window {g a : ForkedBeaconState preset}
    {run : Run config checks g a} (parameters : Parameters preset) (call : QuorumCall run) :
    call.target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < call.before.state.slot.toNat ∧
      call.before.state.slot.toNat < call.target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
  have frame := frame_processSlot call.cachedOk
  -- The successful root read puts the target's first slot strictly before the cached slot.
  have started := getBlockRoot_start_lt call.targetRoot
  rw [frame.slot] at started
  have current : (getCurrentEpoch call.cached).toNat =
      call.before.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp [getCurrentEpoch_toNat, frame.slot]
  have prev := getPreviousEpoch_toNat call.cached
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have division := Nat.mod_add_div call.before.state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have remainder := Nat.mod_lt call.before.state.slot.toNat positive
  have date := congrArg UInt64.toNat call.targetEpoch
  have roots := parameters.roots
  refine ⟨started, ?_⟩
  split at date
  · rw [current] at date
    rw [← date, Nat.mul_comm preset.SLOTS_PER_EPOCH.toNat] at division
    omega
  · rw [prev, current] at date
    have late := UInt64.lt_iff_toNat_lt.mp call.later
    simp only [GENESIS_EPOCH, UInt64.reduceAdd, UInt64.reduceToNat, current] at late
    have epochPositive : 0 < call.before.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by omega
    have pred : call.before.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
        call.target.epoch.toNat + 1 := by omega
    rw [pred, Nat.mul_add, Nat.mul_comm preset.SLOTS_PER_EPOCH.toNat] at division
    simp only [Nat.mul_one] at division
    omega

/-- Two quorum calls of the runs with one target have the same headers up to the target epoch.

Otherwise the headers and states of the runs show a collision of the node hash or a zero root.

The runs start at one genesis built from deposits, and the preset meets the parameters. -/
theorem call_target_binding {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (one : QuorumCall left) (two : QuorumCall right) (same : one.target = two.target) :
    left.checkpointPath one.target.epoch = right.checkpointPath two.target.epoch ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  obtain ⟨earlyOne, recentOne⟩ := call_target_window parameters one
  obtain ⟨earlyTwo, recentTwo⟩ := call_target_window parameters two
  have result := checkpoint_binding_cached left right genesis
    one.advanced two.advanced one.member two.member one.cached two.cached
    one.cachedOk two.cachedOk one.target.epoch one.target.root one.targetRoot
    (by simpa [same] using two.targetRoot) earlyOne
    (by simpa [same] using earlyTwo) recentOne (by simpa [same] using recentTwo)
  simpa [same] using result

end EthLib.Consensus.DirectSafety
