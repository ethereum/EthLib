module

public import EthLib.Consensus.Proofs.DirectSafety.Provenance
public import EthLib.Consensus.Proofs.DirectSafety.Hashes
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.FfgJustification
public import Mathlib.Tactic.FinCases

/-!
# Concrete justification calls and checkpoint fields

Every call below is at an epoch boundary of the supplied run, on the state after caching the slot.

A terminal view adds one justification step on the last state, and its test counts at that state.

The witnesses describe executions of the four bit rules, not an abstract finality relation.

[Gasper] §4 describes justification and finalization.

[Gasper]: https://arxiv.org/abs/2003.03052v3
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

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

/-- An epoch call splits the run before its slot step.

Caching the slot is a frame, and keeps the registry and the balances. -/
theorem EpochCall.selected_prefix {g a : ForkedBeaconState preset}
    {run : Run config checks g a} (call : EpochCall run) :
    ∃ (pre : Run config checks g call.before) (tail : Run config checks call.before a),
      run = pre.append tail ∧
      Frame call.before.state call.cached ∧
      call.cached.validators = call.before.state.validators ∧
      call.cached.balances = call.before.state.balances := by
  obtain ⟨pre, post, same⟩ := run.contains_split (.slot call.advanced) call.member
  refine ⟨pre, (Run.nil.snoc (.slot call.advanced)).append post,
    same.trans (Run.append_assoc pre (Run.nil.snoc (.slot call.advanced)) post).symm,
    frame_processSlot call.cachedOk, ?_⟩
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

/-- A target of the current or the previous epoch is at most one epoch behind the state. -/
private theorem currentEpoch_le_target {fork : Fork} {state : BeaconState preset fork}
    {current : Bool} {target : Checkpoint}
    (targetEpoch : target.epoch =
      if current then getCurrentEpoch state else getPreviousEpoch state) :
    (getCurrentEpoch state).toNat ≤ target.epoch.toNat + 1 := by
  rw [targetEpoch]
  cases current <;> simp [getPreviousEpoch_toNat]
  omega

/-- A quorum call targets its current epoch or the epoch before. -/
theorem QuorumCall.currentEpoch_le {g a : ForkedBeaconState preset}
    {run : Run config checks g a} (call : QuorumCall run) :
    (getCurrentEpoch call.cached).toNat ≤ call.target.epoch.toNat + 1 :=
  currentEpoch_le_target call.targetEpoch

/-- Epoch calls after epoch 1 through the epoch after `high` have active stake above 1.5 increments.

Below that, a test can pass with no vote, since a total balance is at least one increment.

A call at the epoch after `high` can count votes for a target at `high`. -/
def EnoughStake {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (high : Nat) : Prop :=
  ∀ call : EpochCall run, (getCurrentEpoch call.cached).toNat ≤ high + 1 →
    3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
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

The target is at most `high`.

The stake floor covers epoch calls through the epoch after `high`. -/
theorem quorum_count {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g)
    {high : Nat} (enough : EnoughStake run high) (call : QuorumCall run)
    (within : call.target.epoch.toNat ≤ high) :
    2 * Models.stake (effectiveWeight call.cached) (activeKeys call.cached) ≤
      3 * Models.stake (effectiveWeight call.cached) call.voters := by
  obtain ⟨pre, _, _, _, validators, _⟩ := call.toEpochCall.selected_prefix
  obtain ⟨_, _, _, initialized⟩ := genesis
  have unique : PubkeysDistinct call.cached := by
    simpa [PubkeysDistinct, validatorKeys, validators] using
      (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized pre.chainSteps).2
  exact call.passes.stake_le unique (enough call.toEpochCall
    (call.currentEpoch_le.trans (Nat.add_le_add_right within 1)))

/-- At the state of an epoch call, the pending attestations and target flags hold votes of the run.

The run starts at a genesis built from deposits, and the preset meets the parameters. -/
theorem cached_participation {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (call : EpochCall run) :
    ParticipationBacked run call.cached := by
  obtain ⟨pre, tail, same, _⟩ := call.selected_prefix
  have backed := inherited_participation pre tail parameters genesis
  rw [← same] at backed
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
    rcases targetIndices_ok counted with ⟨altair, counted⟩ | ⟨before, _, matching, indicesOk⟩
    · exact (backed.2.attester altair late current counted inside).2
    · obtain ⟨_, data, link, cast⟩ := backed.1.attester before
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
  obtain ⟨pre, tail, same, _, validators, _⟩ := call.toEpochCall.selected_prefix
  refine counted_accepted run (cached_participation run parameters genesis call.toEpochCall)
    call.later call.current call.target call.targetEpoch call.targetRoot call.counted ?_
  intro index data validator found voted
  -- The validator keeps its key from the cached state to the end of the run.
  have atBefore : call.before.state.validators.data[index.toNat]? = some validator := by
    simpa [validators] using found
  obtain ⟨last, atLast, keyLast⟩ := validators_getElem?_of_validatorKeys_prefix
    (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 atBefore
  rw [← keyLast]
  exact selected_vote_key run index data last atLast voted

/-- One passing test of justification at a state, for its previous or its current epoch.

The target is the checkpoint of that epoch, with the root that the state records for it. -/
private structure PassingTest {fork : Fork} (state : BeaconState preset fork) where
  current : Bool
  target : Checkpoint
  targetEpoch : target.epoch =
    if current then getCurrentEpoch state else getPreviousEpoch state
  targetRoot : getBlockRoot state target.epoch = .ok target.root
  indices : List ValidatorIndex
  counted : targetIndices state target.epoch = .ok indices
  passes : JustificationPasses state indices

/-- The justified checkpoint that the counted votes name as their source. -/
private def PassingTest.source {fork : Fork} {state : BeaconState preset fork}
    (test : PassingTest state) : Checkpoint :=
  if test.current then state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint

/-- The quorum call of an epoch call whose test passed at its cached state. -/
private def QuorumCall.ofTest {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : EpochCall run) (test : PassingTest call.cached) : QuorumCall run where
  toEpochCall := call
  current := test.current
  target := test.target
  targetEpoch := test.targetEpoch
  targetRoot := test.targetRoot
  indices := test.indices
  counted := test.counted
  passes := test.passes

/-- The reads of one justification step: two index lists and three balances.

The step weighs them and gives the state after justification. -/
private structure StepReads {fork : Fork} (state after : BeaconState preset fork) where
  previous : List ValidatorIndex
  current : List ValidatorIndex
  total : Gwei
  previousBalance : Gwei
  currentBalance : Gwei
  previousOk : targetIndices state (getPreviousEpoch state) = .ok previous
  currentOk : targetIndices state (getCurrentEpoch state) = .ok current
  totalOk : getTotalActiveBalance state = .ok total
  previousBalanceOk : getTotalBalance state previous = .ok previousBalance
  currentBalanceOk : getTotalBalance state current = .ok currentBalance
  weighed : weighJustificationAndFinalization state total previousBalance currentBalance =
    .ok after

/-- A justification step keeps its state in the first two epochs, and later it reads and weighs. -/
private theorem step_reads {fork : Fork} {state after : BeaconState preset fork}
    (ok : processJustificationAndFinalization state = .ok after) :
    (getCurrentEpoch state ≤ GENESIS_EPOCH + 1 ∧ after = state) ∨
      GENESIS_EPOCH + 1 < getCurrentEpoch state ∧ Nonempty (StepReads state after) := by
  rcases processJustificationAndFinalization_reads ok with early | ⟨later, previous, current,
      total, pb, cb, previousOk, currentOk, totalOk, pbOk, cbOk, weighed⟩
  · exact .inl early
  · exact .inr ⟨later, ⟨⟨previous, current, total, pb, cb, previousOk, currentOk, totalOk, pbOk,
      cbOk, weighed⟩⟩⟩

/-- The passing test of a step whose weighing passes for its previous or its current epoch. -/
private def StepReads.test {fork : Fork} {state after : BeaconState preset fork}
    (reads : StepReads state after) (now : Bool) (target : Checkpoint)
    (targetEpoch : target.epoch =
      if now then getCurrentEpoch state else getPreviousEpoch state)
    (targetRoot : getBlockRoot state target.epoch = .ok target.root)
    {threshold weighted : Gwei} (thresholdOk : Uint64.mulChecked reads.total 2 = .ok threshold)
    (weightedOk : Uint64.mulChecked
      (if now then reads.currentBalance else reads.previousBalance) 3 = .ok weighted)
    (passes : threshold ≤ weighted) : PassingTest state where
  current := now
  target := target
  targetEpoch := targetEpoch
  targetRoot := targetRoot
  indices := if now then reads.current else reads.previous
  counted := by
    rw [targetEpoch]
    cases now
    · exact reads.previousOk
    · exact reads.currentOk
  passes := ⟨reads.total, if now then reads.currentBalance else reads.previousBalance, threshold,
    weighted, reads.totalOk, by cases now <;> [exact reads.previousBalanceOk;
      exact reads.currentBalanceOk], thresholdOk, weightedOk, passes⟩

/-- After epoch 1, the previous epoch is the epoch just before the current one. -/
private theorem previousEpoch_add_one {fork : Fork} {state : BeaconState preset fork}
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
    (getPreviousEpoch state).toNat + 1 = (getCurrentEpoch state).toNat := by
  have previousEpoch := getPreviousEpoch_toNat state
  have late := UInt64.lt_iff_toNat_lt.mp later
  simp only [GENESIS_EPOCH, UInt64.reduceAdd, UInt64.reduceToNat] at late
  omega

private theorem step_bits {fork : Fork} {state after : BeaconState preset fork}
    (reads : StepReads state after) (later : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (i : Fin 4) (set : after.justificationBits.bits[i] = true) :
    (∃ test : PassingTest state,
      test.target.epoch.toNat + i.val = (getCurrentEpoch state).toNat) ∨
      ∃ j : Fin 4, j.val + 1 = i.val ∧ state.justificationBits.bits[j] = true := by
  obtain ⟨threshold, pw, cw, thresholdOk, pwOk, cwOk, zero, one, two, _⟩ :=
    weighJustificationAndFinalization_bits reads.weighed
  fin_cases i
  · obtain ⟨passes, root, rootOk, _⟩ := zero set
    exact .inl ⟨reads.test true ⟨_, root⟩ rfl rootOk thresholdOk cwOk passes, rfl⟩
  · rcases one set with ⟨passes, root, rootOk⟩ | old
    · exact .inl ⟨reads.test false ⟨_, root⟩ rfl rootOk thresholdOk pwOk passes,
        previousEpoch_add_one later⟩
    · exact .inr ⟨0, rfl, old⟩
  · exact .inr ⟨1, rfl, two ▸ set⟩
  · right
    refine ⟨2, rfl, ?_⟩
    have weighed := reads.weighed
    simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at weighed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, eq⟩ := weighed
    rw [← eq] at set
    simpa [shiftJustificationBits] using set

private theorem step_new_bits {fork : Fork} {state after : BeaconState preset fork}
    (reads : StepReads state after) (later : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
    (after.justificationBits.bits[0] = true →
      ∃ test : PassingTest state,
        test.source = state.currentJustifiedCheckpoint ∧
        test.target = after.currentJustifiedCheckpoint ∧
        test.target.epoch = getCurrentEpoch state) ∧
    (after.justificationBits.bits[1] = true →
      (∃ test : PassingTest state,
        test.source = state.previousJustifiedCheckpoint ∧
        test.target.epoch.toNat + 1 = (getCurrentEpoch state).toNat) ∨
      state.justificationBits.bits[0] = true) := by
  obtain ⟨threshold, pw, cw, thresholdOk, pwOk, cwOk, zero, one, _⟩ :=
    weighJustificationAndFinalization_bits reads.weighed
  constructor
  · intro set
    obtain ⟨passes, root, rootOk, target⟩ := zero set
    exact ⟨reads.test true ⟨_, root⟩ rfl rootOk thresholdOk cwOk passes, rfl, target.symm, rfl⟩
  · intro set
    rcases one set with ⟨passes, root, rootOk⟩ | old
    · exact .inl ⟨reads.test false ⟨_, root⟩ rfl rootOk thresholdOk pwOk passes, rfl,
        previousEpoch_add_one later⟩
    · exact .inr old

private theorem step_current {fork : Fork} {state after : BeaconState preset fork}
    (reads : StepReads state after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
      ∃ test : PassingTest state,
        test.target = after.currentJustifiedCheckpoint ∧
        (test.source = state.previousJustifiedCheckpoint ∨
          test.source = state.currentJustifiedCheckpoint) := by
  rcases weighJustificationAndFinalization_currentJustified reads.weighed with ⟨same, _⟩ |
    ⟨now, threshold, weighted, thresholdOk, weightedOk, passes, epoch, root⟩
  · exact .inl same
  · refine .inr ⟨reads.test now after.currentJustifiedCheckpoint epoch root thresholdOk
      weightedOk passes, rfl, ?_⟩
    cases now <;> simp [PassingTest.source, StepReads.test]

private theorem call_reads {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (call : EpochCall run) : Nonempty (StepReads call.cached call.weighed) := by
  rcases step_reads call.weighedOk with ⟨early, _⟩ | ⟨_, reads⟩
  · exact False.elim (UInt64.not_le.mpr call.later early)
  · exact reads

/-- An epoch call made by the last slot step of a run. -/
private def EpochCall.ofSlot {g before after : ForkedBeaconState preset}
    (pre : Run config checks g before) (ok : advanceSlotAcross config checks before = .ok after)
    {cached weighed : BeaconState preset before.fork}
    (boundary : (before.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (cachedOk : processSlot before.state = .ok cached)
    (weighedOk : processJustificationAndFinalization cached = .ok weighed)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch cached) : EpochCall (pre.snoc (.slot ok)) where
  before := before
  after := after
  advanced := ok
  member := .last pre (.slot ok)
  boundary := boundary
  cached := cached
  weighed := weighed
  cachedOk := cachedOk
  weighedOk := weighedOk
  later := later

/-- A slot step keeps the justification of the cached state, or it runs an epoch call.

The state after the step has the justification bits and checkpoints of `weighed`.

Inside an epoch, `weighed` is the cached state and the epoch stays.

At the end of an epoch the epoch moves on by one.

There, in the first two epochs `weighed` is the cached state.

Later, justification takes the cached state to `weighed`. -/
private theorem slot_step {before after : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks before = .ok after) :
    ∃ cached weighed : BeaconState preset before.fork,
      processSlot before.state = .ok cached ∧
      after.state.justificationBits = weighed.justificationBits ∧
      after.state.previousJustifiedCheckpoint = weighed.previousJustifiedCheckpoint ∧
      after.state.currentJustifiedCheckpoint = weighed.currentJustifiedCheckpoint ∧
      after.state.finalizedCheckpoint = weighed.finalizedCheckpoint ∧
      ((weighed = cached ∧
          (getCurrentEpoch after.state).toNat = (getCurrentEpoch before.state).toNat) ∨
        ((before.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
          (getCurrentEpoch after.state).toNat = (getCurrentEpoch before.state).toNat + 1 ∧
          ((getCurrentEpoch cached ≤ GENESIS_EPOCH + 1 ∧ weighed = cached) ∨
            (GENESIS_EPOCH + 1 < getCurrentEpoch cached ∧
              processJustificationAndFinalization cached = .ok weighed)))) := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  obtain ⟨next, cached, epoched, sum, cachedOk, epochOk, rfl⟩ := advanceSlot_ok advancedOk
  have bits := processUpgrades_justificationBits upgraded
  have justified := processUpgrades_justified upgraded
  have finalized : after.state.finalizedCheckpoint = epoched.finalizedCheckpoint :=
    processUpgrades_induction
      (property := fun state => state.state.finalizedCheckpoint = epoched.finalizedCheckpoint)
      (fun same stepOk => (upgradeFrame_upgradeNext stepOk).finalized.trans same) rfl upgraded
  have endEpoch : (getCurrentEpoch after.state).toNat =
      next.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp [getCurrentEpoch_toNat, processUpgrades_slot upgraded]
  unfold epochIfLast at epochOk
  split at epochOk
  · rename_i boundary
    obtain ⟨weighed, weighedOk, frame⟩ := processEpoch_frame epochOk
    refine ⟨cached, weighed, cachedOk, bits.trans frame.justificationBits,
      justified.1.trans frame.previousJustified, justified.2.trans frame.currentJustified,
      finalized.trans frame.finalized, .inr ⟨?_, ?_, ?_⟩⟩
    · have natural := congrArg UInt64.toNat boundary
      simpa [UInt64.toNat_mod, sum] using natural
    · rw [endEpoch, getCurrentEpoch_toNat]
      exact nextSlot_epoch_of_boundary sum boundary
    -- Justification does not run in the first two epochs.
    · by_cases early : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1
      · exact .inl ⟨early, processJustificationAndFinalization_early_eq early weighedOk⟩
      · exact .inr ⟨UInt64.not_le.mp early, weighedOk⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochOk
    subst epochOk
    refine ⟨cached, cached, cachedOk, bits, justified.1, justified.2, finalized, .inl ⟨rfl, ?_⟩⟩
    rw [endEpoch, getCurrentEpoch_toNat]
    exact nextSlot_epoch_of_inside sum ‹_›

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
      obtain ⟨cached, weighed, cachedOk, bits, -, -, -, cases⟩ := slot_step ok
      have cachedFrame := frame_processSlot cachedOk
      have weighedSet : weighed.justificationBits.bits[i] = true := by simpa [bits] using set
      have cacheEpoch : (getCurrentEpoch cached).toNat = (getCurrentEpoch before.state).toNat := by
        simp [getCurrentEpoch_toNat, cachedFrame.slot]
      rcases cases with ⟨same, epoch⟩ | ⟨boundary, epoch, ⟨early, same⟩ | ⟨later, weighedOk⟩⟩
      · subst same
        exact old (bits.trans cachedFrame.justificationBits) epoch
      -- In the first two epochs no bit can name an epoch before genesis.
      · subst same
        obtain ⟨quorum, target⟩ := ih i (by simpa [cachedFrame.justificationBits] using weighedSet)
        have beforeEpoch : (getCurrentEpoch before.state).toNat ≤ 1 := by
          have := UInt64.le_iff_toNat_le.mp early
          simp only [GENESIS_EPOCH, UInt64.reduceAdd, UInt64.reduceToNat] at this
          omega
        have targetLate : 1 ≤ quorum.target.epoch.toNat := by
          have := UInt64.lt_iff_toNat_lt.mp quorum.later
          have prev := getPreviousEpoch_toNat quorum.cached
          rw [quorum.targetEpoch]
          split <;> simp_all [GENESIS_EPOCH] <;> omega
        omega
      · let call := EpochCall.ofSlot pre ok boundary cachedOk weighedOk later
        obtain ⟨reads⟩ := call_reads call
        rcases step_bits reads later i weighedSet with ⟨test, target⟩ | ⟨j, shift, oldSet⟩
        · refine ⟨.ofTest call test, ?_⟩
          change test.target.epoch.toNat + i.val = (getCurrentEpoch cached).toNat at target
          change test.target.epoch.toNat + i.val + 1 = _
          omega
        · obtain ⟨quorum, target⟩ := ih j
            (by simpa [call, EpochCall.ofSlot, cachedFrame.justificationBits] using oldSet)
          refine ⟨quorum.extend (Run.nil.snoc (.slot ok)), ?_⟩
          change quorum.target.epoch.toNat + i.val + 1 = _
          omega

/-- A set bit identifies a successful test on this run, not merely an epoch number. -/
private theorem justification_bit_call {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (call : EpochCall run) (i : Fin 4) (set : call.weighed.justificationBits.bits[i] = true) :
    ∃ witness : QuorumCall run,
      witness.target.epoch.toNat + i.val = (getCurrentEpoch call.cached).toNat := by
  obtain ⟨reads⟩ := call_reads call
  rcases step_bits reads call.later i set with ⟨test, direct⟩ | ⟨j, shift, oldSet⟩
  · exact ⟨.ofTest call test, direct⟩
  · obtain ⟨pre, tail, same, frame, _⟩ := call.selected_prefix
    obtain ⟨quorum, target⟩ := run_bits pre genesis j
      (by simpa [frame.justificationBits] using oldSet)
    have result : ∃ witness : QuorumCall (pre.append tail),
        witness.target.epoch.toNat + i.val = (getCurrentEpoch call.cached).toNat := by
      refine ⟨quorum.extend tail, ?_⟩
      have cachedEpoch : (getCurrentEpoch call.cached).toNat =
          (getCurrentEpoch call.before.state).toNat := by
        simp [getCurrentEpoch_toNat, frame.slot]
      change quorum.target.epoch.toNat + i.val = _
      omega
    exact Eq.mp (by rw [← same]) result

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
      obtain ⟨cached, weighed, cachedOk, bits, previous, current, -, cases⟩ := slot_step ok
      have cachedFrame := frame_processSlot cachedOk
      have weighedSet : weighed.justificationBits.bits[0] = true := by simpa [bits] using set
      rcases cases with ⟨same, epoch⟩ | ⟨boundary, epoch, ⟨early, same⟩ | ⟨later, weighedOk⟩⟩
      · subst same
        exact old (bits.trans cachedFrame.justificationBits)
          (previous.trans cachedFrame.previousJustified)
          (current.trans cachedFrame.currentJustified) epoch
      -- In the first two epochs no bit can name an epoch before genesis.
      · subst same
        obtain ⟨quorum, date⟩ := run_bits pre genesis 0
          (by simpa [cachedFrame.justificationBits] using weighedSet)
        have earlyNat : (getCurrentEpoch before.state).toNat ≤ 1 := by
          simpa [getCurrentEpoch_toNat, cachedFrame.slot, GENESIS_EPOCH] using
            UInt64.le_iff_toNat_le.mp early
        have late := UInt64.lt_iff_toNat_lt.mp quorum.later
        have prev := getPreviousEpoch_toNat quorum.cached
        have target := congrArg UInt64.toNat quorum.targetEpoch
        simp only [GENESIS_EPOCH, UInt64.reduceAdd, UInt64.reduceToNat] at late
        split at target <;> simp only [Fin.val_zero] at date <;> omega
      · let call := EpochCall.ofSlot pre ok boundary cachedOk weighedOk later
        obtain ⟨reads⟩ := call_reads call
        obtain ⟨test, source, target, date⟩ := (step_new_bits reads call.later).1 weighedSet
        have rotated := (weighJustificationAndFinalization_checkpoints reads.weighed).1
        refine ⟨.ofTest call test, source.trans (rotated.symm.trans previous.symm),
          target.trans current.symm, ?_⟩
        have dateNat := congrArg UInt64.toNat date
        change test.target.epoch.toNat = (getCurrentEpoch cached).toNat at dateNat
        change test.target.epoch.toNat + 1 = _
        have cacheEpoch : (getCurrentEpoch cached).toNat =
            (getCurrentEpoch before.state).toNat := by
          simp [getCurrentEpoch_toNat, cachedFrame.slot]
        omega

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
      obtain ⟨cached, weighed, cachedOk, -, previous, current, -, cases⟩ := slot_step ok
      have cachedFrame := frame_processSlot cachedOk
      have fromCached (c : Checkpoint)
          (field : c = cached.previousJustifiedCheckpoint ∨
            c = cached.currentJustifiedCheckpoint) :
          c = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
            Nonempty (JustificationHistory (pre.snoc (.slot ok)) c) :=
        old c (field.elim (fun h => .inl (h.trans cachedFrame.previousJustified))
          (fun h => .inr (h.trans cachedFrame.currentJustified)))
      have weighedField : c = weighed.previousJustifiedCheckpoint ∨
          c = weighed.currentJustifiedCheckpoint :=
        field.elim (fun h => .inl (h.trans previous)) (fun h => .inr (h.trans current))
      rcases cases with ⟨same, -⟩ | ⟨boundary, -, ⟨-, same⟩ | ⟨later, weighedOk⟩⟩
      · subst same
        exact fromCached c weighedField
      · subst same
        exact fromCached c weighedField
      · let call := EpochCall.ofSlot pre ok boundary cachedOk weighedOk later
        rcases weighedField with previous | current
        · rcases processJustificationAndFinalization_ok weighedOk with eq |
            ⟨_, _, _, weighing⟩
          · exact fromCached c (.inl (eq ▸ previous))
          · exact fromCached c (.inr
              (previous.trans (weighJustificationAndFinalization_checkpoints weighing).1))
        · obtain ⟨reads⟩ := call_reads call
          rcases step_current reads with same | ⟨test, target, source⟩
          · exact fromCached c (.inr (current.trans same))
          · have history := history_of_call (.ofTest call test) (fromCached test.source source)
            exact .inr ((target.trans current.symm) ▸ history)

private theorem quorum_source_history {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) (call : QuorumCall run) :
    call.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      Nonempty (JustificationHistory run call.source) := by
  obtain ⟨pre, tail, same, frame, _⟩ := call.toEpochCall.selected_prefix
  have field : call.source = call.before.state.previousJustifiedCheckpoint ∨
      call.source = call.before.state.currentJustifiedCheckpoint := by
    unfold QuorumCall.source
    cases call.current
    · exact .inl frame.previousJustified
    · exact .inr frame.currentJustified
  rcases justified_fields pre genesis call.source field with initial | history
  · exact .inl initial
  · obtain ⟨history⟩ := history
    have result : Nonempty (JustificationHistory (pre.append tail) call.source) :=
      ⟨history.extend tail⟩
    exact .inr (Eq.mp (by rw [← same]) result)

/-- The four rules by which one justification step finalizes a checkpoint, read from its bits. -/
private def StepRule {fork : Fork} (state after : BeaconState preset fork)
    (checkpoint : Checkpoint) : Prop :=
  let bits := after.justificationBits.bits
  let e := (getCurrentEpoch state).toNat
  (checkpoint = state.previousJustifiedCheckpoint ∧
    ((bits[1] = true ∧ bits[2] = true ∧ bits[3] = true ∧ checkpoint.epoch.toNat + 3 = e) ∨
      (bits[1] = true ∧ bits[2] = true ∧ checkpoint.epoch.toNat + 2 = e))) ∨
  (checkpoint = state.currentJustifiedCheckpoint ∧
    ((bits[0] = true ∧ bits[1] = true ∧ bits[2] = true ∧ checkpoint.epoch.toNat + 2 = e) ∨
      (bits[0] = true ∧ bits[1] = true ∧ checkpoint.epoch.toNat + 1 = e)))

private theorem step_rule {fork : Fork} {state after : BeaconState preset fork}
    (computed : processJustificationAndFinalization state = .ok after) :
    after.finalizedCheckpoint = state.finalizedCheckpoint ∨
      StepRule state after after.finalizedCheckpoint := by
  rcases processJustificationAndFinalization_ok computed with same |
    ⟨total, previous, current, ok⟩
  · exact .inl (congrArg BeaconState.finalizedCheckpoint same)
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure,
    Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, b₃, h₃, b₂, h₂, c₂, hc₂, c₁, hc₁, eq⟩ := ok
  unfold StepRule
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
      obtain ⟨cached, weighed, cachedOk, -, -, -, lastEq, cases⟩ := slot_step ok
      have cachedFrame := frame_processSlot cachedOk
      rcases cases with ⟨same, -⟩ | ⟨boundary, -, ⟨-, same⟩ | ⟨later, weighedOk⟩⟩
      · subst same
        exact keep (lastEq.trans cachedFrame.finalized)
      · subst same
        exact keep (lastEq.trans cachedFrame.finalized)
      · let call := EpochCall.ofSlot pre ok boundary cachedOk weighedOk later
        rcases step_rule weighedOk with same | rule
        · exact keep (lastEq.trans (same.trans cachedFrame.finalized))
        · exact .inr ⟨call, lastEq.symm, lastEq ▸ rule⟩

/-- A finalization rule of one step gives a quorum from the checkpoint, one or two epochs ahead.

The caller supplies the quorums behind the bits of the step, fresh or kept from earlier steps.

With a target two epochs ahead, a checkpoint of the epoch between them satisfies the predicate. -/
private theorem rule_quorums {fork : Fork} {state after : BeaconState preset fork} {Q : Type}
    (source target : Q → Checkpoint) (H : Checkpoint → Prop) {c : Checkpoint}
    (rule : StepRule state after c)
    (current : after.justificationBits.bits[0] = true → ∃ q : Q,
      source q = state.currentJustifiedCheckpoint ∧ (target q).epoch = getCurrentEpoch state)
    (previous : after.justificationBits.bits[1] = true → ∃ q : Q,
      source q = state.previousJustifiedCheckpoint ∧
        (target q).epoch.toNat + 1 = (getCurrentEpoch state).toNat)
    (middle : ∀ i : Fin 4, after.justificationBits.bits[i] = true → ∃ m : Checkpoint,
      m.epoch.toNat + i.val = (getCurrentEpoch state).toNat ∧ H m) :
    ∃ q : Q, source q = c ∧
      ((target q).epoch.toNat = c.epoch.toNat + 1 ∨
        (target q).epoch.toNat = c.epoch.toNat + 2) ∧
      ((target q).epoch.toNat = c.epoch.toNat + 2 →
        ∃ m : Checkpoint, m.epoch.toNat = c.epoch.toNat + 1 ∧ H m) := by
  have between (i : Fin 4) (set : after.justificationBits.bits[i] = true)
      (date : c.epoch.toNat + 1 + i.val = (getCurrentEpoch state).toNat) :
      ∃ m : Checkpoint, m.epoch.toNat = c.epoch.toNat + 1 ∧ H m := by
    obtain ⟨m, epoch, holds⟩ := middle i set
    exact ⟨m, by omega, holds⟩
  rcases rule with ⟨named, three | two⟩ | ⟨named, two | one⟩
  · obtain ⟨q, start, date⟩ := previous three.1
    exact ⟨q, start.trans named.symm, .inr (by omega), fun _ => between 2 three.2.1 (by omega)⟩
  · obtain ⟨q, start, date⟩ := previous two.1
    exact ⟨q, start.trans named.symm, .inl (by omega), fun _ => False.elim (by omega)⟩
  · obtain ⟨q, start, date⟩ := current two.1
    have dateNat := congrArg UInt64.toNat date
    exact ⟨q, start.trans named.symm, .inr (by omega), fun _ => between 1 two.2.1 (by omega)⟩
  · obtain ⟨q, start, date⟩ := current one.1
    have dateNat := congrArg UInt64.toNat date
    exact ⟨q, start.trans named.symm, .inl (by omega), fun _ => False.elim (by omega)⟩

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
  have middle (i : Fin 4) (set : call.weighed.justificationBits.bits[i] = true) :
      ∃ middle : Checkpoint, middle.epoch.toNat + i.val = (getCurrentEpoch call.cached).toNat ∧
        Nonempty (JustificationHistory run middle) := by
    obtain ⟨quorum, epoch⟩ := justification_bit_call run genesis call i set
    exact ⟨quorum.target, epoch,
      history_of_call quorum (quorum_source_history run genesis quorum)⟩
  obtain ⟨reads⟩ := call_reads call
  have current (set : call.weighed.justificationBits.bits[0] = true) :
      ∃ outgoing : QuorumCall run,
        outgoing.source = call.cached.currentJustifiedCheckpoint ∧
        outgoing.target.epoch = getCurrentEpoch call.cached := by
    obtain ⟨test, source, -, date⟩ := (step_new_bits reads call.later).1 set
    exact ⟨.ofTest call test, source, date⟩
  have previous (set : call.weighed.justificationBits.bits[1] = true) :
      ∃ outgoing : QuorumCall run,
        outgoing.source = call.cached.previousJustifiedCheckpoint ∧
        outgoing.target.epoch.toNat + 1 = (getCurrentEpoch call.cached).toNat := by
    -- Bit one is either a fresh previous-target quorum or the retained current-target call.
    rcases (step_new_bits reads call.later).2 set with ⟨test, source, epoch⟩ | old
    · exact ⟨.ofTest call test, source, epoch⟩
    · obtain ⟨pre, tail, same, frame, _⟩ := call.selected_prefix
      obtain ⟨quorum, source, _, date⟩ := run_zero pre genesis
        (by simpa [frame.justificationBits] using old)
      have result : ∃ outgoing : QuorumCall (pre.append tail),
          outgoing.source = call.cached.previousJustifiedCheckpoint ∧
          outgoing.target.epoch.toNat + 1 = (getCurrentEpoch call.cached).toNat := by
        refine ⟨quorum.extend tail, source.trans frame.previousJustified.symm, ?_⟩
        change quorum.target.epoch.toNat + 1 = _
        simpa [getCurrentEpoch_toNat, frame.slot] using date
      exact Eq.mp (by rw [← same]) result
  obtain ⟨outgoing, source, gap, mid⟩ := rule_quorums QuorumCall.source QuorumCall.target
    (fun middle => Nonempty (JustificationHistory run middle)) rule current previous middle
  exact ⟨outgoing, source, gap, source ▸ quorum_source_history run genesis outgoing, mid⟩

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

/-! ## A terminal justification step

Fork choice runs justification and finalization once on a held state, without advancing it.

Its checkpoints are fields of no state of a run, so the views below carry that one step.

The step adds no vote: the keys it counts voted in blocks of the run. -/

/-- The checkpoint fields of the last state of a run, or of one justification step on it. -/
inductive TerminalView (a : ForkedBeaconState preset) : Type where
  | realized
  | pulled (after : BeaconState preset a.fork)
      (ok : processJustificationAndFinalization a.state = .ok after)

/-- The state whose checkpoint fields the view reads. -/
def TerminalView.state {a : ForkedBeaconState preset} (view : TerminalView a) :
    BeaconState preset a.fork :=
  match view with
  | .realized => a.state
  | .pulled after _ => after

/-- The step counts votes at the last state, so it needs a stake floor there.

As for epoch calls, the floor is needed only up to one epoch past `high`. -/
def TerminalView.enough {a : ForkedBeaconState preset} (view : TerminalView a) (high : Nat) :
    Prop :=
  match view with
  | .realized => True
  | .pulled _ _ => (getCurrentEpoch a.state).toNat ≤ high + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch a.state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (effectiveWeight a.state) (activeKeys a.state)

/-- A test of justification that passed in the step of the view, at the last state. -/
structure TerminalQuorum {a : ForkedBeaconState preset} (view : TerminalView a) where
  after : BeaconState preset a.fork
  projected : processJustificationAndFinalization a.state = .ok after
  selected : view = .pulled after projected
  later : GENESIS_EPOCH + 1 < getCurrentEpoch a.state
  current : Bool
  target : Checkpoint
  targetEpoch : target.epoch =
    if current then getCurrentEpoch a.state else getPreviousEpoch a.state
  targetRoot : getBlockRoot a.state target.epoch = .ok target.root
  indices : List ValidatorIndex
  counted : targetIndices a.state target.epoch = .ok indices
  passes : JustificationPasses a.state indices

/-- The justified checkpoint that the counted votes name as their source. -/
def TerminalQuorum.source {a : ForkedBeaconState preset} {view : TerminalView a}
    (call : TerminalQuorum view) : Checkpoint :=
  if call.current then a.state.currentJustifiedCheckpoint
    else a.state.previousJustifiedCheckpoint

/-- The keys of the validators that the step counted. -/
noncomputable def TerminalQuorum.voters {a : ForkedBeaconState preset} {view : TerminalView a}
    (call : TerminalQuorum view) : Finset BLSPubkey :=
  keysAt a.state call.indices

/-- A quorum call of the run, or a test that passed in the step of the view. -/
abbrev ViewQuorum {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (view : TerminalView a) :=
  QuorumCall run ⊕ TerminalQuorum view

/-- The source checkpoint of the quorum. -/
def ViewQuorum.source {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {view : TerminalView a} (call : ViewQuorum run view) : Checkpoint :=
  match call with
  | .inl c => c.source
  | .inr c => c.source

/-- The target checkpoint of the quorum. -/
def ViewQuorum.target {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {view : TerminalView a} (call : ViewQuorum run view) : Checkpoint :=
  match call with
  | .inl c => c.target
  | .inr c => c.target

/-- The keys that the quorum counted. -/
noncomputable def ViewQuorum.voters {g a : ForkedBeaconState preset}
    {run : Run config checks g a} {view : TerminalView a}
    (call : ViewQuorum run view) : Finset BLSPubkey :=
  match call with
  | .inl c => c.voters
  | .inr c => c.voters

/-- The state at which the quorum ran its test. -/
def ViewQuorum.state {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {view : TerminalView a} (call : ViewQuorum run view) : ForkedBeaconState preset :=
  match call with
  | .inl c => ⟨c.before.fork, c.cached⟩
  | .inr _ => a

/-- The step counts at most one epoch past the epoch of its target. -/
theorem TerminalQuorum.currentEpoch_le {a : ForkedBeaconState preset}
    {view : TerminalView a} (call : TerminalQuorum view) :
    (getCurrentEpoch a.state).toNat ≤ call.target.epoch.toNat + 1 :=
  currentEpoch_le_target call.targetEpoch

/-- At a view without a step, each quorum is a quorum call of the run. -/
theorem ViewQuorum.eq_inl_of_realized {g a : ForkedBeaconState preset}
    {run : Run config checks g a} (call : ViewQuorum run .realized) :
    ∃ c : QuorumCall run, call = .inl c := by
  rcases call with c | step
  · exact ⟨c, rfl⟩
  · exact nomatch step.selected

/-- The quorum of a step whose test passed at the last state. -/
private def TerminalQuorum.ofTest {a : ForkedBeaconState preset}
    {after : BeaconState preset a.fork}
    (ok : processJustificationAndFinalization a.state = .ok after)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch a.state) (test : PassingTest a.state) :
    TerminalQuorum (.pulled after ok) where
  after := after
  projected := ok
  selected := rfl
  later := later
  current := test.current
  target := test.target
  targetEpoch := test.targetEpoch
  targetRoot := test.targetRoot
  indices := test.indices
  counted := test.counted
  passes := test.passes

/-- The justified checkpoint that a link names as its source is older than its target. -/
private theorem link_source_lt {fork : Fork} {state : BeaconState preset fork}
    (settled : JustifiedSettled state) (separated : JustifiedSeparated state)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch state) (current : Bool) (target : Checkpoint)
    (targetEpoch : target.epoch =
      if current then getCurrentEpoch state else getPreviousEpoch state) :
    (if current then state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint).epoch < target.epoch := by
  have previous := separated later
  rw [targetEpoch]
  cases current
  · exact previous
  · have settledNat := UInt64.le_iff_toNat_le.mp settled
    have laterNat := UInt64.lt_iff_toNat_lt.mp later
    apply UInt64.lt_iff_toNat_lt.mpr
    simp only [getPreviousEpoch_toNat] at settledNat
    have one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := by decide
    rw [one] at laterNat
    simp only [↓reduceIte]
    omega

private theorem call_epochs {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g)
    (call : QuorumCall run) : call.source.epoch < call.target.epoch := by
  obtain ⟨pre, _, _, frame, _⟩ := call.toEpochCall.selected_prefix
  obtain ⟨holds, _, separated⟩ := run_justified_separated pre genesis
  exact link_source_lt (frame.invariant holds).settled (separated.of_frame frame) call.later
    call.current call.target call.targetEpoch

private theorem terminal_epochs {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) {view : TerminalView a}
    (call : TerminalQuorum view) : call.source.epoch < call.target.epoch := by
  obtain ⟨holds, _, separated⟩ := run_justified_separated run genesis
  exact link_source_lt holds.settled separated call.later call.current call.target
    call.targetEpoch

/-- The first call crossing an epoch is chosen from the actual justification history. -/
private theorem history_crossing {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {c : Checkpoint} (history : JustificationHistory run c) (epoch : Nat)
    (positive : 0 < epoch) (reached : epoch ≤ c.epoch.toNat) :
    ∃ call ∈ history.calls,
      call.source.epoch.toNat < epoch ∧ epoch ≤ call.target.epoch.toNat := by
  have crossing (calls : List (QuorumCall run))
      (start : ∀ call, calls.head? = some call → call.source.epoch.toNat < epoch)
      (finish : ∀ call, calls.getLast? = some call → epoch ≤ call.target.epoch.toNat)
      (consecutive : ∀ i one two, calls[i]? = some one → calls[i + 1]? = some two →
        one.target = two.source) (nonempty : calls ≠ []) :
      ∃ call ∈ calls, call.source.epoch.toNat < epoch ∧
        epoch ≤ call.target.epoch.toNat := by
    induction calls with
    | nil => exact False.elim (nonempty rfl)
    | cons first rest ih =>
      by_cases crossed : epoch ≤ first.target.epoch.toNat
      · exact ⟨first, by simp, start first rfl, crossed⟩
      · cases rest with
        | nil => exact False.elim (crossed (finish first rfl))
        | cons second tail =>
          have joined := consecutive 0 first second rfl rfl
          obtain ⟨call, member, bounds⟩ := ih
            (by
              intro call head
              simp only [List.head?_cons, Option.some.injEq] at head
              subst call
              rw [← joined]
              omega)
            (by
              intro call last
              apply finish call
              simpa using last)
            (by
              intro i one two hOne hTwo
              exact consecutive (i + 1) one two hOne hTwo)
            (by simp)
          exact ⟨call, List.mem_cons_of_mem first member, bounds⟩
  refine crossing history.calls ?_ ?_ history.consecutive history.nonempty
  · intro call head
    rw [history.start call head]
    exact positive
  · intro call last
    rw [history.finish call last]
    exact reached

private theorem history_target_bound {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    {c : Checkpoint} (history : JustificationHistory run c)
    (call : QuorumCall run) (member : call ∈ history.calls) :
    call.target.epoch.toNat ≤ c.epoch.toNat := by
  have bound (calls : List (QuorumCall run))
      (finish : ∀ last, calls.getLast? = some last → last.target = c)
      (consecutive : ∀ i one two, calls[i]? = some one → calls[i + 1]? = some two →
        one.target = two.source) :
      ∀ call ∈ calls, call.target.epoch.toNat ≤ c.epoch.toNat := by
    induction calls with
    | nil => simp
    | cons first rest ih =>
      intro call member
      cases rest with
      | nil =>
        have equal := finish first rfl
        have same := List.mem_singleton.mp member
        subst call
        rw [equal]
      | cons second tail =>
        have tailBound := ih (by intro last found; apply finish last; simpa using found)
          (by intro i one two hOne hTwo; exact consecutive (i + 1) one two hOne hTwo)
        rcases List.mem_cons.mp member with same | member
        · subst call
          have joined := consecutive 0 first second rfl rfl
          have secondBound := tailBound second (by simp)
          have forward := UInt64.lt_iff_toNat_lt.mp (call_epochs run genesis second)
          rw [joined]
          omega
        · exact tailBound call member
  exact bound history.calls history.finish history.consecutive call member

/-- The last call of a history targets its checkpoint. -/
private theorem history_last {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {c : Checkpoint} (history : JustificationHistory run c) :
    ∃ call : QuorumCall run, call.target = c :=
  ⟨_, history.finish _ (List.getLast?_eq_some_getLast history.nonempty)⟩

/-- A justified or finalized field of the last state is genesis, or has a history. -/
private theorem field_history {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g) (j : Checkpoint)
    (field : j = a.state.previousJustifiedCheckpoint ∨ j = a.state.currentJustifiedCheckpoint ∨
      j = a.state.finalizedCheckpoint) :
    j = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨ Nonempty (JustificationHistory run j) := by
  rcases field with previous | current | finalized
  · exact justified_fields run genesis j (.inl previous)
  · exact justified_fields run genesis j (.inr current)
  · subst j
    rcases finalized_field run genesis with initial | ⟨call, _, rule⟩
    · exact .inl initial
    · obtain ⟨_, _, _, history, _⟩ := finalization_rule_quorums run genesis call _ rule
      exact history

/-- A justified or finalized field of a view, after a positive epoch, has a call crossing it.

The call's source is before the epoch, and its target is from the epoch up to the field.

The call is a quorum call of the run, or the test of the step of the view.

The run starts at a genesis built from deposits. -/
theorem view_field_crossing {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g)
    (view : TerminalView a) (j : Checkpoint)
    (field : j = view.state.previousJustifiedCheckpoint ∨
      j = view.state.currentJustifiedCheckpoint ∨ j = view.state.finalizedCheckpoint)
    (epoch : Nat) (positive : 0 < epoch) (reached : epoch ≤ j.epoch.toNat) :
    ∃ crossing : ViewQuorum run view, crossing.source.epoch.toNat < epoch ∧
      epoch ≤ crossing.target.epoch.toNat ∧ crossing.target.epoch.toNat ≤ j.epoch.toNat := by
  -- A checkpoint with a history of the run is crossed by one of the calls of that history.
  have historical (k : Checkpoint)
      (history : k = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        Nonempty (JustificationHistory run k))
      (reachedK : epoch ≤ k.epoch.toNat) (bound : k.epoch.toNat ≤ j.epoch.toNat) :
      ∃ crossing : ViewQuorum run view, crossing.source.epoch.toNat < epoch ∧
        epoch ≤ crossing.target.epoch.toNat ∧ crossing.target.epoch.toNat ≤ j.epoch.toNat := by
    rcases history with initial | history
    · have zero : k.epoch.toNat = 0 := by rw [initial]; rfl
      omega
    · obtain ⟨history⟩ := history
      obtain ⟨call, member, below, above⟩ := history_crossing history epoch positive reachedK
      exact ⟨.inl call, below, above,
        (history_target_bound run genesis history call member).trans bound⟩
  have old (field : j = a.state.previousJustifiedCheckpoint ∨
      j = a.state.currentJustifiedCheckpoint ∨ j = a.state.finalizedCheckpoint) :=
    historical j (field_history run genesis j field) reached (Nat.le_refl _)
  cases view with
  | realized => exact old field
  | pulled after ok =>
    change j = after.previousJustifiedCheckpoint ∨ j = after.currentJustifiedCheckpoint ∨
      j = after.finalizedCheckpoint at field
    rcases step_reads ok with ⟨_, rfl⟩ | ⟨later, ⟨reads⟩⟩
    · exact old field
    rcases field with previous | current | finalized
    · exact old (.inr (.inl
        (previous.trans (weighJustificationAndFinalization_checkpoints reads.weighed).1)))
    · rcases step_current reads with same | ⟨test, target, source⟩
      · exact old (.inr (.inl (current.trans same)))
      -- The test of the step is the last call; earlier calls are in the history of its source.
      let call := TerminalQuorum.ofTest ok later test
      have forward := UInt64.lt_iff_toNat_lt.mp (terminal_epochs run genesis call)
      have targetEq : test.target = j := target.trans current.symm
      change test.source.epoch.toNat < test.target.epoch.toNat at forward
      rw [targetEq] at forward
      by_cases crossed : epoch ≤ test.source.epoch.toNat
      · exact historical test.source
          (field_history run genesis _ (source.elim .inl (fun h => .inr (.inl h))))
          crossed (Nat.le_of_lt forward)
      · refine ⟨.inr call, ?_, ?_, ?_⟩
        · change test.source.epoch.toNat < epoch
          omega
        · change epoch ≤ test.target.epoch.toNat
          rw [targetEq]
          exact reached
        · change test.target.epoch.toNat ≤ j.epoch.toNat
          rw [targetEq]
    · rcases step_rule ok with same | rule
      · exact old (.inr (.inr (finalized.trans same)))
      -- A step finalizes one of the justified checkpoints of its state.
      rw [← finalized] at rule
      rcases rule with ⟨named, _⟩ | ⟨named, _⟩
      · exact old (.inl named)
      · exact old (.inr (.inl named))

/-- The finalized field of a view is genesis, or a quorum leaves it one or two epochs ahead.

A quorum also targets it, and with a gap of two, another quorum targets the epoch between.

Each quorum is a call of the run, or the test of the step of the view.

The run starts at a genesis built from deposits. -/
theorem view_finalized_quorums {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g)
    (view : TerminalView a) :
    let f := view.state.finalizedCheckpoint
    f = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      ∃ outgoing : ViewQuorum run view, outgoing.source = f ∧
        (outgoing.target.epoch.toNat = f.epoch.toNat + 1 ∨
          outgoing.target.epoch.toNat = f.epoch.toNat + 2) ∧
        (∃ incoming : ViewQuorum run view, incoming.target = f) ∧
        (outgoing.target.epoch.toNat = f.epoch.toNat + 2 →
          ∃ incoming : ViewQuorum run view,
            incoming.target.epoch.toNat = f.epoch.toNat + 1) := by
  dsimp only
  -- The source of an outgoing quorum is genesis, or the last call of its history targets it.
  have finish {view : TerminalView a} {f : Checkpoint} (outgoing : ViewQuorum run view)
      (source : outgoing.source = f)
      (gap : outgoing.target.epoch.toNat = f.epoch.toNat + 1 ∨
        outgoing.target.epoch.toNat = f.epoch.toNat + 2)
      (sourceHistory : outgoing.source = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        Nonempty (JustificationHistory run outgoing.source))
      (middle : outgoing.target.epoch.toNat = f.epoch.toNat + 2 →
        ∃ incoming : ViewQuorum run view,
          incoming.target.epoch.toNat = f.epoch.toNat + 1) :
      f = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        ∃ outgoing : ViewQuorum run view, outgoing.source = f ∧
          (outgoing.target.epoch.toNat = f.epoch.toNat + 1 ∨
            outgoing.target.epoch.toNat = f.epoch.toNat + 2) ∧
          (∃ incoming : ViewQuorum run view, incoming.target = f) ∧
          (outgoing.target.epoch.toNat = f.epoch.toNat + 2 →
            ∃ incoming : ViewQuorum run view,
              incoming.target.epoch.toNat = f.epoch.toNat + 1) := by
    rcases sourceHistory with initial | history
    · exact .inl (source.symm.trans initial)
    obtain ⟨history⟩ := history
    obtain ⟨incoming, target⟩ := history_last history
    exact .inr ⟨outgoing, source, gap, ⟨.inl incoming, target.trans source⟩, middle⟩
  -- A finalized field of the last state comes from a finalization rule of an epoch call.
  have old {view : TerminalView a} {f : Checkpoint} (same : f = a.state.finalizedCheckpoint) :
      f = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        ∃ outgoing : ViewQuorum run view, outgoing.source = f ∧
          (outgoing.target.epoch.toNat = f.epoch.toNat + 1 ∨
            outgoing.target.epoch.toNat = f.epoch.toNat + 2) ∧
          (∃ incoming : ViewQuorum run view, incoming.target = f) ∧
          (outgoing.target.epoch.toNat = f.epoch.toNat + 2 →
            ∃ incoming : ViewQuorum run view,
              incoming.target.epoch.toNat = f.epoch.toNat + 1) := by
    subst same
    rcases finalized_field run genesis with initial | ⟨call, _, rule⟩
    · exact .inl initial
    obtain ⟨outgoing, source, gap, _, middle⟩ :=
      finalization_rule_quorums run genesis call _ rule
    refine finish (.inl outgoing) source gap
      (quorum_source_history run genesis outgoing) fun two => ?_
    obtain ⟨m, date, history⟩ := middle two
    obtain ⟨history⟩ := history
    obtain ⟨incoming, target⟩ := history_last history
    refine ⟨.inl incoming, ?_⟩
    change incoming.target.epoch.toNat = _
    rw [target, date]
  cases view with
  | realized => exact old rfl
  | pulled after ok =>
    rcases step_reads ok with ⟨_, rfl⟩ | ⟨later, ⟨reads⟩⟩
    · exact old rfl
    rcases step_rule ok with same | rule
    · exact old same
    -- The step finalized: its quorums are tests of the step or calls of the run.
    obtain ⟨outgoing, source, gap, middle⟩ :=
      rule_quorums (Q := ViewQuorum run (.pulled after ok)) ViewQuorum.source ViewQuorum.target
        (fun m => ∃ incoming : ViewQuorum run (.pulled after ok), incoming.target = m) rule
        (fun set => by
          obtain ⟨test, source, -, date⟩ := (step_new_bits reads later).1 set
          exact ⟨.inr (.ofTest ok later test), source, date⟩)
        (fun set => by
          rcases (step_new_bits reads later).2 set with ⟨test, source, epoch⟩ | old
          · exact ⟨.inr (.ofTest ok later test), source, epoch⟩
          · obtain ⟨quorum, source, _, date⟩ := run_zero run genesis old
            exact ⟨.inl quorum, source, date⟩)
        (fun i set => by
          rcases step_bits reads later i set with ⟨test, date⟩ | ⟨k, shift, old⟩
          · exact ⟨test.target, date, .inr (.ofTest ok later test), rfl⟩
          · obtain ⟨quorum, date⟩ := run_bits run genesis k old
            exact ⟨quorum.target, by omega, .inl quorum, rfl⟩)
    refine finish outgoing source gap ?_ fun two => ?_
    · cases outgoing with
      | inl c => exact quorum_source_history run genesis c
      | inr c =>
        apply field_history run genesis
        change c.source = _ ∨ c.source = _ ∨ c.source = _
        unfold TerminalQuorum.source
        cases c.current <;> simp
    · obtain ⟨m, date, incoming, target⟩ := middle two
      exact ⟨incoming, by rw [target, date]; rfl⟩

/-- Each key that a quorum counts has a vote of the run with the source and target of the quorum.

The run starts at a genesis built from deposits, and the preset meets the parameters. -/
theorem view_quorum_attestations {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    {view : TerminalView a} (call : ViewQuorum run view) :
    ∀ key ∈ call.voters, ∃ data, run.Accepted key data ∧
      data.source = call.source ∧ data.target = call.target := by
  cases call with
  | inl c => exact quorum_attestations run parameters genesis c
  | inr c =>
    -- The step counts at the last state, whose votes are those of the whole run.
    exact counted_accepted run (inherited_participation run .nil parameters genesis) c.later
      c.current c.target c.targetEpoch c.targetRoot c.counted
      fun index data validator found voted => selected_vote_key run index data validator found voted

/-- The keys that a quorum counts hold two thirds of the active stake at its state.

The stake floors cover the run's epoch calls and the step's count up to one epoch past `high`.

The target of the quorum is at most `high`.

The run starts at a genesis built from deposits. -/
theorem view_quorum_count {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (genesis : Genesis (config := config) (checks := checks) g)
    {high : Nat} (enough : EnoughStake run high) {view : TerminalView a}
    (terminal : view.enough high) (call : ViewQuorum run view)
    (within : call.target.epoch.toNat ≤ high) :
    2 * Models.stake (effectiveWeight call.state.state) (activeKeys call.state.state) ≤
      3 * Models.stake (effectiveWeight call.state.state) call.voters := by
  cases call with
  | inl c => exact quorum_count run genesis enough c within
  | inr c =>
    obtain ⟨_, _, _, initialized⟩ := genesis
    have unique : PubkeysDistinct a.state := by
      simpa [PubkeysDistinct, validatorKeys] using
        (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized run.chainSteps).2
    rw [c.selected] at terminal
    -- The step counts at most one epoch past its target, so within the horizon of the floor.
    have horizon : (getCurrentEpoch a.state).toNat ≤ high + 1 :=
      c.currentEpoch_le.trans (Nat.add_le_add_right within 1)
    exact c.passes.stake_le unique (terminal horizon c.later)

/-- A quorum's target root is read at the end of a prefix of its run, after the epoch starts. -/
private theorem view_target_prefix {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (parameters : Parameters preset) {view : TerminalView a}
    (call : ViewQuorum run view) :
    ∃ (b : ForkedBeaconState preset) (pre : Run config checks g b) (tail : Run config checks b a),
      run = pre.append tail ∧ getBlockRoot b.state call.target.epoch = .ok call.target.root ∧
      call.target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < b.state.slot.toNat := by
  cases call with
  | inl c =>
    -- The cached root is already in the buffer of the state before the epoch call.
    obtain ⟨early, recent⟩ := call_target_window parameters c
    obtain ⟨pre, tail, same, -⟩ := c.toEpochCall.selected_prefix
    have read := c.targetRoot
    rw [getBlockRoot_processSlot c.cachedOk recent] at read
    exact ⟨c.before, pre, tail, same, read, early⟩
  | inr c => exact ⟨a, run, .nil, rfl, c.targetRoot, getBlockRoot_start_lt c.targetRoot⟩

/-- Two quorums of the runs with one target have the same headers up to the target epoch.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.

The runs start at one genesis built from deposits, and the preset meets the parameters. -/
theorem view_quorum_target_binding {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    {va : TerminalView a} {vb : TerminalView b}
    (one : ViewQuorum left va) (two : ViewQuorum right vb) (same : one.target = two.target) :
    left.checkpointPath one.target.epoch = right.checkpointPath two.target.epoch ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) := by
  obtain ⟨_, preA, tailA, splitA, readA, earlyA⟩ := view_target_prefix left parameters one
  obtain ⟨_, preB, tailB, splitB, readB, earlyB⟩ := view_target_prefix right parameters two
  rw [same] at readA earlyA ⊢
  have result := checkpoint_binding_prefixes genesis preA tailA preB tailB two.target.epoch
    two.target.root readA readB earlyA earlyB
  rwa [← splitA, ← splitB] at result

/-- Two quorum calls of the runs with one target have the same headers up to the target epoch.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.

The runs start at one genesis built from deposits, and the preset meets the parameters. -/
theorem call_target_binding {g a b : ForkedBeaconState preset}
    (left : Run config checks g a) (right : Run config checks g b)
    (parameters : Parameters preset) (genesis : Genesis (config := config) (checks := checks) g)
    (one : QuorumCall left) (two : QuorumCall right) (same : one.target = two.target) :
    left.checkpointPath one.target.epoch = right.checkpointPath two.target.epoch ∨
      HashEvidence (left.hashObjects ++ right.hashObjects) :=
  view_quorum_target_binding left right parameters genesis (va := .realized) (vb := .realized)
    (.inl one) (.inl two) same

end EthLib.Consensus.DirectSafety
