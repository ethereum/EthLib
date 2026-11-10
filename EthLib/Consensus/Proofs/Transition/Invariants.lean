module

public import EthLib.Consensus.Proofs.Transition.BuilderPayments
public import EthLib.Consensus.Proofs.Transition.EpochJustification
public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.Execution
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Proofs.Transition.ParentPayload
public import EthLib.Consensus.Proofs.Transition.Payload
public import EthLib.Consensus.Proofs.Transition.Requests
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: invariants of the state transition

A valid block keeps five properties of a state, at every fork.

The registry and the balances keep one entry for each validator.

Each validator may withdraw no earlier than it exits.

The finalized, previous justified and current justified epochs stay in increasing order.

The current justified epoch is at most the previous epoch.

So the next epoch transition cannot lower the finalized epoch.

The finalized epoch then never decreases.

Let the largest effective balances of the preset be whole numbers of increments.

Each effective balance of the registry is then a whole number of increments too.

Most steps change neither the slot, nor the checkpoints, nor the justification bits.

They also keep the genesis time, and they keep the first two properties.

They keep the fork versions and the genesis validators root, and they never shrink the registry.

Let the largest effective balances of the preset be whole numbers of increments.

These steps then keep each effective balance of the registry a whole number of increments.

While the registry stays below 2^64 validators, they also keep the key of each validator.

Each step of a block other than an attestation also keeps the buffer of block roots.

From Altair, each byte of flags after it is the byte at its position before, or zero.

The steps of an epoch after justification also keep the buffer of block roots.

They keep the latest block header, and from Gloas the latest block hash and the latest bid.

Each of them other than the rotation of the flags also keeps each byte of flags, or zeroes it.

Justification and finalization change the checkpoints, and the slot step moves the epoch on.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- Each validator may withdraw no earlier than it exits. -/
def ExitsOrdered (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data, validator.exitEpoch ≤ validator.withdrawableEpoch

/-- Each validator of the state keeps its key in the state after a step, or after an upgrade. -/
def KeysKept {post : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset post) : Prop :=
  ∀ index validator, getValidator state index = .ok validator →
    ∃ kept, getValidator after index = .ok kept ∧ kept.pubkey = validator.pubkey

theorem KeysKept.refl (state : BeaconState preset fork) : KeysKept state state :=
  fun _ validator found => ⟨validator, found, rfl⟩

theorem KeysKept.trans {middle last : Base.Fork} {first : BeaconState preset fork}
    {second : BeaconState preset middle} {third : BeaconState preset last}
    (one : KeysKept first second) (two : KeysKept second third) : KeysKept first third := by
  intro index validator found
  obtain ⟨middle, middleOk, same⟩ := one index validator found
  obtain ⟨kept, keptOk, same'⟩ := two index middle middleOk
  exact ⟨kept, keptOk, same'.trans same⟩

/-- A state with the same registry keeps each key, at any fork. -/
theorem KeysKept.of_validators {post : Base.Fork} {state : BeaconState preset fork}
    {after : BeaconState preset post} (same : after.validators.data = state.validators.data) :
    KeysKept state after := fun _ validator found =>
  ⟨validator, by unfold getValidator at found ⊢; rw [same]; exact found, rfl⟩

/-- A step that keeps the slot, the three checkpoints and the justification bits.

It also keeps the genesis time, the fork versions and the genesis validators root.

The registry never shrinks.

While the registry stays below 2^64 validators, each validator keeps its key.

With 2^64 validators or more, a 64-bit index can name another validator.

When they hold before it, it also keeps one balance for each validator.

It then also keeps each exit no later than its withdrawal.

Let the largest effective balances of the preset be whole numbers of increments.

When each effective balance is a whole number of increments before it, the same holds after it. -/
structure Frame (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  finalized : after.finalizedCheckpoint = state.finalizedCheckpoint
  previousJustified : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint
  currentJustified : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
  justificationBits : after.justificationBits = state.justificationBits
  genesisTime : after.genesisTime = state.genesisTime
  forkVersions : after.forkVersions = state.forkVersions
  genesisValidatorsRoot : after.genesisValidatorsRoot = state.genesisValidatorsRoot
  registryGrows : state.validators.data.size ≤ after.validators.data.size
  keysKept : after.validators.data.size < 2 ^ 64 → KeysKept state after
  balancesMatch : BalancesMatch state → BalancesMatch after
  exitsOrdered : ExitsOrdered state → ExitsOrdered after
  aligned : MaxEffectiveBalancesAligned preset → EffectiveBalancesAligned state →
    EffectiveBalancesAligned after

theorem Frame.refl (state : BeaconState preset fork) : Frame state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ => KeysKept.refl state, id, id,
    fun _ => id⟩

theorem Frame.trans {first second third : BeaconState preset fork} (one : Frame first second)
    (two : Frame second third) : Frame first third :=
  ⟨two.slot.trans one.slot, two.finalized.trans one.finalized,
    two.previousJustified.trans one.previousJustified,
    two.currentJustified.trans one.currentJustified,
    two.justificationBits.trans one.justificationBits, two.genesisTime.trans one.genesisTime,
    two.forkVersions.trans one.forkVersions,
    two.genesisValidatorsRoot.trans one.genesisValidatorsRoot,
    Nat.le_trans one.registryGrows two.registryGrows,
    fun small =>
      (one.keysKept (Nat.lt_of_le_of_lt two.registryGrows small)).trans (two.keysKept small),
    two.balancesMatch ∘ one.balancesMatch, two.exitsOrdered ∘ one.exitsOrdered,
    fun maxAligned => two.aligned maxAligned ∘ one.aligned maxAligned⟩

/-- A step that keeps the slot, the checkpoints, the justification bits and the registry.

It also keeps the number of balances and the genesis time.

It keeps the fork versions and the genesis validators root. -/
theorem Frame.of_validators (sizes : SameSizes state after)
    (validators : after.validators = state.validators := by rfl)
    (slot : after.slot = state.slot := by rfl)
    (finalized : after.finalizedCheckpoint = state.finalizedCheckpoint := by rfl)
    (previousJustified : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint :=
      by rfl)
    (currentJustified : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint :=
      by rfl)
    (justificationBits : after.justificationBits = state.justificationBits := by rfl)
    (genesisTime : after.genesisTime = state.genesisTime := by rfl)
    (forkVersions : after.forkVersions = state.forkVersions := by rfl)
    (genesisValidatorsRoot : after.genesisValidatorsRoot = state.genesisValidatorsRoot := by rfl) :
    Frame state after :=
  ⟨slot, finalized, previousJustified, currentJustified, justificationBits, genesisTime,
    forkVersions, genesisValidatorsRoot, by rw [validators]; exact Nat.le_refl _,
    fun _ _ validator found => ⟨validator, by rw [getValidator, validators]; exact found, rfl⟩,
    balancesMatch_of_sameSizes sizes,
    fun ordered => by rw [ExitsOrdered, validators]; exact ordered,
    fun _ holds => by rw [EffectiveBalancesAligned, validators]; exact holds⟩

/-- A fold whose every step is a frame is a frame. -/
theorem Frame.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (frame : ∀ s x s', step s x = .ok s' → Frame s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Frame state after :=
  foldlM_ok_invariant (Frame state) (fun _ _ _ before ok => before.trans (frame _ _ _ ok))
    (Frame.refl state) computed

/-- A frame that also keeps the buffer of block roots and the latest block header.

From Gloas it also keeps the latest block hash and the latest bid.

The steps of an epoch after justification form such a frame. -/
structure EpochFrame (state after : BeaconState preset fork) : Prop extends Frame state after where
  blockRoots : after.blockRoots = state.blockRoots
  latestBlockHeader : after.latestBlockHeader = state.latestBlockHeader
  latestBlockHash : after.latestBlockHash = state.latestBlockHash
  latestExecutionPayloadBid : after.latestExecutionPayloadBid = state.latestExecutionPayloadBid

theorem EpochFrame.refl (state : BeaconState preset fork) : EpochFrame state state :=
  ⟨Frame.refl state, rfl, rfl, rfl, rfl⟩

theorem EpochFrame.trans {first second third : BeaconState preset fork}
    (one : EpochFrame first second) (two : EpochFrame second third) : EpochFrame first third :=
  ⟨one.toFrame.trans two.toFrame, two.blockRoots.trans one.blockRoots,
    two.latestBlockHeader.trans one.latestBlockHeader,
    two.latestBlockHash.trans one.latestBlockHash,
    two.latestExecutionPayloadBid.trans one.latestExecutionPayloadBid⟩

/-- A step that keeps the registry, the number of balances and the fields of an epoch frame. -/
theorem EpochFrame.of_validators (sizes : SameSizes state after)
    (validators : after.validators = state.validators := by rfl)
    (slot : after.slot = state.slot := by rfl)
    (finalized : after.finalizedCheckpoint = state.finalizedCheckpoint := by rfl)
    (previousJustified : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint :=
      by rfl)
    (currentJustified : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint :=
      by rfl)
    (justificationBits : after.justificationBits = state.justificationBits := by rfl)
    (genesisTime : after.genesisTime = state.genesisTime := by rfl)
    (forkVersions : after.forkVersions = state.forkVersions := by rfl)
    (genesisValidatorsRoot : after.genesisValidatorsRoot = state.genesisValidatorsRoot := by rfl)
    (blockRoots : after.blockRoots = state.blockRoots := by rfl)
    (latestBlockHeader : after.latestBlockHeader = state.latestBlockHeader := by rfl)
    (latestBlockHash : after.latestBlockHash = state.latestBlockHash := by rfl)
    (latestExecutionPayloadBid :
      after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by rfl) :
    EpochFrame state after :=
  ⟨Frame.of_validators sizes validators slot finalized previousJustified currentJustified
    justificationBits genesisTime forkVersions genesisValidatorsRoot, blockRoots, latestBlockHeader,
    latestBlockHash, latestExecutionPayloadBid⟩

/-- From Altair, each byte of flags after a step is the byte at its position before, or zero.

This holds for the flags of the previous epoch and for those of the current epoch. -/
def FlagsKeptOrZero (state after : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (position : Nat) (flags : ParticipationFlags),
    ((after.previousEpochParticipation altair).data[position]? = some flags →
      (state.previousEpochParticipation altair).data[position]? = some flags ∨ flags = 0) ∧
    ((after.currentEpochParticipation altair).data[position]? = some flags →
      (state.currentEpochParticipation altair).data[position]? = some flags ∨ flags = 0)

theorem FlagsKeptOrZero.refl (state : BeaconState preset fork) : FlagsKeptOrZero state state :=
  fun _ _ _ => ⟨.inl, .inl⟩

theorem FlagsKeptOrZero.trans {first second third : BeaconState preset fork}
    (one : FlagsKeptOrZero first second) (two : FlagsKeptOrZero second third) :
    FlagsKeptOrZero first third := fun altair position flags =>
  ⟨fun found => ((two altair position flags).1 found).elim (one altair position flags).1 .inr,
    fun found => ((two altair position flags).2 found).elim (one altair position flags).2 .inr⟩

/-- Two states with the same lists of flags keep each byte of flags. -/
theorem FlagsKeptOrZero.of_eq
    (previous : after.previousEpochParticipation = state.previousEpochParticipation)
    (current : after.currentEpochParticipation = state.currentEpochParticipation) :
    FlagsKeptOrZero state after := fun _ _ _ => by
  rw [previous, current]
  exact ⟨.inl, .inl⟩

/-- A frame that also keeps the buffer of block roots.

From Altair, each byte of flags after it is the byte at its position before, or zero.

Each step of a block other than an attestation forms such a frame, deposits included. -/
structure BlockFrame (state after : BeaconState preset fork) : Prop extends Frame state after where
  blockRoots : after.blockRoots = state.blockRoots
  flags : FlagsKeptOrZero state after

theorem BlockFrame.refl (state : BeaconState preset fork) : BlockFrame state state :=
  ⟨Frame.refl state, rfl, FlagsKeptOrZero.refl state⟩

theorem BlockFrame.trans {first second third : BeaconState preset fork}
    (one : BlockFrame first second) (two : BlockFrame second third) : BlockFrame first third :=
  ⟨one.toFrame.trans two.toFrame, two.blockRoots.trans one.blockRoots, one.flags.trans two.flags⟩

/-- A step that keeps the registry, the number of balances and the fields of a block frame. -/
theorem BlockFrame.of_validators (sizes : SameSizes state after)
    (validators : after.validators = state.validators := by rfl)
    (slot : after.slot = state.slot := by rfl)
    (finalized : after.finalizedCheckpoint = state.finalizedCheckpoint := by rfl)
    (previousJustified : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint :=
      by rfl)
    (currentJustified : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint :=
      by rfl)
    (justificationBits : after.justificationBits = state.justificationBits := by rfl)
    (genesisTime : after.genesisTime = state.genesisTime := by rfl)
    (forkVersions : after.forkVersions = state.forkVersions := by rfl)
    (genesisValidatorsRoot : after.genesisValidatorsRoot = state.genesisValidatorsRoot := by rfl)
    (blockRoots : after.blockRoots = state.blockRoots := by rfl)
    (previousEpochParticipation :
      after.previousEpochParticipation = state.previousEpochParticipation := by rfl)
    (currentEpochParticipation :
      after.currentEpochParticipation = state.currentEpochParticipation := by rfl) :
    BlockFrame state after :=
  ⟨Frame.of_validators sizes validators slot finalized previousJustified currentJustified
    justificationBits genesisTime forkVersions genesisValidatorsRoot, blockRoots,
    FlagsKeptOrZero.of_eq previousEpochParticipation currentEpochParticipation⟩

/-- A fold whose every step is a block frame is a block frame. -/
theorem BlockFrame.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (frame : ∀ s x s', step s x = .ok s' → BlockFrame s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : BlockFrame state after :=
  foldlM_ok_invariant (BlockFrame state) (fun _ _ _ before ok => before.trans (frame _ _ _ ok))
    (BlockFrame.refl state) computed

/-- An epoch frame after which each byte of flags is the byte at its position before, or zero.

So it is also a block frame.

The mutators of a balance, of the exit queue and of a validator that keeps its key form one.

So do the steps that add a validator to the registry.

So does each step of an epoch after justification, other than the rotation of the flags. -/
structure MutatorFrame (state after : BeaconState preset fork) : Prop extends EpochFrame state after
    where
  flags : FlagsKeptOrZero state after

theorem MutatorFrame.refl (state : BeaconState preset fork) : MutatorFrame state state :=
  ⟨EpochFrame.refl state, FlagsKeptOrZero.refl state⟩

theorem MutatorFrame.trans {first second third : BeaconState preset fork}
    (one : MutatorFrame first second) (two : MutatorFrame second third) :
    MutatorFrame first third :=
  ⟨one.toEpochFrame.trans two.toEpochFrame, one.flags.trans two.flags⟩

theorem MutatorFrame.toBlockFrame (frame : MutatorFrame state after) : BlockFrame state after :=
  ⟨frame.toFrame, frame.blockRoots, frame.flags⟩

/-- A fold whose every step is a mutator frame is a mutator frame. -/
theorem MutatorFrame.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (frame : ∀ s x s', step s x = .ok s' → MutatorFrame s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : MutatorFrame state after :=
  foldlM_ok_invariant (MutatorFrame state) (fun _ _ _ before ok => before.trans (frame _ _ _ ok))
    (MutatorFrame.refl state) computed

/-! ## Mutators -/

theorem mem_of_getValidator {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator) : validator ∈ state.validators.data := by
  unfold getValidator at found
  split at found
  · rename_i read
    cases found
    exact Array.mem_of_getElem? read
  · cases found

/-- Replacing a validator by one that exits no later than it may withdraw keeps the order. -/
theorem ExitsOrdered.putValidator {index : Nat} {validator : Validator}
    (inside : index < state.validators.data.size)
    (ordered : ExitsOrdered state) (le : validator.exitEpoch ≤ validator.withdrawableEpoch) :
    ExitsOrdered (state.putValidator index inside validator) := by
  intro other member
  simp only [BeaconState.putValidator, RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
  · exact ordered other old
  · exact le

/-- Replacing a validator by one with the same key keeps each key. -/
private theorem keysKept_setValidator {index : ValidatorIndex} {validator old : Validator}
    (set : state.setValidator index validator = .ok after)
    (found : getValidator state index = .ok old) (same : validator.pubkey = old.pubkey) :
    KeysKept state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  intro other validator' found'
  by_cases here : other.toNat = index.toNat
  · refine ⟨validator, ?_, ?_⟩
    · simp [getValidator, BeaconState.putValidator, here, inside]
    · obtain rfl := UInt64.toNat_inj.mp here
      rw [found] at found'
      cases found'
      exact same
  · refine ⟨validator', ?_, rfl⟩
    simpa [getValidator, BeaconState.putValidator, Array.getElem?_set, Ne.symm here] using found'

/-- Replacing a validator forms a mutator frame, if the new one exits no later than it withdraws.

Below 2^64 validators after, the old validator at that index must have the same key.

Let the largest values of the preset and the effective balances before be aligned.

Then the new one must have an aligned effective balance. -/
private theorem frame_setValidator_of_small {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after)
    (found : after.validators.data.size < 2 ^ 64 →
      ∃ old, getValidator state index = .ok old ∧ validator.pubkey = old.pubkey)
    (le : ExitsOrdered state → validator.exitEpoch ≤ validator.withdrawableEpoch)
    (whole : MaxEffectiveBalancesAligned preset → EffectiveBalancesAligned state →
      validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0) :
    MutatorFrame state after := by
  have keys : after.validators.data.size < 2 ^ 64 → KeysKept state after := fun small => by
    obtain ⟨_, old, same⟩ := found small
    exact keysKept_setValidator set old same
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have sizes := sameSizes_putValidator state inside validator
  exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_of_eq sizes.1.symm, keys,
    balancesMatch_of_sameSizes sizes,
    fun ordered => ordered.putValidator inside (le ordered),
    fun maxAligned holds =>
      effectiveBalancesAligned_setValidator holds (whole maxAligned holds) set⟩,
    rfl, rfl, rfl, rfl⟩,
    .of_eq rfl rfl⟩

/-- Replacing a validator by one with the same key forms a mutator frame.

The new one must exit no later than it withdraws.

Let the largest values of the preset and the effective balances before be aligned.

Then the new one must have an aligned effective balance. -/
theorem frame_setValidator_of_whole {index : ValidatorIndex} {validator old : Validator}
    (set : state.setValidator index validator = .ok after)
    (found : getValidator state index = .ok old) (same : validator.pubkey = old.pubkey)
    (le : ExitsOrdered state → validator.exitEpoch ≤ validator.withdrawableEpoch)
    (whole : MaxEffectiveBalancesAligned preset → EffectiveBalancesAligned state →
      validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0) :
    MutatorFrame state after :=
  frame_setValidator_of_small set (fun _ => ⟨old, found, same⟩) le whole

/-- Replacing a validator by one with the same key and effective balance forms a mutator frame.

The new one must exit no later than it withdraws. -/
theorem frame_setValidator {index : ValidatorIndex} {validator old : Validator}
    (set : state.setValidator index validator = .ok after)
    (found : getValidator state index = .ok old) (same : validator.pubkey = old.pubkey)
    (le : ExitsOrdered state → validator.exitEpoch ≤ validator.withdrawableEpoch)
    (balance : validator.effectiveBalance = old.effectiveBalance := by rfl) :
    MutatorFrame state after :=
  frame_setValidator_of_whole set found same le fun _ holds => by
    rw [balance]
    exact holds old (mem_of_getValidator found)

theorem frame_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : MutatorFrame state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  have sizes := sameSizes_setBalance set
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact ⟨EpochFrame.of_validators sizes, .of_eq rfl rfl⟩

theorem frame_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : MutatorFrame state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  have sizes := sameSizes_setBalance set
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact ⟨EpochFrame.of_validators sizes, .of_eq rfl rfl⟩

theorem frame_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    MutatorFrame state after := by
  obtain ⟨validators, balances⟩ := exitQueue_validators computed
  unfold exitQueue at computed
  have sizes : SameSizes state after := ⟨by rw [validators], by rw [balances]⟩
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact ⟨EpochFrame.of_validators sizes validators, .of_eq rfl rfl⟩
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact MutatorFrame.refl _

/-- Starting an exit sets a withdrawable epoch no earlier than the exit epoch. -/
theorem frame_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    MutatorFrame state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ |
      ⟨_, queued, exitEpoch, withdrawableEpoch, queue, summed, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact MutatorFrame.refl _
  · have same := (exitQueue_validators queue).1
    refine (frame_exitQueue queue).trans (frame_setValidator (old := validator) set
      (by rw [getValidator, same]; exact found) rfl fun _ => ?_)
    have sum := (addChecked_ok_iff.mp summed).2
    exact UInt64.le_iff_toNat_le.mpr (by simp only at sum ⊢; omega)

theorem frame_slashings (state : BeaconState preset fork) (slashings : RootedVector Gwei _) :
    MutatorFrame state { state with slashings } :=
  ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩

/-- The last step of a slashing, which from Gloas cancels builder payments, keeps the frame. -/
theorem frame_slashValidatorLast {last : BeaconState preset fork} {index : ValidatorIndex}
    (done : (pure (if gloas : .glamsterdam ≤ fork then cancelProposerPayments last gloas index
      else last) : Except AccessorError (BeaconState preset fork)) = .ok after) :
    MutatorFrame last after := by
  simp only [pure, Except.pure, Except.ok.injEq] at done
  subst done
  split
  · exact ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  · exact MutatorFrame.refl _

/-- Slashing a validator only delays its withdrawal. -/
theorem frame_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    MutatorFrame state after := by
  obtain ⟨_, validator, _, _, _, _, _, _, _, _, _, last, exitedOk, found, -, markedOk, -, -, -,
    loweredOk, -, -, raisedOk, lastOk, done⟩ := slashValidator_ok computed
  refine (frame_initiateValidatorExit exitedOk).trans <|
    ((frame_setValidator markedOk found rfl
      fun ordered => ?_).trans
      (frame_slashings _ _)).trans <|
    (frame_decreaseBalance loweredOk).trans <| (frame_increaseBalance raisedOk).trans <|
    (frame_increaseBalance lastOk).trans (frame_slashValidatorLast
      (last := last) (after := after) (index := slashedIndex) (by subst done; rfl))
  refine UInt64.le_trans (ordered validator (mem_of_getValidator found)) ?_
  rw [UInt64.max_def]
  split
  · assumption
  · exact UInt64.le_refl _

/-! ## The steps of a block -/

theorem frame_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : BlockFrame state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : BlockFrame state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : BlockFrame state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    BlockFrame state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact (frame_slashValidator slashed).toBlockFrame

theorem frame_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    BlockFrame step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact (frame_slashValidator slashed).toBlockFrame
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ BlockFrame.refl _

theorem frame_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    BlockFrame state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => BlockFrame state step.1)
    (fun _ _ _ before ok => before.trans (frame_slashIfSlashable ok))
    (show BlockFrame state (state, false).1 from BlockFrame.refl state) folded

theorem frame_setEpochParticipation (current : Bool)
    (participation : EpochParticipation preset fork) :
    Frame state (setEpochParticipation state current participation) := by
  unfold setEpochParticipation
  split <;> exact Frame.of_validators ⟨rfl, rfl⟩

/-- From Altair, an attestation sets flags, pays the proposer, and from Gloas weighs a payment. -/
theorem frame_processAttestationAltair {attestation : Attestation preset fork}
    {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed :
      processAttestationAltair config checks state attestation altair parentSlot = .ok after) :
    Frame state after := by
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, raised, raisedOk, final⟩ := computed
  have last : Frame raised after := by
    split at final
    · rw [recordPaymentWeight_eq final]
      exact Frame.of_validators ⟨rfl, rfl⟩
    · cases final
      exact Frame.refl _
  exact (frame_setEpochParticipation _ _).trans
    ((frame_increaseBalance raisedOk).toFrame.trans last)

theorem frame_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    Frame state after := by
  unfold processAttestation at computed
  split at computed
  · exact frame_processAttestationAltair computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept
  all_goals
    obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact Frame.of_validators ⟨rfl, rfl⟩

/-- A new validator never shrinks the registry. -/
private theorem registryGrows_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    state.validators.data.size ≤ after.validators.data.size := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
    rw [setOrAppendRooted_size validatorsOk]
    split <;> omega
  split at computed
  · cases computed
    simp
  · cases computed

/-- A new validator keeps each key. -/
private theorem keysKept_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    KeysKept state after := by
  have pushed := addValidatorToRegistry_validators_eq_push computed
  intro index validator found
  refine ⟨validator, ?_, rfl⟩
  unfold getValidator at found ⊢
  split at found
  · rename_i read
    cases found
    rw [pushed, Array.getElem?_push, ite_eq_right, read]
    exact Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp read).1
  · cases found

/-- A validator from a deposit has a whole number of increments as effective balance. -/
private theorem getValidatorFromDeposit_aligned (maxAligned : MaxEffectiveBalancesAligned preset)
    (pubkey : BLSPubkey) (withdrawalCredentials : Bytes32) (amount : Gwei) :
    (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount).effectiveBalance %
      preset.EFFECTIVE_BALANCE_INCREMENT = 0 := by
  exact min_sub_mod_mod_self _ (withdrawalMaxEffectiveBalance_aligned maxAligned _)

/-- A new validator exits and withdraws at the far future epoch. -/
theorem frame_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    MutatorFrame state after := by
  have balances := balancesMatch_addValidatorToRegistry computed
  have exits : ExitsOrdered state → ExitsOrdered after := fun ordered validator member => by
    obtain ⟨_, found⟩ := Array.getElem?_of_mem member
    rcases addValidatorToRegistry_validator computed found with old | rfl
    · exact ordered validator (Array.mem_of_getElem? old)
    · exact UInt64.le_refl _
  have aligned : MaxEffectiveBalancesAligned preset → EffectiveBalancesAligned state →
      EffectiveBalancesAligned after := fun maxAligned holds validator member => by
    obtain ⟨_, found⟩ := Array.getElem?_of_mem member
    rcases addValidatorToRegistry_validator computed found with old | rfl
    · exact holds validator (Array.mem_of_getElem? old)
    · exact getValidatorFromDeposit_aligned maxAligned _ _ _
  have grows := registryGrows_addValidatorToRegistry computed
  have keys : after.validators.data.size < 2 ^ 64 → KeysKept state after :=
    fun _ => keysKept_addValidatorToRegistry computed
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, previous, previousOk, current, currentOk, _, _, rfl⟩ := computed
    -- The new validator gets a zero byte of flags, and each other byte stays.
    refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, grows, keys, balances, exits, aligned⟩,
      rfl, rfl, rfl, rfl⟩, fun _ position flags => ⟨fun found => ?_, fun found => ?_⟩⟩
    · rw [setOrAppendList_getElem? previousOk] at found
      split at found
      · exact .inr (Option.some.inj found).symm
      · exact .inl found
    · rw [setOrAppendList_getElem? currentOk] at found
      split at found
      · exact .inr (Option.some.inj found).symm
      · exact .inl found
  split at computed
  · cases computed
    exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, grows, keys, balances, exits, aligned⟩,
      rfl, rfl, rfl, rfl⟩, .of_eq rfl rfl⟩
  · cases computed

/-- The laws that carry a reflexive, transitive relation through most steps of an epoch.

They leave out justification, the builder payments and the rotation of the flags.

A validator write must relate its states only when it keeps the key.

It must also exit no later than it withdraws, when the exits of the state are ordered.

Its effective balance must also be a whole number of increments, when the balances are aligned.

The other laws cover balance changes, exits, new validators and replacements of one field. -/
structure EpochFrameLaws (R : BeaconState preset fork → BeaconState preset fork → Prop) : Prop where
  refl : ∀ state, R state state
  trans : ∀ {first second third}, R first second → R second third → R first third
  setValidator : ∀ {state after : BeaconState preset fork} {index : ValidatorIndex}
    {validator old : Validator},
    state.setValidator index validator = .ok after → getValidator state index = .ok old →
    validator.pubkey = old.pubkey →
    (ExitsOrdered state → validator.exitEpoch ≤ validator.withdrawableEpoch) →
    (MaxEffectiveBalancesAligned preset → EffectiveBalancesAligned state →
      validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0) → R state after
  increaseBalance : ∀ {state after index delta},
    increaseBalance state index delta = .ok after → R state after
  decreaseBalance : ∀ {state after index delta},
    decreaseBalance state index delta = .ok after → R state after
  initiateValidatorExit : ∀ {config state after index},
    initiateValidatorExit config state index = .ok after → R state after
  addValidatorToRegistry : ∀ {state after pubkey withdrawalCredentials amount},
    addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after → R state after
  eth1DataVotes : ∀ state votes, R state { state with eth1DataVotes := votes }
  inactivityScores : ∀ state scores, R state { state with inactivityScores := scores }
  slashings : ∀ state slashings, R state { state with slashings }
  randaoMixes : ∀ state randaoMixes, R state { state with randaoMixes }
  historicalRoots : ∀ state historicalRoots, R state { state with historicalRoots }
  historicalSummaries : ∀ state summaries, R state { state with historicalSummaries := summaries }
  participationRecords : ∀ state, R state
    { state with previousEpochAttestations := state.currentEpochAttestations
                 currentEpochAttestations := fun _ => ⟨#[], by simp⟩ }
  pendingDeposits : ∀ state deposits carried, R state
    { state with pendingDeposits := deposits, depositBalanceToConsume := carried }
  pendingConsolidations : ∀ state consolidations,
    R state { state with pendingConsolidations := consolidations }
  syncCommittees : ∀ state current next,
    R state { state with currentSyncCommittee := current, nextSyncCommittee := next }
  proposerLookahead : ∀ state lookahead, R state { state with proposerLookahead := lookahead }
  ptcWindow : ∀ state window, R state { state with ptcWindow := window }

/-- The mutator frame satisfies the laws of the epoch steps. -/
theorem mutatorEpochFrameLaws : EpochFrameLaws (@MutatorFrame preset fork) where
  refl := MutatorFrame.refl
  trans := MutatorFrame.trans
  setValidator := frame_setValidator_of_whole
  increaseBalance := frame_increaseBalance
  decreaseBalance := frame_decreaseBalance
  initiateValidatorExit := frame_initiateValidatorExit
  addValidatorToRegistry := frame_addValidatorToRegistry
  eth1DataVotes _ _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  inactivityScores _ _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  slashings := frame_slashings
  randaoMixes _ _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  historicalRoots _ _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  historicalSummaries _ _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  participationRecords _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  pendingDeposits _ _ _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  pendingConsolidations _ _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  syncCommittees _ _ _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  proposerLookahead _ _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
  ptcWindow _ _ := ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩

namespace EpochFrameLaws

variable {R : BeaconState preset fork → BeaconState preset fork → Prop}
  (laws : EpochFrameLaws R)

include laws

/-- A fold relates its start to its result when each step relates its input to its output. -/
theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (frame : ∀ s x s', step s x = .ok s' → R s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : R state after :=
  foldlM_ok_invariant (R state) (fun _ _ _ before ok => laws.trans before (frame _ _ _ ok))
    (laws.refl state) computed

/-- A validator write that keeps the key and the effective balance follows the relation.

It must also exit no later than it withdraws, when the exits of the state are ordered. -/
theorem setValidator_of_sameBalance {index : ValidatorIndex} {validator old : Validator}
    (set : state.setValidator index validator = .ok after)
    (found : getValidator state index = .ok old) (same : validator.pubkey = old.pubkey)
    (le : ExitsOrdered state → validator.exitEpoch ≤ validator.withdrawableEpoch)
    (balance : validator.effectiveBalance = old.effectiveBalance := by rfl) : R state after :=
  laws.setValidator set found same le fun _ holds => by
    rw [balance]
    exact holds old (mem_of_getValidator found)

theorem applyPendingDeposit {deposit : PendingDeposit}
    (computed : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    R state after := by
  unfold Consensus.applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact laws.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact laws.addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ laws.refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact laws.increaseBalance computed

end EpochFrameLaws

theorem frame_applyDepositElectra {electra : .pectra ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials
      amount signature = .ok after) :
    MutatorFrame state after := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, added, pushed⟩ := computed
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact (frame_addValidatorToRegistry added).trans
        ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩
    · cases computed
      exact MutatorFrame.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    exact ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩

theorem frame_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.applyPendingDeposit computed

theorem frame_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    MutatorFrame state after := by
  unfold applyDeposit at computed
  split at computed
  · exact frame_applyDepositElectra computed
  · exact frame_applyPendingDeposit computed

theorem frame_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    BlockFrame state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (BlockFrame.of_validators (state := state)
    (after := { state with eth1DepositIndex := fun _ => next })
    ⟨rfl, rfl⟩).trans (frame_applyDeposit applied).toBlockFrame

theorem frame_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    BlockFrame state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact (frame_initiateValidatorExit exited).toBlockFrame

/-! ## Requests of the execution layer -/

theorem frame_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    BlockFrame state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    BlockFrame state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    BlockFrame state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    BlockFrame state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (frame_computeExitEpochAndUpdateChurn churned).trans
      (BlockFrame.of_validators ⟨rfl, rfl⟩)
  · cases computed
    exact BlockFrame.refl _

theorem frame_processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    BlockFrame state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BlockFrame.refl _)
    | exact (frame_initiateValidatorExit (liftAccessor_ok.mp computed)).toBlockFrame
    | exact frame_requestPartialWithdrawal computed

theorem frame_queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    BlockFrame state after := by
  have sizes := sameSizes_queueExcessActiveBalance computed
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact BlockFrame.of_validators sizes
  · cases computed
    exact BlockFrame.refl _

/-- Compounding credentials keep the epochs, and the excess balance moves to the deposit queue. -/
theorem frame_switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    BlockFrame state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (frame_setValidator set found rfl fun ordered =>
    ordered validator (mem_of_getValidator found)).toBlockFrame.trans
    (frame_queueExcessActiveBalance queued)

/-- The source of a consolidation exits, and may withdraw a checked delay later.

The source must be the validator at its index, so that it keeps its key. -/
theorem frame_queueConsolidation {electra : .pectra ≤ fork} {sourceIndex : ValidatorIndex}
    {source : Validator} {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    BlockFrame state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, ⟨_, sum⟩, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  obtain ⟨inside, rfl⟩ := Array.getElem?_eq_some_iff.mp found
  have le : exitEpoch ≤ withdrawable :=
    UInt64.le_iff_toNat_le.mpr (by simp only at sum ⊢; omega)
  have validators : churnedState.validators = state.validators :=
    (computeConsolidationEpochAndUpdateChurn_earliest churned).2.1
  refine (frame_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (frame_setValidator_of_whole set (old := state.validators.data[sourceIndex.toNat]) ?_ rfl
      (fun _ => le) fun _ holds => holds state.validators.data[sourceIndex.toNat] (by
        rw [validators]; exact Array.getElem_mem inside)
      ).toBlockFrame.trans (BlockFrame.of_validators ⟨rfl, rfl⟩)
  rw [getValidator, validators, Array.getElem?_eq_getElem inside]

theorem frame_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    BlockFrame state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BlockFrame.refl _)
    | exact frame_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact frame_queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption)) computed

theorem frame_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    BlockFrame state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (BlockFrame.foldlM (fun _ _ _ ok => frame_processDepositRequest ok) depositsOk).trans <|
    (BlockFrame.foldlM (fun _ _ _ ok => frame_processWithdrawalRequest ok) withdrawalsOk).trans <|
    BlockFrame.foldlM (fun _ _ _ ok => frame_processConsolidationRequest ok) consolidationsOk

/-! ## Withdrawals -/

theorem frame_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : BlockFrame state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact BlockFrame.of_validators ⟨rfl, rfl⟩
  · exact (frame_decreaseBalance computed).toBlockFrame

theorem frame_updateNextWithdrawalIndex {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalIndex state withdrawals = .ok after) :
    BlockFrame state after := by
  unfold updateNextWithdrawalIndex at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact BlockFrame.of_validators ⟨rfl, rfl⟩
  · cases computed
    exact BlockFrame.refl _

theorem frame_updateNextWithdrawalValidatorIndex {capella : .shapella ≤ fork}
    {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalValidatorIndex state capella withdrawals = .ok after) :
    BlockFrame state after := by
  unfold updateNextWithdrawalValidatorIndex at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · cases computed
  · cases computed
    exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_updateNextWithdrawalBuilderIndex {gloas : .glamsterdam ≤ fork} {count : Nat}
    (computed : updateNextWithdrawalBuilderIndex state gloas count = .ok after) :
    BlockFrame state after := by
  unfold updateNextWithdrawalBuilderIndex at computed
  dsimp only at computed
  split at computed
  · cases computed
    exact BlockFrame.of_validators ⟨rfl, rfl⟩
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    BlockFrame state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : BlockFrame state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact BlockFrame.foldlM (fun _ _ _ ok => frame_applyWithdrawal ok) appliedOk
  have queued : ∀ kept : BeaconState preset fork,
      BlockFrame kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact BlockFrame.of_validators ⟨rfl, rfl⟩
  have partials : ∀ kept : BeaconState preset fork,
      BlockFrame kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact BlockFrame.of_validators ⟨rfl, rfl⟩
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → BlockFrame kept finished := by
    intro kept ok
    split at ok
    · exact frame_updateNextWithdrawalBuilderIndex ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ BlockFrame.refl _
  exact one.trans <| (frame_updateNextWithdrawalIndex indexedOk).trans <| (queued _).trans <|
    (partials _).trans <| (swept _ sweptOk).trans (frame_updateNextWithdrawalValidatorIndex last)

theorem frame_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : BlockFrame state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact frame_applyExpectedWithdrawals applied
    · cases computed
      exact BlockFrame.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact frame_applyExpectedWithdrawals applied

theorem frame_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    BlockFrame state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact (frame_setValidator set found rfl fun ordered =>
    ordered validator (mem_of_getValidator found)).toBlockFrame

/-! ## The parent payload and the execution part of a block -/

theorem frame_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    BlockFrame state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    BlockFrame state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BlockFrame.of_validators ⟨rfl, rfl⟩)

theorem frame_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    BlockFrame state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact BlockFrame.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : BlockFrame state after := by
  rw [settleParentPayment_eq computed]
  exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    BlockFrame state after := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, _, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk, buildersOk,
      exitsOk, -, rfl⟩
  · exact BlockFrame.refl _
  · exact (frame_settleParentPayment settledOk).trans <|
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processDepositRequest ok) depositsOk).trans <|
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processWithdrawalRequest ok) withdrawalsOk).trans <|
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processConsolidationRequest ok)
        consolidationsOk).trans <|
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processBuilderDepositRequest ok)
        buildersOk).trans <|
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processBuilderExitRequest ok) exitsOk).trans
        (BlockFrame.of_validators ⟨rfl, rfl⟩)

theorem frame_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    BlockFrame state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact BlockFrame.of_validators ⟨rfl, rfl⟩
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact BlockFrame.of_validators ⟨rfl, rfl⟩

theorem frame_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    BlockFrame state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (frame_processWithdrawals withdrawnOk).trans (frame_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (frame_processWithdrawals withdrawnOk).trans (frame_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact frame_processExecutionPayload computed
    · cases computed
      exact BlockFrame.refl _

/-! ## The sync aggregate -/

theorem frame_applySyncReward {reward proposerReward : Gwei}
    {proposer : Except AccessorError ValidatorIndex} {member : ValidatorIndex × Bool}
    (computed : applySyncReward reward proposerReward proposer state member = .ok after) :
    BlockFrame state after := by
  unfold applySyncReward at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, raised, _, _, paid⟩ := computed
    exact ((frame_increaseBalance raised).trans (frame_increaseBalance paid)).toBlockFrame
  · exact (frame_decreaseBalance (liftAccessor_ok.mp computed)).toBlockFrame

theorem frame_processSyncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    BlockFrame state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  exact BlockFrame.foldlM (fun _ _ _ ok => frame_applySyncReward ok) folded

/-! ## Blocks -/

/-- The operations of a block are a step, its attestations in order, then a block frame.

The step holds of the two kinds of slashings, which run before the attestations.

It must hold of each state to itself, and chain. -/
theorem processOperations_split_of
    (step : BeaconState preset fork → BeaconState preset fork → Prop)
    (refl : ∀ state, step state state)
    (trans : ∀ {first second third}, step first second → step second third → step first third)
    (proposer : ∀ {state after} {slashing : ProposerSlashing},
      processProposerSlashing config checks state slashing = .ok after → step state after)
    (attester : ∀ {state after} {slashing : AttesterSlashing preset fork},
      processAttesterSlashing config checks state slashing = .ok after → step state after)
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ∃ first last, step state first ∧
      body.attestations.data.toList.foldlM (processAttestation config checks · parentSlot ·)
        first = .ok last ∧ BlockFrame last after := by
  have slashed : ∀ {middle : BeaconState preset fork}
      {proposers : List ProposerSlashing} {attesters : List (AttesterSlashing preset fork)},
      proposers.foldlM (processProposerSlashing config checks) state = .ok middle →
      ∀ {first}, attesters.foldlM (processAttesterSlashing config checks) middle = .ok first →
        step state first := fun proposersOk _ attestersOk =>
    trans (foldlM_ok_steps step refl trans (fun _ _ _ ok => proposer ok) proposersOk).1
      (foldlM_ok_steps step refl trans (fun _ _ _ ok => attester ok) attestersOk).1
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    refine ⟨_, _, slashed proposersOk attestersOk, attestedOk, ?_⟩
    exact (BlockFrame.foldlM (fun _ _ _ ok => frame_processVoluntaryExit ok) exitsOk).trans <|
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processBlsToExecutionChange ok) changesOk).trans <|
      BlockFrame.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact BlockFrame.refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : BlockFrame exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact BlockFrame.foldlM (fun _ _ _ ok => frame_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ BlockFrame.refl _
  have requests : BlockFrame changed after := by
    split at requestsOk
    · exact frame_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ BlockFrame.refl _
  refine ⟨_, _, slashed proposersOk attestersOk, attestedOk, ?_⟩
  exact (BlockFrame.foldlM (fun _ _ _ ok => frame_processDeposit ok) depositedOk).trans <|
    (BlockFrame.foldlM (fun _ _ _ ok => frame_processVoluntaryExit ok) exitsOk).trans <|
    changes.trans requests

/-- The operations of a block are a block frame, its attestations in order, then a block frame. -/
theorem processOperations_split {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ∃ first last, BlockFrame state first ∧
      body.attestations.data.toList.foldlM (processAttestation config checks · parentSlot ·)
        first = .ok last ∧ BlockFrame last after :=
  processOperations_split_of BlockFrame BlockFrame.refl BlockFrame.trans
    frame_processProposerSlashing frame_processAttesterSlashing computed

/-- A block is a step, its operations, then a block frame.

The step holds of each part of the block that runs before its operations.

Those are the header and the RANDAO reveal, at every fork.

They are also the payload of the parent from Gloas and the execution part from Bellatrix.

The last is the vote on the deposit contract, before Heze.

It must hold of each state to itself, and chain.

The operations read the parent slot from the latest block header before the block. -/
theorem processBlock_split_of
    (step : BeaconState preset fork → BeaconState preset fork → Prop)
    (refl : ∀ state, step state state)
    (trans : ∀ {first second third}, step first second → step second third → step first third)
    {block : BeaconBlock preset fork}
    (paid : ∀ {state after} (gloas : .glamsterdam ≤ fork),
      processParentExecutionPayload config checks state gloas block.body = .ok after →
        step state after)
    (header : ∀ {state after}, processBlockHeader state block = .ok after → step state after)
    (execution : ∀ {state after} (bellatrix : .bellatrix ≤ fork),
      processBlockExecution config checks engine state block.body bellatrix = .ok after →
        step state after)
    (randao : ∀ {state after},
      processRandao config checks state block.body = .ok after → step state after)
    (eth1 : ∀ {state after} (before : fork < .hegota),
      processEth1Data before state block.body = .ok after → step state after)
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ first last, step state first ∧
      processOperations config checks first block.body state.latestBlockHeader.slot = .ok last ∧
      BlockFrame last after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid', paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidStep : step state paid' := by
      split at paidOk
      · exact paid _ paidOk
      · cases paidOk
        exact refl _
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedStep : step headed executed := by
      split at executedOk
      · exact execution _ executedOk
      · cases executedOk
        exact refl _
    -- Heze drops the vote on the deposit contract.
    have votedStep : step revealed voted := by
      split at votedOk
      · exact eth1 _ votedOk
      · cases votedOk
        exact refl _
    exact ⟨_, _, trans paidStep <| trans (header headedOk) <|
      trans executedStep <| trans (randao revealedOk) votedStep, operatedOk,
      frame_processSyncAggregate synced⟩
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact ⟨_, _, trans (header headerOk) <| trans (randao randaoOk) <|
    eth1 _ eth1Ok, operationsOk, BlockFrame.refl _⟩

/-- A block is a block frame, its operations, then a block frame.

The operations read the parent slot from the latest block header before the block. -/
theorem processBlock_split {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ first last, BlockFrame state first ∧
      processOperations config checks first block.body state.latestBlockHeader.slot = .ok last ∧
      BlockFrame last after :=
  processBlock_split_of BlockFrame BlockFrame.refl BlockFrame.trans
    (fun _ ok => frame_processParentExecutionPayload ok) frame_processBlockHeader
    (fun _ ok => frame_processBlockExecution ok) frame_processRandao
    (fun _ ok => frame_processEth1Data ok) computed

/-- The operations of a block form a frame. -/
theorem frame_processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    Frame state after := by
  obtain ⟨_, _, first, attested, last⟩ := processOperations_split computed
  exact first.toFrame.trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processAttestation ok) attested).trans last.toFrame

/-- A block forms a frame. -/
theorem frame_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) : Frame state after := by
  obtain ⟨_, _, first, operated, last⟩ := processBlock_split computed
  exact first.toFrame.trans <| (frame_processOperations operated).trans last.toFrame

/-! ## Relations through the steps of an epoch -/

/-- Joining the activation queue changes neither the exit nor the withdrawable epoch. -/
theorem queueForActivation_epochs {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    queued.exitEpoch = validator.exitEpoch ∧
      queued.withdrawableEpoch = validator.withdrawableEpoch := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ ⟨rfl, rfl⟩

/-- Joining the activation queue keeps the effective balance. -/
private theorem queueForActivation_effectiveBalance {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    queued.effectiveBalance = validator.effectiveBalance := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ rfl

/-- Joining the activation queue keeps the key. -/
private theorem queueForActivation_pubkey {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    queued.pubkey = validator.pubkey := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ rfl

namespace EpochFrameLaws

variable {R : BeaconState preset fork → BeaconState preset fork → Prop}
  (laws : EpochFrameLaws R)

include laws

theorem applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : Consensus.applyDeltas rewards penalties state index = .ok after) :
    R state after := by
  simp only [Consensus.applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, raised, lowered⟩ := computed
  exact laws.trans (laws.increaseBalance raised) (laws.decreaseBalance lowered)

theorem applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : Consensus.applyAllDeltas state deltas = .ok after) : R state after :=
  laws.foldlM (fun _ _ _ ok => laws.applyDeltas ok) computed

theorem processRewardsAndPenalties
    (computed : Consensus.processRewardsAndPenalties config state = .ok after) :
    R state after := by
  unfold Consensus.processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ laws.refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact laws.foldlM (fun _ _ _ ok => laws.applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact laws.applyAllDeltas applied

theorem updateRegistryEntry {index : Nat}
    (computed : Consensus.updateRegistryEntry config state index = .ok after) : R state after := by
  simp only [Consensus.updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  obtain ⟨exitSame, withdrawableSame⟩ := queueForActivation_epochs queuedOk
  have set : R state marked := laws.setValidator_of_sameBalance markedOk found
    (queueForActivation_pubkey queuedOk) fun ordered => by
      rw [exitSame, withdrawableSame]
      exact ordered validator (mem_of_getValidator found)
    (balance := queueForActivation_effectiveBalance queuedOk)
  split at computed
  · rw [liftAccessor_ok] at computed
    exact laws.trans set (laws.initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

theorem activateValidator {index : ValidatorIndex}
    (computed : Consensus.activateValidator state index = .ok after) : R state after := by
  simp only [Consensus.activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, set⟩ := computed
  exact laws.setValidator_of_sameBalance set found rfl fun ordered =>
    ordered validator (mem_of_getValidator found)

theorem updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (computed : Consensus.updateRegistryEntryElectra config activationEpoch state index =
      .ok after) :
    R state after := by
  simp only [Consensus.updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, computed⟩ := computed
  have kept : ExitsOrdered state → validator.exitEpoch ≤ validator.withdrawableEpoch :=
    fun ordered => ordered validator (mem_of_getValidator found)
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact laws.setValidator_of_sameBalance set found rfl kept
  split at computed
  · rw [liftAccessor_ok] at computed
    exact laws.initiateValidatorExit computed
  split at computed
  · rw [liftAccessor_ok] at computed
    exact laws.setValidator_of_sameBalance computed found rfl kept
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ laws.refl _

theorem processRegistryUpdates
    (computed : Consensus.processRegistryUpdates config state = .ok after) : R state after := by
  unfold Consensus.processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact laws.foldlM (fun _ _ _ ok => laws.updateRegistryEntryElectra ok) computed
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  exact laws.trans (laws.foldlM (fun _ _ _ ok => laws.updateRegistryEntry ok) updatedOk)
    (laws.foldlM (fun _ _ _ ok => laws.activateValidator ok) activated)

theorem applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (computed : Consensus.applySlashingPenalty state total adjusted index = .ok after) :
    R state after := by
  simp only [Consensus.applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact laws.decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ laws.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ laws.refl _

theorem applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (computed : Consensus.applySlashingPenaltyElectra state perIncrement index = .ok after) :
    R state after := by
  simp only [Consensus.applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, lowered⟩ := computed
      exact laws.decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ laws.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ laws.refl _

theorem processSlashings (computed : Consensus.processSlashings state = .ok after) :
    R state after := by
  unfold Consensus.processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact laws.foldlM (fun _ _ _ ok => laws.applySlashingPenaltyElectra ok) applied
  · exact laws.foldlM (fun _ _ _ ok => laws.applySlashingPenalty ok) computed

theorem processEth1DataReset {before : fork < .hegota}
    (computed : Consensus.processEth1DataReset before state = .ok after) : R state after := by
  simp only [Consensus.processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact (laws.eth1DataVotes _ _)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ laws.refl _

theorem updateEffectiveBalance {index : Nat}
    (computed : Consensus.updateEffectiveBalance state index = .ok after) : R state after := by
  simp only [Consensus.updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, _, updated, set⟩ := computed
  refine laws.setValidator set found rfl
    (fun ordered => ordered validator (mem_of_getValidator found)) fun maxAligned holds => ?_
  exact updatedEffectiveBalance_aligned (withdrawalMaxEffectiveBalance_aligned maxAligned validator)
    (holds validator (mem_of_getValidator found)) updated

theorem processEffectiveBalanceUpdates
    (computed : Consensus.processEffectiveBalanceUpdates state = .ok after) : R state after := by
  unfold Consensus.processEffectiveBalanceUpdates at computed
  exact laws.foldlM (fun _ _ _ ok => laws.updateEffectiveBalance ok) computed

theorem processSlashingsReset (computed : Consensus.processSlashingsReset state = .ok after) :
    R state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq computed
  exact laws.slashings _ _

theorem processRandaoMixesReset (computed : Consensus.processRandaoMixesReset state = .ok after) :
    R state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq computed
  exact (laws.randaoMixes _ _)

theorem processHistoricalRootsUpdate
    (computed : Consensus.processHistoricalRootsUpdate state = .ok after) : R state after := by
  unfold Consensus.processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact (laws.historicalRoots _ _)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ laws.refl _

theorem processParticipationRecordUpdates
    (computed : Consensus.processParticipationRecordUpdates state = .ok after) :
    R state after := by
  unfold Consensus.processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact (laws.participationRecords _)

theorem processInactivityUpdates {altair : .altair ≤ fork}
    (computed : Consensus.processInactivityUpdates config state altair = .ok after) :
    R state after := by
  unfold Consensus.processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ laws.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact (laws.inactivityScores _ _)

theorem passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      Consensus.passPendingDeposits config checks stop nextEpoch available state processed count
        postponed deposits = .ok pass →
      R state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [Consensus.passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact laws.refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold Consensus.passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact laws.refl _
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact laws.trans (laws.applyPendingDeposit credited)
        (passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact laws.refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact laws.trans (laws.applyPendingDeposit credited)
      (passPendingDeposits (deposits := rest) ‹_›)

theorem processPendingDeposits {electra : .pectra ≤ fork}
    (computed : Consensus.processPendingDeposits config checks state electra = .ok after) :
    R state after := by
  unfold Consensus.processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals
    exact laws.trans (laws.passPendingDeposits ‹_›)
      (laws.pendingDeposits _ _ _)

theorem passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      Consensus.passPendingConsolidations nextEpoch state consolidations = .ok result →
      R state result.1
  | [], _, _, computed => by
    simp only [Consensus.passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact laws.refl _
  | consolidation :: rest, state, result, computed => by
    simp only [Consensus.passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact laws.refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact laws.trans (laws.trans (laws.decreaseBalance loweredOk)
      (laws.increaseBalance raisedOk))
      (passPendingConsolidations (result := (passed, read)) passedOk)

theorem processPendingConsolidations {electra : .pectra ≤ fork}
    (computed : Consensus.processPendingConsolidations state electra = .ok after) :
    R state after := by
  unfold Consensus.processPendingConsolidations at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals
    exact laws.trans (laws.passPendingConsolidations ‹_›)
      (laws.pendingConsolidations _ _)

theorem processPendingBalances
    (computed : Consensus.processPendingBalances config checks state = .ok after) :
    R state after := by
  unfold Consensus.processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    exact laws.trans (laws.processPendingDeposits deposited)
      (laws.processPendingConsolidations consolidated)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ laws.refl _

theorem processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (computed : Consensus.processHistoricalSummariesUpdate state capella = .ok after) :
    R state after := by
  unfold Consensus.processHistoricalSummariesUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals first
    | exact laws.refl _
    | exact (laws.historicalSummaries _ _)

theorem processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (computed : Consensus.processSyncCommitteeUpdates state altair = .ok after) :
    R state after := by
  unfold Consensus.processSyncCommitteeUpdates at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals first
    | exact laws.refl _
    | exact (laws.syncCommittees _ _ _)

theorem processProposerLookahead {fulu : .fusaka ≤ fork}
    (computed : Consensus.processProposerLookahead state fulu = .ok after) : R state after := by
  simp only [Consensus.processProposerLookahead, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact (laws.proposerLookahead _ _)

theorem processPtcWindow {gloas : .glamsterdam ≤ fork}
    (computed : Consensus.processPtcWindow state gloas = .ok after) : R state after := by
  simp only [Consensus.processPtcWindow, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact (laws.ptcWindow _ _)

/-- From Altair, the epoch transition is justification, then steps in the relation.

The builder payments follow, which change nothing before Gloas, then more steps in the relation.

The rotation of the participation flags comes next, then the last steps in the relation. -/
theorem processEpochAltair_split {altair : .altair ≤ fork}
    (computed : Consensus.processEpochAltair config checks state altair = .ok after) :
    ∃ justified pending paid rooted,
      processJustificationAndFinalization state = .ok justified ∧ R justified pending ∧
      (if gloas : .glamsterdam ≤ fork then
        liftAccessor (processBuilderPendingPayments pending gloas) else pure pending) =
          (Except.ok paid : Except TransitionError _) ∧
      R paid rooted ∧ R (processParticipationFlagUpdates rooted altair) after := by
  unfold Consensus.processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetFrame : R slashed reset := by
    split at resetOk
    · exact laws.processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ laws.refl _
  have head : R justified pending :=
    laws.trans (laws.processInactivityUpdates scoredOk) <|
    laws.trans (laws.processRewardsAndPenalties rewardedOk) <|
    laws.trans (laws.processRegistryUpdates registeredOk) <|
    laws.trans (laws.processSlashings slashedOk) <|
    laws.trans resetFrame (laws.processPendingBalances pendingOk)
  have middle : R paid mixed :=
    laws.trans (laws.processEffectiveBalanceUpdates balancedOk) <|
    laws.trans (laws.processSlashingsReset clearedOk) (laws.processRandaoMixesReset mixedOk)
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  all_goals
    have lookedFrame : R synced looked := by
      split at lookedOk
      · exact laws.processProposerLookahead (liftAccessor_ok.mp lookedOk)
      · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
        exact lookedOk ▸ laws.refl _
    have windowedFrame : R looked after := by
      split at windowed
      · exact laws.processPtcWindow (liftAccessor_ok.mp windowed)
      · simp only [pure, Except.pure, Except.ok.injEq] at windowed
        exact windowed ▸ laws.refl _
    refine ⟨justified, pending, paid, rooted, justifiedOk, head, paidOk, ?_, ?_⟩
    · first
      | exact laws.trans middle (laws.processHistoricalSummariesUpdate rootedOk)
      | exact laws.trans middle (laws.processHistoricalRootsUpdate rootedOk)
    · exact laws.trans (laws.processSyncCommitteeUpdates syncedOk)
        (laws.trans lookedFrame windowedFrame)

end EpochFrameLaws

/-! ## The steps of an epoch -/

theorem frame_applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.applyDeltas computed

theorem frame_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : MutatorFrame state after :=
  mutatorEpochFrameLaws.applyAllDeltas computed

theorem frame_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processRewardsAndPenalties computed

theorem frame_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) : MutatorFrame state after :=
  mutatorEpochFrameLaws.updateRegistryEntry computed

theorem frame_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : MutatorFrame state after :=
  mutatorEpochFrameLaws.activateValidator computed

theorem frame_updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.updateRegistryEntryElectra computed

theorem frame_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : MutatorFrame state after :=
  mutatorEpochFrameLaws.processRegistryUpdates computed

theorem frame_applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.applySlashingPenalty computed

theorem frame_applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (computed : applySlashingPenaltyElectra state perIncrement index = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.applySlashingPenaltyElectra computed

theorem frame_processSlashings (computed : processSlashings state = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processSlashings computed

theorem frame_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) : MutatorFrame state after :=
  mutatorEpochFrameLaws.processEth1DataReset computed

theorem frame_updateEffectiveBalance {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) : MutatorFrame state after :=
  mutatorEpochFrameLaws.updateEffectiveBalance computed

theorem frame_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : MutatorFrame state after :=
  mutatorEpochFrameLaws.processEffectiveBalanceUpdates computed

theorem frame_processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processSlashingsReset computed

theorem frame_processRandaoMixesReset (computed : processRandaoMixesReset state = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processRandaoMixesReset computed

theorem frame_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : MutatorFrame state after :=
  mutatorEpochFrameLaws.processHistoricalRootsUpdate computed

theorem frame_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processParticipationRecordUpdates computed

theorem frame_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processInactivityUpdates computed

theorem frame_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      MutatorFrame state pass.1.state := by
  intro deposits state processed count postponed pass computed
  exact mutatorEpochFrameLaws.passPendingDeposits computed

theorem frame_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processPendingDeposits computed

theorem frame_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      MutatorFrame state result.1 := by
  intro consolidations state result computed
  exact mutatorEpochFrameLaws.passPendingConsolidations computed

theorem frame_processPendingConsolidations {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processPendingConsolidations computed

theorem frame_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processPendingBalances computed

theorem frame_processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (computed : processHistoricalSummariesUpdate state capella = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processHistoricalSummariesUpdate computed

theorem frame_processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (computed : processSyncCommitteeUpdates state altair = .ok after) :
    MutatorFrame state after :=
  mutatorEpochFrameLaws.processSyncCommitteeUpdates computed

theorem frame_processProposerLookahead {fulu : .fusaka ≤ fork}
    (computed : processProposerLookahead state fulu = .ok after) : MutatorFrame state after :=
  mutatorEpochFrameLaws.processProposerLookahead computed

theorem frame_processPtcWindow {gloas : .glamsterdam ≤ fork}
    (computed : processPtcWindow state gloas = .ok after) : MutatorFrame state after :=
  mutatorEpochFrameLaws.processPtcWindow computed

theorem frame_processBuilderPendingPayments {gloas : .glamsterdam ≤ fork}
    (computed : processBuilderPendingPayments state gloas = .ok after) :
    MutatorFrame state after := by
  rw [processBuilderPendingPayments_eq computed]
  exact ⟨EpochFrame.of_validators ⟨rfl, rfl⟩, .of_eq rfl rfl⟩

theorem frame_processParticipationFlagUpdates (state : BeaconState preset fork)
    (altair : .altair ≤ fork) : EpochFrame state (processParticipationFlagUpdates state altair) :=
  EpochFrame.of_validators ⟨rfl, rfl⟩

/-- From Altair, the epoch transition is justification, then a mutator frame.

The rotation of the participation flags follows, then another mutator frame. -/
theorem processEpochAltair_split {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    ∃ justified rooted, processJustificationAndFinalization state = .ok justified ∧
      MutatorFrame justified rooted ∧
      MutatorFrame (processParticipationFlagUpdates rooted altair) after := by
  obtain ⟨justified, pending, paid, rooted, justifiedOk, head, paidOk, middle, tail⟩ :=
    mutatorEpochFrameLaws.processEpochAltair_split computed
  have paidFrame : MutatorFrame pending paid := by
    split at paidOk
    · exact frame_processBuilderPendingPayments (liftAccessor_ok.mp paidOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ MutatorFrame.refl _
  exact ⟨justified, rooted, justifiedOk, head.trans (paidFrame.trans middle), tail⟩

/-- From Altair, the epoch transition is justification, then steps that form an epoch frame. -/
theorem processEpochAltair_frame {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    ∃ justified, processJustificationAndFinalization state = .ok justified ∧
      EpochFrame justified after := by
  obtain ⟨justified, rooted, justifiedOk, head, tail⟩ := processEpochAltair_split computed
  exact ⟨justified, justifiedOk, head.toEpochFrame.trans <|
    (frame_processParticipationFlagUpdates rooted altair).trans tail.toEpochFrame⟩

/-- The epoch transition is justification, then steps that form an epoch frame.

This holds at every fork. -/
theorem processEpoch_frame (computed : processEpoch config checks state = .ok after) :
    ∃ justified, processJustificationAndFinalization state = .ok justified ∧
      EpochFrame justified after := by
  unfold processEpoch at computed
  split at computed
  · exact processEpochAltair_frame computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  exact ⟨justified, justifiedOk,
    ((frame_processRewardsAndPenalties rewardedOk).trans <|
    (frame_processRegistryUpdates registeredOk).trans <|
    (frame_processSlashings slashedOk).trans <|
    (frame_processEth1DataReset resetOk).trans <|
    (frame_processEffectiveBalanceUpdates balancedOk).trans <|
    (frame_processSlashingsReset clearedOk).trans <|
    (frame_processRandaoMixesReset mixedOk).trans <|
    (frame_processHistoricalRootsUpdate rootedOk).trans <|
    frame_processParticipationRecordUpdates rotated).toEpochFrame⟩

/-! ## Justification and the epoch transition -/

/-- Justification and finalization keep the genesis time and the buffer of block roots.

They also keep the latest block header, and from Gloas the latest block hash and bid.

They keep the registry, the fork versions and the genesis validators root.

They also keep the flags of both epochs. -/
theorem processJustificationAndFinalization_keeps
    (computed : processJustificationAndFinalization state = .ok after) :
    after.genesisTime = state.genesisTime ∧ after.blockRoots = state.blockRoots ∧
      after.latestBlockHeader = state.latestBlockHeader ∧
      after.latestBlockHash = state.latestBlockHash ∧
      after.latestExecutionPayloadBid = state.latestExecutionPayloadBid ∧
      after.validators = state.validators ∧ after.forkVersions = state.forkVersions ∧
      after.genesisValidatorsRoot = state.genesisValidatorsRoot ∧
      after.previousEpochParticipation = state.previousEpochParticipation ∧
      after.currentEpochParticipation = state.currentEpochParticipation := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact ⟨by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest],
      by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest]⟩

/-- The current justified epoch is at most the previous epoch. -/
def JustifiedSettled (state : BeaconState preset fork) : Prop :=
  state.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch state

/-- The properties that each valid block keeps.

The last one says that each effective balance is a whole number of increments.

It holds when the largest effective balances of the preset are whole numbers of increments. -/
structure Invariant (state : BeaconState preset fork) : Prop where
  balancesMatch : BalancesMatch state
  exitsOrdered : ExitsOrdered state
  ordered : CheckpointsOrdered state
  settled : JustifiedSettled state
  aligned : MaxEffectiveBalancesAligned preset → EffectiveBalancesAligned state

theorem Frame.invariant (frame : Frame state after) (holds : Invariant state) :
    Invariant after where
  balancesMatch := frame.balancesMatch holds.balancesMatch
  exitsOrdered := frame.exitsOrdered holds.exitsOrdered
  ordered := by
    have := holds.ordered
    unfold CheckpointsOrdered at this ⊢
    rw [frame.finalized, frame.previousJustified, frame.currentJustified]
    exact this
  settled := by
    have := holds.settled
    unfold JustifiedSettled getPreviousEpoch getCurrentEpoch at this ⊢
    rw [frame.currentJustified, frame.slot]
    exact this
  aligned maxAligned := frame.aligned maxAligned (holds.aligned maxAligned)

/-- Justification and finalization keep the checkpoints in order, and the finalized epoch rises.

They change neither the slot, nor the registry, nor the balances.

The new current justified epoch is at most the current epoch. -/
theorem processJustificationAndFinalization_invariant (ordered : CheckpointsOrdered state)
    (settled : JustifiedSettled state)
    (computed : processJustificationAndFinalization state = .ok after) :
    CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch ∧
      after.currentJustifiedCheckpoint.epoch ≤ getCurrentEpoch state ∧
      after.slot = state.slot ∧ after.validators = state.validators ∧
      after.balances = state.balances := by
  obtain ⟨ordered', finalized⟩ :=
    processJustificationAndFinalization_ordered ordered settled computed
  have previous := getPreviousEpoch_le state
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact ⟨ordered', finalized, UInt64.le_trans settled previous, rfl, rfl, rfl⟩
  · obtain ⟨_, current, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    refine ⟨ordered', finalized, ?_, by rw [← rest], by rw [← rest], by rw [← rest]⟩
    rcases current with same | same | same
    · rw [same]
      exact UInt64.le_trans settled previous
    · rw [same]
      exact previous
    · rw [same]
      exact UInt64.le_refl _

/-- What an epoch transition keeps when it is justification, then steps that keep the frame. -/
private theorem epoch_invariant {justified : BeaconState preset fork} (holds : Invariant state)
    (justifiedOk : processJustificationAndFinalization state = .ok justified)
    (frame : Frame justified after) :
    after.slot = state.slot ∧ BalancesMatch after ∧ ExitsOrdered after ∧
      CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch ∧
      after.currentJustifiedCheckpoint.epoch ≤ getCurrentEpoch state := by
  obtain ⟨ordered, finalized, current, slot, validators, balances⟩ :=
    processJustificationAndFinalization_invariant holds.ordered holds.settled justifiedOk
  have balancesMatch : BalancesMatch justified := by
    have := holds.balancesMatch
    unfold BalancesMatch at this ⊢
    rw [validators, balances]
    exact this
  have exitsOrdered : ExitsOrdered justified := by
    have := holds.exitsOrdered
    unfold ExitsOrdered at this ⊢
    rw [validators]
    exact this
  refine ⟨frame.slot.trans slot, frame.balancesMatch balancesMatch,
    frame.exitsOrdered exitsOrdered, ?_, ?_, ?_⟩
  · unfold CheckpointsOrdered at ordered ⊢
    rw [frame.finalized, frame.previousJustified, frame.currentJustified]
    exact ordered
  · rw [frame.finalized]
    exact finalized
  · rw [frame.currentJustified]
    exact current

/-- An epoch transition keeps the effective balances whole when the largest ones are. -/
private theorem processEpoch_aligned (holds : Invariant state)
    (computed : processEpoch config checks state = .ok after)
    (maxAligned : MaxEffectiveBalancesAligned preset) : EffectiveBalancesAligned after := by
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame computed
  obtain ⟨_, _, _, _, validators, _⟩ :=
    processJustificationAndFinalization_invariant holds.ordered holds.settled justifiedOk
  refine frame.toFrame.aligned maxAligned ?_
  unfold EffectiveBalancesAligned
  rw [validators]
  exact holds.aligned maxAligned

/-- The epoch transition keeps the order of the checkpoints and the slot.

The finalized epoch does not decrease.

The current justified epoch ends at most at the current epoch.

The registry keeps one balance for each validator, and each exit no later than its withdrawal. -/
theorem processEpoch_invariant (holds : Invariant state)
    (computed : processEpoch config checks state = .ok after) :
    after.slot = state.slot ∧ BalancesMatch after ∧ ExitsOrdered after ∧
      CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch ∧
      after.currentJustifiedCheckpoint.epoch ≤ getCurrentEpoch state := by
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame computed
  exact epoch_invariant holds justifiedOk frame.toFrame

/-! ## Slots and blocks -/

theorem frame_processSlot (computed : processSlot state = .ok after) : Frame state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact Frame.of_validators ⟨rfl, rfl⟩

/-- One slot keeps the invariant, and the finalized epoch does not decrease.

When the slot ends an epoch, the current justified epoch is at most that epoch.

The next slot starts the next epoch, whose previous epoch is that one. -/
theorem advanceSlot_invariant (holds : Invariant state)
    (computed : advanceSlot config checks state = .ok after) :
    Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  have cachedHolds := cachedFrame.invariant holds
  have stateEpoch := getCurrentEpoch_toNat state
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    obtain ⟨_, balancesMatch, exitsOrdered, ordered, finalized, current⟩ :=
      processEpoch_invariant cachedHolds epochedOk
    have step := nextSlot_epoch_of_boundary sum boundary
    have whole := fun maxAligned => processEpoch_aligned cachedHolds epochedOk maxAligned
    refine ⟨⟨balancesMatch, exitsOrdered, ordered, ?_, whole⟩, ?_⟩
    · have current' := UInt64.le_iff_toNat_le.mp current
      rw [getCurrentEpoch_toNat, cachedFrame.slot] at current'
      unfold JustifiedSettled
      rw [UInt64.le_iff_toNat_le, getPreviousEpoch_toNat, getCurrentEpoch_toNat]
      dsimp only
      omega
    · rw [← cachedFrame.finalized]
      exact finalized
  · rename_i notBoundary
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have step := nextSlot_epoch_of_inside sum notBoundary
    refine ⟨⟨cachedHolds.balancesMatch, cachedHolds.exitsOrdered, cachedHolds.ordered, ?_,
      cachedHolds.aligned⟩, ?_⟩
    · have settled := UInt64.le_iff_toNat_le.mp holds.settled
      rw [getPreviousEpoch_toNat, getCurrentEpoch_toNat] at settled
      unfold JustifiedSettled
      rw [UInt64.le_iff_toNat_le, getPreviousEpoch_toNat, getCurrentEpoch_toNat]
      dsimp only
      rw [cachedFrame.currentJustified, step]
      exact settled
    · rw [cachedFrame.finalized]
      exact UInt64.le_refl _

theorem advanceSlots_invariant :
    ∀ {count : Nat} {state after : BeaconState preset fork}, Invariant state →
      advanceSlots config checks count state = .ok after →
      Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch
  | 0, state, after, holds, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨holds, UInt64.le_refl _⟩
  | count + 1, state, after, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    obtain ⟨nextHolds, first⟩ := advanceSlot_invariant holds nextOk
    obtain ⟨afterHolds, second⟩ := advanceSlots_invariant nextHolds rest
    exact ⟨afterHolds, UInt64.le_trans first second⟩

/-- Advancing to a later slot keeps the invariant.

The finalized epoch does not decrease. -/
theorem processSlots_invariant {slot : Slot} (holds : Invariant state)
    (computed : processSlots config checks state slot = .ok after) :
    Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact advanceSlots_invariant holds advanced

/-- Each valid block keeps the invariant, and the finalized epoch never decreases.

The registry and the balances keep one entry for each validator.

Each validator may withdraw no earlier than it exits.

The checkpoints stay in order, and the current justified epoch stays at most the previous epoch.

This holds for every signature check and with or without validating the result. -/
theorem stateTransition_invariant
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool} (holds : Invariant state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  obtain ⟨advancedHolds, finalized⟩ := processSlots_invariant holds slotsOk
  have frame := frame_processBlock blockOk
  refine ⟨frame.invariant advancedHolds, ?_⟩
  rw [frame.finalized]
  exact finalized

end EthLib.Consensus
