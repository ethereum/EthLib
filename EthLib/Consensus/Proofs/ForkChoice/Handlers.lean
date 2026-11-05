module

public import EthLib.Base.Except
public import EthLib.Consensus.ForkChoice.Handlers
public import EthLib.Consensus.Proofs.ForkChoice.Head
public import EthLib.Consensus.Proofs.Time

/-!
# Proofs: the handlers of the fork choice

No handler lowers the epoch of the justified or of the finalized checkpoint.

Nor does a block together with the votes that it carries.

A tick sets the clock to its time, and the catch-up loop never stalls.

A new block enters the store with the state that the transition computes for it.

From Deneb its blobs were available, and their proofs matched its commitments.

At Bellatrix the first payload passes exactly when it follows a terminal block of proof of work.

A known block leaves the store as it was.

An attestation leaves each voter not marked as an equivocator a vote at its target epoch or later.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork}

namespace Store

/-- The justified and finalized epochs of one store are at most those of another. -/
def EpochsLe (before after : Store preset fork) : Prop :=
  before.justifiedCheckpoint.epoch ≤ after.justifiedCheckpoint.epoch ∧
    before.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch

theorem EpochsLe.refl (store : Store preset fork) : store.EpochsLe store :=
  ⟨UInt64.le_refl _, UInt64.le_refl _⟩

theorem EpochsLe.trans {a b c : Store preset fork} (ab : a.EpochsLe b) (bc : b.EpochsLe c) :
    a.EpochsLe c :=
  ⟨UInt64.le_trans ab.1 bc.1, UInt64.le_trans ab.2 bc.2⟩

variable {config : Config} {store : Store preset fork}

/-- Replacing the checkpoints lowers neither epoch. -/
theorem updateCheckpoints_epochsLe (justified finalized : Checkpoint) :
    store.EpochsLe (store.updateCheckpoints justified finalized) := by
  unfold updateCheckpoints EpochsLe
  by_cases j : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.finalizedCheckpoint.epoch < finalized.epoch <;>
    simp [j, f, UInt64.le_of_lt]

/-- Two stores with the same checkpoints have the same epochs. -/
theorem EpochsLe.of_eq {a b : Store preset fork}
    (justified : b.justifiedCheckpoint = a.justifiedCheckpoint)
    (finalized : b.finalizedCheckpoint = a.finalizedCheckpoint) : a.EpochsLe b := by
  rw [EpochsLe, justified, finalized]
  exact ⟨UInt64.le_refl _, UInt64.le_refl _⟩

@[simp] theorem updateCheckpoints_blocks (justified finalized : Checkpoint) :
    (store.updateCheckpoints justified finalized).blocks = store.blocks := by
  unfold updateCheckpoints
  by_cases j : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.finalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

@[simp] theorem updateCheckpoints_blockStates (justified finalized : Checkpoint) :
    (store.updateCheckpoints justified finalized).blockStates = store.blockStates := by
  unfold updateCheckpoints
  by_cases j : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.finalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

@[simp] theorem updateUnrealizedCheckpoints_justifiedCheckpoint (justified finalized : Checkpoint) :
    (store.updateUnrealizedCheckpoints justified finalized).justifiedCheckpoint =
      store.justifiedCheckpoint := by
  unfold updateUnrealizedCheckpoints
  by_cases j : store.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

@[simp] theorem updateUnrealizedCheckpoints_finalizedCheckpoint (justified finalized : Checkpoint) :
    (store.updateUnrealizedCheckpoints justified finalized).finalizedCheckpoint =
      store.finalizedCheckpoint := by
  unfold updateUnrealizedCheckpoints
  by_cases j : store.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

@[simp] theorem updateUnrealizedCheckpoints_blocks (justified finalized : Checkpoint) :
    (store.updateUnrealizedCheckpoints justified finalized).blocks = store.blocks := by
  unfold updateUnrealizedCheckpoints
  by_cases j : store.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

@[simp] theorem updateUnrealizedCheckpoints_blockStates (justified finalized : Checkpoint) :
    (store.updateUnrealizedCheckpoints justified finalized).blockStates = store.blockStates := by
  unfold updateUnrealizedCheckpoints
  by_cases j : store.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

/-- The tip pulled up to the end of its epoch lowers neither epoch, and keeps the blocks. -/
theorem computePulledUpTip_frame {root : Root} {after : Store preset fork}
    (pulled : store.computePulledUpTip config root = .ok after) :
    store.EpochsLe after ∧ after.blocks = store.blocks ∧ after.blockStates = store.blockStates := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨state, -, pulledState, -, block, -, epoch, -, pulled⟩ := pulled
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled
  · exact ⟨(EpochsLe.of_eq (by simp) (by simp)).trans (updateCheckpoints_epochsLe _ _),
      by simp, by simp⟩
  · exact ⟨EpochsLe.of_eq (by simp) (by simp), by simp, by simp⟩

@[simp] theorem updateCheckpoints_timeMs (justified finalized : Checkpoint) :
    (store.updateCheckpoints justified finalized).timeMs = store.timeMs := by
  unfold updateCheckpoints
  by_cases j : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.finalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

@[simp] theorem updateCheckpoints_genesisTimeMs (justified finalized : Checkpoint) :
    (store.updateCheckpoints justified finalized).genesisTimeMs = store.genesisTimeMs := by
  unfold updateCheckpoints
  by_cases j : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.finalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

/-- A tick within a slot sets the clock to its time, keeps the blocks and lowers no epoch. -/
theorem onTickPerSlot_frame {timeMs : UInt64} {after : Store preset fork}
    (ticked : store.onTickPerSlot config timeMs = .ok after) :
    after.timeMs = timeMs ∧ after.genesisTimeMs = store.genesisTimeMs ∧ store.EpochsLe after ∧
      after.blocks = store.blocks ∧ after.blockStates = store.blockStates := by
  unfold onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    · obtain ⟨_, _, ticked⟩ := ticked
      split at ticked
      · simp only [pure, Except.pure, Except.ok.injEq] at ticked
        subst ticked
        refine ⟨by simp, by simp, ?_, by simp, by simp⟩
        exact (EpochsLe.of_eq (by rfl) (by rfl)).trans (updateCheckpoints_epochsLe _ _)
      · simp only [pure, Except.pure, Except.ok.injEq] at ticked
        subst ticked
        exact ⟨rfl, rfl, EpochsLe.of_eq (by rfl) (by rfl), rfl, rfl⟩


/-- The catch-up loop keeps the time of genesis and the blocks, and lowers no epoch. -/
theorem catchUp_frame {tickSlot : Slot} {start after : Store preset fork}
    (caught : catchUp config start tickSlot = .ok after) :
    after.genesisTimeMs = start.genesisTimeMs ∧ start.EpochsLe after ∧
      after.blocks = start.blocks ∧ after.blockStates = start.blockStates := by
  induction start using catchUp.induct config tickSlot with
  | _ start ih =>
    rw [catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTimeMs, -, ticked, tick, caught⟩ := caught
      split at caught
      · obtain ⟨g, le, b, bs⟩ := ih ticked ‹_› caught
        obtain ⟨-, g', le', b', bs'⟩ := onTickPerSlot_frame tick
        exact ⟨g.trans g', le'.trans le, b.trans b', bs.trans bs'⟩
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst caught
      exact ⟨rfl, EpochsLe.refl _, rfl, rfl⟩

/-- A tick sets the clock to its time, keeps the blocks and lowers no epoch. -/
theorem onTick_frame {timeMs : UInt64} {after : Store preset fork}
    (ticked : store.onTick config timeMs = .ok after) :
    after.timeMs = timeMs ∧ store.EpochsLe after ∧
      after.blocks = store.blocks ∧ after.blockStates = store.blockStates := by
  unfold onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨tickSlot, -, caught, caughtUp, ticked⟩ := ticked
  obtain ⟨-, le, b, bs⟩ := catchUp_frame caughtUp
  obtain ⟨time, -, le', b', bs'⟩ := onTickPerSlot_frame ticked
  exact ⟨time, le.trans le', b'.trans b, bs'.trans bs⟩

/-- A tick within a slot fails only on an arithmetic error, never as a stalled clock. -/
theorem onTickPerSlot_ne_tickNotAdvancing {timeMs : UInt64} {slot : Slot} :
    store.onTickPerSlot config timeMs ≠ .error (.tickNotAdvancing slot) := by
  intro stalled
  unfold onTickPerSlot getCurrentSlot at stalled
  cases a : computeSlotAtTimeMs config store.genesisTimeMs store.timeMs with
  | error e => simp [a, Except.mapError, bind, Except.bind] at stalled
  | ok previous =>
    cases b : computeSlotAtTimeMs config store.genesisTimeMs timeMs with
    | error e => simp [a, b, Except.mapError, bind, Except.bind] at stalled
    | ok current =>
      cases c : computeSlotsSinceEpochStart preset current with
      | error e => simp [a, b, c, Except.mapError, bind, Except.bind] at stalled
      | ok since =>
        simp only [a, b, c, Except.mapError, bind, Except.bind] at stalled
        split at stalled <;> simp only [pure, Except.pure, reduceCtorEq] at stalled

/-- A slot that the clock reads implies a slot duration above zero. -/
theorem slotDuration_pos {slot : Slot} (current : store.getCurrentSlot config = .ok slot) :
    0 < config.SLOT_DURATION_MS := by
  unfold getCurrentSlot computeSlotAtTimeMs at current
  cases elapsed : subChecked store.timeMs store.genesisTimeMs with
  | error e => simp [elapsed, bind, Except.bind, Except.mapError] at current
  | ok elapsed' =>
    simp only [elapsed, bind, Except.bind] at current
    cases quotient : divChecked elapsed' config.SLOT_DURATION_MS with
    | error e => simp [quotient, Except.mapError] at current
    | ok q =>
      have := (divChecked_ok_iff.mp quotient).1
      exact UInt64.pos_iff_ne_zero.mpr this

/-- The catch-up loop never stalls: each tick moves the clock to the next slot. -/
theorem catchUp_ne_tickNotAdvancing {tickSlot slot : Slot} (start : Store preset fork) :
    catchUp config start tickSlot ≠ .error (.tickNotAdvancing slot) := by
  induction start using catchUp.induct config tickSlot with
  | _ start ih =>
    intro stalled
    rw [catchUp.eq_1] at stalled
    cases current : start.getCurrentSlot config with
    | error e =>
      simp only [current, bind, Except.bind, Except.error.injEq] at stalled
      subst stalled
      unfold getCurrentSlot at current
      cases h : computeSlotAtTimeMs config start.genesisTimeMs start.timeMs <;>
        simp [h, Except.mapError] at current
    | ok c =>
      simp only [current, bind, Except.bind] at stalled
      split at stalled
      · rename_i lt
        cases n : addChecked c 1 with
        | error e => simp [n, Except.mapError] at stalled
        | ok next =>
          cases t : computeTimeAtSlotMs config start.genesisTimeMs next with
          | error e => simp [n, t, Except.mapError] at stalled
          | ok nextTime =>
            cases tick : start.onTickPerSlot config nextTime with
            | error e =>
              simp only [n, t, tick, Except.mapError] at stalled
              exact onTickPerSlot_ne_tickNotAdvancing (by rw [tick, stalled])
            | ok ticked =>
              simp only [n, t, tick, Except.mapError] at stalled
              split at stalled
              · exact ih ticked ‹_› stalled
              · rename_i notCloser
                apply notCloser
                obtain ⟨time, genesis, -⟩ := onTickPerSlot_frame tick
                have slot : ticked.getCurrentSlot config = .ok next := by
                  unfold getCurrentSlot
                  rw [time, genesis,
                    computeSlotAtTimeMs_computeTimeAtSlotMs (slotDuration_pos current) t]
                  rfl
                obtain ⟨-, nextValue⟩ := addChecked_ok_iff.mp n
                simp only [slotsBefore, slot, current]
                have := UInt64.lt_iff_toNat_lt.mp lt
                simp only [UInt64.toNat_one] at nextValue
                omega
      · simp [pure, Except.pure] at stalled

/-- Storing the state of a target keeps the checkpoints, the blocks and their states. -/
theorem storeTargetCheckpointState_frame {target : Checkpoint} {after : Store preset fork}
    (stored : store.storeTargetCheckpointState config target = .ok after) :
    store.EpochsLe after ∧ after.blocks = store.blocks ∧ after.blockStates = store.blockStates := by
  unfold storeTargetCheckpointState at stored
  split at stored
  · simp only [pure, Except.pure, Except.ok.injEq] at stored
    subst stored
    exact ⟨EpochsLe.refl _, rfl, rfl⟩
  · simp only [bind_ok_iff] at stored
    obtain ⟨_, _, stored⟩ := stored
    simp only [pure, Except.pure, Except.ok.injEq] at stored
    subst stored
    exact ⟨EpochsLe.of_eq (by rfl) (by rfl), rfl, rfl⟩

/-- An attestation lowers no epoch, and keeps the blocks and their states. -/
theorem onAttestation_frame {checks : SignatureChecks} {attestation : Attestation preset fork}
    {isFromBlock : Bool} {after : Store preset fork}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    store.EpochsLe after ∧ after.blocks = store.blocks ∧ after.blockStates = store.blockStates := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, valid, _, attested⟩ := attested
  obtain ⟨le, b, bs⟩ := storeTargetCheckpointState_frame storing
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    exact ⟨le, b, bs⟩
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

/-- An attester slashing lowers no epoch, and keeps the blocks and their states. -/
theorem onAttesterSlashing_frame {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork} {after : Store preset fork}
    (slashed : store.onAttesterSlashing config checks slashing = .ok after) :
    store.EpochsLe after ∧ after.blocks = store.blocks ∧ after.blockStates = store.blockStates := by
  unfold onAttesterSlashing at slashed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
  obtain ⟨_, _, slashed⟩ := slashed
  subst slashed
  exact ⟨EpochsLe.of_eq (by rfl) (by rfl), rfl, rfl⟩

/-- Recording the timeliness of a block changes only the timeliness. -/
theorem recordBlockTimeliness_frame {root : Root} {after : Store preset fork}
    (recorded : store.recordBlockTimeliness config root = .ok after) :
    store.EpochsLe after ∧ after.blocks = store.blocks ∧ after.blockStates = store.blockStates := by
  unfold recordBlockTimeliness at recorded
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at recorded
  obtain ⟨_, _, _, _, _, _, _, _, recorded⟩ := recorded
  subst recorded
  exact ⟨EpochsLe.of_eq (by rfl) (by rfl), rfl, rfl⟩

/-- Updating the boost changes only the boosted root. -/
theorem updateProposerBoostRoot_frame {head root : Root} {after : Store preset fork}
    (updated : store.updateProposerBoostRoot config head root = .ok after) :
    store.EpochsLe after ∧ after.blocks = store.blocks ∧ after.blockStates = store.blockStates := by
  unfold updateProposerBoostRoot at updated
  split at updated
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at updated
  simp only [bind_ok_iff, pure_bind] at updated
  obtain ⟨_, _, _, _, _, _, updated⟩ := updated
  split at updated <;> simp only [pure, Except.pure, Except.ok.injEq] at updated <;>
    subst updated <;> exact ⟨EpochsLe.of_eq (by rfl) (by rfl), rfl, rfl⟩

/-- A new block that passes the checks has a known parent, and its blobs are available.

Its state is the one that the state transition computes from the parent's. -/
theorem validateOnBlock_ok {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    {blockRoot : Root} {state : BeaconState preset fork}
    (valid : store.validateOnBlock config checks sources signed blockRoot = .ok state) :
    ∃ pre, store.blockStates[signed.message.parentRoot]? = some pre ∧
      validateDataAvailability sources signed.message blockRoot = .ok () ∧
      stateTransition config checks sources.engine pre signed true = .ok state := by
  unfold validateOnBlock at valid
  dsimp only at valid
  cases found : store.blockStates[signed.message.parentRoot]? with
  | none =>
    simp [blockState, found, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at valid
  | some pre =>
    refine ⟨pre, rfl, ?_⟩
    simp only [blockState, found, bind_ok_iff] at valid
    obtain ⟨a, ha, _, _, valid⟩ := valid
    simp only [pure, Except.pure, Except.ok.injEq] at ha
    subst ha
    split at valid
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at valid
    simp only [bind_ok_iff] at valid
    obtain ⟨_, _, valid⟩ := valid
    split at valid
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at valid
    simp only [bind_ok_iff] at valid
    obtain ⟨_, _, valid⟩ := valid
    split at valid
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at valid
    simp only [bind_ok_iff] at valid
    obtain ⟨_, available, after, transition, valid⟩ := valid
    -- The merge check returns the state of the transition, or fails.
    have same : after = state := by
      split at valid
      · split at valid
        · simp only [bind_ok_iff] at valid
          obtain ⟨_, _, valid⟩ := valid
          simpa [pure, Except.pure] using valid
        · simpa [pure, Except.pure] using valid
      · simpa [pure, Except.pure] using valid
    subst same
    exact ⟨available, mapError_ok_iff.mp transition⟩

/-- Before Deneb a block has no blobs, and the check of their availability passes. -/
theorem validateDataAvailability_of_lt {sources : BlockSources preset fork}
    {block : BeaconBlock preset fork} {blockRoot : Root} (before : fork < .dencun) :
    validateDataAvailability sources block blockRoot = .ok () := by
  have early : ¬ .dencun ≤ fork := Nat.not_le_of_lt before
  have later : ¬ .fusaka ≤ fork := fun fulu => early (Nat.le_trans (by decide) fulu)
  simp [validateDataAvailability, early, later, pure, Except.pure]

/-- From Deneb and before Fulu, the check passes exactly when the node holds the blobs and proofs.

The proofs must also show that the blobs match the commitments of the block. -/
theorem validateDataAvailability_ok {sources : BlockSources preset fork}
    {block : BeaconBlock preset fork} {blockRoot : Root}
    (deneb : .dencun ≤ fork) (before : fork < .fusaka) :
    validateDataAvailability sources block blockRoot = .ok () ↔
      ∃ blobs proofs, sources.blobsAndProofs blockRoot = some (blobs, proofs) ∧
        Cryptography.Kzg.verifyBlobKzgProofBatch sources.setup blobs
          (block.body.blobKzgCommitments ⟨deneb, Nat.lt_trans before (by decide)⟩).data proofs =
          .ok true := by
  have later : ¬ .fusaka ≤ fork := Nat.not_le_of_lt before
  unfold validateDataAvailability isDataAvailable
  cases found : sources.blobsAndProofs blockRoot with
  | none => simp [later, deneb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  | some data =>
    obtain ⟨blobs, proofs⟩ := data
    cases verified : Cryptography.Kzg.verifyBlobKzgProofBatch sources.setup blobs
        (block.body.blobKzgCommitments ⟨deneb, Nat.lt_trans before (by decide)⟩).data proofs with
    | error e => simp_all [bind, Except.bind, Except.mapError]
    | ok result =>
      cases result
      · simp_all [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, Except.mapError]
      · refine iff_of_true ?_ ⟨blobs, proofs, rfl, verified⟩
        simp [later, deneb, verified, bind, Except.bind, Except.mapError, pure, Except.pure]

/-- The first payload passes exactly when it follows a terminal block of proof of work.

With a configured terminal block hash, the epoch must reach its activation.

The payload must then follow that hash.

Otherwise the node must know the parent of the payload and its own parent.

The first of the two must then be terminal. -/
theorem validateMergeBlock_ok {powBlock : Hash32 → Option PowBlock}
    {block : BeaconBlock preset fork} {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} :
    validateMergeBlock config powBlock block bellatrix = .ok () ↔
      if config.TERMINAL_BLOCK_HASH ≠ Vector.replicate 32 0 then
        config.TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH ≤ computeEpochAtSlot preset block.slot ∧
          (block.body.executionPayload bellatrix).parentHash = config.TERMINAL_BLOCK_HASH
      else ∃ terminal parent,
        powBlock (block.body.executionPayload bellatrix).parentHash = some terminal ∧
          powBlock terminal.parentHash = some parent ∧
          isValidTerminalPowBlock config terminal parent = true := by
  unfold validateMergeBlock
  dsimp only
  by_cases hash : config.TERMINAL_BLOCK_HASH ≠ Vector.replicate 32 0
  · simp only [ne_eq, hash, not_false_eq_true, ↓reduceIte]
    by_cases early :
        computeEpochAtSlot preset block.slot < config.TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH
    · simp [early, UInt64.not_le.mpr early, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind]
    · by_cases same :
          (block.body.executionPayload bellatrix).parentHash = config.TERMINAL_BLOCK_HASH
      · simp [early, same, pure, Except.pure, UInt64.not_lt.mp early]
      · simp [early, same, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · simp only [hash, ↓reduceIte]
    cases found : powBlock (block.body.executionPayload bellatrix).parentHash with
    | none => simp [throw, throwThe, MonadExceptOf.throw]
    | some terminal =>
      cases foundParent : powBlock terminal.parentHash with
      | none => simp [foundParent, throw, throwThe, MonadExceptOf.throw]
      | some parent =>
        cases valid : isValidTerminalPowBlock config terminal parent <;>
          simp [foundParent, valid, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- At Bellatrix, a new block with the first payload of its chain passed the merge check. -/
theorem validateOnBlock_merge {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} {blockRoot : Root}
    {state pre : BeaconState preset fork} (bellatrix : fork = .bellatrix)
    (range : .bellatrix ≤ fork ∧ fork < .glamsterdam)
    (found : store.blockStates[signed.message.parentRoot]? = some pre)
    (merge : isMergeTransitionBlock pre signed.message.body range = true)
    (valid : store.validateOnBlock config checks sources signed blockRoot = .ok state) :
    validateMergeBlock config sources.powBlock signed.message range = .ok () := by
  unfold validateOnBlock at valid
  dsimp only at valid
  simp only [blockState, found, bind_ok_iff] at valid
  obtain ⟨a, ha, _, _, valid⟩ := valid
  simp only [pure, Except.pure, Except.ok.injEq] at ha
  subst ha
  split at valid
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at valid
  simp only [bind_ok_iff] at valid
  obtain ⟨_, _, valid⟩ := valid
  split at valid
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at valid
  simp only [bind_ok_iff] at valid
  obtain ⟨_, _, valid⟩ := valid
  split at valid
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at valid
  simp only [bind_ok_iff] at valid
  -- The merge test holds, so the step after the transition is the merge check.
  obtain ⟨_, _, _, _, _, checked, _⟩ := valid
  exact checked

/-- A new block enters the store with the state after it, and no epoch falls.

That state is the one the state transition computes from the state after the parent. -/
theorem addBlock_ok {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    {blockRoot : Root} {after : Store preset fork}
    (added : store.addBlock config checks sources signed blockRoot = .ok after) :
    store.EpochsLe after ∧ after.blocks[blockRoot]? = some signed.message ∧
      ∃ pre state, store.blockStates[signed.message.parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre signed true = .ok state ∧
        after.blockStates[blockRoot]? = some state := by
  unfold addBlock at added
  simp only [bind_ok_iff] at added
  obtain ⟨state, valid, head, -, recorded, record, boosted, boost, added⟩ := added
  obtain ⟨le1, b1, bs1⟩ := recordBlockTimeliness_frame record
  obtain ⟨le2, b2, bs2⟩ := updateProposerBoostRoot_frame boost
  obtain ⟨le3, b3, bs3⟩ := computePulledUpTip_frame added
  refine ⟨(le1.trans le2).trans ((updateCheckpoints_epochsLe _ _).trans le3), ?_, ?_⟩
  · rw [b3, updateCheckpoints_blocks, b2, b1]
    simp
  · obtain ⟨pre, found, -, transition⟩ := validateOnBlock_ok valid
    refine ⟨pre, state, found, transition, ?_⟩
    rw [bs3, updateCheckpoints_blockStates, bs2, bs1]
    simp

/-- From Fulu columns of data replace the blobs, which is not yet specified here. -/
theorem onBlock_of_fulu {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    (fulu : .fusaka ≤ fork) :
    store.onBlock config checks sources signed = .error (.forkNotYetSpecified fork) := by
  simp [onBlock, fulu, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A block that the store holds already leaves the store as it was. -/
theorem onBlock_known {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    {blockRoot : Root} (before : fork < .fusaka)
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (known : store.blocks.contains blockRoot) :
    store.onBlock config checks sources signed = .ok store := by
  have later : ¬ .fusaka ≤ fork := Nat.not_le_of_lt before
  simp [onBlock, later, root, known, bind, Except.bind, Except.mapError, pure, Except.pure]

/-- A new block enters the store with the state after it, and no epoch falls.

That state is the one the state transition computes from the state after the parent. -/
theorem onBlock_new {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    {blockRoot : Root} {after : Store preset fork}
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    store.EpochsLe after ∧ after.blocks[blockRoot]? = some signed.message ∧
      ∃ pre state, store.blockStates[signed.message.parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre signed true = .ok state ∧
        after.blockStates[blockRoot]? = some state := by
  by_cases fulu : .fusaka ≤ fork
  · rw [onBlock_of_fulu fulu] at added
    cases added
  simp only [onBlock, fulu, root, new, bind, Except.bind, Except.mapError, ↓reduceIte,
    Bool.false_eq_true] at added
  exact addBlock_ok added

/-- No block lowers the epoch of the justified or the finalized checkpoint. -/
theorem onBlock_epochsLe {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    {after : Store preset fork} (added : store.onBlock config checks sources signed = .ok after) :
    store.EpochsLe after := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e =>
    unfold onBlock at added
    split at added
    · cases added
    · simp [root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · by_cases fulu : .fusaka ≤ fork
      · rw [onBlock_of_fulu fulu] at added
        cases added
      rw [onBlock_known (Nat.lt_of_not_le fulu) root known] at added
      cases added
      exact EpochsLe.refl _
    · exact (onBlock_new root known added).1

/-- A block and the votes that it carries lower no epoch. -/
theorem onBlockWithVotes_epochsLe {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} {after : Store preset fork}
    (added : store.onBlockWithVotes config checks sources signed = .ok after) :
    store.EpochsLe after := by
  unfold onBlockWithVotes at added
  simp only [bind_ok_iff, ← Array.foldlM_toList] at added
  obtain ⟨blocked, block, voted, attested, slashed⟩ := added
  -- Each fold keeps the epochs of the store it starts from at or below those of its store.
  have votes := foldlM_ok_invariant blocked.EpochsLe
    (fun _ _ _ le step => le.trans (onAttestation_frame step).1) (EpochsLe.refl _) attested
  have slashings := foldlM_ok_invariant voted.EpochsLe
    (fun _ _ _ le step => le.trans (onAttesterSlashing_frame step).1) (EpochsLe.refl _) slashed
  exact (onBlock_epochsLe block).trans (votes.trans slashings)

/-- A vote keeps every other vote at or after its epoch at or after it. -/
theorem recordVote_keeps {equivocating : List ValidatorIndex} {message : LatestMessage}
    {messages : Std.TreeMap ValidatorIndex LatestMessage} {i j : ValidatorIndex}
    {old : LatestMessage}
    (found : messages[j]? = some old) (late : message.epoch ≤ old.epoch) :
    ∃ m, (recordVote equivocating message messages i)[j]? = some m ∧ message.epoch ≤ m.epoch := by
  unfold recordVote
  split
  · exact ⟨old, found, late⟩
  · split
    · split
      · by_cases same : i = j
        · subst same
          exact ⟨message, by simp, UInt64.le_refl _⟩
        · refine ⟨old, ?_, late⟩
          rw [Std.TreeMap.getElem?_insert]
          simp [same, found]
      · exact ⟨old, found, late⟩
    · by_cases same : i = j
      · subst same
        exact ⟨message, by simp, UInt64.le_refl _⟩
      · refine ⟨old, ?_, late⟩
        rw [Std.TreeMap.getElem?_insert]
        simp [same, found]

/-- After the vote of a validator that does not equivocate, its vote is at or after the epoch. -/
theorem recordVote_self {equivocating : List ValidatorIndex} {message : LatestMessage}
    {messages : Std.TreeMap ValidatorIndex LatestMessage} {i : ValidatorIndex}
    (honest : i ∉ equivocating) :
    ∃ m, (recordVote equivocating message messages i)[i]? = some m ∧ message.epoch ≤ m.epoch := by
  unfold recordVote
  have : equivocating.contains i = false := by simpa using honest
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i old found
    split
    · exact ⟨message, by simp, UInt64.le_refl _⟩
    · rename_i notLater
      exact ⟨old, found, UInt64.not_lt.mp notLater⟩
  · exact ⟨message, by simp, UInt64.le_refl _⟩

/-- After a run of votes, each voter that does not equivocate has a vote at or after the epoch. -/
theorem foldl_recordVote {equivocating : List ValidatorIndex} {message : LatestMessage}
    (indices : List ValidatorIndex) (messages : Std.TreeMap ValidatorIndex LatestMessage)
    {i : ValidatorIndex} (voted : i ∈ indices) (honest : i ∉ equivocating) :
    ∃ m, (indices.foldl (recordVote equivocating message) messages)[i]? = some m ∧
      message.epoch ≤ m.epoch := by
  -- A vote at or after the epoch survives the rest of the run.
  have keep : ∀ (rest : List ValidatorIndex) (messages : Std.TreeMap ValidatorIndex LatestMessage)
      (old : LatestMessage), messages[i]? = some old → message.epoch ≤ old.epoch →
      ∃ m, (rest.foldl (recordVote equivocating message) messages)[i]? = some m ∧
        message.epoch ≤ m.epoch := by
    intro rest
    induction rest with
    | nil => exact fun messages old found late => ⟨old, found, late⟩
    | cons j rest ih =>
      intro messages old found late
      obtain ⟨m, found', late'⟩ :=
        recordVote_keeps (i := j) (equivocating := equivocating) found late
      exact ih _ m found' late'
  induction indices generalizing messages with
  | nil => cases voted
  | cons j rest ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp voted with rfl | voted
    · obtain ⟨m, found, late⟩ := recordVote_self (message := message) (messages := messages) honest
      exact keep rest _ m found late
    · exact ih _ voted

/-- After an attestation, each of its voters that does not equivocate has a recent vote.

That vote is at the target epoch of the attestation or later. -/
theorem onAttestation_voted {checks : SignatureChecks} {attestation : Attestation preset fork}
    {isFromBlock : Bool} {after : Store preset fork}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    ∃ targetState indexed, after.checkpointStates[attestation.data.target]? = some targetState ∧
      getIndexedAttestation targetState attestation = .ok indexed ∧
      ∀ i ∈ indexed.attestingIndices.data.toList, i ∉ after.equivocatingIndices →
        ∃ m, after.latestMessages[i]? = some m ∧ attestation.data.target.epoch ≤ m.epoch := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, _, targetState, found, indexed, mapped, valid, _, attested⟩ := attested
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    refine ⟨targetState, indexed, ?_, ?_, fun i voted honest => ?_⟩
    · unfold checkpointState at found
      split at found <;>
        simp_all [throw, throwThe, MonadExceptOf.throw, pure, Except.pure, updateLatestMessages]
    · cases g : getIndexedAttestation targetState attestation <;> simp_all [Except.mapError]
    · exact foldl_recordVote _ _ voted honest
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

end Store

end EthLib.Consensus
