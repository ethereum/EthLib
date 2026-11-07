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

At Deneb and Electra the node held its blobs, and their proofs matched its commitments.

From Fulu the node got every column that it samples, and each column was valid.

From Gloas the data comes with the payload, and the check of the block passes.

From Gloas a block that builds on the payload of its parent finds that payload verified.

At Bellatrix the first payload passes exactly when it follows a terminal block of proof of work.

A known block leaves the store as it was.

An attestation leaves each voter not marked as an equivocator a vote at its target epoch or later.

From Gloas the vote of an attestation on the payload passes exactly in the three allowed cases.

From Gloas a block also records whether it came before the votes of the payload committee.

A vote of the payload committee sets the votes of its validator at each of its positions.

Such a vote for another slot than its block's, or carried by a block at slot 0, changes nothing.

An accepted envelope had its data and passed its checks, and the store then keeps it.

Its payload then counts as verified, and nothing else changes.

From Gloas a block may fix the proposers of a slot when it is the head.

So may a block that a known block after the slot has as parent.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- Setting the votes at some positions leaves every other position as it was. -/
theorem setPtcVotes_get_of_not_mem {n : Nat} {votes : Vector (Option Bool) n}
    {positions : List (Fin n)} {value : Bool} {position : Fin n} (notMem : position ∉ positions) :
    (setPtcVotes votes positions value)[position] = votes[position] := by
  unfold setPtcVotes
  induction positions generalizing votes with
  | nil => rfl
  | cons p rest ih =>
    rw [List.foldl_cons, ih (fun h => notMem (List.mem_cons_of_mem _ h))]
    have other : p.val ≠ position.val := fun same => notMem (by simp [Fin.ext same])
    simp [Fin.getElem_fin, other]

/-- Setting the votes at some positions puts the value at each of them. -/
theorem setPtcVotes_get_of_mem {n : Nat} {votes : Vector (Option Bool) n}
    {positions : List (Fin n)} {value : Bool} {position : Fin n} (mem : position ∈ positions) :
    (setPtcVotes votes positions value)[position] = some value := by
  induction positions generalizing votes with
  | nil => cases mem
  | cons first rest ih =>
    by_cases later : position ∈ rest
    · exact ih later
    · obtain rfl : position = first := by simpa [later] using mem
      -- No later position writes this one again.
      have step : setPtcVotes votes (position :: rest) value =
          setPtcVotes (votes.set position.val (some value) position.isLt) rest value := rfl
      rw [step, setPtcVotes_get_of_not_mem later]
      simp [Fin.getElem_fin]

/-- The positions of a validator in a committee are the positions that hold it. -/
theorem mem_ptcPositions {committee : PayloadTimelinessCommittee preset}
    {validator : ValidatorIndex} {position : Fin preset.PTC_SIZE.toNat} :
    position ∈ ptcPositions committee validator ↔ committee[position] = validator := by
  simp [ptcPositions]

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

/-- The lookup of the state of a block succeeds exactly when the store holds it. -/
theorem blockState_ok_iff {root : Root} {state : BeaconState preset fork} :
    store.blockState root = .ok state ↔ store.blockStates[root]? = some state := by
  unfold blockState
  cases store.blockStates[root]? <;>
    simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

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
theorem storeTargetCheckpointState_frame {checks : SignatureChecks} {target : Checkpoint}
    {after : Store preset fork}
    (stored : store.storeTargetCheckpointState config checks target = .ok after) :
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
  simp only [bind_ok_iff, pure, Except.pure] at recorded
  obtain ⟨_, _, _, _, _, _, _, _, recorded⟩ := recorded
  split at recorded
  · simp only [bind_ok_iff, Except.ok.injEq] at recorded
    obtain ⟨_, _, rfl⟩ := recorded
    exact ⟨EpochsLe.of_eq (by rfl) (by rfl), rfl, rfl⟩
  · cases recorded
    exact ⟨EpochsLe.of_eq (by rfl) (by rfl), rfl, rfl⟩

/-- From Gloas a recorded block also gets whether it came before the payload committee's deadline.

That holds when the clock is in the block's slot, before the deadline of those votes. -/
theorem recordBlockTimeliness_ptc {root : Root} {after : Store preset fork}
    (gloas : .glamsterdam ≤ fork)
    (recorded : store.recordBlockTimeliness config root = .ok after) :
    ∃ block current time deadline, store.blocks[root]? = some block ∧
      store.getCurrentSlot config = .ok current ∧ store.getTimeIntoSlotMs config = .ok time ∧
      getPayloadAttestationDueMs config = .ok deadline ∧
      (after.ptcTimeliness gloas)[root]? =
        some (decide (current = block.slot ∧ time < deadline)) := by
  unfold recordBlockTimeliness at recorded
  simp only [bind_ok_iff, pure, Except.pure] at recorded
  obtain ⟨block, found, time, timeOk, _, _, current, currentOk, recorded⟩ := recorded
  simp only [gloas, ↓reduceDIte, bind_ok_iff, Except.ok.injEq, mapError_ok_iff] at recorded
  obtain ⟨deadline, deadlineOk, rfl⟩ := recorded
  exact ⟨block, current, time, deadline, block_ok_iff.mp found, currentOk, timeOk, deadlineOk,
    by simp⟩

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

/-- The store changes at most in its two vote maps of the payload committee. -/
def OnlyPtcVotes (before after : Store preset fork) : Prop :=
  ∃ timeliness availability, after = { before with
    payloadTimelinessVote := timeliness, payloadDataAvailabilityVote := availability }

theorem OnlyPtcVotes.refl (store : Store preset fork) : OnlyPtcVotes store store :=
  ⟨store.payloadTimelinessVote, store.payloadDataAvailabilityVote, rfl⟩

theorem OnlyPtcVotes.trans {a b c : Store preset fork} (ab : OnlyPtcVotes a b)
    (bc : OnlyPtcVotes b c) : OnlyPtcVotes a c := by
  obtain ⟨_, _, rfl⟩ := ab
  obtain ⟨t, v, rfl⟩ := bc
  exact ⟨t, v, rfl⟩

/-- A store that changes only in its votes keeps its checkpoints, blocks and states. -/
theorem OnlyPtcVotes.frame {a b : Store preset fork} (only : OnlyPtcVotes a b) :
    a.EpochsLe b ∧ b.blocks = a.blocks ∧ b.blockStates = a.blockStates := by
  obtain ⟨_, _, rfl⟩ := only
  exact ⟨EpochsLe.refl _, rfl, rfl⟩

/-- Recording the votes of a payload vote changes only the vote maps. -/
theorem recordPtcVotes_onlyPtcVotes {gloas : .glamsterdam ≤ fork}
    {data : PayloadAttestationData} {positions : List (Fin preset.PTC_SIZE.toNat)}
    {after : Store preset fork}
    (recorded : store.recordPtcVotes gloas data positions = .ok after) :
    OnlyPtcVotes store after := by
  unfold recordPtcVotes at recorded
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at recorded
  obtain ⟨_, _, _, _, rfl⟩ := recorded
  exact ⟨_, _, rfl⟩

/-- A vote of the payload committee changes only the vote maps. -/
theorem onPayloadAttestationMessage_onlyPtcVotes {checks : SignatureChecks}
    {gloas : .glamsterdam ≤ fork} {message : PayloadAttestationMessage} {isFromBlock : Bool}
    {after : Store preset fork}
    (accepted : store.onPayloadAttestationMessage config checks gloas message isFromBlock =
      .ok after) :
    OnlyPtcVotes store after := by
  unfold onPayloadAttestationMessage at accepted
  simp only [bind_ok_iff] at accepted
  obtain ⟨_, _, accepted⟩ := accepted
  split at accepted
  · simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst accepted
    exact .refl _
  · simp only [bind_ok_iff] at accepted
    obtain ⟨_, _, _, _, accepted⟩ := accepted
    -- Both kinds of vote end with the same record of the votes.
    cases isFromBlock
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at accepted
      obtain ⟨_, -, accepted⟩ := accepted
      exact recordPtcVotes_onlyPtcVotes accepted
    · exact recordPtcVotes_onlyPtcVotes (by simpa using accepted)

/-- The votes of the payload committee that a block carries change only the vote maps. -/
theorem notifyPtcMessages_onlyPtcVotes {checks : SignatureChecks}
    {gloas : .glamsterdam ≤ fork} {state : BeaconState preset fork}
    {attestations : List (PayloadAttestation preset)} {after : Store preset fork}
    (notified : store.notifyPtcMessages config checks gloas state attestations = .ok after) :
    OnlyPtcVotes store after := by
  unfold notifyPtcMessages at notified
  split at notified
  · simp only [pure, Except.pure, Except.ok.injEq] at notified
    subst notified
    exact .refl _
  · refine foldlM_ok_invariant (OnlyPtcVotes store) (fun other attestation next held step => ?_)
      (.refl _) notified
    simp only [bind_ok_iff] at step
    obtain ⟨_, _, step⟩ := step
    exact foldlM_ok_invariant (OnlyPtcVotes store) (fun _ _ _ held step =>
      held.trans (onPayloadAttestationMessage_onlyPtcVotes step)) held step

/-- The votes of the payload committee on a new block change only the vote maps. -/
theorem recordBlockPtcVotes_onlyPtcVotes {checks : SignatureChecks}
    {signed : SignedBeaconBlock preset fork} {blockRoot : Root}
    {state : BeaconState preset fork} {after : Store preset fork}
    (recorded : store.recordBlockPtcVotes config checks signed blockRoot state = .ok after) :
    OnlyPtcVotes store after := by
  unfold recordBlockPtcVotes at recorded
  split at recorded
  · dsimp only at recorded
    exact (OnlyPtcVotes.trans ⟨_, _, rfl⟩ (notifyPtcMessages_onlyPtcVotes recorded))
  · simp only [pure, Except.pure, Except.ok.injEq] at recorded
    subst recorded
    exact .refl _

/-- Before Gloas a block holds its own payload, and the check of its parent's payload passes. -/
theorem validateParentPayload_of_lt {block : BeaconBlock preset fork}
    (before : fork < .glamsterdam) : store.validateParentPayload block = .ok () := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp [validateParentPayload, later, pure, Except.pure]

/-- From Gloas the check passes exactly when the store holds the parent.

A block that builds on the payload of its parent must also find that payload verified. -/
theorem validateParentPayload_ok_iff {block : BeaconBlock preset fork}
    (gloas : .glamsterdam ≤ fork) :
    store.validateParentPayload block = .ok () ↔
      ∃ parent, store.blocks[block.parentRoot]? = some parent ∧
        (parentPayloadStatus block parent = .full →
          store.isPayloadVerified gloas block.parentRoot = true) := by
  unfold validateParentPayload isParentNodeFull getParentPayloadStatus
  cases found : store.blocks[block.parentRoot]? with
  | none =>
    simp [gloas, Store.block, found, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  | some parent =>
    cases verified : store.isPayloadVerified gloas block.parentRoot <;>
      by_cases full : parentPayloadStatus block parent = .full <;>
      simp [gloas, Store.block, found, verified, full, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw]

/-- A new block that passes the checks has a known parent, and its data is available.

From Gloas the payload of its parent passed its check.

Its state is the one that the state transition computes from the parent's. -/
theorem validateOnBlock_ok {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    {blockRoot : Root} {state : BeaconState preset fork}
    (valid : store.validateOnBlock config checks sources signed blockRoot = .ok state) :
    ∃ pre, store.blockStates[signed.message.parentRoot]? = some pre ∧
      store.validateParentPayload signed.message = .ok () ∧
      validateDataAvailability config sources signed.message blockRoot = .ok () ∧
      stateTransition config checks sources.engine pre signed true = .ok state := by
  unfold validateOnBlock at valid
  dsimp only at valid
  cases found : store.blockStates[signed.message.parentRoot]? with
  | none =>
    simp [blockState, found, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at valid
  | some pre =>
    simp only [blockState, found, bind_ok_iff] at valid
    obtain ⟨a, ha, checked, parent, _, _, valid⟩ := valid
    cases checked
    refine ⟨pre, rfl, parent, ?_⟩
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

/-- From Gloas the data comes with the payload, so the check of a block passes. -/
theorem validateDataAvailability_of_gloas {sources : BlockSources preset fork}
    {block : BeaconBlock preset fork} {blockRoot : Root} (gloas : .glamsterdam ≤ fork) :
    validateDataAvailability config sources block blockRoot = .ok () := by
  simp [validateDataAvailability, gloas, pure, Except.pure]

/-- Before Deneb a block has no blobs, and the check of their availability passes. -/
theorem validateDataAvailability_of_lt {sources : BlockSources preset fork}
    {block : BeaconBlock preset fork} {blockRoot : Root} (before : fork < .dencun) :
    validateDataAvailability config sources block blockRoot = .ok () := by
  have early : ¬ .dencun ≤ fork := Nat.not_le_of_lt before
  have later : ¬ .glamsterdam ≤ fork := fun gloas => early (Nat.le_trans (by decide) gloas)
  simp [validateDataAvailability, early, later, pure, Except.pure]

/-- At Deneb and Electra, the check passes exactly when the node holds the blobs and proofs.

The proofs must also show that the blobs match the commitments of the block. -/
theorem validateDataAvailability_ok {sources : BlockSources preset fork}
    {block : BeaconBlock preset fork} {blockRoot : Root}
    (deneb : .dencun ≤ fork) (before : fork < .fusaka) :
    validateDataAvailability config sources block blockRoot = .ok () ↔
      ∃ blobs proofs, sources.blobsAndProofs blockRoot = some (blobs, proofs) ∧
        Cryptography.Kzg.verifyBlobKzgProofBatch sources.setup blobs
          (block.body.blobKzgCommitments ⟨deneb, Nat.lt_trans before (by decide)⟩).data proofs =
          .ok true := by
  have fulu : ¬ .fusaka ≤ fork := Nat.not_le_of_lt before
  have gloas : ¬ .glamsterdam ≤ fork := fun later => fulu (Nat.le_trans (by decide) later)
  unfold validateDataAvailability isDataAvailable
  cases found : sources.blobsAndProofs blockRoot with
  | none => simp [fulu, gloas, deneb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  | some data =>
    obtain ⟨blobs, proofs⟩ := data
    cases verified : Cryptography.Kzg.verifyBlobKzgProofBatch sources.setup blobs
        (block.body.blobKzgCommitments ⟨deneb, Nat.lt_trans before (by decide)⟩).data proofs with
    | error e => simp_all [bind, Except.bind, Except.mapError]
    | ok result =>
      cases result
      · simp_all [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, Except.mapError]
      · refine iff_of_true ?_ ⟨blobs, proofs, rfl, verified⟩
        simp [fulu, gloas, deneb, verified, bind, Except.bind, Except.mapError, pure, Except.pure]

/-- A check of each item of a list returns true exactly when each item returns true. -/
private theorem allM_ok_true {ε α : Type} {f : α → Except ε Bool} :
    ∀ l : List α, l.allM f = .ok true ↔ ∀ x ∈ l, f x = .ok true
  | [] => by simp [pure, Except.pure]
  | a :: l => by
    rw [List.allM_cons]
    cases h : f a with
    | error e => simp [h, bind, Except.bind]
    | ok b =>
      cases b
      · simp [h, bind, Except.bind, pure, Except.pure]
      · simp [h, bind, Except.bind, allM_ok_true l]

/-- A check that fails with an error unless a test returns true passes exactly then. -/
private theorem unless_ok_iff {ε : Type} {test : Except ε Bool} {e : ε} :
    (do unless (← test) do throw e : Except ε Unit) = .ok () ↔ test = .ok true := by
  cases test with
  | error _ => simp [bind, Except.bind]
  | ok b => cases b <;> simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
      Except.pure]

/-- The columns are available exactly when the node gets every column that it samples.

Each column must have a valid shape, and the proofs of its cells must match the commitments. -/
theorem columnsAvailable_ok_iff {sources : BlockSources preset fork} {root : Root}
    {bidCommitments : Since .glamsterdam fork (BlobKZGCommitments preset fork)} :
    columnsAvailable config sources root bidCommitments = .ok true ↔
      ∃ sidecars, sources.columns root = some sidecars ∧ ∀ sidecar ∈ sidecars,
        verifyDataColumnSidecar preset config sidecar bidCommitments = true ∧
          verifyDataColumnSidecarKzgProofs sources.setup sidecar bidCommitments = .ok true := by
  unfold columnsAvailable
  cases found : sources.columns root with
  | none => simp [throw, throwThe, MonadExceptOf.throw]
  | some sidecars =>
    simp only [Option.some.injEq, exists_eq_left', ← Array.allM_toList]
    -- One column passes exactly when its shape is valid and its proofs match.
    have each : ∀ sidecar : DataColumnSidecar preset fork,
        (if verifyDataColumnSidecar preset config sidecar bidCommitments then
          (verifyDataColumnSidecarKzgProofs sources.setup sidecar bidCommitments).mapError
            ForkChoiceError.kzg
        else pure false) = .ok true ↔
        verifyDataColumnSidecar preset config sidecar bidCommitments = true ∧
          verifyDataColumnSidecarKzgProofs sources.setup sidecar bidCommitments = .ok true := by
      intro sidecar
      split
      · cases verifyDataColumnSidecarKzgProofs sources.setup sidecar bidCommitments <;>
          simp_all [Except.mapError]
      · simp_all [pure, Except.pure]
    rw [allM_ok_true]
    exact ⟨fun all sidecar mem => (each sidecar).mp (all sidecar (Array.mem_toList_iff.mpr mem)),
      fun valid sidecar mem => (each sidecar).mpr (valid sidecar (Array.mem_toList_iff.mp mem))⟩

/-- At Fulu, the check passes exactly when the node gets every column that it samples.

Each column must have a valid shape, and the proofs of its cells must match its commitments. -/
theorem validateDataAvailability_ok_of_fulu {sources : BlockSources preset fork}
    {block : BeaconBlock preset fork} {blockRoot : Root}
    (fulu : .fusaka ≤ fork) (before : fork < .glamsterdam) :
    validateDataAvailability config sources block blockRoot = .ok () ↔
      ∃ sidecars, sources.columns blockRoot = some sidecars ∧ ∀ sidecar ∈ sidecars,
        verifyDataColumnSidecar preset config sidecar
            (fun gloas => absurd gloas (not_glamsterdam_le before)) = true ∧
          verifyDataColumnSidecarKzgProofs sources.setup sidecar
            (fun gloas => absurd gloas (not_glamsterdam_le before)) = .ok true := by
  have deneb : .dencun ≤ fork := Nat.le_trans (by decide) fulu
  have gloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  unfold validateDataAvailability isDataAvailable
  simp only [gloas, deneb, fulu, dite_false, dite_true, ite_true]
  rw [unless_ok_iff]
  exact columnsAvailable_ok_iff

/-- From Gloas the data of a payload is available exactly when each sampled column is valid.

The commitments are those of the bid. -/
theorem validatePayloadData_ok_iff {sources : BlockSources preset fork} {root : Root}
    {bid : ExecutionPayloadBid preset fork} :
    validatePayloadData config sources root bid = .ok () ↔
      ∃ sidecars, sources.columns root = some sidecars ∧ ∀ sidecar ∈ sidecars,
        verifyDataColumnSidecar preset config sidecar (fun _ => bid.blobKzgCommitments) = true ∧
          verifyDataColumnSidecarKzgProofs sources.setup sidecar
            (fun _ => bid.blobKzgCommitments) = .ok true := by
  unfold validatePayloadData
  rw [unless_ok_iff]
  exact columnsAvailable_ok_iff

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
  obtain ⟨a, ha, _, _, _, _, valid⟩ := valid
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
  obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
  obtain ⟨le0, b0, bs0⟩ := (recordBlockPtcVotes_onlyPtcVotes vote).frame
  obtain ⟨le1, b1, bs1⟩ := recordBlockTimeliness_frame record
  obtain ⟨le2, b2, bs2⟩ := updateProposerBoostRoot_frame boost
  obtain ⟨le3, b3, bs3⟩ := computePulledUpTip_frame added
  refine ⟨((EpochsLe.of_eq rfl rfl).trans (le0.trans (le1.trans le2))).trans
    ((updateCheckpoints_epochsLe _ _).trans le3), ?_, ?_⟩
  · rw [b3, updateCheckpoints_blocks, b2, b1, b0]
    simp
  · obtain ⟨pre, found, -, -, transition⟩ := validateOnBlock_ok valid
    refine ⟨pre, state, found, transition, ?_⟩
    rw [bs3, updateCheckpoints_blockStates, bs2, bs1, bs0]
    simp

/-- A block that the store holds already leaves the store as it was. -/
theorem onBlock_known {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    {blockRoot : Root} (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (known : store.blocks.contains blockRoot) :
    store.onBlock config checks sources signed = .ok store := by
  simp [onBlock, root, known, bind, Except.bind, Except.mapError, pure, Except.pure]

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
  simp only [onBlock, root, new, bind, Except.bind, Except.mapError, ↓reduceIte,
    Bool.false_eq_true] at added
  exact addBlock_ok added

/-- A new block enters the store at its root, with the state that the transition computes for it.

No other block and no other state changes. -/
theorem onBlock_insert {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    {blockRoot : Root} {after : Store preset fork}
    (root : SszType.hashTreeRoot signed.message = .ok blockRoot)
    (new : ¬ store.blocks.contains blockRoot)
    (added : store.onBlock config checks sources signed = .ok after) :
    after.blocks = store.blocks.insert blockRoot signed.message ∧
      ∃ pre state, store.blockStates[signed.message.parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre signed true = .ok state ∧
        after.blockStates = store.blockStates.insert blockRoot state := by
  simp only [onBlock, root, new, bind, Except.bind, Except.mapError, ↓reduceIte,
    Bool.false_eq_true] at added
  unfold addBlock at added
  simp only [bind_ok_iff] at added
  obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
  obtain ⟨-, b0, bs0⟩ := (recordBlockPtcVotes_onlyPtcVotes vote).frame
  obtain ⟨-, b1, bs1⟩ := recordBlockTimeliness_frame record
  obtain ⟨-, b2, bs2⟩ := updateProposerBoostRoot_frame boost
  obtain ⟨-, b3, bs3⟩ := computePulledUpTip_frame added
  obtain ⟨pre, found, -, -, transition⟩ := validateOnBlock_ok valid
  refine ⟨by rw [b3, updateCheckpoints_blocks, b2, b1, b0], pre, state, found, transition, ?_⟩
  rw [bs3, updateCheckpoints_blockStates, bs2, bs1, bs0]

/-- No block lowers the epoch of the justified or the finalized checkpoint. -/
theorem onBlock_epochsLe {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork}
    {after : Store preset fork} (added : store.onBlock config checks sources signed = .ok after) :
    store.EpochsLe after := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e => simp [onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [onBlock_known root known] at added
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

/-- A vote keeps every other vote at or after its rank at or after it. -/
theorem recordVote_keeps {equivocating : List ValidatorIndex} {message : LatestMessage fork}
    {messages : Std.TreeMap ValidatorIndex (LatestMessage fork)} {i j : ValidatorIndex}
    {old : LatestMessage fork}
    (found : messages[j]? = some old) (late : message.rank ≤ old.rank) :
    ∃ m, (recordVote equivocating message messages i)[j]? = some m ∧ message.rank ≤ m.rank := by
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

/-- After the vote of a validator that does not equivocate, its vote is at or after the rank. -/
theorem recordVote_self {equivocating : List ValidatorIndex} {message : LatestMessage fork}
    {messages : Std.TreeMap ValidatorIndex (LatestMessage fork)} {i : ValidatorIndex}
    (honest : i ∉ equivocating) :
    ∃ m, (recordVote equivocating message messages i)[i]? = some m ∧ message.rank ≤ m.rank := by
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

/-- After a run of votes, each voter that does not equivocate has a vote at or after the rank. -/
theorem foldl_recordVote {equivocating : List ValidatorIndex} {message : LatestMessage fork}
    (indices : List ValidatorIndex) (messages : Std.TreeMap ValidatorIndex (LatestMessage fork))
    {i : ValidatorIndex} (voted : i ∈ indices) (honest : i ∉ equivocating) :
    ∃ m, (indices.foldl (recordVote equivocating message) messages)[i]? = some m ∧
      message.rank ≤ m.rank := by
  -- A vote at or after the rank survives the rest of the run.
  have keep : ∀ (rest : List ValidatorIndex)
      (messages : Std.TreeMap ValidatorIndex (LatestMessage fork))
      (old : LatestMessage fork), messages[i]? = some old → message.rank ≤ old.rank →
      ∃ m, (rest.foldl (recordVote equivocating message) messages)[i]? = some m ∧
        message.rank ≤ m.rank := by
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

That vote is at the rank of the attestation's vote or later.

Its rank is the target epoch before Gloas, and the slot of the attestation from Gloas. -/
theorem onAttestation_voted {checks : SignatureChecks} {attestation : Attestation preset fork}
    {isFromBlock : Bool} {after : Store preset fork}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    ∃ targetState indexed, after.checkpointStates[attestation.data.target]? = some targetState ∧
      getIndexedAttestation targetState attestation = .ok indexed ∧
      ∀ i ∈ indexed.attestingIndices.data.toList, i ∉ after.equivocatingIndices →
        ∃ m, after.latestMessages[i]? = some m ∧
          (LatestMessage.ofAttestation attestation).rank ≤ m.rank := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, _, targetState, found, indexed, mapped, valid, _, attested⟩ := attested
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    refine ⟨targetState, indexed, ?_, ?_, fun i voted honest => ?_⟩
    · simpa [updateLatestMessages] using checkpointState_ok_iff.mp found
    · cases g : getIndexedAttestation targetState attestation <;> simp_all [Except.mapError]
    · exact foldl_recordVote _ _ voted honest
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

/-- From Gloas the vote of an attestation on the payload passes exactly in three cases.

Its index is 0 or 1, it is 0 in the slot of the block, and 1 only with a verified payload. -/
theorem validatePayloadVote_ok_iff {gloas : .glamsterdam ≤ fork}
    {attestation : Attestation preset fork} {voted : BeaconBlock preset fork} :
    store.validatePayloadVote gloas attestation voted = .ok () ↔
      (attestation.data.index = 0 ∨ attestation.data.index = 1) ∧
      (voted.slot = attestation.data.slot → attestation.data.index = 0) ∧
      (attestation.data.index = 1 →
        store.isPayloadVerified gloas attestation.data.beaconBlockRoot = true) := by
  unfold validatePayloadVote
  dsimp only
  have failed : ∀ {e : ForkChoiceError}, (throw e : Except ForkChoiceError Unit) ≠ .ok () :=
    fun h => by simp [throw, throwThe, MonadExceptOf.throw] at h
  split
  next bad =>
    refine ⟨fun h => absurd h failed, fun ⟨range, _⟩ => ?_⟩
    rcases range with zero | one
    · exact absurd zero bad.1
    · exact absurd one bad.2
  next bad =>
  split
  next same => exact ⟨fun h => absurd h failed, fun ⟨_, zero, _⟩ => absurd (zero same.1) same.2⟩
  next same =>
  split
  next unverified =>
    refine ⟨fun h => absurd h failed, fun ⟨_, _, verified⟩ => ?_⟩
    have notVerified := unverified.2
    rw [verified unverified.1] at notVerified
    exact absurd notVerified (by decide)
  next unverified =>
  refine ⟨fun _ => ⟨?_, fun slot => ?_, fun one => ?_⟩, fun _ => rfl⟩
  · exact Classical.byContradiction fun range =>
      bad ⟨fun h => range (.inl h), fun h => range (.inr h)⟩
  · exact Classical.byContradiction fun ne => same ⟨slot, ne⟩
  · cases verified : store.isPayloadVerified gloas attestation.data.beaconBlockRoot
    · exact absurd ⟨one, by simp [verified]⟩ unverified
    · rfl

/-- A vote of the payload committee for another slot than its block's changes nothing. -/
theorem onPayloadAttestationMessage_of_other_slot {checks : SignatureChecks}
    {gloas : .glamsterdam ≤ fork} {message : PayloadAttestationMessage} {isFromBlock : Bool}
    {state : BeaconState preset fork}
    (found : store.blockStates[message.data.beaconBlockRoot]? = some state)
    (other : message.data.slot ≠ state.slot) :
    store.onPayloadAttestationMessage config checks gloas message isFromBlock = .ok store := by
  simp [onPayloadAttestationMessage, blockState, found, other, bind, Except.bind, pure,
    Except.pure]

/-- A vote of the payload committee from a block does not read the signature checks. -/
theorem onPayloadAttestationMessage_from_block {checks checks' : SignatureChecks}
    {gloas : .glamsterdam ≤ fork} {message : PayloadAttestationMessage} :
    store.onPayloadAttestationMessage config checks gloas message true =
      store.onPayloadAttestationMessage config checks' gloas message true := by
  simp [onPayloadAttestationMessage]

/-- An accepted vote of the payload committee for the slot of its block sets its votes.

The validator holds at least one position in the committee of that slot.

At each of its positions, the store then holds both values of the vote for that block. -/
theorem onPayloadAttestationMessage_votes {checks : SignatureChecks}
    {gloas : .glamsterdam ≤ fork} {message : PayloadAttestationMessage} {isFromBlock : Bool}
    {state : BeaconState preset fork} {after : Store preset fork}
    (found : store.blockStates[message.data.beaconBlockRoot]? = some state)
    (same : message.data.slot = state.slot)
    (accepted : store.onPayloadAttestationMessage config checks gloas message isFromBlock =
      .ok after) :
    ∃ ptc timeliness availability, getPtc config state gloas message.data.slot = .ok ptc ∧
      ptcPositions ptc message.validatorIndex ≠ [] ∧
      (after.payloadTimelinessVote gloas)[message.data.beaconBlockRoot]? = some timeliness ∧
      (after.payloadDataAvailabilityVote gloas)[message.data.beaconBlockRoot]? =
        some availability ∧
      ∀ position ∈ ptcPositions ptc message.validatorIndex,
        timeliness[position] = some message.data.payloadPresent ∧
        availability[position] = some message.data.blobDataAvailable := by
  unfold onPayloadAttestationMessage at accepted
  rw [bind_ok_iff] at accepted
  obtain ⟨_, stateOk, accepted⟩ := accepted
  rw [blockState_ok_iff, found, Option.some.injEq] at stateOk
  subst stateOk
  simp only [same, ne_eq, not_true_eq_false, ↓reduceIte, bind_ok_iff, mapError_ok_iff] at accepted
  obtain ⟨ptc, ptcOk, first, firstOk, accepted⟩ := accepted
  have nonempty : ptcPositions ptc message.validatorIndex ≠ [] := by
    intro empty
    simp [empty, throw, throwThe, MonadExceptOf.throw] at firstOk
  -- Both kinds of vote end with the same record of the votes.
  replace accepted :
      store.recordPtcVotes gloas message.data (ptcPositions ptc message.validatorIndex) =
        .ok after := by
    cases isFromBlock
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at accepted
      obtain ⟨_, -, accepted⟩ := accepted
      exact accepted
    · simpa using accepted
  unfold recordPtcVotes at accepted
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨timeliness, -, availability, -, rfl⟩ := accepted
  refine ⟨ptc, setPtcVotes timeliness (ptcPositions ptc message.validatorIndex)
    message.data.payloadPresent, setPtcVotes availability
    (ptcPositions ptc message.validatorIndex) message.data.blobDataAvailable,
    same ▸ ptcOk, nonempty, by simp, by simp, fun position mem =>
    ⟨setPtcVotes_get_of_mem mem, setPtcVotes_get_of_mem mem⟩⟩

/-- The votes of the payload committee in a block change nothing at slot 0. -/
theorem notifyPtcMessages_of_zero {checks : SignatureChecks} {gloas : .glamsterdam ≤ fork}
    {state : BeaconState preset fork} {attestations : List (PayloadAttestation preset)}
    (zero : state.slot = 0) :
    store.notifyPtcMessages config checks gloas state attestations = .ok store := by
  simp [notifyPtcMessages, zero, pure, Except.pure]

/-- An accepted envelope names a block whose state the store holds.

The data of the payload is available against the bid in that state.

The envelope passes its checks against that state.

From Heze the store then records whether the payload satisfied its inclusion lists.

The store then keeps the envelope at the root of its block, and nothing else changes. -/
theorem onExecutionPayloadEnvelope_ok {checks : SignatureChecks}
    {sources : BlockSources preset fork} {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork} {after : Store preset fork}
    (accepted : store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after) :
    ∃ state, store.blockStates[signed.message.beaconBlockRoot]? = some state ∧
      validatePayloadData config sources signed.message.beaconBlockRoot
        (state.latestExecutionPayloadBid gloas) = .ok () ∧
      verifyExecutionPayloadEnvelope config checks sources.engine state gloas signed = .ok () ∧
      ∃ recorded, store.recordEnvelope sources signed.message.beaconBlockRoot
          signed.message.payload = .ok recorded ∧
        after = { recorded with payloads := fun _ =>
          (recorded.payloads gloas).insert signed.message.beaconBlockRoot signed.message } := by
  unfold onExecutionPayloadEnvelope at accepted
  simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨state, found, available, data, checked, verified, recorded, record, rfl⟩ := accepted
  cases available
  cases checked
  exact ⟨state, blockState_ok_iff.mp found, data, verified, recorded, record, rfl⟩

/-- After an accepted envelope, the payload of its block counts as verified. -/
theorem onExecutionPayloadEnvelope_verified {checks : SignatureChecks}
    {sources : BlockSources preset fork} {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork} {after : Store preset fork}
    (accepted : store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after) :
    after.isPayloadVerified gloas signed.message.beaconBlockRoot = true := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
  simp [isPayloadVerified]

/-- From Heze: after an accepted envelope, the store holds the answer of the execution layer.

The answer is for the payload and the timely transactions of the slot before its block.

They are those of the dependent root of that slot, on the chain of the block. -/
theorem onExecutionPayloadEnvelope_inclusionListSatisfied {checks : SignatureChecks}
    {sources : BlockSources preset fork} {gloas : .glamsterdam ≤ fork} (heze : .hegota ≤ fork)
    {signed : SignedExecutionPayloadEnvelope preset fork} {after : Store preset fork}
    (accepted : store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after) :
    ∃ block slot dependentRoot, store.blocks[signed.message.beaconBlockRoot]? = some block ∧
      subChecked block.slot 1 = .ok slot ∧
      store.getShufflingDependentRoot signed.message.beaconBlockRoot
        (computeEpochAtSlot preset slot) = .ok dependentRoot ∧
      after.isPayloadInclusionListSatisfied heze signed.message.beaconBlockRoot =
        .ok (sources.inclusionListSatisfied signed.message.payload
          ((store.inclusionLists heze).transactions slot dependentRoot true)) := by
  obtain ⟨_, _, _, _, recorded, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
  simp only [recordEnvelope, heze, dite_true, recordPayloadInclusionListSatisfaction, Store.block,
    bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at record
  obtain ⟨block, found, slot, sub, dependentRoot, dependent, rfl⟩ := record
  refine ⟨block, slot, dependentRoot, ?_, sub, dependent, ?_⟩
  · revert found
    split <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  · simp [isPayloadInclusionListSatisfied, isPayloadVerified, pure, Except.pure]

/-- From Heze: an inclusion list that passes its checks passed those of its sender.

Its dependent block may fix the committee of its slot, and that block's state is known.

In that state, advanced to the start of the lookahead, its sender sits on the committee.

The sender signed it with its key in that state. -/
theorem checkInclusionList_ok {checks : SignatureChecks} {signed : SignedInclusionList}
    {timely : Bool} (passed : store.checkInclusionList config checks signed = .ok timely) :
    ∃ dependentSlot start dependentState state committee,
      computeShufflingDependentSlot preset (computeEpochAtSlot preset signed.message.slot) =
        .ok dependentSlot ∧
      store.isValidDependentRoot config signed.message.dependentRoot dependentSlot = .ok true ∧
      store.blockStates[signed.message.dependentRoot]? = some dependentState ∧
      computeShufflingLookaheadStartSlot preset (computeEpochAtSlot preset signed.message.slot) =
        .ok start ∧
      lookaheadState config checks dependentState start = .ok state ∧
      getInclusionListCommittee state signed.message.slot = .ok committee ∧
      signed.message.validatorIndex ∈ committee.toList ∧
      isValidInclusionListSignature config state signed = .ok true := by
  unfold checkInclusionList at passed
  simp only [bind_ok_iff, mapError_ok_iff, ensure_ok_iff] at passed
  obtain ⟨_, -, -, -, _, -, -, -, -, -, -, -, _, -, dependentState, held, dependentSlot, dependent,
    -, -, possible, checked, -, rfl, start, started, state, advanced, committee, made, -, seated,
    valid, signature, _, isValid, -⟩ := passed
  subst isValid
  exact ⟨dependentSlot, start, dependentState, state, committee, dependent, checked,
    blockState_ok_iff.mp held, started, advanced, made, seated, signature⟩

/-- From Heze: an accepted inclusion list passed its checks, and the store then keeps it.

Nothing else in the store changes. -/
theorem onInclusionList_ok {checks : SignatureChecks} (heze : .hegota ≤ fork)
    {signed : SignedInclusionList} {after : Store preset fork}
    (accepted : store.onInclusionList config checks heze signed = .ok after) :
    ∃ timely, store.checkInclusionList config checks signed = .ok timely ∧
      after = { store with inclusionLists := fun _ =>
        (store.inclusionLists heze).process signed timely } := by
  unfold onInclusionList at accepted
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨timely, checked, rfl⟩ := accepted
  exact ⟨timely, checked, rfl⟩

/-- Recording an envelope changes at most the answers on the inclusion lists. -/
theorem recordEnvelope_frame {sources : BlockSources preset fork} {root : Root}
    {payload : ExecutionPayload preset fork} {recorded : Store preset fork}
    (record : store.recordEnvelope sources root payload = .ok recorded) :
    ∃ satisfaction, recorded = { store with payloadInclusionListSatisfaction := satisfaction } := by
  unfold recordEnvelope at record
  split at record
  · unfold recordPayloadInclusionListSatisfaction at record
    simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at record
    obtain ⟨_, _, _, _, _, _, rfl⟩ := record
    exact ⟨_, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at record
    exact ⟨_, record.symm⟩

/-- An accepted envelope lowers no epoch, and keeps the blocks and their states. -/
theorem onExecutionPayloadEnvelope_frame {checks : SignatureChecks}
    {sources : BlockSources preset fork} {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork} {after : Store preset fork}
    (accepted : store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after) :
    store.EpochsLe after ∧ after.blocks = store.blocks ∧ after.blockStates = store.blockStates := by
  obtain ⟨_, _, _, _, _, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
  obtain ⟨_, rfl⟩ := recordEnvelope_frame record
  exact ⟨EpochsLe.refl _, rfl, rfl⟩

/-- From Heze: an accepted inclusion list lowers no epoch, and keeps the blocks and their states. -/
theorem onInclusionList_frame {checks : SignatureChecks} {heze : .hegota ≤ fork}
    {signed : SignedInclusionList} {after : Store preset fork}
    (accepted : store.onInclusionList config checks heze signed = .ok after) :
    store.EpochsLe after ∧ after.blocks = store.blocks ∧ after.blockStates = store.blockStates := by
  obtain ⟨_, _, rfl⟩ := onInclusionList_ok heze accepted
  exact ⟨EpochsLe.refl _, rfl, rfl⟩

/-- From Gloas: the rule for a possible dependent block, once the head is computed.

A block may be the last one at or before a slot when it is the head.

It may also be when a known block after the slot has it as parent.

The rule fails exactly when the head fails. -/
theorem isValidDependentRoot_ok_iff {root : Root} {dependentSlot : Slot} {possible : Bool} :
    store.isValidDependentRoot config root dependentSlot = .ok possible ↔
      ∃ head, store.getHead config = .ok head ∧
        (possible = true ↔ root = head.root ∨ ∃ childRoot : Root, ∃ child : BeaconBlock preset fork,
          store.blocks[childRoot]? = some child ∧ child.parentRoot = root ∧
            dependentSlot < child.slot) := by
  unfold isValidDependentRoot
  cases headOk : store.getHead config with
  | error e => simp [bind, Except.bind]
  | ok head =>
    simp only [bind, Except.bind, Except.ok.injEq, exists_eq_left']
    split
    · rename_i isHead
      cases possible <;> simp [pure, Except.pure, isHead]
    · rename_i isHead
      cases possible <;> simp [pure, Except.pure, isHead, List.any_eq_true,
        Std.TreeMap.mem_toList_iff_getElem?_eq_some]

end Store

end EthLib.Consensus
