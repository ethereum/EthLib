module

public import EthLib.Consensus.HonestAggregation
public import EthLib.Consensus.Proofs.ForkChoice.Network
import EthLib.Consensus.Proofs.HonestAggregation
import EthLib.Consensus.Proofs.Signing

/-!
# Proofs: the duties of honest validators that run the fork choice

The model is that of the fast confirmation paper, §2 of
[arXiv 2405.00549v4](https://arxiv.org/abs/2405.00549v4).

A validator in the committee of a slot casts one vote in that slot, for the head of its view.

Honest validators never sign votes that can be slashed together.

Here the votes are the attestations of the fork choice.

A vote signs its data for each validator that a store reads in its bits.

A store reads them in the state of the target of the vote, with a valid signature.

A store reachable from the anchor may read an attestation, and all of its readings count.

So two stores read the same signers, unless they hold two states for one checkpoint.

An attester slashing signs the data of its two votes for each of their validators.

A block signs what its attestations and attester slashings sign.

An honest validator signs a vote of its own only as its duty allows.

It votes at the attestation deadline of a slot of its assignment, with an up-to-date store.

The vote holds the data that the guide of the honest validator builds from the head.

It cannot be slashed together with a vote of the validator that its view holds.

The assignment of validators to slots is a parameter, shared by honest validators.

The paper shares it too once GST has passed long enough.

The duty to vote is a condition on an execution, and the paper asks it of every slot.

So an execution with that duty never asks for a vote that slashing protection forbids.

The paper assumes that as well: an honest validator votes in each of its slots, never slashable.

A signature of a block by its proposer is no statement here, so any validator may send any block.

That only strengthens the adversary.

Each honest vote then reaches every honest validator before the next slot, under synchrony.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} (config : Config) (checks : SignatureChecks)
  (sources : BlockSources preset fork)

/-- A store reads an attestation as an indexed attestation, as its handler of attestations does.

The store takes the state of the target, and reads the indices that the bits name there.

The indexed attestation must be valid there, signature included. -/
def ReadsVote (store : Store preset fork) (attestation : Attestation preset fork)
    (indexed : IndexedAttestation preset fork) : Prop :=
  ∃ withTarget targetState,
    store.storeTargetCheckpointState config checks attestation.data.target = .ok withTarget ∧
      withTarget.checkpointState attestation.data.target = .ok targetState ∧
      getIndexedAttestation targetState attestation = .ok indexed ∧
      isValidIndexedAttestation config checks targetState indexed = .ok true

/-- The statements of an indexed attestation: each of its validators with its data. -/
def indexedStatements (indexed : IndexedAttestation preset fork) :
    Set (ValidatorIndex × AttestationData) :=
  {x | x.1 ∈ indexed.attestingIndices.data ∧ x.2 = indexed.data}

variable {config checks} (anchorState : BeaconState preset fork)
  (anchorBlock : BeaconBlock preset fork)

/-- The statements of an attestation: those that a store reachable from the anchor reads in it. -/
def attestationStatements (attestation : Attestation preset fork) :
    Set (ValidatorIndex × AttestationData) :=
  {x | ∃ store indexed, Store.Reachable config anchorState anchorBlock store ∧
    ReadsVote config checks store attestation indexed ∧ x ∈ indexedStatements indexed}

variable (config checks) in
/-- The statements of a message of the fork choice, each a validator and the data it signs.

An attestation and an attester slashing sign their votes.

A block signs what its attestations and its attester slashings sign.

The other messages carry no vote of the fork choice, and no statement here. -/
def statements : Message preset fork → Set (ValidatorIndex × AttestationData)
  | .block signed =>
    {x | ∃ attestation ∈ signed.message.body.attestations.data,
        x ∈ attestationStatements (config := config) (checks := checks) anchorState anchorBlock
          attestation} ∪
      {x | ∃ slashing ∈ signed.message.body.attesterSlashings.data,
        x ∈ indexedStatements slashing.attestation1 ∪ indexedStatements slashing.attestation2}
  | .attestation attestation =>
    attestationStatements (config := config) (checks := checks) anchorState anchorBlock attestation
  | .attesterSlashing slashing =>
    indexedStatements slashing.attestation1 ∪ indexedStatements slashing.attestation2
  | _ => ∅

variable (config checks)

/-- The data of an honest vote in a slot, for a committee, from the head of a store.

The state of the head block goes through the empty slots up to the slot, when it is older.

The data then follows the guide of the honest validator. -/
def HonestVoteData (store : Store preset fork) (slot : Slot) (committeeIndex : CommitteeIndex)
    (data : AttestationData) : Prop :=
  ∃ head block headState state, store.getHead config = .ok head ∧
    store.blocks[head.root]? = some block ∧ store.blockState head.root = .ok headState ∧
    (if headState.slot < slot then processSlots config checks headState slot
      else .ok headState) = .ok state ∧
    getAttestationData state head.root block.slot committeeIndex head.payloadStatus = .ok data

/-- A store is up to date at a time, with a view.

Its clock shows the time, and each move at that time with that view keeps it as it is.

So it has processed every message of the view that its handlers accept. -/
def UpToDate (time : ℕ) (view : Set (Message preset fork)) (store : Store preset fork) : Prop :=
  store.timeMs.toNat = time ∧ ∀ after, Handles config checks sources time view store after →
    after = store

variable (fork) in
/-- The attestation deadline of a slot, in milliseconds, for a time of genesis. -/
def IsAttestationDeadline (genesisTimeMs : UInt64) (slot : Slot) (time : ℕ) : Prop :=
  ∃ start due, computeTimeAtSlotMs config genesisTimeMs slot = .ok start ∧
    getAttestationDueMs config fork = .ok due ∧ time = start.toNat + due.toNat

variable {config checks sources anchorState anchorBlock}

variable (config checks sources anchorState anchorBlock)
  (assignment : ValidatorIndex → Slot → Option CommitteeIndex) (genesisTimeMs : UInt64)

/-- A vote that an honest validator may sign at a time, with its view and its store.

The validator sits in a committee of the slot of the vote, and the time is its attestation deadline.

Its store follows the time of genesis, and is up to date.

The data is that of an honest vote from the store.

No vote of the validator in its view is slashable together with it, in either order. -/
def MaySign (validator : ValidatorIndex) (time : ℕ) (view : Set (Message preset fork))
    (store : Store preset fork) (data : AttestationData) : Prop :=
  ∃ committeeIndex, assignment validator data.slot = some committeeIndex ∧
    IsAttestationDeadline fork config genesisTimeMs data.slot time ∧
    store.genesisTimeMs = genesisTimeMs ∧ UpToDate config checks sources time view store ∧
    HonestVoteData config checks store data.slot committeeIndex data ∧
    ∀ m ∈ view, ∀ y ∈ statements config checks anchorState anchorBlock m, y.1 = validator →
      isSlashableAttestationData y.2 data = false ∧ isSlashableAttestationData data y.2 = false

/-- The messages that an honest validator may send.

Each statement of its own is a statement of its view, or a vote that it may sign then. -/
def HonestSends (validator : ValidatorIndex) (time : ℕ) (view : Set (Message preset fork))
    (store : Store preset fork) (message : Message preset fork) : Prop :=
  ∀ x ∈ statements config checks anchorState anchorBlock message, x.1 = validator →
    (∃ m ∈ view, x ∈ statements config checks anchorState anchorBlock m) ∨
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs validator
        time view store x.2

/-- The protocol of honest validators that run the fork choice and vote.

The messages carry the statements above, and honest validators send as their duty allows. -/
abbrev honestForkChoice : Protocol ValidatorIndex (Message preset fork) (Store preset fork)
    AttestationData :=
  forkChoice config checks sources (statements config checks anchorState anchorBlock)
    (HonestSends config checks sources anchorState anchorBlock assignment genesisTimeMs)

variable {config checks sources anchorState anchorBlock assignment genesisTimeMs}

/-- The duty to vote, on an execution with honest validators `J`.

Take an honest validator, a slot of its assignment, and the attestation deadline of that slot.

When the execution starts by then, the validator sends an attestation at that time.

Its store then follows the time of genesis, and is up to date.

The data of the attestation is that of an honest vote from its store.

Its store reads the attestation as the vote of the validator alone, with a valid signature. -/
def Votes {J : Set ValidatorIndex}
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) : Prop :=
  ∀ v ∈ J, ∀ slot committeeIndex time, assignment v slot = some committeeIndex →
    IsAttestationDeadline fork config genesisTimeMs slot time → e.startTime ≤ time →
    ∃ n attestation indexed, e.events n = .send v (.attestation attestation) ∧
      (e.world n).time = time ∧ ((e.world n).state v).genesisTimeMs = genesisTimeMs ∧
      UpToDate config checks sources time ((e.world n).view v) ((e.world n).state v) ∧
      HonestVoteData config checks ((e.world n).state v) slot committeeIndex attestation.data ∧
      ReadsVote config checks ((e.world n).state v) attestation indexed ∧
      indexed.attestingIndices.data.toList = [v]

/-- Under synchrony with delay `Δ`, the vote of a duty reaches every honest validator `Δ` later.

The vote is that of the duty to vote, with all that the duty says of it.

When `Δ` fits between the attestation deadline and the next slot, it arrives within the slot. -/
theorem Votes.mem_view {J : Set ValidatorIndex}
    {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J} (votes : Votes e) {Δ : ℕ} (sync : e.Synchronous Δ) {v u : ValidatorIndex}
    (honest : v ∈ J) (receiver : u ∈ J) {slot : Slot} {committeeIndex : CommitteeIndex}
    {time : ℕ} (assigned : assignment v slot = some committeeIndex)
    (deadline : IsAttestationDeadline fork config genesisTimeMs slot time)
    (started : e.startTime ≤ time) :
    ∃ n attestation indexed, e.events n = .send v (.attestation attestation) ∧
      (e.world n).time = time ∧ ((e.world n).state v).genesisTimeMs = genesisTimeMs ∧
      UpToDate config checks sources time ((e.world n).view v) ((e.world n).state v) ∧
      HonestVoteData config checks ((e.world n).state v) slot committeeIndex attestation.data ∧
      ReadsVote config checks ((e.world n).state v) attestation indexed ∧
      indexed.attestingIndices.data.toList = [v] ∧
      ∀ k, time + Δ ≤ (e.world k).time → .attestation attestation ∈ (e.world k).view u := by
  unfold Votes at votes
  obtain ⟨n, attestation, indexed, sends, atTime, rest⟩ :=
    votes v honest slot committeeIndex time assigned deadline started
  refine ⟨n, attestation, indexed, sends, atTime, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1,
    rest.2.2.2.2, fun k late => e.mem_view_of_send sync sends honest receiver ?_⟩
  rw [atTime, Nat.max_zero]
  exact late

/-! ## An execution where an honest validator votes -/

/-- A new store from an anchor at slot zero starts its clock at genesis.

It holds the anchor state for the checkpoint of the anchor. -/
private theorem getForkchoiceStore_clock {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store)
    (stateZero : anchorState.slot = 0) :
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      store.timeMs = store.genesisTimeMs ∧
      store.checkpointStates[(⟨getCurrentEpoch anchorState, anchorRoot⟩ : Checkpoint)]? =
        some anchorState := by
  unfold getForkchoiceStore at made
  cases stateRoot : SszType.hashTreeRoot anchorState with
  | error e => simp [stateRoot, bind, Except.bind, Except.mapError] at made
  | ok stateRoot' =>
    simp only [stateRoot, Except.mapError, bind, Except.bind] at made
    split at made
    · simp [throw, throwThe, MonadExceptOf.throw] at made
    · cases blockRoot : SszType.hashTreeRoot anchorBlock with
      | error e => simp [blockRoot] at made
      | ok anchorRoot =>
        simp only [blockRoot] at made
        cases time : computeTimeAtSlotMs config (secondsToMilliseconds anchorState.genesisTime)
            anchorState.slot with
        | error e => simp [time] at made
        | ok timeMs =>
          simp only [time, pure, Except.pure, Except.ok.injEq] at made
          subst made
          -- The order of checkpoints is by epoch then by root, which is transitive.
          have : Std.TransCmp Checkpoint.compare := inferInstanceAs
            (Std.TransCmp (compareLex (compareOn Checkpoint.epoch) (compareOn Checkpoint.root)))
          refine ⟨anchorRoot, rfl, ?_, by simp⟩
          have fits := UInt64.toNat_lt (secondsToMilliseconds anchorState.genesisTime)
          simp [stateZero, computeTimeAtSlotMs, Uint64.mulChecked, Uint64.addChecked, bind,
            Except.bind, fits] at time ⊢
          exact time.symm

/-- The slot at a time inside the first slot after genesis is zero. -/
private theorem computeSlotAtTimeMs_inside {config : Config} {genesisTimeMs due : UInt64}
    (inSlot : due < config.SLOT_DURATION_MS)
    (fits : genesisTimeMs.toNat + due.toNat < 2 ^ 64) :
    computeSlotAtTimeMs config genesisTimeMs (genesisTimeMs.toNat + due.toNat).toUInt64 =
      .ok 0 := by
  have round : (genesisTimeMs.toNat + due.toNat).toUInt64.toNat =
      genesisTimeMs.toNat + due.toNat := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt fits
  have elapsed :
      Uint64.subChecked (genesisTimeMs.toNat + due.toNat).toUInt64 genesisTimeMs = .ok due :=
    Uint64.subChecked_ok_iff.mpr ⟨by omega, by omega⟩
  have below := UInt64.lt_iff_toNat_lt.mp inSlot
  have quotient : Uint64.divChecked due config.SLOT_DURATION_MS = .ok 0 :=
    Uint64.divChecked_ok_iff.mpr ⟨fun zero => by simp [zero] at below,
      by simp [Nat.div_eq_of_lt below]⟩
  simp only [computeSlotAtTimeMs, elapsed, quotient, bind, Except.bind]

/-- A tick within the current slot zero only sets the clock. -/
private theorem onTick_sameSlot {config : Config} {store : Store preset fork} {timeMs : UInt64}
    (current : store.getCurrentSlot config = .ok 0)
    (slotted : computeSlotAtTimeMs config store.genesisTimeMs timeMs = .ok 0) :
    store.onTick config timeMs = .ok { store with timeMs } := by
  have caught : Store.catchUp config store 0 = .ok store := by
    rw [Store.catchUp]
    simp [current, bind, Except.bind, pure, Except.pure]
  have later : ({ store with timeMs } : Store preset fork).getCurrentSlot config = .ok 0 := by
    simp [Store.getCurrentSlot, slotted, Except.mapError]
  have ticked : store.onTickPerSlot config timeMs = .ok { store with timeMs } := by
    simp [Store.onTickPerSlot, current, later, computeSlotsSinceEpochStart,
      computeStartSlotAtEpoch_computeEpochAtSlot, bind, Except.bind, pure, Except.pure,
      Except.mapError]
  simp [Store.onTick, slotted, caught, ticked, Except.mapError, bind, Except.bind]

/-- Before Gloas, a store that holds only an anchor block at slot zero has that block as head.

The clock of the store is at slot zero, and both checkpoints are the anchor. -/
private theorem getHead_anchor {config : Config} {store : Store preset fork}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {anchorRoot : Root} (before : fork < .glamsterdam)
    (blocks : store.blocks =
      (∅ : Std.TreeMap Root (BeaconBlock preset fork)).insert anchorRoot anchorBlock)
    (states : store.blockStates =
      (∅ : Std.TreeMap Root (BeaconState preset fork)).insert anchorRoot anchorState)
    (justified : store.justifiedCheckpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩)
    (finalized : store.finalizedCheckpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩)
    (current : store.getCurrentSlot config = .ok 0) (stateZero : anchorState.slot = 0)
    (blockZero : anchorBlock.slot = 0) (parent : anchorBlock.parentRoot ≠ anchorRoot) :
    store.getHead config = .ok ⟨anchorRoot, .pending⟩ := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  have epochZero : getCurrentEpoch anchorState = 0 := by
    simp [getCurrentEpoch, computeEpochAtSlot, stateZero]
  have epoch : store.getCurrentStoreEpoch config = .ok 0 := by
    simp [Store.getCurrentStoreEpoch, current, computeEpochAtSlot, bind, Except.bind, pure,
      Except.pure]
  -- The anchor block is not its own parent, so it has no child.
  have children : store.getNodeChildren ⟨anchorRoot, .pending⟩ = .ok [] := by
    simp [Store.getNodeChildren, notGloas, blocks, pure, Except.pure,
      Std.TreeMap.getElem?_insert]
    exact parent
  have ancestor : store.getAncestor ⟨anchorRoot, .pending⟩ 0 = .ok ⟨anchorRoot, .pending⟩ :=
    Store.getAncestor_of_le (block := anchorBlock) (by simp [blocks]) (by simp [blockZero])
  -- Both checkpoints sit at the genesis epoch, so the anchor is a viable leaf.
  have viable : store.isViableLeaf config ⟨anchorRoot, .pending⟩ = .ok true := by
    simp [Store.isViableLeaf, epoch, Store.getVotingSource, Store.block, blocks, states,
      Store.getCheckpointBlock, ancestor, justified, finalized, epochZero, GENESIS_EPOCH,
      computeStartSlotAtEpoch, Uint64.mulChecked, bind, Except.bind, pure, Except.pure,
      Except.mapError, blockZero, computeEpochAtSlot]
  have tree : store.getFilteredNodeTree config = .ok [⟨anchorRoot, .pending⟩] := by
    rw [Store.getFilteredNodeTree, justified, Store.filterNodeTree]
    simp [children, viable, bind, Except.bind, pure, Except.pure]
  have none : store.heaviestChild config store.justifiedTally [⟨anchorRoot, .pending⟩]
      ⟨anchorRoot, .pending⟩ = .ok none := by
    simp [Store.heaviestChild, children, chooseHeaviest, bind, Except.bind, pure, Except.pure]
  rw [Store.getHead, tree]
  simp only [notGloas, false_and, ite_false, justified, bind, Except.bind]
  rw [Store.getHeadFrom, none]
  rfl

/-- An indexed attestation keeps the data of its attestation. -/
private theorem getIndexedAttestation_data {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (read : getIndexedAttestation state attestation = .ok indexed) :
    indexed.data = attestation.data := by
  unfold getIndexedAttestation at read
  rw [bind_ok_iff] at read
  obtain ⟨indices, -, read⟩ := read
  split at read
  · simp only [pure, Except.pure, Except.ok.injEq] at read
    rw [← read]
  · simp [throw, throwThe, MonadExceptOf.throw] at read

/-- Before Electra, a store reads a vote with the first seat of a committee as that seat alone.

The store holds the state of the target, and the committee is that of the data there. -/
private theorem readsVote_firstSeat {config : Config} {store : Store preset fork}
    {state : BeaconState preset fork} (before : fork < .pectra)
    {attestation : Attestation preset fork}
    (stored : store.checkpointStates[attestation.data.target]? = some state)
    {committee : Array ValidatorIndex}
    (committeeOk : getBeaconCommittee state 0 0 = .ok committee)
    (slotZero : attestation.data.slot = 0) (indexZero : attestation.data.index = 0)
    {v : ValidatorIndex} (first : committee[0]? = some v)
    (small : committee.size ≤ maxAttesters preset fork)
    (bits : attestation.aggregationBits.bits =
      Array.ofFn fun seat : Fin committee.size => decide (seat.val = 0)) :
    ∃ indexed, ReadsVote config .acceptAll store attestation indexed ∧
      indexed.attestingIndices.data.toList = [v] := by
  have notElectra : ¬ .pectra ≤ fork := Nat.not_le_of_lt before
  have notGloas : fork < .glamsterdam := Nat.lt_trans before (by decide)
  -- The store holds the state of the target, so it keeps itself.
  have contains : store.checkpointStates.contains attestation.data.target := by
    have : Std.TransCmp Checkpoint.compare := inferInstanceAs
      (Std.TransCmp (compareLex (compareOn Checkpoint.epoch) (compareOn Checkpoint.root)))
    rw [Std.TreeMap.contains_eq_isSome_getElem?, stored]
    rfl
  have targetOk :
      store.storeTargetCheckpointState config .acceptAll attestation.data.target = .ok store := by
    simp [Store.storeTargetCheckpointState, contains, pure, Except.pure]
  have stateOk : store.checkpointState attestation.data.target = .ok state := by
    simp [Store.checkpointState, stored, pure, Except.pure]
  -- The bits set the first seat alone, which the validator holds.
  obtain ⟨seated, member⟩ := Array.getElem?_eq_some_iff.mp first
  obtain ⟨attesters, attestersOk⟩ :=
    committeeAttesters_ok (bits := attestation.aggregationBits.bits) (committee := committee)
      (by simp [bits])
  have attestersEq : sortedSet attesters = [v] := by
    refine eq_singleton_of_pairwise_lt (sortedSet_sorted _) fun index => ?_
    rw [mem_sortedSet, mem_committeeAttesters_iff attestersOk, bits]
    constructor
    · rintro ⟨seat, inside, rfl, set⟩
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, inside, ↓reduceDIte,
        Option.getD_some, decide_eq_true_eq, Nat.zero_add] at set
      subst set
      exact member
    · rintro rfl
      exact ⟨0, seated, member, by simp [seated]⟩
  have indicesOk : getAttestingIndices state attestation = .ok [v] := by
    unfold getAttestingIndices
    dsimp only
    split
    · exact absurd ‹_› notElectra
    simp only [slotZero, indexZero, committeeOk, attestersOk, bind, Except.bind, pure,
      Except.pure, attestersEq]
  have fitsOne : [v].length ≤ maxAttesters preset fork := by
    simp only [List.length_singleton]
    omega
  obtain ⟨indexed, indexedOk, single, sameData⟩ : ∃ indexed,
      getIndexedAttestation state attestation = .ok indexed ∧
        indexed.attestingIndices.data.toList = [v] ∧ indexed.data = attestation.data := by
    unfold getIndexedAttestation
    rw [indicesOk]
    simp only [bind, Except.bind]
    split
    · exact ⟨_, rfl, rfl, rfl⟩
    · exact absurd (fun _ => fitsOne) ‹_›
  refine ⟨indexed, ⟨store, state, targetOk, stateOk, indexedOk, ?_⟩, single⟩
  -- The validator sits in a committee, so it is in the registry, and every signature passes.
  obtain ⟨validator, found, -⟩ :=
    (mem_getActiveValidatorIndices (BeaconState.registryWithinLimit_of_lt notGloas state)).mp
      (mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
        (member ▸ Array.getElem_mem seated))
  obtain ⟨domain, domainOk⟩ := computeDomain_total config DOMAIN_BEACON_ATTESTER
    (if indexed.data.target.epoch < state.forkVersions.epoch then
      state.forkVersions.previousVersion else state.forkVersions.currentVersion)
    state.genesisValidatorsRoot
  obtain ⟨root, rootOk⟩ := computeSigningRoot_total indexed.data domain
  have sortedOne : sortedSet [v] = [v] := by
    simp [sortedSet, keepNew]
  have notGloas' : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt notGloas
  simp [isValidIndexedAttestation, single, sortedOne, notGloas', getValidator, found, getDomain,
    domainOk, rootOk, liftAccessor, liftSsz, SignatureChecks.acceptAll, bind, Except.bind, pure,
    Except.pure, Except.mapError]

/-- The events of the witness: wait for the deadline, tick, vote, then let time go on. -/
private def voteEvents {ν μ σ : Type*} (deadline : ℕ) (v : ν) (ticked : σ) (m : μ) :
    ℕ → Event ν μ σ
  | 0 => .wait deadline
  | 1 => .move v ticked
  | 2 => .send v m
  | n + 3 => .wait (deadline + n + 1)

/-- After the tick, the clock is at the deadline, nothing is sent, and the validator has ticked. -/
private theorem worldAt_vote_two {ν μ σ : Type*} [DecidableEq ν] {time deadline : ℕ}
    {state : ν → σ} {v : ν} {ticked : σ} {m : μ} :
    worldAt (World.initial time state) (voteEvents deadline v ticked m) 2 =
      ⟨deadline, ∅, fun _ => ∅, Function.update state v ticked⟩ := by
  simp [worldAt, voteEvents, World.initial, World.apply]

/-- After the vote, only the vote is sent, and the clock moves on by one at each event. -/
private theorem worldAt_vote {ν μ σ : Type*} [DecidableEq ν] {time deadline : ℕ}
    {state : ν → σ} {v : ν} {ticked : σ} {m : μ} (n : ℕ) :
    worldAt (World.initial time state) (voteEvents deadline v ticked m) (n + 3) =
      ⟨deadline + n, {m}, Function.update (fun _ => ∅) v {m}, Function.update state v ticked⟩ := by
  induction n with
  | zero =>
    rw [worldAt, worldAt_vote_two]
    simp only [voteEvents, World.apply, Nat.add_zero]
    congr 1
    · simp
    · funext u
      by_cases same : u = v
      · subst same
        simp
      · simp [Function.update_of_ne same]
  | succ n ih =>
    rw [worldAt, ih]
    simp [voteEvents, World.apply]
    omega

/-- Honest validators that vote have an execution, with one honest validator that votes.

The store starts from an anchor whose block and state sit at slot zero, before Electra.

The anchor block does not name its own root as its parent.

The validator `v` holds the first seat of the first committee of slot zero, in the anchor state.

That committee fits in the bits of an attestation.

The assignment puts the validator in that committee, and in no other slot.

The attestation deadline of slot zero falls inside the slot, and fits in 64 bits.

Signature checks accept every signature, as the consensus test vectors with placeholders do.

The execution starts at the time of the anchor, and the validator votes at the deadline.

It is synchronous for every positive delay, and the validator does its duty to vote.

The store of the validator stays reachable from the anchor. -/
theorem exists_votes {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok store)
    (stateZero : anchorState.slot = 0) (blockZero : anchorBlock.slot = 0)
    (before : fork < .pectra)
    (parent : ∀ root, SszType.hashTreeRoot anchorBlock = .ok root → anchorBlock.parentRoot ≠ root)
    {committee : Array ValidatorIndex}
    (committeeOk : getBeaconCommittee anchorState 0 0 = .ok committee) {v : ValidatorIndex}
    (first : committee[0]? = some v) (small : committee.size ≤ maxAttesters preset fork)
    (slots : 0 < config.SLOT_DURATION_MS) {due : UInt64}
    (dueOk : getAttestationDueMs config fork = .ok due) (inSlot : due < config.SLOT_DURATION_MS)
    (fits : store.genesisTimeMs.toNat + due.toNat < 2 ^ 64) {Δ : ℕ} (positive : 0 < Δ) :
    ∃ e : Execution (honestForkChoice config .acceptAll sources anchorState anchorBlock
        (fun u slot => if u = v ∧ slot = 0 then some 0 else none) store.genesisTimeMs) {v},
      e.startTime = store.timeMs.toNat ∧ e.start = (fun _ => store) ∧
      (∃ attestation, e.events 2 = .send v (.attestation attestation)) ∧
      Votes e ∧ e.Synchronous Δ ∧
      ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state v) := by
  obtain ⟨anchorRoot, blockRooted, clock, stored⟩ := getForkchoiceStore_clock anchored stateZero
  obtain ⟨anchorRoot', blockRooted', blocks, states⟩ := getForkchoiceStore_maps anchored
  obtain ⟨anchorRoot'', blockRooted'', -, -, justified, finalized, -, -⟩ :=
    getForkchoiceStore_anchor anchored
  rw [blockRooted, Except.ok.injEq] at blockRooted' blockRooted''
  subst blockRooted' blockRooted''
  have notGloas : fork < .glamsterdam := Nat.lt_trans before (by decide)
  have epochZero : getCurrentEpoch anchorState = 0 := by
    simp [getCurrentEpoch, computeEpochAtSlot, stateZero]
  -- The validator ticks its store to the deadline, which stays in slot zero.
  set deadline := store.genesisTimeMs.toNat + due.toNat with deadlineDef
  set ticked : Store preset fork := { store with timeMs := deadline.toUInt64 } with tickedDef
  have startSlot : store.getCurrentSlot config = .ok 0 :=
    stateZero ▸ getCurrentSlot_getForkchoiceStore slots anchored
  have slotted : computeSlotAtTimeMs config store.genesisTimeMs deadline.toUInt64 = .ok 0 :=
    computeSlotAtTimeMs_inside inSlot fits
  have tickedSlot : ticked.getCurrentSlot config = .ok 0 := by
    rw [Store.getCurrentSlot, show ticked.timeMs = deadline.toUInt64 from rfl,
      show ticked.genesisTimeMs = store.genesisTimeMs from rfl, slotted]
    rfl
  have onTicked : store.onTick config deadline.toUInt64 = .ok ticked :=
    onTick_sameSlot startSlot slotted
  have tickedTime : ticked.timeMs.toNat = deadline := by
    simp only [ticked, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt fits
  have upToDate : UpToDate config .acceptAll sources deadline ∅ ticked := by
    refine ⟨tickedTime, fun after handles => ?_⟩
    cases handles with
    | tick _ _ ticks =>
      rw [show deadline.toUInt64 = ticked.timeMs from rfl, onTick_timeMs tickedSlot] at ticks
      exact (Except.ok.inj ticks).symm
    | _ => simp_all
  -- The head of the ticked store is the anchor, and the vote follows from it.
  have head : ticked.getHead config = .ok ⟨anchorRoot, .pending⟩ :=
    getHead_anchor notGloas blocks states justified finalized tickedSlot stateZero blockZero
      (parent _ blockRooted)
  let data : AttestationData :=
    { slot := 0, index := 0, beaconBlockRoot := anchorRoot
      source := anchorState.currentJustifiedCheckpoint
      target := ⟨getCurrentEpoch anchorState, anchorRoot⟩ }
  have honestData : HonestVoteData config .acceptAll ticked 0 0 data := by
    refine ⟨_, anchorBlock, anchorState, anchorState, head, by simp [ticked, blocks], ?_,
      by simp [stateZero], ?_⟩
    · simp [Store.blockState, ticked, states, pure, Except.pure]
    · have notElectra : ¬ .pectra ≤ fork := Nat.not_le_of_lt before
      have notGloas' : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt notGloas
      simp [getAttestationData, attestationDataIndex, notElectra, notGloas',
        getEpochBoundaryBlockRoot, computeStartSlotAtEpoch, epochZero, stateZero, data,
        Uint64.mulChecked, bind, Except.bind, pure, Except.pure, Except.mapError]
  -- The attestation sets the bit of the first seat of the committee.
  let attestation : Attestation preset fork :=
    { aggregationBits :=
        ⟨Array.ofFn fun seat : Fin committee.size => decide (seat.val = 0),
          fun _ => by simpa using small⟩
      data, signature := default
      committeeBits := fun electra => absurd electra (Nat.not_le_of_lt before) }
  obtain ⟨indexed, reads, single⟩ : ∃ indexed,
      ReadsVote config .acceptAll ticked attestation indexed ∧
        indexed.attestingIndices.data.toList = [v] :=
    readsVote_firstSeat (config := config) (store := ticked) (attestation := attestation) before
      stored committeeOk rfl rfl first
      small rfl
  have statementData : ∀ x ∈ statements config .acceptAll anchorState anchorBlock
      (.attestation attestation), x.2 = data := by
    intro x mem
    obtain ⟨_, read, -, ⟨_, _, -, -, readIndexed, -⟩, member⟩ := mem
    rw [member.2, getIndexedAttestation_data readIndexed]
  have deadlineOk : IsAttestationDeadline fork config store.genesisTimeMs 0 deadline := by
    refine ⟨store.genesisTimeMs, due, ?_, dueOk, rfl⟩
    have bounded := UInt64.toNat_lt store.genesisTimeMs
    simp [computeTimeAtSlotMs, Uint64.mulChecked, Uint64.addChecked, bind, Except.bind, bounded]
  have maySign : MaySign config .acceptAll sources anchorState anchorBlock
      (fun u slot => if u = v ∧ slot = 0 then some 0 else none) store.genesisTimeMs v deadline ∅
      ticked data :=
    ⟨0, by simp [data], deadlineOk, rfl, upToDate, honestData, by simp⟩
  -- The execution waits for the deadline, ticks the store, votes, then lets time go on.
  let e : Execution (honestForkChoice config .acceptAll sources anchorState anchorBlock
      (fun u slot => if u = v ∧ slot = 0 then some 0 else none) store.genesisTimeMs) {v} :=
    { startTime := store.timeMs.toNat
      start := fun _ => store
      events := voteEvents deadline v ticked (.attestation attestation)
      allowed := fun n => by
        match n with
        | 0 =>
          show store.timeMs.toNat ≤ deadline
          rw [clock]
          omega
        | 1 =>
          refine ⟨rfl, ?_⟩
          show Handles config .acceptAll sources deadline ∅ store ticked
          exact .tick (by rw [clock]; omega) fits onTicked
        | 2 =>
          refine ⟨fun x _ honest other => (other honest).elim, fun _ => ?_⟩
          rw [worldAt_vote_two]
          intro x mem _
          refine .inr ?_
          rw [statementData x mem]
          simpa using maySign
        | n + 3 =>
          rw [worldAt_vote]
          show deadline + n ≤ deadline + n + 1
          omega }
  have worldTwo :
      e.world 2 = ⟨deadline, ∅, fun _ => ∅, Function.update (fun _ => store) v ticked⟩ :=
    worldAt_vote_two
  have later : ∀ n, e.world (n + 3) = ⟨deadline + n, {.attestation attestation},
      Function.update (fun _ => ∅) v {.attestation attestation},
      Function.update (fun _ => store) v ticked⟩ :=
    worldAt_vote
  refine ⟨e, rfl, rfl, ⟨attestation, rfl⟩, ?_, ⟨positive, fun T => ⟨T + 3, ?_⟩, ?_⟩,
    fun n => e.reachable (fun u _ => .anchor anchored) n v rfl⟩
  · -- The only duty is in slot zero, at the deadline, and the vote of the third event does it.
    intro u honest slot committeeIndex time assigned atDeadline _
    rw [Set.mem_singleton_iff] at honest
    subst honest
    obtain ⟨rfl, rfl⟩ : slot = 0 ∧ committeeIndex = 0 := by
      dsimp only at assigned
      split_ifs at assigned with zero
      · exact ⟨zero.2, (Option.some.inj assigned).symm⟩
    obtain ⟨start, due', started, dued, rfl⟩ := atDeadline
    obtain ⟨start', due'', started', dued', atTime⟩ := deadlineOk
    rw [started, Except.ok.injEq] at started'
    rw [dued, Except.ok.injEq] at dued'
    subst started' dued'
    rw [← atTime]
    refine ⟨2, attestation, indexed, rfl, by rw [worldTwo], ?_, ?_, ?_, ?_, single⟩
    · rw [worldTwo]
      dsimp only
      rw [Function.update_self]
    · rw [worldTwo]
      simpa using upToDate
    · rw [worldTwo]
      simpa using honestData
    · rw [worldTwo]
      simpa using reads
  · rw [later]
    show T ≤ deadline + T
    omega
  · intro n k le w honest u receiver m member _
    rw [Set.mem_singleton_iff] at honest receiver
    subst honest receiver
    exact e.monotone_view _ le member

end EthLib.Consensus.Models.Network
