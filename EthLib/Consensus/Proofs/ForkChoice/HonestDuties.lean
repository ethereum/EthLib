module

public import EthLib.Consensus.HonestAggregation
public import EthLib.Consensus.Proofs.ForkChoice.Network
import EthLib.Consensus.Proofs.HonestAggregation
import EthLib.Consensus.Proofs.Signing

/-!
# Proofs: the duties of honest validators that run the fork choice

The model is that of §2 of the fast confirmation paper, [arXiv 2405.00549v4][fcr].

A validator in the committee of a slot casts one vote in that slot, for the head of its view.

Honest validators never sign votes that can be slashed together.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} (config : Config) (checks : SignatureChecks)
  (sources : BlockSources preset fork)

/-- A store reads an attestation as an indexed attestation, as its handler of attestations does.

The store takes the state of the target, and reads the indices that the bits name there.

The indexed attestation must be valid there, signature included. -/
def ReadsAttestation (store : Store preset fork) (attestation : Attestation preset fork)
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
  -- A vote signs its data for each validator that a store reads in its bits.
  --
  -- A store reachable from the anchor may read an attestation, and all of its readings count.
  --
  -- Two stores can read different signers only when they hold two states for one checkpoint.
  {x | ∃ store indexed, Store.Reachable config anchorState anchorBlock store ∧
    -- A store reads those validators in the state of the target, with a valid signature.
    ReadsAttestation config checks store attestation indexed ∧ x ∈ indexedStatements indexed}

variable (config checks) in
/-- The statements of a message of the fork choice, each a validator and the data it signs.

An attestation and an attester slashing sign their votes.

A block signs what its attestations and its attester slashings sign.

The other messages carry no vote of the fork choice, and no statement here. -/
def statements : Message preset fork → Set (ValidatorIndex × AttestationData)
  -- A signature of a block by its proposer is no statement here.
  --
  -- So any validator may send a block whose votes it may carry.
  --
  -- That strengthens the adversary, and no honest validator has to propose.
  | .block signed =>
    {x | ∃ attestation ∈ signed.message.body.attestations.data,
        x ∈ attestationStatements (config := config) (checks := checks) anchorState anchorBlock
          attestation} ∪
      {x | ∃ slashing ∈ signed.message.body.attesterSlashings.data,
        x ∈ indexedStatements slashing.attestation1 ∪ indexedStatements slashing.attestation2}
  -- Here the votes are the attestations of the fork choice.
  | .attestation attestation =>
    attestationStatements (config := config) (checks := checks) anchorState anchorBlock attestation
  -- An attester slashing signs the data of its two votes for each of their validators.
  --
  -- Its signatures are not checked there, which only forbids slashings that every store rejects.
  | .attesterSlashing slashing =>
    indexedStatements slashing.attestation1 ∪ indexedStatements slashing.attestation2
  | _ => ∅

variable (config checks)

/-- The data of an honest vote in a slot, for a committee, from the head of a store.

The state of the head block goes through the empty slots up to the slot, when it is older.

The data is then that of an honest validator. -/
def HonestVoteData (store : Store preset fork) (slot : Slot) (committeeIndex : CommitteeIndex)
    (data : AttestationData) : Prop :=
  ∃ head block headState state, store.getHead config = .ok head ∧
    store.blocks[head.root]? = some block ∧ store.blockState head.root = .ok headState ∧
    lookaheadState config checks headState slot = .ok state ∧
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

variable (preset) in
/-- An assignment of validators to the committees of slots, a parameter shared by honest validators.

It gives each validator at most one slot in each epoch.

The committees of an epoch split its validators that way, as §2 of the paper says.

The paper shares it too once GST has passed long enough, in §2, under stabilization time. -/
structure Assignment where
  /-- The committee of a validator in a slot, if it has one. -/
  committee : ValidatorIndex → Slot → Option CommitteeIndex
  /-- A validator has at most one slot in each epoch. -/
  once : ∀ v first second firstIndex secondIndex, committee v first = some firstIndex →
    committee v second = some secondIndex →
    computeEpochAtSlot preset first = computeEpochAtSlot preset second → first = second

/-- The assignment of one validator to one committee of one slot, and of no one else. -/
def Assignment.single (v : ValidatorIndex) (slot : Slot) (committeeIndex : CommitteeIndex) :
    Assignment preset where
  committee u s := if u = v ∧ s = slot then some committeeIndex else none
  once u first second _ _ isFirst isSecond _ := by
    split at isFirst <;> split at isSecond <;> simp_all

variable (config checks sources anchorState anchorBlock)
  (assignment : Assignment preset) (genesisTimeMs : UInt64)

/-- A vote that an honest validator may sign at a time, with its view and its store. -/
def MaySign (validator : ValidatorIndex) (time : ℕ) (view : Set (Message preset fork))
    (store : Store preset fork) (data : AttestationData) : Prop :=
  -- The validator sits in a committee of the slot of the vote.
  ∃ committeeIndex, assignment.committee validator data.slot = some committeeIndex ∧
    -- The time is the attestation deadline of that slot.
    IsAttestationDeadline fork config genesisTimeMs data.slot time ∧
    -- The store of the validator follows the time of genesis, and is up to date.
    store.genesisTimeMs = genesisTimeMs ∧ UpToDate config checks sources time view store ∧
    -- The data is that of an honest vote from the store.
    --
    -- An honest validator builds that data from the head.
    HonestVoteData config checks store data.slot committeeIndex data ∧
    -- No vote of the validator in its view is slashable together with it, in either order.
    ∀ m ∈ view, ∀ y ∈ statements config checks anchorState anchorBlock m, y.1 = validator →
      isSlashableAttestationData y.2 data = false ∧ isSlashableAttestationData data y.2 = false

/-- The messages that an honest validator may send.

Each statement of its own is a statement of its view, or a vote that it may sign then. -/
def HonestSends (validator : ValidatorIndex) (time : ℕ) (view : Set (Message preset fork))
    (store : Store preset fork) (message : Message preset fork) : Prop :=
  ∀ x ∈ statements config checks anchorState anchorBlock message, x.1 = validator →
    (∃ m ∈ view, x ∈ statements config checks anchorState anchorBlock m) ∨
      -- An honest validator signs a vote of its own only as its duty allows.
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs validator
        time view store x.2

/-- The protocol of honest validators that run the fork choice and vote.

The messages carry the statements above, and honest validators send as their duty allows. -/
abbrev honestForkChoice : Protocol ValidatorIndex (Message preset fork) (Store preset fork)
    AttestationData :=
  forkChoice config checks sources (statements config checks anchorState anchorBlock)
    (HonestSends config checks sources anchorState anchorBlock assignment genesisTimeMs)

variable {config checks sources anchorState anchorBlock assignment genesisTimeMs}

/-- A vote of an honest validator, as its duty asks, at the `n`-th event of an execution. -/
structure VoteAt {J : Set ValidatorIndex}
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (v : ValidatorIndex) (slot : Slot) (committeeIndex : CommitteeIndex)
    (time n : ℕ) (attestation : Attestation preset fork)
    (indexed : IndexedAttestation preset fork) : Prop where
  -- The event sends the attestation.
  sends : e.events n = .send v (.attestation attestation)
  -- It sends it at the attestation deadline of the slot.
  atTime : (e.world n).time = time
  -- The store of the validator then follows the time of genesis.
  genesis : ((e.world n).state v).genesisTimeMs = genesisTimeMs
  -- That store is up to date.
  upToDate : UpToDate config checks sources time ((e.world n).view v) ((e.world n).state v)
  -- The data of the attestation is that of an honest vote from that store, for the committee.
  honestData : HonestVoteData config checks ((e.world n).state v) slot committeeIndex
    attestation.data
  -- That store reads the attestation, with a valid signature.
  reads : ReadsAttestation config checks ((e.world n).state v) attestation indexed
  -- It reads the attestation as the vote of the validator alone.
  alone : indexed.attestingIndices.data.toList = [v]

/-- The duty to vote, on an execution with honest validators `J`, from a time `stable` on.

The duty to vote is a condition on an execution, and the paper asks it of every slot.

So an execution with that duty never asks for a vote that slashing protection forbids.

That excludes the schedules where the adversary would lead an honest validator there. -/
def Votes {J : Set ValidatorIndex} (stable : ℕ)
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) : Prop :=
  -- Take an honest validator and a slot of its assignment.
  ∀ v ∈ J, ∀ slot committeeIndex time, assignment.committee v slot = some committeeIndex →
    -- Take the attestation deadline of that slot, when the execution starts by then.
    IsAttestationDeadline fork config genesisTimeMs slot time → e.startTime ≤ time →
    -- Before `stable`, honest stores may disagree with the assignment on the committees.
    --
    -- From `stable` on, each honest validator's store reads its vote at its deadline as assigned.
    --
    -- The time is in milliseconds, like the deadlines.
    --
    -- The paper shares committees after its stabilization time, in §2, which comes after GST.
    --
    -- Each theorem relates that time to GST itself.
    stable ≤ time →
    -- When `stable` is past too, the validator votes, as its duty asks.
    --
    -- The paper assumes such a duty in §2, under slashing and under voting time.
    --
    -- There an honest validator votes once in each of its slots.
    --
    -- It never commits a slashable offence.
    ∃ n attestation indexed, VoteAt e v slot committeeIndex time n attestation indexed

/-- The committee check succeeds whenever the store successfully reads the target state.

This condition does not require the target cache operations themselves to succeed. -/
def VoteCommittees (store : Store preset fork)
    (attestation : Attestation preset fork) : Prop :=
  ∀ withTarget targetState,
    store.storeTargetCheckpointState config checks attestation.data.target = .ok withTarget →
    withTarget.checkpointState attestation.data.target = .ok targetState →
    checkAttestationCommittees targetState attestation = .ok ()

/-- Assigned honest validators vote in the half-open slot interval `[first, last)`.

The selected vote also passes the committee check in its target state.

Both conditions concern the same attestation at the same event, not separate witnesses.

No vote is required outside the interval, or before the execution starts. -/
def VotesInSlots {J : Set ValidatorIndex}
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (first last : Slot) : Prop :=
  ∀ v ∈ J, ∀ slot committeeIndex deadline,
    first ≤ slot → slot < last →
    assignment.committee v slot = some committeeIndex →
    IsAttestationDeadline fork config genesisTimeMs slot deadline →
    e.startTime ≤ deadline →
    ∃ n attestation indexed,
      VoteAt e v slot committeeIndex deadline n attestation indexed ∧
      VoteCommittees (config := config) (checks := checks)
        ((e.world n).state v) attestation

/-- Under synchrony with delay `Δ`, a vote of a duty reaches every honest validator `Δ` later. -/
theorem VoteAt.mem_view {J : Set ValidatorIndex}
    {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J} {Δ : ℕ} (sync : e.Synchronous Δ) {v u : ValidatorIndex}
    (honest : v ∈ J) (receiver : u ∈ J) {slot : Slot} {committeeIndex : CommitteeIndex}
    {time n : ℕ} {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed) {k : ℕ}
    (late : time + Δ ≤ (e.world k).time) : .attestation attestation ∈ (e.world k).view u := by
  refine e.mem_view_of_send sync vote.sends honest receiver ?_
  rw [vote.atTime, Nat.max_zero]
  exact late

/-! ## An execution where an honest validator votes -/

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
  exact EthLib.Consensus.computeSlotAtTimeMs_inside
    (by simp [computeTimeAtSlotMs, Uint64.mulChecked, Uint64.addChecked,
      bind, Except.bind, genesisTimeMs.toNat_lt]) round inSlot

/-- Before Gloas, a store that holds only an anchor block at slot zero has that block as head.

The clock of the store is in epoch zero, and both checkpoints are the anchor. -/
theorem getHead_anchor_of_epoch {config : Config} {store : Store preset fork}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {anchorRoot : Root} (before : fork < .glamsterdam)
    (blocks : store.blocks =
      (∅ : Std.TreeMap Root (BeaconBlock preset fork)).insert anchorRoot anchorBlock)
    (states : store.blockStates =
      (∅ : Std.TreeMap Root (BeaconState preset fork)).insert anchorRoot anchorState)
    (justified : store.justifiedCheckpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩)
    (finalized : store.finalizedCheckpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩)
    (epoch : store.getCurrentStoreEpoch config = .ok 0) (stateZero : anchorState.slot = 0)
    (blockZero : anchorBlock.slot = 0) (parent : anchorBlock.parentRoot ≠ anchorRoot) :
    store.getHead config = .ok ⟨anchorRoot, .pending⟩ := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  have epochZero : getCurrentEpoch anchorState = 0 := by
    simp [getCurrentEpoch, computeEpochAtSlot, stateZero]
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

/-- Before Gloas, a store that holds only an anchor block at slot zero has that block as head.

The clock of the store is at slot zero, and both checkpoints are the anchor. -/
theorem getHead_anchor {config : Config} {store : Store preset fork}
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
    store.getHead config = .ok ⟨anchorRoot, .pending⟩ :=
  -- Slot zero is in epoch zero.
  getHead_anchor_of_epoch before blocks states justified finalized
    (by simp [Store.getCurrentStoreEpoch, current, computeEpochAtSlot, bind, Except.bind, pure,
      Except.pure]) stateZero blockZero parent

/-- Before Electra, a store reads a vote with the first seat of a committee as that seat alone.

The store holds the state of the target, and the committee is that of the data there. -/
private theorem readsAttestation_firstSeat {config : Config} {store : Store preset fork}
    {state : BeaconState preset fork} (before : fork < .pectra)
    {attestation : Attestation preset fork}
    (stored : store.checkpointStates[attestation.data.target]? = some state)
    {committee : Array ValidatorIndex}
    (committeeOk : getBeaconCommittee state 0 0 = .ok committee)
    (slotZero : attestation.data.slot = 0) (indexZero : attestation.data.index = 0)
    {v : ValidatorIndex} (first : committee[0]? = some v)
    (bits : attestation.aggregationBits.bits =
      Array.ofFn fun seat : Fin committee.size => decide (seat.val = 0)) :
    ∃ indexed, ReadsAttestation config .acceptAll store attestation indexed ∧
      indexed.attestingIndices.data.toList = [v] := by
  have notElectra : ¬ .pectra ≤ fork := Nat.not_le_of_lt before
  have notGloas : fork < .glamsterdam := Nat.lt_trans before (by decide)
  -- The store holds the state of the target, so it keeps itself.
  have contains : store.checkpointStates.contains attestation.data.target := by
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
    rw [getAttestingIndices_of_lt_electra before]
    simp only [slotZero, indexZero, committeeOk, attestersOk, bind, Except.bind, pure,
      Except.pure, attestersEq]
  obtain ⟨indexed, indexedOk, indices, -, -⟩ :=
    getIndexedAttestation_of_getAttestingIndices indicesOk
  have single : indexed.attestingIndices.data.toList = [v] := by
    rw [indices]
  refine ⟨indexed, ⟨store, state, targetOk, stateOk, indexedOk, ?_⟩, single⟩
  -- The validator sits in a committee, so it is in the registry, and every signature passes.
  obtain ⟨validator, found, -⟩ :=
    (mem_getActiveValidatorIndices (BeaconState.registryWithinLimit_of_lt notGloas state)).mp
      (mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
        (member ▸ Array.getElem_mem seated))
  obtain ⟨domain, domainOk⟩ := computeDomain_total config DOMAIN_BEACON_ATTESTER
    (state.forkVersions.versionAt indexed.data.target.epoch)
    state.genesisValidatorsRoot
  obtain ⟨root, rootOk⟩ := computeSigningRoot_total indexed.data domain
  have sortedOne : sortedSet [v] = [v] := by
    simp [sortedSet, keepNew]
  have notGloas' : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt notGloas
  simp [isValidIndexedAttestation, single, sortedOne, notGloas', getValidator, found, getDomain,
    domainOk, rootOk, liftAccessor, liftSsz, SignatureChecks.acceptAll, bind, Except.bind, pure,
    Except.pure, Except.mapError]

/-- The events of a witness: wait for a time, tick, send, then let time go on. -/
def tickSendEvents {ν μ σ : Type*} (tickTime : ℕ) (v : ν) (ticked : σ) (m : μ) :
    ℕ → Event ν μ σ
  | 0 => .wait tickTime
  | 1 => .move v ticked
  | 2 => .send v m
  | n + 3 => .wait (tickTime + n + 1)

/-- After the tick, the clock is at the time, nothing is sent, and the validator has ticked. -/
theorem worldAt_tickSend_two {ν μ σ : Type*} [DecidableEq ν] {time tickTime : ℕ}
    {state : ν → σ} {v : ν} {ticked : σ} {m : μ} :
    worldAt (World.initial time state) (tickSendEvents tickTime v ticked m) 2 =
      ⟨tickTime, ∅, fun _ => ∅, Function.update state v ticked⟩ := by
  simp [worldAt, tickSendEvents, World.initial, World.apply]

/-- After the send, only that message is sent, and the clock moves on by one at each event. -/
theorem worldAt_tickSend {ν μ σ : Type*} [DecidableEq ν] {time tickTime : ℕ}
    {state : ν → σ} {v : ν} {ticked : σ} {m : μ} (n : ℕ) :
    worldAt (World.initial time state) (tickSendEvents tickTime v ticked m) (n + 3) =
      ⟨tickTime + n, {m}, Function.update (fun _ => ∅) v {m}, Function.update state v ticked⟩ := by
  induction n with
  | zero =>
    rw [worldAt, worldAt_tickSend_two]
    simp only [tickSendEvents, World.apply, Nat.add_zero]
    congr 1
    · simp
    · funext u
      by_cases same : u = v
      · subst same
        simp
      · simp [Function.update_of_ne same]
  | succ n ih =>
    rw [worldAt, ih]
    simp [tickSendEvents, World.apply]
    omega

/-- Honest validators that vote have an execution, with one honest validator that votes.

The witness covers one validator, one slot and one fork range, with no state built here. -/
theorem exists_votes_execution {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    -- The store starts from an anchor.
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok store)
    -- The block and the state of the anchor sit at slot zero.
    (stateZero : anchorState.slot = 0) (blockZero : anchorBlock.slot = 0)
    -- The fork is before Electra.
    (before : fork < .pectra)
    -- The anchor block does not name its own root as its parent.
    (parent : ∀ root, SszType.hashTreeRoot anchorBlock = .ok root → anchorBlock.parentRoot ≠ root)
    {committee : Array ValidatorIndex}
    -- The committee is the first committee of slot zero, in the anchor state.
    (committeeOk : getBeaconCommittee anchorState 0 0 = .ok committee) {v : ValidatorIndex}
    -- The validator `v` holds the first seat of that committee.
    --
    -- That committee fits in the bits of an attestation.
    (first : committee[0]? = some v) (small : committee.size ≤ maxAttesters preset fork)
    (slots : 0 < config.SLOT_DURATION_MS) {due : UInt64}
    -- The attestation deadline of slot zero falls inside the slot.
    (dueOk : getAttestationDueMs config fork = .ok due) (inSlot : due < config.SLOT_DURATION_MS)
    -- That deadline fits in 64 bits.
    (fits : store.genesisTimeMs.toNat + due.toNat < 2 ^ 64) {Δ : ℕ} (positive : 0 < Δ) :
    -- Signature checks accept every signature, as the consensus test vectors with placeholders do.
    ∃ e : Execution (honestForkChoice config .acceptAll sources anchorState anchorBlock
        -- The assignment puts the validator in that committee, and in no other slot.
        (Assignment.single v 0 0) store.genesisTimeMs) {v},
      -- The execution starts at the time of the anchor.
      e.startTime = store.timeMs.toNat ∧ e.start = (fun _ => store) ∧
      -- The validator votes at the deadline.
      (∃ attestation, e.events 2 = .send v (.attestation attestation)) ∧
      -- The validator does its duty to vote.
      --
      -- The execution is synchronous for every positive delay.
      Votes 0 e ∧ e.Synchronous Δ ∧
      -- The store of the validator stays reachable from the anchor.
      ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state v) := by
  obtain ⟨anchorRoot, blockRooted, checkpoints⟩ := getForkchoiceStore_checkpointStates anchored
  have stored : store.checkpointStates[(⟨getCurrentEpoch anchorState, anchorRoot⟩ : Checkpoint)]? =
      some anchorState := by
    simp [checkpoints]
  -- The anchor sits at slot zero, so the clock of the store starts at genesis.
  have clock : store.timeMs = store.genesisTimeMs := by
    have timeOk := (getForkchoiceStore_timeMs anchored).2
    have bounded := UInt64.toNat_lt store.genesisTimeMs
    simp [stateZero, computeTimeAtSlotMs, Uint64.mulChecked, Uint64.addChecked, bind,
      Except.bind, bounded] at timeOk
    exact timeOk.symm
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
      by simp [lookaheadState, stateZero, pure, Except.pure], ?_⟩
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
      ReadsAttestation config .acceptAll ticked attestation indexed ∧
        indexed.attestingIndices.data.toList = [v] :=
    readsAttestation_firstSeat (config := config) (store := ticked) (attestation := attestation)
      before stored committeeOk rfl rfl first rfl
  have statementData : ∀ x ∈ statements config .acceptAll anchorState anchorBlock
      (.attestation attestation), x.2 = data := by
    intro x mem
    obtain ⟨_, read, -, ⟨_, targetState, -, -, readIndexed, -⟩, member⟩ := mem
    rw [member.2]
    -- The read succeeds, so the signers have a value, and the indexed form keeps the data.
    cases computed : getAttestingIndices targetState attestation with
    | error failure =>
      rw [← getIndexedAttestation_eq_error_iff, readIndexed] at computed
      cases computed
    | ok attesters =>
      obtain ⟨indexed', indexedOk, -, sameData, -⟩ :=
        getIndexedAttestation_of_getAttestingIndices computed
      rw [readIndexed, Except.ok.injEq] at indexedOk
      rw [indexedOk, sameData]
  have deadlineOk : IsAttestationDeadline fork config store.genesisTimeMs 0 deadline := by
    refine ⟨store.genesisTimeMs, due, ?_, dueOk, rfl⟩
    have bounded := UInt64.toNat_lt store.genesisTimeMs
    simp [computeTimeAtSlotMs, Uint64.mulChecked, Uint64.addChecked, bind, Except.bind, bounded]
  have maySign : MaySign config .acceptAll sources anchorState anchorBlock
      (Assignment.single v 0 0) store.genesisTimeMs v deadline ∅
      ticked data :=
    ⟨0, by simp [data, Assignment.single], deadlineOk, rfl, upToDate, honestData, by simp⟩
  -- The execution waits for the deadline, ticks the store, votes, then lets time go on.
  let e : Execution (honestForkChoice config .acceptAll sources anchorState anchorBlock
      (Assignment.single v 0 0) store.genesisTimeMs) {v} :=
    { startTime := store.timeMs.toNat
      start := fun _ => store
      events := tickSendEvents deadline v ticked (.attestation attestation)
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
          rw [worldAt_tickSend_two]
          intro x mem _
          refine .inr ?_
          rw [statementData x mem]
          simpa using maySign
        | n + 3 =>
          rw [worldAt_tickSend]
          show deadline + n ≤ deadline + n + 1
          omega }
  have worldTwo :
      e.world 2 = ⟨deadline, ∅, fun _ => ∅, Function.update (fun _ => store) v ticked⟩ :=
    worldAt_tickSend_two
  have later : ∀ n, e.world (n + 3) = ⟨deadline + n, {.attestation attestation},
      Function.update (fun _ => ∅) v {.attestation attestation},
      Function.update (fun _ => store) v ticked⟩ :=
    worldAt_tickSend
  refine ⟨e, rfl, rfl, ⟨attestation, rfl⟩, ?_, ⟨positive, fun T => ⟨T + 3, ?_⟩, ?_⟩,
    fun n => e.reachable (fun u _ => .anchor anchored) n v rfl⟩
  · -- The only duty is in slot zero, at the deadline, and the vote of the third event does it.
    intro u honest slot committeeIndex time assigned atDeadline _ _
    rw [Set.mem_singleton_iff] at honest
    subst honest
    obtain ⟨rfl, rfl⟩ : slot = 0 ∧ committeeIndex = 0 := by
      simp only [Assignment.single] at assigned
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
