module

public import EthLib.Consensus.Proofs.Containers.State
public import EthLib.Consensus.Proofs.ForkChoice.ForwardClock
public import EthLib.Consensus.Proofs.Models.Network.Model

/-!
# Proofs: honest validators that run the fork choice over the network

Each honest validator keeps a store of the fork choice.

At each move it ticks its store to the current time, or processes a message of its view.

The messages are those of the fork choice handlers.

A block is processed with the votes and slashings that it carries.

The block is rejected with them when one of them is rejected.

A message that the handler rejects leaves the store as it was, and may be processed later.

What lies outside the beacon chain, such as the execution engine, is one source for all.

The store of each honest validator stays reachable from the anchor along every execution.

Along an execution of the network model, an honest store that starts with a forward clock keeps one.

An honest store built with the signature checks of the model stays built that way.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- A message of the fork choice. -/
inductive Message (preset : Preset) (fork : Fork)
  /-- A signed block. -/
  | block (signed : SignedBeaconBlock preset fork)
  /-- An attestation. -/
  | attestation (attestation : Attestation preset fork)
  /-- An attester slashing. -/
  | attesterSlashing (slashing : AttesterSlashing preset fork)
  /-- From Gloas, a vote of a member of the payload committee. -/
  | payloadAttestation (gloas : .glamsterdam ≤ fork) (message : PayloadAttestationMessage)
  /-- From Gloas, a signed envelope. -/
  | envelope (gloas : .glamsterdam ≤ fork) (signed : SignedExecutionPayloadEnvelope preset fork)
  /-- From Heze, a signed inclusion list. -/
  | inclusionList (heze : .hegota ≤ fork) (signed : SignedInclusionList)

/-- The moves of the store of an honest validator, at a time and with a view.

A tick sets the store to the time, which must fit in 64 bits.

That time must not lie before the clock of the store.

Every other move processes a message of the view, as one from the network.

The votes inside a block are processed with it, and a rejected vote rejects the block.

Blocks and envelopes are judged with the given sources outside the beacon chain. -/
inductive Handles (config : Config) (checks : SignatureChecks) (sources : BlockSources preset fork)
    (time : ℕ) (view : Set (Message preset fork)) (store : Store preset fork) :
    Store preset fork → Prop
  /-- The store after a tick at the time. -/
  | tick {after : Store preset fork} :
    store.timeMs.toNat ≤ time → time < 2 ^ 64 → store.onTick config time.toUInt64 = .ok after →
      Handles config checks sources time view store after
  /-- The store after a block of the view, with its votes. -/
  | block {after : Store preset fork} {signed : SignedBeaconBlock preset fork} :
    .block signed ∈ view → store.onBlockWithVotes config checks sources signed = .ok after →
      Handles config checks sources time view store after
  /-- The store after an attestation of the view. -/
  | attestation {after : Store preset fork} {attestation : Attestation preset fork} :
    .attestation attestation ∈ view →
      store.onAttestation config checks attestation false = .ok after →
      Handles config checks sources time view store after
  /-- The store after an attester slashing of the view. -/
  | attesterSlashing {after : Store preset fork} {slashing : AttesterSlashing preset fork} :
    .attesterSlashing slashing ∈ view →
      store.onAttesterSlashing config checks slashing = .ok after →
      Handles config checks sources time view store after
  /-- From Gloas, the store after a vote of the payload committee from the view. -/
  | payloadAttestation {after : Store preset fork} {gloas : .glamsterdam ≤ fork}
      {message : PayloadAttestationMessage} :
    .payloadAttestation gloas message ∈ view →
      store.onPayloadAttestationMessage config checks gloas message false = .ok after →
      Handles config checks sources time view store after
  /-- From Gloas, the store after a signed envelope of the view. -/
  | envelope {after : Store preset fork} {gloas : .glamsterdam ≤ fork}
      {signed : SignedExecutionPayloadEnvelope preset fork} :
    .envelope gloas signed ∈ view →
      store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after →
      Handles config checks sources time view store after
  /-- From Heze, the store after an inclusion list of the view. -/
  | inclusionList {after : Store preset fork} {heze : .hegota ≤ fork}
      {signed : SignedInclusionList} :
    .inclusionList heze signed ∈ view →
      store.onInclusionList config checks heze signed = .ok after →
      Handles config checks sources time view store after

/-- The protocol where honest validators run the fork choice.

The signed statements of a message and the messages that honest validators send are parameters.

The moves of an honest validator are those of its store, with sources shared by all. -/
def forkChoice {ν κ : Type*} (config : Config) (checks : SignatureChecks)
    (sources : BlockSources preset fork) (signed : Message preset fork → Set (ν × κ))
    (sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop) :
    Protocol ν (Message preset fork) (Store preset fork) κ where
  signed := signed
  Sends := sends
  Moves := fun _ time view store after => Handles config checks sources time view store after

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork}

/-- A move of the store leads from a reachable store to a reachable store. -/
theorem Handles.reachable {checks : SignatureChecks} {sources : BlockSources preset fork}
    {time : ℕ} {view : Set (Message preset fork)} {store after : Store preset fork}
    (handles : Handles config checks sources time view store after)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    Store.Reachable config anchorState anchorBlock after := by
  cases handles with
  | tick _ _ ticked => exact reachable.tick ticked
  | block _ added => exact reachable.onBlockWithVotes added
  | attestation _ attested => exact reachable.attestation attested
  | attesterSlashing _ slashed => exact reachable.attesterSlashing slashed
  | payloadAttestation _ voted => exact reachable.payloadAttestation voted
  | envelope _ accepted => exact reachable.envelope accepted
  | inclusionList _ accepted => exact reachable.inclusionList accepted

/-- Once a store admits a block, every later event retains it. -/
theorem Execution.blocks_of_le {ν κ : Type*} [DecidableEq ν] {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    {u : ν} {n k : ℕ} (later : n ≤ k) {root : Root} {block : BeaconBlock preset fork}
    (found : ((e.world n).state u).blocks[root]? = some block) :
    ((e.world k).state u).blocks[root]? = some block := by
  induction k, later using Nat.le_induction with
  | base => exact found
  | succ k _ ih =>
    rcases e.state_succ k u with same | ⟨_, moved⟩
    · exact same ▸ ih
    · cases moved with
      | tick _ _ step => exact (Store.onTick_frame step).2.2.1 ▸ ih
      | block _ step =>
        exact Store.onBlockWithVotes_preserves
          (fun held ok => Store.onBlock_blocks_of_found ok held)
          (fun _ held ok => (Store.onAttestation_frame ok).2.1 ▸ held)
          (fun _ held ok => (Store.onAttesterSlashing_frame ok).2.1 ▸ held) ih step
      | attestation _ step => exact (Store.onAttestation_frame step).2.1 ▸ ih
      | attesterSlashing _ step => exact (Store.onAttesterSlashing_frame step).2.1 ▸ ih
      | payloadAttestation _ step =>
        exact (Store.onPayloadAttestationMessage_onlyPtcVotes step).frame.2.1 ▸ ih
      | envelope _ step => exact (Store.onExecutionPayloadEnvelope_frame step).2.1 ▸ ih
      | inclusionList _ step => exact (Store.onInclusionList_frame step).2.1 ▸ ih

/-- A move of the store keeps each checkpoint, or moves it to one at a greater epoch. -/
theorem Handles.checkpointsAdvance {checks : SignatureChecks}
    {sources : BlockSources preset fork} {time : ℕ} {view : Set (Message preset fork)}
    {store after : Store preset fork}
    (handles : Handles config checks sources time view store after) :
    store.CheckpointsAdvance after := by
  cases handles with
  | tick _ _ ticked => exact (Store.onTick_frame ticked).2.1
  | block _ added => exact Store.onBlockWithVotes_checkpointsAdvance added
  | attestation _ attested => exact (Store.onAttestation_frame attested).1
  | attesterSlashing _ slashed => exact (Store.onAttesterSlashing_frame slashed).1
  | payloadAttestation _ voted =>
    exact (Store.onPayloadAttestationMessage_onlyPtcVotes voted).frame.1
  | envelope _ accepted => exact (Store.onExecutionPayloadEnvelope_frame accepted).1
  | inclusionList _ accepted => exact (Store.onInclusionList_frame accepted).1

/-- Realized checkpoint epochs never decrease along an execution. -/
theorem Execution.checkpointsAdvance_of_le {ν κ : Type*} [DecidableEq ν]
    {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    (u : ν) {n k : ℕ} (later : n ≤ k) :
    ((e.world n).state u).CheckpointsAdvance ((e.world k).state u) := by
  induction k, later using Nat.le_induction with
  | base => exact Store.CheckpointsAdvance.refl _
  | succ k _ ih =>
    rcases e.state_succ k u with same | ⟨_, moved⟩
    · exact same ▸ ih
    · exact ih.trans moved.checkpointsAdvance

/-- Store clocks stay between the initial clock and the maximum of it and network time.

Non-honest local states are frozen by this network model. -/
theorem Execution.clock_bounds {ν κ : Type*} [DecidableEq ν] {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    (v : ν) (i : ℕ) :
    ((e.world i).state v).genesisTimeMs = (e.start v).genesisTimeMs ∧
      (e.start v).timeMs ≤ ((e.world i).state v).timeMs ∧
      ((e.world i).state v).timeMs.toNat ≤ max (e.start v).timeMs.toNat (e.world i).time := by
  have bounds {time : ℕ} {view} {s t : Store preset fork}
      (h : Handles config checks sources time view s t) :
      t.genesisTimeMs = s.genesisTimeMs ∧ s.timeMs ≤ t.timeMs ∧
        t.timeMs.toNat ≤ max s.timeMs.toNat time := by
    have same (h : Store.SameClock s t) :
        t.genesisTimeMs = s.genesisTimeMs ∧ s.timeMs ≤ t.timeMs ∧
          t.timeMs.toNat ≤ max s.timeMs.toNat time := by
      rw [h.1, h.2]
      exact ⟨rfl, UInt64.le_refl _, Nat.le_max_left _ _⟩
    cases h with
    | tick le fits tick =>
      have g : t.genesisTimeMs = s.genesisTimeMs := by
        unfold Store.onTick at tick
        simp only [bind_ok_iff] at tick
        obtain ⟨_, _, _, catchup, perSlot⟩ := tick
        exact (Store.onTickPerSlot_frame perSlot).2.1.trans (Store.catchUp_frame catchup).1
      have tm : t.timeMs.toNat = time := by
        rw [(Store.onTick_frame tick).1]
        exact UInt64.toNat_ofNat_of_lt' fits
      exact ⟨g, UInt64.le_iff_toNat_le.mpr (tm ▸ le), by rw [tm]; omega⟩
    | block _ h => exact same (Store.onBlockWithVotes_sameClock h)
    | attestation _ h => exact same (Store.onAttestation_sameClock h)
    | attesterSlashing _ h => exact same (Store.onAttesterSlashing_sameClock h)
    | payloadAttestation _ h => exact same (Store.onPayloadAttestationMessage_sameClock h)
    | envelope _ h => exact same (Store.onExecutionPayloadEnvelope_sameClock h)
    | inclusionList _ h => exact same (Store.onInclusionList_sameClock h)
  induction i with
  | zero => exact ⟨rfl, UInt64.le_refl _, Nat.le_max_left _ _⟩
  | succ i ih =>
    have time := e.monotone_time (Nat.le_succ i)
    change (e.world i).time ≤ (e.world (i+1)).time at time
    rcases e.state_succ i v with eq | ⟨_, move⟩
    · rw [eq]
      exact ⟨ih.1, ih.2.1, by omega⟩
    · have h := bounds move
      exact ⟨h.1.trans ih.1, UInt64.le_trans ih.2.1 h.2.1, by omega⟩

/-- A newly held block passed validation at an earlier event of the execution. -/
theorem Execution.exists_validated_of_blocks {ν κ : Type*} [DecidableEq ν]
    {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    {v : ν} {n : ℕ} {r : Root} {b : BeaconBlock preset fork}
    (found : ((e.world n).state v).blocks[r]? = some b) :
    (e.start v).blocks[r]? = some b ∨
      ∃ i, i < n ∧ ∃ sb post,
        .block sb ∈ (e.world i).view v ∧ sb.message = b ∧
        SszType.hashTreeRoot sb.message = .ok r ∧
        ((e.world i).state v).validateOnBlock config checks sources sb r = .ok post := by
  induction n with
  | zero => exact .inl found
  | succ n ih =>
    by_cases held : ((e.world n).state v).blocks[r]? = some b
    · rcases ih held with old | ⟨i, lt, rest⟩
      · exact .inl old
      · exact .inr ⟨i, Nat.lt_trans lt (Nat.lt_succ_self n), rest⟩
    have frames {s t : Store preset fork} (h : t.blocks = s.blocks)
        (old : s = (e.world n).state v) (new : t = (e.world (n+1)).state v) : False := by
      subst s
      subst t
      exact held (h ▸ found)
    rcases e.state_succ n v with same | ⟨_, moved⟩
    · exact False.elim (held (same ▸ found))
    cases moved with
    | tick _ _ h => exact False.elim (frames (Store.onTick_frame h).2.2.1 rfl rfl)
    | attestation _ h => exact False.elim (frames (Store.onAttestation_frame h).2.1 rfl rfl)
    | attesterSlashing _ h =>
      exact False.elim (frames (Store.onAttesterSlashing_frame h).2.1 rfl rfl)
    | payloadAttestation _ h =>
      exact False.elim (frames (Store.onPayloadAttestationMessage_onlyPtcVotes h).frame.2.1 rfl rfl)
    | envelope _ h =>
      exact False.elim (frames (Store.onExecutionPayloadEnvelope_frame h).2.1 rfl rfl)
    | inclusionList _ h =>
      exact False.elim (frames (Store.onInclusionList_frame h).2.1 rfl rfl)
    | @block sb mem added =>
      unfold Store.onBlockWithVotes at added
      simp only [bind_ok_iff, ← Array.foldlM_toList] at added
      obtain ⟨blocked, blockOk, voted, attested, slashed⟩ := added
      have av := foldlM_ok_invariant (fun s => s.blocks = blocked.blocks)
        (fun _ _ _ eq step => (Store.onAttestation_frame step).2.1.trans eq) rfl attested
      have sv := foldlM_ok_invariant (fun s => s.blocks = blocked.blocks)
        (fun _ _ _ eq step => (Store.onAttesterSlashing_frame step).2.1.trans eq) av slashed
      have bf : blocked.blocks[r]? = some b := sv ▸ found
      rcases Store.onBlock_same_or_insert blockOk with same | ⟨q, hash, fresh, maps, rest⟩
      · exact False.elim (held (same ▸ bf))
      rw [maps, getElem?_insert_root] at bf
      by_cases eq : q = r
      · subst q
        simp only [↓reduceIte, Option.some.injEq] at bf
        right
        refine ⟨n, Nat.lt_succ_self n, sb, ?_⟩
        unfold Store.onBlock at blockOk
        simp only [hash, Except.mapError, bind, Except.bind,
          Std.TreeMap.contains_eq_isSome_getElem?, fresh, Option.isSome_none,
          Bool.false_eq_true, ↓reduceIte] at blockOk
        unfold Store.addBlock at blockOk
        simp only [bind_ok_iff] at blockOk
        obtain ⟨post, valid, _⟩ := blockOk
        exact ⟨post, mem, bf, hash, valid⟩
      · simp only [eq, ↓reduceIte] at bf
        exact False.elim (held bf)

/-- Along an execution, the store of each honest validator stays reachable from the anchor.

The stores of the honest validators must be reachable at the start. -/
theorem Execution.reachable {ν κ : Type*} [DecidableEq ν] {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    (start : ∀ v ∈ J, Store.Reachable config anchorState anchorBlock (e.start v)) (n : ℕ) :
    ∀ v ∈ J, Store.Reachable config anchorState anchorBlock ((e.world n).state v) :=
  e.state_induction start (fun _ _ _ _ _ _ reachable moved => moved.reachable reachable) n

/-- A move of an honest validator keeps its store reachable with a forward clock. -/
theorem Handles.forwardReachable {checks : SignatureChecks} {sources : BlockSources preset fork}
    {time : ℕ} {view : Set (Message preset fork)} {store after : Store preset fork}
    (handles : Handles config checks sources time view store after)
    (forward : Store.ForwardReachable config anchorState anchorBlock store) :
    Store.ForwardReachable config anchorState anchorBlock after := by
  cases handles with
  | tick le lt ticked =>
    refine forward.tick ?_ ticked
    rw [UInt64.le_iff_toNat_le, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' lt]
    exact le
  | block _ added => exact forward.onBlockWithVotes added
  | attestation _ attested => exact forward.attestation attested
  | attesterSlashing _ slashed => exact forward.attesterSlashing slashed
  | payloadAttestation _ voted => exact forward.payloadAttestation voted
  | envelope _ accepted => exact forward.envelope accepted
  | inclusionList _ accepted => exact forward.inclusionList accepted

/-- Along an execution, the store of each honest validator stays reachable with a forward clock.

The stores of the honest validators must be reachable with a forward clock at the start. -/
theorem Execution.forwardReachable {ν κ : Type*} [DecidableEq ν] {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    (start : ∀ v ∈ J, Store.ForwardReachable config anchorState anchorBlock (e.start v)) (n : ℕ) :
    ∀ v ∈ J, Store.ForwardReachable config anchorState anchorBlock ((e.world n).state v) :=
  e.state_induction start (fun _ _ _ _ _ _ forward moved => moved.forwardReachable forward) n

/-- A move of an honest validator keeps its store built with the setting of the checks of the model.

The clock of that store also stays forward. -/
theorem Handles.forwardReachableWith {checks : SignatureChecks}
    {sources : BlockSources preset fork} {time : ℕ} {view : Set (Message preset fork)}
    {store after : Store preset fork}
    (handles : Handles config checks sources time view store after)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store) :
    Store.ForwardReachableWith config checks anchorState anchorBlock after := by
  cases handles with
  | tick le lt ticked =>
    refine reached.tick ?_ ticked
    rw [UInt64.le_iff_toNat_le, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' lt]
    exact le
  | block _ added => exact reached.onBlockWithVotes added
  | attestation _ attested => exact reached.attestation attested
  | attesterSlashing _ slashed => exact reached.attesterSlashing slashed
  | payloadAttestation _ voted => exact reached.payloadAttestation voted
  | envelope _ accepted => exact reached.envelope accepted
  | inclusionList _ accepted => exact reached.inclusionList accepted

/-- Along an execution, each honest store stays built with the setting of the checks of the model.

The stores of the honest validators must be built that way at the start. -/
theorem Execution.forwardReachableWith {ν κ : Type*} [DecidableEq ν] {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    (start : ∀ v ∈ J, Store.ForwardReachableWith config checks anchorState anchorBlock (e.start v))
    (n : ℕ) :
    ∀ v ∈ J, Store.ForwardReachableWith config checks anchorState anchorBlock
      ((e.world n).state v) :=
  e.state_induction start (fun _ _ _ _ _ _ reached moved => moved.forwardReachableWith reached) n

/-- A store can start from a mainnet state at slot zero and a block with the root of that state.

Other presets are not covered.
-/
theorem exists_getForkchoiceStore (config : Config) {state : BeaconState .mainnet fork}
    (zero : state.slot = 0) (block : BeaconBlock .mainnet fork) :
    ∃ stateRoot store, SszType.hashTreeRoot state = .ok stateRoot ∧
      getForkchoiceStore config state { block with stateRoot } = .ok store := by
  have : NeZero Preset.mainnet.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
  obtain ⟨stateRoot, rooted⟩ := SszType.hashTreeRoot_total state
  obtain ⟨blockRoot, blockRooted⟩ :=
    SszType.hashTreeRoot_total ({ block with stateRoot } : BeaconBlock .mainnet fork)
  have time : computeTimeAtSlotMs config (secondsToMilliseconds state.genesisTime) state.slot =
      .ok (secondsToMilliseconds state.genesisTime) := by
    have fits := UInt64.toNat_lt (secondsToMilliseconds state.genesisTime)
    simp [computeTimeAtSlotMs, zero, Uint64.mulChecked, Uint64.addChecked, bind, Except.bind,
      fits]
  refine ⟨stateRoot, ?_⟩
  simp only [true_and, getForkchoiceStore, rooted, blockRooted, time, Except.mapError, bind,
    Except.bind, ne_eq, not_true_eq_false, ite_false]
  exact ⟨_, rfl⟩

/-- A store ticks to a time in its current slot by setting its clock to that time alone. -/
theorem onTick_sameSlot {store : Store preset fork} {slot : Slot} {timeMs : UInt64}
    (current : store.getCurrentSlot config = .ok slot)
    (slotted : computeSlotAtTimeMs config store.genesisTimeMs timeMs = .ok slot) :
    store.onTick config timeMs = .ok { store with timeMs } := by
  have caught : Store.catchUp config store slot = .ok store := by
    rw [Store.catchUp]
    simp [current, bind, Except.bind, pure, Except.pure]
  have later : ({ store with timeMs } : Store preset fork).getCurrentSlot config = .ok slot := by
    simp [Store.getCurrentSlot, slotted, Except.mapError]
  have ticked : store.onTickPerSlot config timeMs = .ok { store with timeMs } := by
    simp [Store.onTickPerSlot, current, later, computeSlotsSinceEpochStart,
      computeStartSlotAtEpoch_computeEpochAtSlot, bind, Except.bind, pure, Except.pure,
      Except.mapError]
  simp [Store.onTick, slotted, caught, ticked, Except.mapError, bind, Except.bind]

/-- A store whose clock has a slot ticks to its own time and stays as it is. -/
theorem onTick_timeMs {store : Store preset fork} {slot : Slot}
    (current : store.getCurrentSlot config = .ok slot) :
    store.onTick config store.timeMs = .ok store := by
  have slotted : computeSlotAtTimeMs config store.genesisTimeMs store.timeMs = .ok slot := by
    unfold Store.getCurrentSlot at current
    cases computed : computeSlotAtTimeMs config store.genesisTimeMs store.timeMs with
    | error e => simp [computed, Except.mapError] at current
    | ok s => simpa [computed, Except.mapError] using current
  exact onTick_sameSlot current slotted

/-- A store built from an anchor can tick to its own time, when slots last a positive time.

So an honest validator can move from such a store, whatever its view. -/
theorem Handles.tick_anchor {checks : SignatureChecks} {sources : BlockSources preset fork}
    {store : Store preset fork} (positive : 0 < config.SLOT_DURATION_MS)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok store)
    (view : Set (Message preset fork)) :
    Handles config checks sources store.timeMs.toNat view store store := by
  refine .tick le_rfl (UInt64.toNat_lt _) ?_
  have round : store.timeMs.toNat.toUInt64 = store.timeMs :=
    UInt64.toNat_inj.mp (by simp)
  rw [round]
  exact onTick_timeMs (getCurrentSlot_getForkchoiceStore positive anchored)

/-- Honest validators that run the fork choice have an execution where a block reaches all.

No message carries a signed statement here, so unforgeability asks nothing.

Each validator starts from a store built from an anchor, and the clock starts at its time.

An honest validator sends a block from an empty view, as the protocol allows.

Two events later every validator has the block, with the clock and the stores as at the start.

The stores stay reachable.

There the honest validator may also move to its own store, when slots last a positive time.

The execution is partially synchronous for every GST and every positive delay. -/
theorem exists_forkChoice_execution {ν κ : Type*} [DecidableEq ν] (checks : SignatureChecks)
    (sources : BlockSources preset fork) {store : Store preset fork}
    (slots : 0 < config.SLOT_DURATION_MS)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok store)
    {J : Set ν} {v : ν} (honest : v ∈ J) (signed : SignedBeaconBlock preset fork) {Δ : ℕ}
    (positive : 0 < Δ) :
    ∃ e : Execution (forkChoice config checks sources (fun _ => (∅ : Set (ν × κ)))
        fun _ _ _ _ m => m = .block signed) J,
      e.startTime = store.timeMs.toNat ∧ e.start = (fun _ => store) ∧
      e.events 0 = .send v (.block signed) ∧ (e.world 2).time = store.timeMs.toNat ∧
      (e.world 2).state = (fun _ => store) ∧ (∀ u, .block signed ∈ (e.world 2).view u) ∧
      Allowed (forkChoice config checks sources (fun _ => (∅ : Set (ν × κ)))
        fun _ _ _ _ m => m = .block signed) J (e.world 2) (.move v store) ∧
      (∀ GST, e.PartiallySynchronous GST Δ) ∧
      ∀ n, ∀ u ∈ J, Store.Reachable config anchorState anchorBlock ((e.world n).state u) := by
  obtain ⟨e, startTime, start, sends, time, states, delivered, sync⟩ :=
    exists_partiallySynchronous
      (P := forkChoice config checks sources (fun _ => (∅ : Set (ν × κ)))
        fun _ _ _ _ m => m = .block signed) (time := store.timeMs.toNat)
      (state := fun _ => store) honest rfl (fun _ none => none.elim) positive
  refine ⟨e, startTime, start, sends, time, states, delivered, ⟨honest, ?_⟩, sync,
    e.reachable fun u _ => ?_⟩
  · show Handles config checks sources (e.world 2).time ((e.world 2).view v)
      ((e.world 2).state v) store
    rw [time, states]
    exact Handles.tick_anchor slots anchored _
  rw [start]
  exact .anchor anchored

end EthLib.Consensus.Models.Network
