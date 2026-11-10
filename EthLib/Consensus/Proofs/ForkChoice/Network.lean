module

public import EthLib.Consensus.Proofs.Containers.State
public import EthLib.Consensus.Proofs.ForkChoice.Reachable
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

/-- Along an execution, the store of each honest validator stays reachable from the anchor.

The stores of the honest validators must be reachable at the start. -/
theorem Execution.reachable {ν κ : Type*} [DecidableEq ν] {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    (start : ∀ v ∈ J, Store.Reachable config anchorState anchorBlock (e.start v)) (n : ℕ) :
    ∀ v ∈ J, Store.Reachable config anchorState anchorBlock ((e.world n).state v) :=
  e.state_induction start (fun _ _ _ _ _ _ reachable moved => moved.reachable reachable) n

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
