module

public import EthLib.Consensus.Exports.Transition
public import EthLib.Consensus.ForkChoice.Handlers
public import EthLib.Consensus.ForkChoice.ProposerHead

/-!
# `Exports.ForkChoice`

A C-ABI export that runs a case of the fork choice vectors on one store.

The store starts from an anchor state and an anchor block, given in SSZ.

The steps arrive one after another in one byte string.

Each step is one byte for its kind, a 4-byte length, then that many bytes.

Kind 0 moves the clock to a time in seconds, given in 8 bytes.

Kind 1 adds a signed block with its votes, kind 2 an attestation and kind 3 an attester slashing.

Kind 4 reads the store, and a byte of 1 also asks where the proposer of the slot builds.

After each step comes one byte: 0 when the store takes the step, 1 when it rejects it.

A rejection leaves the store as it was, and carries its error code, a length and a message.

A read gives the head as a slot and a root, then the time and the genesis time in milliseconds.

Then come the justified and the finalized checkpoints, each an epoch and a root.

Last come the boosted root and, when asked, the root on which the proposer builds.

Numbers are little-endian, and a code is 4 bytes.

An input that the export reads itself, such as a wrong length, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result)

/-- A result of the fork choice, with the code of its error. -/
def runForkChoice {α : Type} (result : Except ForkChoiceError α) : Result α :=
  result.mapError fun e => (e.code, s!"fork choice: {reprStr e}")

/-- The little-endian bytes of a number, in a given width. -/
def littleEndian (width value : Nat) : ByteArray :=
  Base.packBytes (uintToBytes width value)

/-- A step of a fork choice case: its kind and its bytes. -/
abbrev ForkChoiceStep := UInt8 × ByteArray

/-- The steps that the bytes hold from an offset.

Each step reads at least 5 bytes, so one round more than the bytes suffices. -/
def readForkChoiceSteps : (rounds : Nat) → ByteArray → Nat → Result (List ForkChoiceStep)
  | 0, _, _ => throw (0, "steps do not end")
  | rounds + 1, bytes, offset =>
    if offset = bytes.size then return []
    else if bytes.size < offset + 5 then throw (0, "a step is cut short")
    else do
      let length := (← decodeInput UInt32 (bytes.extract (offset + 1) (offset + 5))).toNat
      let stop := offset + 5 + length
      if bytes.size < stop then throw (0, "the bytes of a step are cut short")
      let rest ← readForkChoiceSteps rounds bytes stop
      return (bytes.get! offset, bytes.extract (offset + 5) stop) :: rest

/-- The epoch and the root of a checkpoint, in 40 bytes. -/
def checkpointRecord (checkpoint : Checkpoint) : ByteArray :=
  littleEndian 8 checkpoint.epoch.toNat ++ Base.packBytes checkpoint.root

/-- What a read of the store gives, and if asked where the proposer of the slot builds. -/
def storeRecord {preset : Preset} {fork : Fork} (config : Config) (store : Store preset fork)
    (proposerHead : Bool) : Except ForkChoiceError ByteArray := do
  let head ← store.getHead config
  let headBlock ← store.block head.root
  let record := littleEndian 8 headBlock.slot.toNat ++ Base.packBytes head.root ++
    littleEndian 8 store.timeMs.toNat ++ littleEndian 8 store.genesisTimeMs.toNat ++
    checkpointRecord store.justifiedCheckpoint ++ checkpointRecord store.finalizedCheckpoint ++
    Base.packBytes store.proposerBoostRoot
  if proposerHead then
    let slot ← store.getCurrentSlot config
    return record ++ Base.packBytes (← store.getProposerHead config head slot).root
  return record

/-- The store after a step and the bytes that the step reports, or the error that rejects it. -/
def runForkChoiceStep {preset : Preset} {fork : Fork} (config : Config) (checks : SignatureChecks)
    (store : Store preset fork) :
    ForkChoiceStep → Result (Except ForkChoiceError (Store preset fork × ByteArray))
  | (0, data) => do
    let seconds ← decodeInput UInt64 data
    return (·, .empty) <$> store.onTick config (secondsToMilliseconds seconds)
  | (1, data) => do
    let signed ← decodeInput (SignedBeaconBlock preset fork) data
    return (·, .empty) <$> store.onBlockWithVotes config checks signed
  | (2, data) => do
    let attestation ← decodeInput (Attestation preset fork) data
    return (·, .empty) <$> store.onAttestation config checks attestation false
  | (3, data) => do
    let slashing ← decodeInput (AttesterSlashing preset fork) data
    return (·, .empty) <$> store.onAttesterSlashing config checks slashing
  | (4, data) => do
    let proposerHead ← match data.toList with
      | [0] => pure false
      | [1] => pure true
      | _ => throw (0, "a read takes one byte, 0 or 1")
    return (store, ·) <$> storeRecord config store proposerHead
  | (kind, _) => throw (0, s!"no step of kind {kind}")

/-- The outcome of each step of a fork choice case, from an anchor state and an anchor block.

The preset, the configuration and the fork are named in UTF-8.

The signature checks run unless the last argument is false.

From Bellatrix a block is not yet specified here, and from Gloas neither is the store. -/
@[export eth_consensus_fork_choice]
def forkChoiceExport (name fork anchorState anchorBlock steps replacements : ByteArray)
    (verify : Bool) : Result ByteArray := do
  let preset ← presetOf (← nameOf name)
  let fork ← forkOf fork
  let config ← configWith name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let anchorState ← decodeInput (BeaconState preset fork) anchorState
  let anchorBlock ← decodeInput (BeaconBlock preset fork) anchorBlock
  let mut store ← runForkChoice (getForkchoiceStore config anchorState anchorBlock)
  let mut out := ByteArray.empty
  for step in ← readForkChoiceSteps (steps.size + 1) steps 0 do
    match ← runForkChoiceStep config checks store step with
    | .ok (next, record) =>
      store := next
      out := out.push 0 ++ record
    | .error e =>
      let message := (reprStr e).toUTF8
      out := out.push 1 ++ littleEndian 4 e.code.toNat ++ littleEndian 4 message.size ++ message
  return out

end EthLib.Consensus.Exports
