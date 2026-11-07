module

public import EthLib.Consensus.Exports.Transition
public import EthLib.Consensus.ForkChoice.FastConfirmation
public import EthLib.Consensus.ForkChoice.Handlers
public import EthLib.Consensus.ForkChoice.Optimistic
public import EthLib.Consensus.ForkChoice.ProposerHead
public import EthLib.Cryptography.Exports.Kzg

/-!
# `Exports.ForkChoice`

A C-ABI export that runs a case of the fork choice vectors on one store.

The store starts from an anchor state and an anchor block, given in SSZ.

The steps arrive one after another in one byte string.

Each step is one byte for its kind, a 4-byte length, then that many bytes.

Kind 0 moves the clock to a time in seconds, given in 8 bytes.

Kind 1 adds a signed block with its votes, kind 2 an attestation and kind 3 an attester slashing.

Kind 4 reads the store, and a byte of 1 also asks where the proposer of the slot builds.

Kind 5 makes a block of proof of work known, in SSZ, for the merge check of later blocks.

Kind 6 gives the blobs and the proofs that the node holds for the next block.

It is a 4-byte count of blobs, then the blobs, then the proofs of 48 bytes each.

Without it the node holds no blob and no proof for a block.

Kind 7 gives the columns that the node samples for the next block.

It is a 4-byte count, then each column as a 4-byte length and its SSZ bytes.

A count of zero means that the node cannot get the columns.

Without it the node samples no column for a block.

Kind 8 gives the verdict of the execution layer on the payload of the next block.

A byte of 0 accepts the payload, and a byte of 1 finds it invalid.

An invalid verdict may add the 32 bytes of the latest valid hash of the chain.

The block then fails, and the blocks that the verdict finds invalid leave the store.

Without a verdict the execution layer accepts the payload.

Kind 9 runs the fast confirmation of the slot, on a store of its own that starts with the case.

It gives three checkpoints, each an epoch and a root.

They are the justified checkpoints that the node saw in the previous and the current epoch.

The third is the greatest unrealized checkpoint of the previous epoch.

Then come the heads of the previous and the current slot, and the confirmed root.

Before Bellatrix a byte of 0 ends it.

From Bellatrix a byte of 1 and the hash of the safe execution block end it.

After each step comes one byte: 0 when the store takes the step, 1 when it rejects it.

A rejection carries its error code, a length and a message.

It leaves the store as it was, except for the blocks that an invalid verdict removes.

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
    else if short : bytes.size < offset + 5 then throw (0, "a step is cut short")
    else do
      let length := (← decodeInput UInt32 (bytes.extract (offset + 1) (offset + 5))).toNat
      let stop := offset + 5 + length
      if bytes.size < stop then throw (0, "the bytes of a step are cut short")
      let rest ← readForkChoiceSteps rounds bytes stop
      return (bytes[offset]'(by omega), bytes.extract (offset + 5) stop) :: rest

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

/-- The bytes of a rejected step: a byte of 1, the error code, then the length and the message. -/
def rejection (e : ForkChoiceError) : ByteArray :=
  let message := (reprStr e).toUTF8
  (ByteArray.empty.push 1) ++ littleEndian 4 e.code.toNat ++ littleEndian 4 message.size ++ message

/-- What the fast confirmation of a slot gives, from Bellatrix with the safe execution block. -/
def fastConfirmationRecord {preset : Preset} {fork : Fork} (store : Store preset fork)
    (fcr : FastConfirmationStore) : Except ForkChoiceError ByteArray := do
  let record := checkpointRecord fcr.previousEpochObservedJustifiedCheckpoint ++
    checkpointRecord fcr.currentEpochObservedJustifiedCheckpoint ++
    checkpointRecord fcr.previousEpochGreatestUnrealizedCheckpoint ++
    Base.packBytes fcr.previousSlotHead ++ Base.packBytes fcr.currentSlotHead ++
    Base.packBytes fcr.confirmedRoot
  if bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam then
    return record.push 1 ++ Base.packBytes (← store.getSafeExecutionBlockHash fcr bellatrix)
  return record.push 0

/-- The store after a step and the bytes that the step reports, or the error that rejects it. -/
def runForkChoiceStep {preset : Preset} {fork : Fork} (config : Config) (checks : SignatureChecks)
    (sources : BlockSources preset fork) (store : Store preset fork) :
    ForkChoiceStep → Result (Except ForkChoiceError (Store preset fork × ByteArray))
  | (0, data) => do
    let seconds ← decodeInput UInt64 data
    return (·, .empty) <$> store.onTick config (secondsToMilliseconds seconds)
  | (1, data) => do
    let signed ← decodeInput (SignedBeaconBlock preset fork) data
    return (·, .empty) <$> store.onBlockWithVotes config checks sources signed
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

/-- The blobs and the proofs of a step: a count of blobs, the blobs, then the proofs. -/
def readBlobData (data : ByteArray) : Result (Array Cryptography.Kzg.Blob ×
    Array Cryptography.Kzg.KZGProof) := do
  if data.size < 4 then throw (0, "the count of blobs is cut short")
  let count := (← decodeInput UInt32 (data.extract 0 4)).toNat
  let blobBytes := count * Cryptography.Kzg.Constants.BYTES_PER_BLOB
  if data.size < 4 + blobBytes then throw (0, "the blobs are cut short")
  let proofBytes := data.size - (4 + blobBytes)
  if proofBytes % 48 ≠ 0 then throw (0, "the proofs are not 48 bytes each")
  let blobs ← (Array.range count).mapM fun i =>
    decodeInput Cryptography.Kzg.Blob
      (data.extract (4 + i * Cryptography.Kzg.Constants.BYTES_PER_BLOB)
        (4 + (i + 1) * Cryptography.Kzg.Constants.BYTES_PER_BLOB))
  let proofs ← (Array.range (proofBytes / 48)).mapM fun i =>
    decodeInput Cryptography.Kzg.KZGProof
      (data.extract (4 + blobBytes + i * 48) (4 + blobBytes + (i + 1) * 48))
  return (blobs, proofs)

/-- The columns of a step: a count, then each column as a length and its SSZ bytes.

A count of zero means that the node cannot get the columns. -/
def readColumnData {preset : Preset} {fork : Fork} (data : ByteArray) :
    Result (Option (Array (DataColumnSidecar preset fork))) := do
  if data.size < 4 then throw (0, "the count of columns is cut short")
  let count := (← decodeInput UInt32 (data.extract 0 4)).toNat
  let mut offset := 4
  let mut columns := #[]
  for _ in [0:count] do
    if data.size < offset + 4 then throw (0, "the length of a column is cut short")
    let length := (← decodeInput UInt32 (data.extract offset (offset + 4))).toNat
    let stop := offset + 4 + length
    if data.size < stop then throw (0, "a column is cut short")
    columns := columns.push (← decodeInput (DataColumnSidecar preset fork)
      (data.extract (offset + 4) stop))
    offset := stop
  if offset ≠ data.size then throw (0, "bytes follow the last column")
  return if count = 0 then none else some columns

/-- The verdict of a step on a payload: none when the execution layer accepts it.

Otherwise it is the latest valid hash, when the execution layer knows one. -/
def readPayloadVerdict (data : ByteArray) : Result (Option (Option Hash32)) :=
  match data.toList with
  | [0] => return none
  | [1] => return some none
  | 1 :: _ => return some (some (← decodeInput Hash32 (data.extract 1 data.size)))
  | _ => throw (0, "a verdict is 0, or 1 with an optional hash of 32 bytes")

/-- The outcome of each step of a fork choice case, from an anchor state and an anchor block.

The preset, the configuration and the fork are named in UTF-8.

The signature checks run unless the last argument is false.

From Gloas the store starts and gives its head.

From Gloas a block, a vote or the node on which a proposer builds is not yet specified here.

So such a step fails from Gloas. -/
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
  let mut fcr := getFastConfirmationStore store
  let mut out := ByteArray.empty
  let mut powBlocks : List PowBlock := []
  let mut blobData : Array Cryptography.Kzg.Blob × Array Cryptography.Kzg.KZGProof := (#[], #[])
  let mut columnData : Option (Array (DataColumnSidecar preset fork)) := some #[]
  let mut verdict : Option (Option Hash32) := none
  let setup ← Cryptography.Kzg.Exports.embeddedSetup.mapError fun e => (0, e.message)
  for step in ← readForkChoiceSteps (steps.size + 1) steps 0 do
    if step.1 = 5 then
      powBlocks := (← decodeInput PowBlock step.2) :: powBlocks
      out := out.push 0
      continue
    if step.1 = 6 then
      blobData ← readBlobData step.2
      out := out.push 0
      continue
    if step.1 = 7 then
      columnData ← readColumnData step.2
      out := out.push 0
      continue
    if step.1 = 8 then
      verdict ← readPayloadVerdict step.2
      out := out.push 0
      continue
    if step.1 = 9 then
      if step.2.size ≠ 0 then throw (0, "a fast confirmation takes no bytes")
      match do
          let next ← store.onFastConfirmation config fcr
          return (next, ← fastConfirmationRecord store next) with
      | .ok (next, record) =>
        fcr := next
        out := out.push 0 ++ record
      | .error e =>
        out := out ++ rejection e
      continue
    let known := powBlocks
    let held := blobData
    let sampled := columnData
    let invalid := if step.1 = 1 then verdict else none
    let sources : BlockSources preset fork := {
      engine := .constant invalid.isNone
      powBlock := fun hash => known.find? (·.blockHash = hash)
      blobsAndProofs := fun _ => some held
      columns := fun _ => sampled
      setup }
    -- The blobs, the columns and the verdict of a step serve only the block that follows it.
    if step.1 = 1 then
      blobData := (#[], #[])
      columnData := some #[]
      verdict := none
    let mut outcome ← runForkChoiceStep config checks sources store step
    -- An invalid verdict removes blocks, whether the block itself fails or not.
    if let some latestValidHash := invalid then
      let signed ← decodeInput (SignedBeaconBlock preset fork) step.2
      let after := match outcome with
        | .ok (next, _) => next
        | .error _ => store
      match after.onInvalidPayload signed.message latestValidHash with
      | .ok removed =>
        store := removed
        outcome := outcome.map fun (_, record) => (removed, record)
      | .error e => outcome := .error e
    match outcome with
    | .ok (next, record) =>
      store := next
      out := out.push 0 ++ record
    | .error e =>
      out := out ++ rejection e
  return out

end EthLib.Consensus.Exports
