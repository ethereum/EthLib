module

public import EthLib.Consensus.Exports.ForkChoiceValues
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

The steps and the outcome of each step are typed Python values.

A read of the store or a fast confirmation gives a `dict`, and another step gives `None`.

A step that the store rejects gives its error as its outcome, and the run goes on.

An input that the export reads itself, such as bytes that do not decode, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)

/-- A result of the fork choice, with the code of its error. -/
def runForkChoice {α : Type} (result : Except ForkChoiceError α) : Result α :=
  result.mapError fun e => (e.code, s!"fork choice: {reprStr e}")

/-- The little-endian bytes of a number, in a given width. -/
def littleEndian (width value : Nat) : ByteArray :=
  Base.packBytes (uintToBytes width value)

/-- The leaves of the filtered tree, which the vectors check with their weights.

With no viable node, the pending node of the justified block stands alone. -/
def viableLeaves {preset : Preset} {fork : Fork} (config : Config) (store : Store preset fork) :
    Except ForkChoiceError (List ForkChoiceNode) := do
  let nodes ← store.getFilteredNodeTree config
  if nodes.isEmpty then return [⟨store.justifiedCheckpoint.root, .pending⟩]
  nodes.filterM fun node => do
    return (← store.getNodeChildren node).all (· ∉ nodes)

/-- What a read of the store gives, with what it asks. -/
def storeRead {preset : Preset} {fork : Fork} (config : Config) (store : Store preset fork)
    (read : ReadRequest) : Except ForkChoiceError StoreRead := do
  let head ← store.getHead config
  let headBlock ← store.block head.root
  let proposerHead ← if read.proposerHead then
      let slot ← store.getCurrentSlot config
      pure (some (← store.getProposerHead config head slot).root)
    else pure none
  let viable ← if read.viable then
      let leaves ← viableLeaves config store
      let tally := store.justifiedTally
      some <$> leaves.mapM fun leaf => do
        return ⟨leaf.root, ← store.getWeight config tally leaf, leaf.payloadStatus.code⟩
    else pure none
  let votes ← match read.root with
    | none => pure (none, none)
    | some root =>
      if gloas : .glamsterdam ≤ fork then
        let timeliness ← Store.ptcVotes (store.payloadTimelinessVote gloas) root
        let availability ← Store.ptcVotes (store.payloadDataAvailabilityVote gloas) root
        pure (some timeliness.toList, some availability.toList)
      else throw (.forkNotYetSpecified fork)
  return {
    head := ⟨headBlock.slot, head.root, head.payloadStatus.code⟩
    timeMs := store.timeMs
    genesisTimeMs := store.genesisTimeMs
    justifiedCheckpoint := .of store.justifiedCheckpoint
    finalizedCheckpoint := .of store.finalizedCheckpoint
    proposerBoostRoot := store.proposerBoostRoot
    proposerHead
    viableForHeadRootsAndWeights := viable
    payloadTimelinessVote := votes.1
    payloadDataAvailabilityVote := votes.2 }

/-- What the fast confirmation of a slot gives, from Bellatrix with the safe execution block. -/
def fastConfirmationRead {preset : Preset} {fork : Fork} (store : Store preset fork)
    (fcr : FastConfirmationStore) : Except ForkChoiceError FastConfirmationRead := do
  let safe ← if bellatrix : .bellatrix ≤ fork then
      some <$> store.getSafeExecutionBlockHash fcr bellatrix
    else pure none
  return {
    previousEpochObservedJustifiedCheckpoint := .of fcr.previousEpochObservedJustifiedCheckpoint
    currentEpochObservedJustifiedCheckpoint := .of fcr.currentEpochObservedJustifiedCheckpoint
    previousEpochGreatestUnrealizedCheckpoint := .of fcr.previousEpochGreatestUnrealizedCheckpoint
    previousSlotHead := fcr.previousSlotHead
    currentSlotHead := fcr.currentSlotHead
    confirmedRoot := fcr.confirmedRoot
    safeExecutionBlockHash := safe }

/-- The outcome of a step: what it reads, or the code and the message of the error that rejects it.

The message carries no prefix, unlike an error of the whole call. -/
abbrev StepOutcome := Except (UInt32 × String) (Option StepRead)

/-- The outcome of a step that the store rejects. -/
def rejected (e : ForkChoiceError) : StepOutcome := .error (e.code, reprStr e)

/-- The store after a step and what the step reads, or the error that rejects it.

Three kinds of step run before this: a PoW block, a payload verdict and the fast confirmation. -/
def runForkChoiceStep {preset : Preset} {fork : Fork} (config : Config) (checks : SignatureChecks)
    (sources : BlockSources preset fork) (store : Store preset fork) :
    ForkChoiceStep → Result (Except ForkChoiceError (Store preset fork × Option StepRead))
  | .tick seconds => return (·, none) <$> store.onTick config (secondsToMilliseconds seconds)
  | .block input => do
    let signed ← decodeInput (SignedBeaconBlock preset fork) input.block
    return (·, none) <$> store.onBlockWithVotes config checks sources signed
  | .attestation data => do
    let attestation ← decodeInput (Attestation preset fork) data
    return (·, none) <$> store.onAttestation config checks attestation false
  | .attesterSlashing data => do
    let slashing ← decodeInput (AttesterSlashing preset fork) data
    return (·, none) <$> store.onAttesterSlashing config checks slashing
  | .checks read => return (fun r => (store, some (.store r))) <$> storeRead config store read
  | .executionPayload data => do
    let signed ← decodeInput (SignedExecutionPayloadEnvelope preset fork) data
    if gloas : .glamsterdam ≤ fork then
      return (·, none) <$> store.onExecutionPayloadEnvelope config checks sources gloas signed
    else throw (0, "an envelope needs Gloas or later")
  | .payloadAttestationMessage data => do
    let message ← decodeInput PayloadAttestationMessage data
    if gloas : .glamsterdam ≤ fork then
      return (·, none) <$> store.onPayloadAttestationMessage config checks gloas message false
    else throw (0, "a vote of the payload committee needs Gloas or later")
  | .powBlock _ | .payload _ | .fastConfirmation _ =>
    throw (0, "this step does not run on the store alone")

/-- The blobs and the proofs that the node holds for a block. -/
def heldBlobs (blobs proofs : List ByteArray) :
    Result (Array Cryptography.Kzg.Blob × Array Cryptography.Kzg.KZGProof) := do
  let blobs ← blobs.toArray.mapM (decodeInput Cryptography.Kzg.Blob)
  let proofs ← proofs.toArray.mapM (decodeInput Cryptography.Kzg.KZGProof)
  return (blobs, proofs)

/-- The verdicts of the execution layer that find a payload invalid, by their Engine API names. -/
def invalidStatuses : List String := ["INVALID", "INVALID_BLOCK_HASH"]

/-- The store after each step of a fork choice case, and the outcome of each step.

The store starts from an anchor state and an anchor block.

The caller may change the sources that each step reads.

The change to the sources does not change which blocks an invalid verdict removes. -/
def replayForkChoice {preset : Preset} {fork : Fork} (config : Config) (checks : SignatureChecks)
    (anchorState : BeaconState preset fork) (anchorBlock : BeaconBlock preset fork)
    (steps : List ForkChoiceStep)
    (adjust : BlockSources preset fork → BlockSources preset fork := id) :
    Result (Store preset fork × List StepOutcome) := do
  let mut store ← runForkChoice (getForkchoiceStore config anchorState anchorBlock)
  let mut fcr := getFastConfirmationStore store
  let mut outcomes : Array StepOutcome := #[]
  let mut powBlocks : List PowBlock := []
  let mut verdict : Option (Option Hash32) := none
  let setup ← Cryptography.Kzg.Exports.embeddedSetup.mapError fun e => (0, e.message)
  for step in steps do
    match step with
    | .powBlock data =>
      powBlocks := (← decodeInput PowBlock data) :: powBlocks
      outcomes := outcomes.push (.ok none)
      continue
    | .payload ⟨status, latestValidHash⟩ =>
      verdict := if status ∈ invalidStatuses then some latestValidHash else none
      outcomes := outcomes.push (.ok none)
      continue
    | .fastConfirmation () =>
      match do
          let next ← store.onFastConfirmation config fcr
          return (next, ← fastConfirmationRead store next) with
      | .ok (next, read) =>
        fcr := next
        outcomes := outcomes.push (.ok (some (.fastConfirmation read)))
      | .error e => outcomes := outcomes.push (rejected e)
      continue
    | _ => pure ()
    -- The blobs, the columns and the verdict of a block serve only that block.
    let (held, sampled) ← match step with
      | .block (.withBlobs _ blobs proofs) => do
        let held ← heldBlobs blobs proofs
        pure (held, some #[])
      | .block (.withColumns _ []) => pure ((#[], #[]), none)
      | .block (.withColumns _ columns) => do
        let columns ← columns.toArray.mapM (decodeInput (DataColumnSidecar preset fork))
        pure ((#[], #[]), some columns)
      | _ => pure ((#[], #[]), some #[])
    let known := powBlocks
    let invalid := match step with
      | .block _ => verdict
      | _ => none
    if let .block _ := step then verdict := none
    let sources : BlockSources preset fork := {
      engine := .constant invalid.isNone
      powBlock := fun hash => known.find? (·.blockHash = hash)
      blobsAndProofs := fun _ => some held
      columns := fun _ => sampled
      setup
      -- The execution layer of the vectors finds that every payload satisfies its lists.
      inclusionListSatisfied := fun _ _ => true }
    let mut outcome ← runForkChoiceStep config checks (adjust sources) store step
    -- An invalid verdict removes blocks, whether the block itself fails or not.
    if let some latestValidHash := invalid then
      if let .block input := step then
        let signed ← decodeInput (SignedBeaconBlock preset fork) input.block
        let after := match outcome with
          | .ok (next, _) => next
          | .error _ => store
        match after.onInvalidPayload signed.message latestValidHash with
        | .ok removed =>
          store := removed
          outcome := outcome.map fun (_, read) => (removed, read)
        | .error e => outcome := .error e
    match outcome with
    | .ok (next, read) =>
      store := next
      outcomes := outcomes.push (.ok read)
    | .error e => outcomes := outcomes.push (rejected e)
  return (store, outcomes.toList)

/-- The outcome of each step of a fork choice case, from an anchor state and an anchor block.

A step that the store rejects gives the error as its outcome, and the run goes on.

From Gloas the node on which a proposer builds is not yet specified here, so that read fails. -/
def forkChoice (args : String × String × ByteArray × ByteArray × List ForkChoiceStep × Bool ×
    Option PyValue) : Result (List StepOutcome) := do
  let (name, fork, anchorState, anchorBlock, steps, verify, replacements) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let anchorState ← decodeInput (BeaconState preset fork) anchorState
  let anchorBlock ← decodeInput (BeaconBlock preset fork) anchorBlock
  return (← replayForkChoice config checks anchorState anchorBlock steps).2

/-- The outcome of each step of a fork choice case, from an anchor state and an anchor block.

The arguments are the preset, the fork, the anchor state and the anchor block in SSZ, and the steps.

Then come whether the signature checks run, and replacements of values of the configuration.

From Gloas the node on which a proposer builds is not yet specified here, so that read fails. -/
@[export eth_consensus_fork_choice]
def forkChoiceExport (args : PyValue) : Result PyValue := pyExport forkChoice args

end EthLib.Consensus.Exports
