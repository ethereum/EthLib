module

public import EthLib.Consensus.Exports.BeaconApiChainEvents
public import EthLib.Engine.BeaconApiEvents
public import EthLib.Engine.Exports.PreparePayload

/-!
# `Exports.BeaconApiEvents`

The C exports of the Beacon API event that gives the payload attributes of a proposal.

One covers Bellatrix to Fulu, on a state.

The other covers Gloas, on the store of a fork choice case.

Each first computes the forkchoice update of the proposer, as the exports of that update do.

The event is the name of its topic and the text of its JSON data.

A step of the proposer that fails gives the code of its error.

An input that does not decode, an unknown name or a fork that the export does not cover has code 0.
-/

public section

namespace EthLib.Engine.Exports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Consensus
open EthLib.Consensus.Exports

/-- From Bellatrix to Fulu: the event of the payload attributes of a proposer.

It is none when the proposer asks for nothing, before the merge. -/
def payloadAttributesEventOf (args : String × String × ByteArray × Option PyValue × ByteArray ×
    ByteArray × ByteArray × List ByteArray × UInt64) : Result (Option (String × String)) := do
  let (name, fork, state, replacements, safe, finalized, feeRecipient, powChain,
    terminalNumber) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let ⟨bellatrix⟩ ← holds (.bellatrix ≤ fork ∧ fork < .glamsterdam)
    s!"no payload preparation at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  let safe ← decodeInput Root safe
  let finalized ← decodeInput Root finalized
  let feeRecipient ← decodeInput ExecutionAddress feeRecipient
  let powChain ← powChain.mapM (decodeInput PowBlock)
  let prepared ← runProposer
    (prepareExecutionPayload config state bellatrix safe finalized feeRecipient powChain)
  let some (update, attributes) := prepared | return none
  let forks := ⟨bellatrix.1, Nat.lt_trans bellatrix.2 (by decide)⟩
  let event ← runProposer (payloadAttributesEvent state forks update attributes terminalNumber)
  return some (eventRecord event.toApiEvent)

/-- From Bellatrix to Fulu: the event of the payload attributes of a proposer.

The arguments are those of the forkchoice update of a proposer to Fulu.

Last comes the number of the terminal block of proof of work, read only before the merge.

It is `None` when the proposer asks for nothing, before the merge. -/
@[export eth_engine_payload_attributes_event]
def payloadAttributesEventExport (args : PyValue) : Result PyValue :=
  pyExport payloadAttributesEventOf args

/-- Gloas: the event of the payload attributes of a proposer, on the store of a case.

The event reads the state on which the proposer builds its payload. -/
def payloadAttributesEventGloasOf
    (args : String × String × ByteArray × ByteArray × List ForkChoiceStep × ByteArray × UInt64 ×
      ByteArray × ByteArray × ByteArray × UInt64 × Bool × Option PyValue) :
    Result (String × String) := do
  let (name, fork, anchorState, anchorBlock, steps, headRoot, headStatus, state, safe,
    feeRecipient, targetGasLimit, verify, replacements) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let ⟨forks⟩ ← holds (.glamsterdam ≤ fork ∧ fork < .hegota)
    s!"no payload attributes event on a store at {fork.name}"
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let anchorState ← decodeInput (BeaconState preset fork) anchorState
  let anchorBlock ← decodeInput (BeaconBlock preset fork) anchorBlock
  let (store, _) ← replayForkChoice config checks anchorState anchorBlock steps
  let head : ForkChoiceNode :=
    { root := ← decodeInput Root headRoot, payloadStatus := ← payloadStatusOfCode headStatus }
  let state ← decodeInput (BeaconState preset fork) state
  let safe ← decodeInput Root safe
  let feeRecipient ← decodeInput ExecutionAddress feeRecipient
  let finalized ← runProposer
    ((store.getFinalizedExecutionBlockHash (Nat.le_trans (by decide) forks.1)).mapError
      .forkChoice)
  let (update, attributes, _) ← runProposer (prepareExecutionPayloadGloas config checks
    store head state forks.1 safe finalized feeRecipient targetGasLimit)
  let (base, _, _) ← runProposer (payloadParentGloas config checks store head state forks.1)
  let event ← runProposer (payloadAttributesEvent base
    ⟨Nat.le_trans (by decide) forks.1, forks.2⟩ update attributes 0)
  return eventRecord event.toApiEvent

/-- Gloas: the event of the payload attributes of a proposer.

The arguments are the preset, the fork, the anchor state and the anchor block, and the steps.

Then come the head root and status, the state, the safe hash, the fee recipient and the gas target.

Last come whether the signature checks run, and replacements of the configuration.

The finalized hash is that of the store. -/
@[export eth_engine_payload_attributes_event_gloas]
def payloadAttributesEventGloasExport (args : PyValue) : Result PyValue :=
  pyExport payloadAttributesEventGloasOf args

end EthLib.Engine.Exports
