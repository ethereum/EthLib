module

public import EthLib.Consensus.BeaconApi.ChainEvents
public import EthLib.Consensus.Exports.BeaconApiDebug

/-!
# `Exports.BeaconApiChainEvents`

C-ABI exports of the events that the fork choice of a beacon node sends.

Each export replays the steps of a fork choice case to build its stores.

An event is the name of its topic and the text of its JSON data, as the stream sends them.

A store that cannot be read gives the code of the fork choice error.

A dependent root that cannot be read gives code 0.

An unknown name or fork, an input that does not decode or a bad configuration has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base
open EthLib.Exports (Result PyValue pyExport)

/-- The code and the message of an error of the events. -/
def chainEventError : BeaconApi.ChainEventError → UInt32 × String
  | .forkChoice e => (e.code, s!"fork choice: {reprStr e}")
  | .dependentRoot e => (0, s!"dependent root: {e.message}")

/-- An event of the stream as the name of its topic and the text of its data. -/
def eventRecord (event : BeaconApi.ApiEvent) : String × String :=
  (event.topic.name, event.data.compress)

/-- The events between the store after the first steps of a case and the store after all.

After the arguments of the case comes the number of first steps.

Then come the genesis root and the roots not yet verified, and replacements of the configuration. -/
def apiChainEventsOf (args : StoreCaseArgs (Nat × ByteArray × List Root × Option PyValue)) :
    Result (List (String × String)) := do
  let (name, fork, anchorState, anchorBlock, steps, verify, first, genesisRoot, roots,
    replacements) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let anchorState ← decodeInput (BeaconState preset fork) anchorState
  let anchorBlock ← decodeInput (BeaconBlock preset fork) anchorBlock
  let genesisRoot ← decodeInput Root genesisRoot
  let (before, _) ← replayForkChoice config checks anchorState anchorBlock (steps.take first)
  let (after, _) ← replayForkChoice config checks anchorState anchorBlock steps
  let events ← (BeaconApi.chainEvents config roots.contains genesisRoot before after).mapError
    chainEventError
  return events.map fun e => eventRecord (e.toApiEvent fork)

/-- The events of the fork choice between two stores of a case.

The first arguments build the store as a fork choice case does.

Next comes the number of first steps that the earlier store takes.

Then come the genesis root and the roots not yet verified.

Last come replacements of the configuration, or None. -/
@[export eth_consensus_api_chain_events]
def apiChainEventsExport (args : PyValue) : Result PyValue := pyExport apiChainEventsOf args

/-- The event of the last run of the fast confirmation rule in a case that passed.

The slot of the clock is that of the store at that run.

A case with no such run gives code 0. -/
def apiFastConfirmationEventOf (args : StoreCaseArgs (Option PyValue)) :
    Result (String × String) := do
  let (name, fork, anchorState, anchorBlock, steps, verify, replacements) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let anchorState ← decodeInput (BeaconState preset fork) anchorState
  let anchorBlock ← decodeInput (BeaconBlock preset fork) anchorBlock
  let (_, lastRun, _) ← replayForkChoiceConfirming config checks anchorState anchorBlock steps
  let some (store, fcr) := lastRun | throw (0, "no run of the fast confirmation rule passed")
  let currentSlot ← runForkChoice (store.getCurrentSlot config)
  let event ← runForkChoice (BeaconApi.fastConfirmationEvent store fcr currentSlot)
  return eventRecord ((BeaconApi.ChainEvent.fastConfirmation event).toApiEvent fork)

/-- The event of the last run of the fast confirmation rule in a case that passed.

The first arguments build the store as a fork choice case does.

Then come replacements of the configuration, or None.

The slot of the clock is that of the store at the run.

A case with no run that passed gives code 0. -/
@[export eth_consensus_api_fast_confirmation_event]
def apiFastConfirmationEventExport (args : PyValue) : Result PyValue :=
  pyExport apiFastConfirmationEventOf args

end EthLib.Consensus.Exports
