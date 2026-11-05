module

public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.Transition.Block

/-!
# `Exports.Transition`

A C-ABI export of the steps of the beacon state transition, for the consensus test vectors.

The export runs one block operation on a state, both as SSZ bytes, and returns the state after it.

It checks the BLS signatures, or accepts every signature for the vectors with placeholder ones.

An input that does not decode, or an unknown name, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result)

/-- The value of a type that SSZ bytes encode. -/
def decodeInput (α : Type) [SszType α] (data : ByteArray) : Result α :=
  (SszType.deserialize α data).mapError fun e => (0, s!"input rejected: {reprStr e}")

/-- The result of a step of the transition, with the code and the text of its error. -/
def runTransition {α : Type} (result : Except TransitionError α) : Result α :=
  result.mapError fun e => (e.code, reprStr e)

/-- The state after a block operation of a handler of the vectors, the operation given as bytes. -/
def runOperation {preset : Preset} {fork : Fork} (config : Config) (checks : SignatureChecks)
    (handler : String) (state : BeaconState preset fork) (operation : ByteArray) :
    Result (BeaconState preset fork) :=
  match handler with
  | "block_header" => do
    runTransition (processBlockHeader state (← decodeInput (BeaconBlock preset fork) operation))
  | "proposer_slashing" => do
    runTransition (processProposerSlashing config checks state
      (← decodeInput ProposerSlashing operation))
  | "attester_slashing" => do
    runTransition (processAttesterSlashing config checks state
      (← decodeInput (AttesterSlashing preset fork) operation))
  | handler => throw (0, s!"no operation {handler}")

/-- The state after a block operation of a handler of the vectors, as SSZ bytes.

The preset, the configuration and the fork are named in UTF-8, and the handler too.

The signature checks run unless the last argument is false. -/
@[export eth_consensus_process_operation]
def processOperationExport (name fork handler pre operation : ByteArray) (verify : Bool) :
    Result ByteArray := do
  let (preset, fork) ← presetAndFork name fork
  let config ← configOf (← nameOf name)
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let state ← decodeInput (BeaconState preset fork) pre
  let after ← runOperation config checks (← nameOf handler) state operation
  (SszType.serialize after).mapError fun e => (0, s!"state rejected: {reprStr e}")

end EthLib.Consensus.Exports
