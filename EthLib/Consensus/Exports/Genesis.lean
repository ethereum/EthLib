module

public import EthLib.Consensus.Exports.Transition
public import EthLib.Consensus.Transition.Genesis

/-!
# `Exports.Genesis`

C-ABI exports of the genesis of the beacon chain, for the consensus test vectors.

One export builds the candidate genesis state of a block and its deposits.

Another tells whether a candidate state launches the chain.

They take and return states as SSZ bytes.

The configuration of a name holds, with the replacements that a `dict` gives.

The exports take the tuple of their arguments as typed Python values.

An input that does not decode, or an unknown name, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)

/-- The candidate genesis state of a block of the proof-of-work chain, as SSZ bytes. -/
def initializeGenesisOf
    (args : String × String × Hash32 × Array ByteArray × Option PyValue × UInt64 × Bool) :
    Result ByteArray := do
  let (name, fork, eth1BlockHash, deposits, replacements, eth1Timestamp, verify) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let deposits ← deposits.mapM (decodeInput Deposit)
  let state : BeaconState preset fork ← runTransition
    (initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits)
  (SszType.serialize state).mapError fun e => (0, s!"state rejected: {reprStr e}")

/-- The candidate genesis state of a block of the proof-of-work chain, as SSZ bytes.

The preset, the configuration and the fork are named by `str`.

Each deposit comes as its SSZ bytes, in a list.

The signature checks of the deposits run unless the last argument is false. -/
@[export eth_consensus_initialize_genesis]
def initializeGenesisExport (args : PyValue) : Result PyValue := pyExport initializeGenesisOf args

/-- Whether a candidate genesis state launches the chain. -/
def isValidGenesisStateOf (args : String × String × ByteArray × Option PyValue) : Result Bool := do
  let (name, fork, state, replacements) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  return isValidGenesisState config state

/-- Whether a candidate genesis state launches the chain.

The preset, the configuration and the fork are named by `str`. -/
@[export eth_consensus_is_valid_genesis_state]
def isValidGenesisStateExport (args : PyValue) : Result PyValue :=
  pyExport isValidGenesisStateOf args

end EthLib.Consensus.Exports
