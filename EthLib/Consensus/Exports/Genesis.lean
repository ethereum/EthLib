module

public import EthLib.Consensus.Exports.Transition
public import EthLib.Consensus.Transition.Genesis

/-!
# `Exports.Genesis`

C-ABI exports of the genesis of the beacon chain, for the consensus test vectors.

One export builds the candidate genesis state of a block and its deposits.

Another tells whether a candidate state launches the chain.

They take and return states as SSZ bytes.

The configuration of a name holds, with the replacements that a JSON object gives.

An input that does not decode, or an unknown name, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result)

/-- The candidate genesis state of a block of the proof-of-work chain, as SSZ bytes.

The preset, the configuration and the fork are named in UTF-8.

The deposits come as the SSZ bytes of a list of deposits.

The signature checks of the deposits run unless the last argument is false. -/
@[export eth_consensus_initialize_genesis]
def initializeGenesisExport (name fork eth1BlockHash deposits replacements : ByteArray)
    (eth1Timestamp : UInt64) (verify : Bool) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let hash ← decodeInput Hash32 eth1BlockHash
  let deposits ← decodeInput (SszList Deposit DEPOSIT_CONTRACT_LIMIT) deposits
  let state : BeaconState preset fork ← runTransition
    (initializeBeaconStateFromEth1 config checks hash eth1Timestamp deposits.data)
  (SszType.serialize state).mapError fun e => (0, s!"state rejected: {reprStr e}")

/-- Whether a candidate genesis state launches the chain.

The preset, the configuration and the fork are named in UTF-8. -/
@[export eth_consensus_is_valid_genesis_state]
def isValidGenesisStateExport (name fork state replacements : ByteArray) : Result Bool := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) state
  return isValidGenesisState config state

end EthLib.Consensus.Exports
