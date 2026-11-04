module

public import EthLib.Base.Exports
public import EthLib.Consensus.DataAvailability.Custody
public import EthLib.Consensus.Exports.Parameters

/-!
# `Exports.Custody`

C-ABI exports of the custody groups of a node and the columns of a group.

Each one comes back as a JSON list of integers, or as the code and the message of its error.

A malformed node ID or an unknown name has code 0.

A preset and a configuration are named together, by `mainnet` or `minimal`.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result)

open Lean Base DataAvailability

/-- The steps that the search for groups may take.

No bound on the search is proved, so EthLib picks this one.

Uniform draws among 128 groups would find 127 of them in about 570 steps on average. -/
def custodyFuel : Nat := 2 ^ 16

/-- The message of a custody error, for a Python traceback. -/
def custodyErrorText : CustodyError → String
  | .tooManyGroups count => s!"custody group count {count} exceeds the number of groups"
  | .groupOutOfRange group => s!"custody group {group} is not below the number of groups"
  | .outOfFuel => "the search for custody groups ran out of steps"

/-- The result of a custody function as JSON, or the code and the message of its error. -/
def custodyResult (result : Except CustodyError (List UInt64)) : Result ByteArray :=
  (result.map fun values => jsonBytes (toJson values)).mapError
    fun e => (e.code, custodyErrorText e)

/-- The custody groups of a node ID of 32 bytes, most significant first. -/
@[export eth_consensus_get_custody_groups]
def getCustodyGroupsExport (name nodeId : ByteArray) (count : UInt64) : Result ByteArray := do
  let config ← configOf (← nameOf name)
  unless nodeId.size = 32 do throw (0, "a node ID is 32 bytes")
  let id : NodeID := BitVec.ofNat 256 (bytesToNat nodeId.toList)
  custodyResult (getCustodyGroups config id count custodyFuel)

/-- The columns of a custody group. -/
@[export eth_consensus_compute_columns_for_custody_group]
def computeColumnsForCustodyGroupExport (name : ByteArray) (group : UInt64) :
    Result ByteArray := do
  let name ← nameOf name
  custodyResult (computeColumnsForCustodyGroup (← configOf name) (← presetOf name) group)

end EthLib.Consensus.Exports
