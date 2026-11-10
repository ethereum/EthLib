module

public import EthLib.Consensus.DataAvailability.CustodyColumns
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Serialization.Exports.Ssz

/-!
# `Exports.Custody`

C-ABI exports of the custody groups of a node, the columns of a group and the custody bits.

Each one takes typed Python values, and comes back as a list of integers or as an error.

The custody bits come back as the bytes of an SSZ bitvector instead.

An argument out of range or of the wrong type, or an unknown name, has code 0.

A preset and a configuration are named together, by `mainnet` or `minimal`.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result PyValue pyExport)

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

/-- The result of a custody function, or the code and the message of its error. -/
def custodyResult (result : Except CustodyError (List UInt64)) : Result (List UInt64) :=
  result.mapError fun e => (e.code, custodyErrorText e)

/-- The custody groups of a node ID, in increasing order. -/
def getCustodyGroupsOf (args : String × NodeID × UInt64) : Result (List UInt64) := do
  let (name, id, count) := args
  custodyResult (getCustodyGroups (← configOf name) id count custodyFuel)

/-- The custody groups of a node ID, in increasing order, as a list.

The arguments are the name of the configuration, the node ID and the custody group count. -/
@[export eth_consensus_get_custody_groups]
def getCustodyGroupsExport (args : PyValue) : Result PyValue := pyExport getCustodyGroupsOf args

/-- The columns of a custody group. -/
def computeColumnsForCustodyGroupOf (args : String × UInt64) : Result (List UInt64) := do
  let (name, group) := args
  custodyResult (computeColumnsForCustodyGroup (← configOf name) (← presetOf name) group)

/-- The columns of a custody group, as a list.

The arguments are the name of the preset and the configuration, and the custody group. -/
@[export eth_consensus_compute_columns_for_custody_group]
def computeColumnsForCustodyGroupExport (args : PyValue) : Result PyValue :=
  pyExport computeColumnsForCustodyGroupOf args

/-- The columns that a node custodies, as the bytes of an SSZ bitvector. -/
def getCustodyColumnBitsOf (args : String × NodeID × UInt64) : Result ByteArray := do
  let (name, id, count) := args
  let preset ← presetOf name
  let bits ← (getCustodyColumnBits (← configOf name) preset id count custodyFuel).mapError
    fun e => (e.code, custodyErrorText e)
  Serialization.Ssz.Exports.runSsz "bits rejected" (Serialization.Ssz.SszType.serialize bits)

/-- The columns that a node custodies, one bit per column, as the bytes of an SSZ bitvector.

The arguments are the name of the preset and the configuration, the node ID and the group count.
-/
@[export eth_consensus_get_custody_column_bits]
def getCustodyColumnBitsExport (args : PyValue) : Result PyValue :=
  pyExport getCustodyColumnBitsOf args

end EthLib.Consensus.Exports
