module

public import EthLib.Consensus.DataAvailability.Custody
public import EthLib.Serialization.Ssz.Typed.Collections

/-!
# `Consensus.DataAvailability.CustodyColumns`

From Gloas, a node tells its execution layer which columns it custodies, one bit per column.

The execution layer samples the blob transactions of its pool on those columns.

A bit is set when its column belongs to one of the custody groups of the node.

[EIP-8070][eip8070], "Engine API extensions", adds this set to the forkchoice update.

[eip8070]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8070.md#engine-api-extensions
-/

@[expose] public section

namespace EthLib.Consensus.DataAvailability

open Serialization.Ssz (Bitvector)

/-- From Gloas: the columns that a node custodies, one bit per column.

The choice of the groups takes at most `fuel` steps.

It fails when the choice of the groups fails. -/
def getCustodyColumnBits (config : Config) (preset : Preset) (nodeId : NodeID) (count : UInt64)
    (fuel : Nat) : Except CustodyError (Bitvector preset.NUMBER_OF_COLUMNS.toNat) := do
  -- The custody groups of the node ID, for the custody group count.
  let groups ← getCustodyGroups config nodeId count fuel
  -- The columns of each of those groups.
  let columns ← groups.mapM (computeColumnsForCustodyGroup config preset)
  -- Bit `i` is set when the node custodies column `i`, as EIP-8070 specifies.
  --
  -- It does when column `i` belongs to one of its groups.
  return ⟨Vector.ofFn fun column => columns.any (·.contains (UInt64.ofNat column))⟩

end EthLib.Consensus.DataAvailability
