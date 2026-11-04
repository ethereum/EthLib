module

public import EthLib.Base.BigEndian

/-!
# `Networking.Discv5.Distance`

The distance between two node IDs of the Node Discovery Protocol v5 (discv5).

The source is "Nodes, Records and Distances" of `discv5-theory.md` in `ethereum/devp2p`:
<https://github.com/ethereum/devp2p/blob/88f1c80800d6/discv5/discv5-theory.md>

The distance is the XOR of the two IDs, read as big-endian numbers.

The logarithmic distance is the number of bits of the distance.

So it is 0 for equal IDs, and 256 when the first bits differ.
-/

@[expose] public section

namespace EthLib.Networking.Discv5

/-- A node ID: 32 bytes, read as a big-endian number. -/
abbrev NodeId := Vector UInt8 32

/-- The distance between two node IDs: the XOR of their big-endian values. -/
def distance (a b : NodeId) : Nat :=
  Base.bytesToNat a.toList ^^^ Base.bytesToNat b.toList

/-- The logarithmic distance: the number of bits of the distance, and 0 for equal IDs. -/
def logDistance (a b : NodeId) : Nat :=
  let d := distance a b
  if d = 0 then 0 else d.log2 + 1

end EthLib.Networking.Discv5
