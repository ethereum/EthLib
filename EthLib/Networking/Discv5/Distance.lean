module

public import EthLib.Base.BigEndian

/-!
# `Networking.Discv5.Distance`

The distance between two node IDs of the Node Discovery Protocol v5 (discv5).

The source is the section Nodes, Records and Distances of `discv5-theory.md` in `ethereum/devp2p`:
<https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/discv5/discv5-theory.md>

The logarithmic distance is 0 for equal IDs, and 256 when the first bits differ.
-/

@[expose] public section

namespace EthLib.Networking.Discv5

/-- A node ID: 32 bytes, read as a big-endian number. -/
abbrev NodeId := Vector UInt8 32

/-- The distance between two node IDs: the XOR of their big-endian values. -/
def distance (a b : NodeId) : Nat :=
  -- `distance(n₁, n₂) = n₁ XOR n₂`, the IDs taken as big-endian numbers.
  Base.bytesToNat a.toList ^^^ Base.bytesToNat b.toList

/-- The logarithmic distance: the number of bits of the distance, and 0 for equal IDs. -/
def logDistance (a b : NodeId) : Nat :=
  let d := distance a b
  -- The source writes `logdistance(n₁, n₂) = log2(distance(n₁, n₂))`.
  --
  -- It calls it the length of the differing suffix in bits, so EthLib takes `floor(log2 d) + 1`.
  --
  -- That bit length runs from 1 to 256 for distinct IDs.
  --
  -- Equal IDs differ in no bit, so they are at logarithmic distance 0, where `log2 0` is undefined.
  if d = 0 then 0 else d.log2 + 1

end EthLib.Networking.Discv5
