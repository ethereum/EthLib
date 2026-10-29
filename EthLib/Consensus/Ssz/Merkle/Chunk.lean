/-! The width of a tree node. -/

namespace EthLib.Consensus.Ssz

/--
Width of a tree node in bytes.

The specification fixes it at the width of the hash output.
-/
abbrev bytesPerChunk : Nat :=
  32

/-- Width of a tree node in bits. -/
abbrev bitsPerChunk : Nat :=
  8 * bytesPerChunk

end EthLib.Consensus.Ssz
