import EthLib.Consensus.Proofs.Ssz.Flat.Walk
import EthLib.Consensus.Proofs.Ssz.Merkle.Tree

/-! The upward walk, read against the tree the specification defines. -/

namespace EthLib.Consensus.Ssz

/-- Reading a list of nodes as leaves is reading the array it becomes. -/
theorem paddedList_eq_padded (fill : Bytes) (nodes : List Bytes) :
    paddedList fill nodes = padded fill nodes.toArray := by
  -- List-to-array conversion preserves every present position and the same default beyond the end.
  funext position
  simp [paddedList, padded]

/--
The walk from the leaves reaches the node the walk from the root names.

Both walks use the zero subtree of the required depth.
-/
theorem merkleizeFlat_eq_subtreeAt (chunks : Array Bytes) {depth : Nat} :
    merkleizeFlat combine zeroChunk depth chunks.toList = subtreeAt chunks depth 0 := by
  -- A list made from an array and read back as one is that array, so the leaves match.
  rw [merkleizeFlat_eq, subtreeAt_zero_eq chunks, paddedList_eq_padded]

/--
Root of the bounded tree, built from the leaves upward.

This is the shape an implementation has: a buffer of nodes, folded a level at a time.
-/
def merkleizeUpward (chunks : Array Bytes) (limit : Option Nat) : Except Err Bytes := do
  match limit with
  | some capacity =>
    -- A capacity under the data would silently drop nodes.
    if capacity < chunks.size then throw (.merkleizeLimit chunks.size capacity)
    return merkleizeFlat combine zeroChunk (depthFor capacity) chunks.toList
  | none => return merkleizeFlat combine zeroChunk (depthFor chunks.size) chunks.toList

/-- Folding upward and reading downward give the same root, and refuse the same inputs. -/
theorem merkleizeUpward_eq (chunks : Array Bytes) (limit : Option Nat) :
    merkleizeUpward chunks limit = merkleizeBoundedUnchecked chunks limit := by
  -- Either both refuse the capacity, or both fold the same tree at the same width.
  cases limit <;> simp [merkleizeUpward, merkleizeBoundedUnchecked, merkleizeFlat_eq_subtreeAt chunks]

end EthLib.Consensus.Ssz
