import EthLib.Consensus.Proofs.Ssz.Merkle.Authentication
import EthLib.Consensus.Proofs.Ssz.Codec.RoundTripScalar

/-! Complete leaves, padding, and mixing words produce complete 32-byte roots. -/

namespace EthLib.Consensus.Ssz

/-- The absent leaf is one complete zero node. -/
@[simp] theorem zeroChunk_size : zeroChunk.size = bytesPerChunk := by
  -- The absent leaf allocates one zero byte for each of the thirty-two node positions.
  simp [zeroChunk]

/-- Every empty subtree has one complete node as its root. -/
@[simp] theorem zeroRoot_size (depth : Nat) :
    (zeroRoot combine zeroChunk depth).size = bytesPerChunk := by
  -- At depth zero the root is a complete leaf, and every deeper root is a digest.
  cases depth <;> simp [zeroRoot]

/-- Cached empty subtrees have the same width at every depth. -/
@[simp] theorem zeroSubtree_size (depth : Nat) : (zeroSubtree depth).size = bytesPerChunk := by
  -- The cache equivalence transfers the width of the mathematical empty subtree.
  rw [zeroSubtree_eq, zeroRoot_size]

/-- Padding adds complete zero nodes to an array of complete leaves. -/
theorem padded_size (chunks : Array Bytes) (complete : ∀ chunk ∈ chunks, chunk.size = bytesPerChunk)
    (position : Nat) : (padded zeroChunk chunks position).size = bytesPerChunk := by
  -- A position either names a supplied leaf or the fixed-width zero node.
  cases found : chunks[position]? <;> simp [padded, found]
  exact complete _ (Array.mem_of_getElem? found)

/-- A bounded subtree preserves complete-node width, including its padding. -/
theorem subtreeAt_size (chunks : Array Bytes)
    (complete : ∀ chunk ∈ chunks, chunk.size = bytesPerChunk) (depth start : Nat) :
    (subtreeAt chunks depth start).size = bytesPerChunk := by
  -- At depth zero the root is a leaf.
  -- Every deeper root is a SHA-256 digest.
  rw [subtreeAt.eq_def]
  split
  · exact zeroSubtree_size depth
  · cases depth with
    | zero => exact padded_size chunks complete start
    | succ depth => exact combine_size _ _

/-- Every successful bounded root over complete leaves has the SSZ node width. -/
theorem merkleizeBoundedUnchecked_size {chunks : Array Bytes} {limit : Option Nat} {root : Bytes}
    (complete : ∀ chunk ∈ chunks, chunk.size = bytesPerChunk)
    (made : merkleizeBoundedUnchecked chunks limit = .ok root) : root.size = bytesPerChunk := by
  -- A successful capacity check leaves a bounded subtree whose leaves already have valid widths.
  cases limit <;> simp only [merkleizeBoundedUnchecked] at made <;> (try split at made) <;> cases made
  all_goals exact subtreeAt_size chunks complete _ _

/-- A progressive root is either a zero node or a digest, regardless of its leaf widths. -/
@[simp] theorem merkleizeProgressiveUnchecked_size (chunks : List Bytes) (level : Nat) :
    (merkleizeProgressiveUnchecked chunks level).size = bytesPerChunk := by
  -- An empty spine returns a complete zero node, and a nonempty spine returns a digest.
  rw [merkleizeProgressiveUnchecked]
  split <;> simp

/-- A count is written into one full node, including its high zero bytes. -/
@[simp] theorem lengthWord_size (count : Nat) : (lengthWord count).size = bytesPerChunk := by
  -- Writing the count always allocates thirty-two bytes, including any leading zero digits.
  exact uintBytes_size _ _

/-- Active fields occupy one full node, with unused positions clear. -/
@[simp] theorem activeFieldsWord_size (active : List Bool) :
    (activeFieldsWord active).size = bytesPerChunk := by
  -- The requested byte count fixes the packed layout word at thirty-two bytes.
  simp [activeFieldsWord, packBits]

/-- Each bit of the layout word records its corresponding active field, with absent positions clear. -/
theorem activeFieldsWord_bit (active : List Bool) (position : Nat)
    (inside : position < bitsPerChunk) :
    (((activeFieldsWord active)[position / 8]! >>> UInt8.ofNat (position % 8)) &&& 1 == 1) =
      active[position]?.getD false := by
  -- Whole bytes choose the node offset, and the remainder chooses the bit inside that byte.
  have byteInside : position / 8 < bytesPerChunk := by simp only [bitsPerChunk, bytesPerChunk] at inside ⊢; omega
  have lookup : (activeFieldsWord active)[position / 8]! = packByte active.toArray (position / 8) := by
    simp [activeFieldsWord, packBits, getElem!_pos, byteInside]
  rw [lookup]
  have same : position / 8 * 8 + position % 8 = position := by omega
  simpa only [same, List.getElem?_toArray] using
    packByte_bit active.toArray (position / 8) (position % 8) (by omega)

/-- Mixing in a count, layout, or selector always returns a complete digest. -/
@[simp] theorem mixIn_size (root word : Bytes) : (mixIn root word).size = bytesPerChunk := by
  -- The final pairing is another SHA-256 digest, regardless of the two input words.
  exact combine_size _ _

end EthLib.Consensus.Ssz
