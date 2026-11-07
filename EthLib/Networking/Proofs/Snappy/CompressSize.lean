module

public import EthLib.Networking.Proofs.Snappy.Compress
public import EthLib.Networking.Proofs.Encoding.Varint

/-!
# `Networking.Proofs.Snappy.CompressSize`

The block that the compressor writes for `n` bytes takes at most `32 + n + n / 6` bytes.

The bound holds for every input.

The proof bounds six times the output by seven times the input, plus 10:

- A copy element copies at least 4 bytes and takes at most 3 bytes.
- Six times a literal header is at most `m + 10` for a literal of `m` bytes.
- The copies after a literal cover its 10: six times a copy of `L ≥ 4` bytes is at most `7 L - 10`.
- The last literal adds its 10 once, and the preamble adds at most 5 bytes.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.CompressSize

open EthLib.Networking.Snappy
open EthLib.Networking.Proofs.Snappy.Compress

/-! ## Elements -/

/-- A byte array made of a list has the length of the list. -/
private theorem size_mk_toArray (l : List UInt8) : (⟨l.toArray⟩ : ByteArray).size = l.length := by
  simp [ByteArray.size]

/-- A copy element takes at most three bytes. -/
private theorem length_copyElement_le (offset len : Nat) : (copyElement offset len).length ≤ 3 := by
  unfold copyElement
  split <;> simp [copyOne, copyTwo]

/-- Copies of one offset take at most three bytes for each four bytes that they copy. -/
private theorem size_emitCopies_le (offset : Nat) :
    ∀ (len : Nat) (out : ByteArray), (len = 0 ∨ 4 ≤ len) →
      4 * (emitCopies offset out len).size ≤ 4 * out.size + 3 * len := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
      intro out hlen
      rw [emitCopies]
      by_cases h0 : len = 0
      · subst h0
        simp
      · simp only [h0, ↓reduceIte]
        generalize hn : (if maxCopyLength + 4 ≤ len then maxCopyLength
          else if maxCopyLength < len then maxCopyLength - 4 else len) = n
        have hb : 4 ≤ n ∧ n ≤ len ∧ (len - n = 0 ∨ 4 ≤ len - n) := by
          subst hn; simp only [maxCopyLength]; grind
        obtain ⟨hn4, hnl, hrest⟩ := hb
        have := ih (len - n) (by omega) (out ++ ⟨(copyElement offset n).toArray⟩) hrest
        have hl := length_copyElement_le offset n
        simp only [ByteArray.size_append, size_mk_toArray] at this
        omega

/-- Six times the header of a literal of `n` bytes is at most `n + 10`. -/
private theorem length_literalHeader_le {n : Nat} (h1 : 1 ≤ n) :
    6 * (literalHeader n).length ≤ n + 10 := by
  unfold literalHeader
  split
  · simp
  · rename_i hn
    have hk : literalLengthBytes (n - 1) ≤ 4 := by
      unfold literalLengthBytes
      split <;> (try split) <;> (try split) <;> omega
    simp
    omega

/-- After a literal over a range, six times the output grows by at most 7 times the range plus 10.
-/
private theorem size_emitLiteral_le (out src : ByteArray) {lo hi : Nat}
    (hhi : hi ≤ src.size) :
    6 * (emitLiteral out src lo hi).size ≤ 6 * out.size + 7 * (hi - lo) + 10 := by
  unfold emitLiteral
  split
  · rename_i hlt
    have hh := length_literalHeader_le (n := hi - lo) (by omega)
    rw [ByteArray.copySlice_eq_append]
    simp only [ByteArray.size_append, ByteArray.size_extract, size_mk_toArray, ByteArray.size_data]
    omega
  · omega

/-! ## The scan -/

/-- Six times the bytes that the scan writes is at most seven times the input, plus 10.

The invariant is that six times the bytes written so far is at most seven times `lit`.
-/
private theorem size_compressLoop_le (src : ByteArray) (table : Array Nat) (i lit : Nat)
    (out : ByteArray) (hli : lit ≤ i) (his : i ≤ src.size) (hout : 6 * out.size ≤ 7 * lit) :
    6 * (compressLoop src table i lit out).size ≤ 7 * src.size + 10 := by
  have hmin : minCopyLength = 4 := rfl
  fun_induction compressLoop src table i lit out with
  | case1 tb i lit out hi s c tb' hc len hl ih =>
      have hle : i + len ≤ src.size := matchLength_le src c i hc.1 (by omega)
      have h1 := size_emitLiteral_le out src (lo := lit) his
      have h2 := size_emitCopies_le (i - c) len (emitLiteral out src lit i) (Or.inr (by omega))
      exact ih (Nat.le_refl _) (by omega) (by omega)
  | case2 tb i lit out hi s c tb' hc len hl ih => exact ih (by omega) (by omega) hout
  | case3 tb i lit out hi s c tb' hc ih => exact ih (by omega) (by omega) hout
  | case4 tb i lit out hi =>
      have h1 := size_emitLiteral_le out src (lo := lit) (hi := src.size)
        (Nat.le_refl _)
      omega

/-! ## The bound -/

/-- Six times the block of an input of `n` bytes is at most `7 n + 40` bytes.

The bound holds for every input.

Only the block of an input of at most 2^32 - 1 bytes decompresses back to the input.
-/
theorem six_mul_size_compress_le (src : ByteArray) :
    6 * (compress src).size ≤ 7 * src.size + 40 := by
  have hloop := size_compressLoop_le src (Array.replicate (2 ^ tableBits) 0) 0 0
    ByteArray.empty (Nat.le_refl _) (Nat.zero_le _) (by simp)
  have hpre : (EthLib.Networking.Encoding.Varint.encodeAux src.size preambleMaxLength).length ≤ 5 :=
    EthLib.Networking.Proofs.Encoding.Varint.length_encodeAux_le _ _
  rw [compress_eq]
  simp only [ByteArray.size_append, size_mk_toArray]
  omega

/-- The block of an input of `n` bytes takes at most `32 + n + n / 6` bytes. -/
theorem size_compress_le (src : ByteArray) :
    (compress src).size ≤ 32 + src.size + src.size / 6 := by
  have := six_mul_size_compress_le src
  omega

end EthLib.Networking.Proofs.Snappy.CompressSize
