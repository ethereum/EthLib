module

public import EthLib.Networking.Proofs.Snappy.Compress
public import EthLib.Networking.Proofs.Encoding.Varint

/-!
# `Networking.Proofs.Snappy.CompressSize`

The block that the compressor writes takes at most `32 + n + n / 6` bytes for `n` input bytes.

Source: `max_compressed_len` of the Phase 0 networking specification.

The commit is the one of `tests/sources.toml`:

<https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/specs/phase0/p2p-interface.md#max_compressed_len>

The function there is `32 + n + n // 6`.

It cites `snappy.cc` of `google/snappy` as the worst case of the reference compressor.

The proof counts bytes, with six times the output at most seven times the input read so far:

- A literal of `m` bytes takes `m` plus a header of 1 to 5 bytes.
- Copies of `L` bytes, with `L` at least four, take at most `3 L / 4` bytes.
- Each element copies at least four bytes and takes at most three.
- Six times a header is at most `m + 10`, and the copies after a literal pay for the 10.
- The last literal has no copy after it, so it pays 10 itself.
- The preamble takes at most five bytes.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.CompressSize

open EthLib.Networking.Snappy
open EthLib.Networking.Proofs.Snappy.Compress

/-! ## Elements -/

/-- A byte array made of a list has the length of the list. -/
theorem size_mk_toArray (l : List UInt8) : (⟨l.toArray⟩ : ByteArray).size = l.length := by
  simp [ByteArray.size]

/-- A copy element takes at most three bytes. -/
theorem length_copyElement_le (offset len : Nat) : (copyElement offset len).length ≤ 3 := by
  unfold copyElement
  split <;> simp [copyOne, copyTwo]

/-- Copies of one offset take at most three bytes for each four bytes that they copy. -/
theorem size_emitCopies_le (offset : Nat) :
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
theorem length_literalHeader_le {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 2 ^ 32) :
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

/-- A literal over a range adds its header and the range, and six times the sum has a bound.

The bound is seven times the length of the range, plus ten.
-/
theorem size_emitLiteral_le (out src : ByteArray) {lo hi : Nat}
    (hhi : hi ≤ src.size) (hlen : hi - lo ≤ 2 ^ 32) :
    6 * (emitLiteral out src lo hi).size ≤ 6 * out.size + 7 * (hi - lo) + 10 := by
  unfold emitLiteral
  split
  · rename_i hlt
    have hh := length_literalHeader_le (n := hi - lo) (by omega) hlen
    rw [ByteArray.copySlice_eq_append]
    simp only [ByteArray.size_append, ByteArray.size_extract, size_mk_toArray, ByteArray.size_data]
    omega
  · omega

/-! ## The scan -/

/-- Six times the bytes that the scan writes is at most seven times the input, plus ten.

The invariant is that six times the bytes written so far is at most seven times `lit`.
-/
theorem size_compressLoop_le (src : ByteArray) (hsz : src.size ≤ maxUncompressedLength)
    (table : Array Nat) (i lit : Nat) (out : ByteArray) (hli : lit ≤ i) (his : i ≤ src.size)
    (hout : 6 * out.size ≤ 7 * lit) :
    6 * (compressLoop src table i lit out).size ≤ 7 * src.size + 10 := by
  have hmin : minCopyLength = 4 := rfl
  have hmax : src.size ≤ 2 ^ 32 := by simp only [maxUncompressedLength] at hsz; omega
  fun_induction compressLoop src table i lit out with
  | case1 tb i lit out hi s c tb' hc len hl ih =>
      have hle : i + len ≤ src.size := matchLength_le src c i hc.1 (by omega)
      have h1 := size_emitLiteral_le out src (lo := lit) his (by omega)
      have h2 := size_emitCopies_le (i - c) len (emitLiteral out src lit i) (Or.inr (by omega))
      exact ih (Nat.le_refl _) (by omega) (by omega)
  | case2 tb i lit out hi s c tb' hc len hl ih => exact ih (by omega) (by omega) hout
  | case3 tb i lit out hi s c tb' hc ih => exact ih (by omega) (by omega) hout
  | case4 tb i lit out hi =>
      have h1 := size_emitLiteral_le out src (lo := lit) (hi := src.size)
        (Nat.le_refl _) (by omega)
      omega

/-! ## The bound -/

/-- The block of an input of at most 2^32 - 1 bytes takes at most `32 + n + n / 6` bytes. -/
theorem size_compress_le {src : ByteArray} (h : src.size ≤ maxUncompressedLength) :
    (compress src).size ≤ src.size + src.size / 6 + 32 := by
  have hloop := size_compressLoop_le src h (Array.replicate (2 ^ tableBits) 0) 0 0
    ByteArray.empty (Nat.le_refl _) (Nat.zero_le _) (by simp)
  have hpre : (EthLib.Networking.Encoding.Varint.encodeAux src.size preambleMaxLength).length ≤ 5 :=
    EthLib.Networking.Proofs.Encoding.Varint.length_encodeAux_le _ _
  unfold compress
  simp only [ByteArray.size_append, size_mk_toArray]
  omega

end EthLib.Networking.Proofs.Snappy.CompressSize
