module

public import EthLib.Networking.Proofs.Snappy.Encode
public import EthLib.Networking.Snappy.Compress

/-!
# `Networking.Proofs.Snappy.Compress`

The block that the compressor writes decompresses to its input, against `format_description.txt`:

<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt>.

- A proposal that counts agrees with the input on every byte the copy writes (§2.2).
- At each step, the elements written so far take an empty output to the prefix of the input that
  the scan has passed.
- So the block of an input of at most 2^32 - 1 bytes decompresses to that input.

The table of positions never enters the proofs.

The compressor reads the input to count the bytes a proposal agrees on.

So the theorem holds for every table.

The kernel checks everything here, so no `native_decide` or `bv_decide` axiom appears.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.Compress

open EthLib.Networking.Snappy
open EthLib.Networking.Proofs.Snappy.Block
open EthLib.Networking.Proofs.Snappy.Encode

/-! ## The match length -/

/-- A match from a position at most the end of the input ends within the input. -/
theorem matchLength_le (src : ByteArray) (c j : Nat) (hc : c < j) (hj : j ≤ src.size) :
    j + matchLength src c j hc ≤ src.size := by
  fun_induction matchLength src c j hc with
  | case1 c j hc h heq ih => have := ih (by omega); omega
  | case2 c j hc h hne => omega
  | case3 c j hc h => omega

/-- Every byte in a match equals the byte that many places before it. -/
theorem matchLength_get (src : ByteArray) (c j : Nat) (hc : c < j) :
    ∀ (m : Nat), m < matchLength src c j hc → ∀ (h1 : c + m < src.size) (h2 : j + m < src.size),
      src[c + m] = src[j + m] := by
  fun_induction matchLength src c j hc with
  | case1 c j hc h heq ih =>
      intro m hm h1 h2
      cases m with
      | zero => simpa using heq
      | succ m =>
          have := ih m (by omega) (by omega) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 m] using this
  | case2 c j hc h hne => intro m hm; omega
  | case3 c j hc h => intro m hm; omega

/-! ## The scan -/

/-- The scan writes bytes that take an empty output to the whole input.

The invariant is that the bytes written so far take the empty output to the prefix before `lit`.
-/
theorem compressLoop_reads (src : ByteArray) (hsz : src.size ≤ maxUncompressedLength)
    (table : Array Nat) (i lit : Nat) (out : ByteArray) (hli : lit ≤ i) (his : i ≤ src.size)
    (hout : Reads src.size out.data.toList [] (src.data.toList.take lit)) :
    Reads src.size (compressLoop src table i lit out).data.toList [] src.data.toList := by
  have hlen : src.data.toList.length = src.size := Array.length_toList
  have hmin : minMatch = 4 := rfl
  have hmax : src.size ≤ 2 ^ 32 := by simp only [maxUncompressedLength] at hsz; omega
  fun_induction compressLoop src table i lit out with
  | case1 tb i lit out hi s c tb' hc hl ih =>
      have hle := matchLength_le src c i hc.1 (by omega)
      have hmatch := matchLength_get src c i hc.1
      have hwin : i - c < copyTwoOffsetBound := hc.2
      obtain ⟨e₁, he₁, hr₁⟩ := emitLiteral_reads (declared := src.size) out hli
        (by omega) (by omega) (by omega)
      obtain ⟨e₂, he₂, hr₂⟩ := emitCopies_reads (declared := src.size) (L := src.data.toList)
        (offset := i - c) (by omega) hwin (matchLength src c i hc.1) i (emitLiteral out src lit i)
        (by omega) (by omega) (by omega) (fun j hj hjn h1 h2 => by
          have hA := hmatch (j - i) (by omega) (by omega) (by omega)
          have e₁ : c + (j - i) = j - (i - c) := by omega
          have e₂ : i + (j - i) = j := by omega
          simp only [e₁, e₂] at hA
          simpa [ByteArray.getElem_eq_getElem_data] using hA.symm)
      refine ih (Nat.le_refl _) (by omega) ?_
      rw [he₂, he₁]
      exact ((hout.trans hr₁).trans hr₂)
  | case2 tb i lit out hi s c tb' hc hl ih => exact ih (by omega) (by omega) hout
  | case3 tb i lit out hi s c tb' hc ih => exact ih (by omega) (by omega) hout
  | case4 tb i lit out hi =>
      obtain ⟨e, he, hr⟩ := emitLiteral_reads (declared := src.size) out (hi := src.size)
        (lo := lit) (src := src) (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _)
      rw [he]
      have := hout.trans hr
      rwa [List.take_of_length_le (by omega)] at this

/-! ## The round trip -/

/-- The block of an input of at most 2^32 - 1 bytes decompresses back to the input. -/
theorem decompress_compress {src : ByteArray} (h : src.size ≤ maxUncompressedLength) :
    decompress (compress src) = .ok src := by
  have hreads := compressLoop_reads src h (Array.replicate (2 ^ tableBits) 0) 0 0 ByteArray.empty
    (Nat.le_refl _) (Nat.zero_le _) (by simpa using Reads.nil src.size [])
  rw [decompress, toList_eq_data_toList, compress, ByteArray.data_append, Array.toList_append,
    List.toList_toArray, decompressToArray, readPreamble_encode _ (by simpa using h)]
  generalize compressLoop src (Array.replicate (2 ^ tableBits) 0) 0 0 ByteArray.empty = body
    at hreads ⊢
  have hbody := hreads []
  have hbs : src.data.toList.toByteArray = src := ByteArray.ext (by simp)
  rw [List.append_nil, show ([] : List UInt8).toByteArray = ByteArray.empty from rfl] at hbody
  simp only [List.length_nil, decompressElements, hbs] at hbody
  simp only [hbody]
  simp

end EthLib.Networking.Proofs.Snappy.Compress
