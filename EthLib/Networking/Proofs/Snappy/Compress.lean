module

public import EthLib.Networking.Proofs.Snappy.Encode
public import EthLib.Networking.Snappy.Compress

/-!
# `Networking.Proofs.Snappy.Compress`

The block that the compressor writes decompresses to its input.

Source: `format_description.txt` of `google/snappy`, at
<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt>.

- A proposal that counts matches the input on every byte the copy writes (§2.2).
- After each step, the elements written so far decode to the input before the pending literal.
- So the block of an input of at most 2^32 - 1 bytes decompresses to that input.

The table of positions never enters the proofs.

The compressor reads the input to count the bytes a proposal matches.

So the theorem holds for every table.

One input has many blocks, so the round trip goes one way only.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.Compress

open EthLib.Networking.Snappy
open EthLib.Networking.Proofs.Snappy.Block
open EthLib.Networking.Proofs.Snappy.Encode

/-! ## The match length -/

/-- A count of agreeing bytes only grows, and stops within the input. -/
theorem le_matchLength (src : ByteArray) (c j : Nat) (hc : c < j) (m : Nat)
    (hm : j + m ≤ src.size) :
    m ≤ matchLength src c j hc m ∧ j + matchLength src c j hc m ≤ src.size := by
  fun_induction matchLength src c j hc m with
  | case1 m h heq ih => have := ih (by omega); omega
  | case2 m h hne => omega
  | case3 m h => omega

/-- A match that starts at or before the end of the input ends within the input. -/
theorem matchLength_le (src : ByteArray) (c j : Nat) (hc : c < j) (hj : j ≤ src.size) :
    j + matchLength src c j hc ≤ src.size :=
  (le_matchLength src c j hc 0 (by omega)).2

/-- Each byte that a count from `m` adds equals the byte that many places before it. -/
theorem matchLength_get_of_le (src : ByteArray) (c j : Nat) (hc : c < j) (m : Nat) :
    ∀ (k : Nat), m ≤ k → k < matchLength src c j hc m →
      ∀ (h1 : c + k < src.size) (h2 : j + k < src.size), src[c + k] = src[j + k] := by
  fun_induction matchLength src c j hc m with
  | case1 m h heq ih =>
      intro k hmk hk h1 h2
      by_cases hkm : k = m
      · subst hkm
        exact heq
      · exact ih k (by omega) hk h1 h2
  | case2 m h hne => intro k hmk hk; omega
  | case3 m h => intro k hmk hk; omega

/-- Every byte in a match equals the byte `j - c` places before it. -/
theorem matchLength_get (src : ByteArray) (c j : Nat) (hc : c < j) :
    ∀ (m : Nat), m < matchLength src c j hc → ∀ (h1 : c + m < src.size) (h2 : j + m < src.size),
      src[c + m] = src[j + m] :=
  fun m => matchLength_get_of_le src c j hc 0 m (Nat.zero_le m)

/-! ## The scan -/

/-- The scan writes bytes that take an empty output to the whole input.

The invariant: the bytes written so far take the empty output to the input before `lit`.
-/
theorem compressLoop_reads (src : ByteArray) (hsz : src.size ≤ maxUncompressedLength)
    (table : Array Nat) (i lit : Nat) (out : ByteArray) (hli : lit ≤ i) (his : i ≤ src.size)
    (hout : Reads src.size out.data.toList [] (src.data.toList.take lit)) :
    Reads src.size (compressLoop src table i lit out).data.toList [] src.data.toList := by
  have hlen : src.data.toList.length = src.size := Array.length_toList
  have hmin : minCopyLength = 4 := rfl
  have hmax : src.size ≤ 2 ^ 32 := by simp only [maxUncompressedLength] at hsz; omega
  fun_induction compressLoop src table i lit out with
  | case1 tb i lit out hi s c tb' hc len hl ih =>
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
  | case2 tb i lit out hi s c tb' hc len hl ih => exact ih (by omega) (by omega) hout
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

/-- The block of an input of at most 2^32 - 1 bytes, read as a list, decompresses to the input. -/
theorem decompressList_compress {src : ByteArray} (h : src.size ≤ maxUncompressedLength) :
    decompressList (compress src).data.toList = .ok src.data.toList := by
  have hd := decompress_compress h
  rw [decompress, toList_eq_data_toList] at hd
  simp [decompressList, hd, Except.map]

/-- The block of an input of at most 2^32 - 1 bytes declares the size of the input. -/
theorem readPreamble_compress {src : ByteArray} (h : src.size ≤ maxUncompressedLength) :
    ∃ rest, readPreamble (compress src).data.toList = .ok (src.size, rest) := by
  obtain ⟨rest, hpre⟩ := decompressList_length_eq_declared (decompressList_compress h)
  exact ⟨rest, by simpa using hpre⟩

end EthLib.Networking.Proofs.Snappy.Compress
