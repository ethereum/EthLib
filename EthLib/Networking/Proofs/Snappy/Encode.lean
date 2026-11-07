module

public import EthLib.Networking.Proofs.Snappy.Block
public import EthLib.Networking.Snappy.Encode

/-!
# `Networking.Proofs.Snappy.Encode`

The decoder reads the elements that the encoder writes.

Source: [`format_description.txt`][format] of `google/snappy`.

Bytes `e` take the output `o` to the output `o'` in this sense.

Start the element loop on `e`, followed by any bytes, with the output `o`.

It then reaches the end of `e` with the output `o'`.

- The bytes of a literal take the output `o` to `o` followed by the data (§2.1).
- A copy takes a prefix of a list `L` to a longer prefix, if it repeats bytes of `L` (§2.2).
- The copies that the encoder writes for one offset do the same, one after the other.
- The literal that the encoder writes for a range of the input takes it from its start to its end.

[format]: https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.Encode

open EthLib.Base (uintToBytes)
open EthLib.Networking.Snappy
open EthLib.Networking.Proofs.Snappy.Block

/-- Bytes `e` take the output `o` to the output `o'`, for a block that declares `declared` bytes.

The element loop reads `e` followed by any `s`, and then reads `s` with the output `o'`.

Each side runs with fuel equal to the length of its input.
-/
def Reads (declared : Nat) (e o o' : List UInt8) : Prop :=
  ∀ s, decompressElements declared (e ++ s) o.toByteArray (e ++ s).length =
    decompressElements declared s o'.toByteArray s.length

/-- No bytes leave the output as it is. -/
theorem Reads.nil (declared : Nat) (o : List UInt8) : Reads declared [] o o :=
  fun _ => rfl

/-- Bytes that take `o` to `o'`, then bytes that take `o'` to `o''`, take `o` to `o''`. -/
theorem Reads.trans {declared : Nat} {e₁ e₂ o o' o'' : List UInt8}
    (h₁ : Reads declared e₁ o o') (h₂ : Reads declared e₂ o' o'') :
    Reads declared (e₁ ++ e₂) o o'' := by
  intro s
  rw [List.append_assoc, h₁ (e₂ ++ s), h₂ s]

/-- Nonempty bytes that the loop reads in one step, whatever follows, take `o` to `o'`. -/
theorem reads_of_step {declared : Nat} {e o o' : List UInt8} (he : e ≠ [])
    (h : ∀ (s : List UInt8) (fuel : Nat), decompressElements declared (e ++ s) o.toByteArray
      (fuel + 1) = decompressElements declared s o'.toByteArray fuel) :
    Reads declared e o o' := by
  intro s
  obtain ⟨k, hk⟩ : ∃ k, e.length = k + 1 :=
    ⟨e.length - 1, by have := List.length_pos_iff.mpr he; omega⟩
  rw [show (e ++ s).length = (k + s.length) + 1 by simp [hk]; omega, h]
  exact decompressElements_fuel declared s _ (by omega)

/-! ## Literals (§2.1) -/

/-- The bytes of a literal take the output to the output followed by the data. -/
theorem reads_literal {declared : Nat} {o data : List UInt8} (hne : data ≠ [])
    (h : data.length ≤ 2 ^ 32) (hd : o.length + data.length ≤ declared) :
    Reads declared (literal data) o (o ++ data) :=
  reads_of_step (by simp [literal, hne]) fun _ fuel =>
    decompressElements_literal_append hne h hd fuel

/-! ## Copies (§2.2) -/

/-- A list `r` that starts with the first `p` bytes of `L` is the first `p + n` bytes of `L`.

The list `r` has `p + n` bytes, and `L` has at least as many.

The offset is positive and at most `p`.

Each byte of `r` from `p` on equals the byte `offset` places before it in `r`.

Each byte of `L` from `p` up to `p + n` equals the byte `offset` places before it in `L`.
-/
private theorem eq_take_of_repeat {L r : List UInt8} {p n offset : Nat} (hoff : 0 < offset)
    (hle : offset ≤ p)
    (hpn : p + n ≤ L.length) (hlen : r.length = p + n) (hpre : L.take p <+: r)
    (hr : ∀ (j : Nat) (hj : p ≤ j) (hjr : j < r.length), r[j] = r[j - offset]'(by omega))
    (hmatch : ∀ (j : Nat) (_hj : p ≤ j) (_hjn : j < p + n) (h1 : j < L.length)
      (h2 : j - offset < L.length), L[j] = L[j - offset]) :
    r = L.take (p + n) := by
  have key : ∀ (j : Nat) (hjr : j < r.length), r[j] = L[j]'(by omega) := by
    intro j
    induction j using Nat.strongRecOn with
    | _ j ih =>
        intro hjr
        by_cases hjp : j < p
        · have := hpre.getElem (i := j) (by simp; omega)
          simp only [List.getElem_take] at this
          exact this.symm
        · rw [hr j (by omega) hjr, ih (j - offset) (by omega) (by omega),
            hmatch j (by omega) (by omega) (by omega) (by omega)]
  refine List.ext_getElem (by simp; omega) fun j h1 h2 => ?_
  simp only [List.getElem_take]
  exact key j h1

/-- A copy element takes the first `p` bytes of a list `L` to its first `p + len` bytes.

Each byte of the copy is the byte `offset` places before it in `L`.

The offset is from 1 to 65535 and at most `p`, and the length is from 1 to 64.

Both `L` and the declared length hold at least `p + len` bytes.
-/
theorem reads_copyElement {declared : Nat} {L : List UInt8} {p offset len : Nat}
    (hoff : 0 < offset) (hle : offset ≤ p) (hlen1 : 1 ≤ len) (hlen2 : len ≤ maxCopyLength)
    (hbound : offset < copyTwoOffsetBound) (hL : p + len ≤ L.length)
    (hfit : p + len ≤ declared)
    (hmatch : ∀ (j : Nat) (_hj : p ≤ j) (_hjn : j < p + len) (h1 : j < L.length)
      (h2 : j - offset < L.length), L[j] = L[j - offset]) :
    Reads declared (copyElement offset len) (L.take p) (L.take (p + len)) := by
  have hlp : (L.take p).length = p := by simp; omega
  obtain ⟨r, hr, hrlen, hpre, hrep⟩ := copyBytes_spec (o := L.take p) len hoff (by omega)
  have hrL : r = L.take (p + len) :=
    eq_take_of_repeat hoff hle hL (by omega) hpre (fun j hj hjr => hrep j (by omega) hjr) hmatch
  subst hrL
  simp only [maxCopyLength, copyTwoOffsetBound] at hlen2 hbound
  refine reads_of_step ?_ fun s fuel => ?_
  · unfold copyElement; split <;> simp [copyOne, copyTwo]
  unfold copyElement
  by_cases hc : 4 ≤ len ∧ len ≤ 11 ∧ offset < copyOneOffsetBound
  -- A copy with a one-byte offset.
  · obtain ⟨hc1, hc2, hc3⟩ := hc
    simp only [copyOneOffsetBound] at hc3
    have ht : (UInt8.ofNat (1 + (len - 4) * 4 + offset / 256 * 32)).toNat =
        1 + (len - 4) * 4 + offset / 256 * 32 := by
      rw [UInt8.toNat_ofNat']; omega
    have hb : (UInt8.ofNat (offset % 256)).toNat = offset % 256 := by
      rw [UInt8.toNat_ofNat']; omega
    simp only [copyOneOffsetBound, hc1, hc2, hc3, and_self, ↓reduceIte, copyOne, List.cons_append,
      List.nil_append, decompressElements, ht]
    simp [show (1 + (len - 4) * 4 + offset / 256 * 32) % 4 = 1 by omega,
      show (1 + (len - 4) * 4 + offset / 256 * 32) / 4 % 8 = len - 4 by omega,
      show (1 + (len - 4) * 4 + offset / 256 * 32) / 4 / 8 = offset / 256 by omega,
      EthLib.Base.bytesToUint_toVector, hb, show 4 + (len - 4) = len by omega,
      show offset / 256 * 256 + offset % 256 = offset by omega,
      Nat.min_eq_left (show p ≤ L.length by omega), show offset ≠ 0 by omega,
      show ¬ declared < p + len by omega, hr]
  -- A copy with a two-byte offset.
  · have ht : (UInt8.ofNat (2 + (len - 1) * 4)).toNat = 2 + (len - 1) * 4 := by
      rw [UInt8.toNat_ofNat']; omega
    have hb0 : (UInt8.ofNat (offset % 256)).toNat = offset % 256 := by
      rw [UInt8.toNat_ofNat']; omega
    have hb1 : (UInt8.ofNat (offset / 256)).toNat = offset / 256 := by
      rw [UInt8.toNat_ofNat']; omega
    simp only [hc, ↓reduceIte, copyTwo, List.cons_append, List.nil_append, decompressElements, ht]
    simp [show (2 + (len - 1) * 4) % 4 = 2 by omega,
      show (2 + (len - 1) * 4) / 4 = len - 1 by omega,
      EthLib.Base.bytesToUint_toVector, hb0, hb1, show len - 1 + 1 = len by omega,
      show offset % 256 + 256 * (offset / 256) = offset by omega,
      Nat.min_eq_left (show p ≤ L.length by omega), show offset ≠ 0 by omega,
      show ¬ declared < p + len by omega, show ¬ s.length + 1 + 1 < 2 by omega, hr]

/-! ## The encoder -/

/-- The copies that the encoder appends for one offset copy the next `len` bytes of a list.

At each step the output is a prefix of the list.

Each byte the copies write repeats the byte `offset` places before it.
-/
theorem emitCopies_reads {declared : Nat} {L : List UInt8} {offset : Nat} (hoff : 0 < offset)
    (hbound : offset < copyTwoOffsetBound) (len : Nat) :
    ∀ (p : Nat) (out : ByteArray), offset ≤ p → p + len ≤ L.length → p + len ≤ declared →
      (∀ (j : Nat) (_ : p ≤ j) (_ : j < p + len) (h1 : j < L.length) (h2 : j - offset < L.length),
        L[j] = L[j - offset]) →
      ∃ e, (emitCopies offset out len).data.toList = out.data.toList ++ e ∧
        Reads declared e (L.take p) (L.take (p + len)) := by
  induction len using Nat.strongRecOn with
  | _ len ih =>
      intro p out hle hL hfit hmatch
      rw [emitCopies]
      by_cases h0 : len = 0
      · subst h0
        exact ⟨[], by simp, Reads.nil declared _⟩
      · simp only [h0, ↓reduceIte]
        -- The length of the next element: 1 to 64 bytes, and at most what remains.
        generalize hn : (if maxCopyLength + 4 ≤ len then maxCopyLength
          else if maxCopyLength < len then maxCopyLength - 4 else len) = n
        have hb : 1 ≤ n ∧ n ≤ len ∧ n ≤ maxCopyLength := by
          subst hn; simp only [maxCopyLength]; grind
        obtain ⟨hn1, hnl, hn2⟩ := hb
        have h₁ := reads_copyElement (declared := declared) (L := L) (p := p) hoff hle hn1 hn2
          hbound (by omega) (by omega)
          (fun j hj hjn h1 h2 => hmatch j hj (by omega) h1 h2)
        obtain ⟨e, he, hr⟩ := ih (len - n) (by omega) (p + n)
          (out ++ ⟨(copyElement offset n).toArray⟩)
          (by omega) (by omega) (by omega)
          (fun j hj hjn h1 h2 => hmatch j (by omega) (by omega) h1 h2)
        refine ⟨copyElement offset n ++ e, ?_, ?_⟩
        · rw [he]; simp
        · rw [show p + len = p + n + (len - n) by omega]
          exact h₁.trans hr

/-- The literal that the encoder appends for the bytes of `src` from `lo` up to `hi`.

It takes the first `lo` bytes of `src` to its first `hi` bytes.
-/
theorem emitLiteral_reads {declared : Nat} {src : ByteArray} {lo hi : Nat} (out : ByteArray)
    (hlh : lo ≤ hi) (hhi : hi ≤ src.size) (hlen : hi - lo ≤ 2 ^ 32) (hfit : hi ≤ declared) :
    ∃ e, (emitLiteral out src lo hi).data.toList = out.data.toList ++ e ∧
      Reads declared e (src.data.toList.take lo) (src.data.toList.take hi) := by
  unfold emitLiteral
  by_cases hlt : lo < hi
  · have hsz : src.data.toList.length = src.size := Array.length_toList
    have hlo : (src.data.toList.take lo).length = lo := by simp; omega
    have hdl : ((src.data.toList.drop lo).take (hi - lo)).length = hi - lo := by simp; omega
    refine ⟨literal ((src.data.toList.drop lo).take (hi - lo)), ?_, ?_⟩
    -- The slice appends the data after the header, and leaves nothing behind it.
    · simp only [hlt, ↓reduceIte, ByteArray.copySlice, literal, hdl]
      have hm : min (hi - lo) (src.data.size - lo) = hi - lo := by
        rw [ByteArray.size_data]; omega
      have h0 : ∀ a b c : Nat, b - (a + b + c - a) = 0 := by intros; omega
      simp [Array.toList_extract, List.extract, Nat.add_sub_cancel' hlh, ← ByteArray.size_data,
        hm, h0, List.take_of_length_le]
      omega
    · rw [show hi = lo + (hi - lo) by omega, List.take_add, Nat.add_sub_cancel_left]
      refine reads_literal (fun h => ?_) (by omega) (by omega)
      rw [h] at hdl
      simp at hdl
      omega
  · obtain rfl : lo = hi := by omega
    simp only [Nat.lt_irrefl, ↓reduceIte]
    exact ⟨[], by simp, Reads.nil declared _⟩

end EthLib.Networking.Proofs.Snappy.Encode
