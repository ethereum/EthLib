module

public import EthLib.Networking.Proofs.Snappy.Block
public import EthLib.Networking.Snappy.Encode

/-!
# `Networking.Proofs.Snappy.Encode`

The decoder reads the elements that the encoder writes, against `format_description.txt`:

<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt>.

Bytes `e` take the output `o` to the output `o'` when the element loop reads `e` and writes `o'`.

It then goes on with any bytes `s` that follow.

- The bytes of a literal take the output `o` to `o` followed by the data (§2.1).
- The bytes of a copy take an output that is a prefix of a list `L` to a longer prefix of `L`,
  when each byte the copy writes is the byte `offset` places before it in `L` (§2.2).
- The copies that the encoder writes for one offset, and the literal that it writes for a range of
  the input, do the same one after the other.

The kernel checks everything here, so no `native_decide` or `bv_decide` axiom appears.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.Encode

open EthLib.Base (uintToBytes)
open EthLib.Networking.Snappy
open EthLib.Networking.Proofs.Snappy.Block

/-- Bytes `e` take the output `o` to the output `o'`, for a block that declares `declared` bytes.

The element loop reads `e` followed by any `s`, and then reads `s` with the output `o'`.

Both sides have just the fuel that their input needs.
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

/-- Bytes that read as one element, whatever follows, take the output to its successor. -/
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

/-- A literal, then any bytes: the literal appends its data to the output.

The output need not be empty, and bytes may follow.
-/
theorem decompressElements_literal_append {declared : Nat} {o data s : List UInt8}
    (hne : data ≠ []) (h : data.length ≤ 2 ^ 32) (hd : o.length + data.length ≤ declared)
    (fuel : Nat) :
    decompressElements declared (literal data ++ s) o.toByteArray (fuel + 1) =
      decompressElements declared s (o ++ data).toByteArray fuel := by
  have hpos : 0 < data.length := List.length_pos_iff.mpr hne
  dsimp only [literal]
  split
  -- The length sits in the tag.
  · rename_i hn
    have ht : (UInt8.ofNat ((data.length - 1) * 4)).toNat = (data.length - 1) * 4 := by
      rw [UInt8.toNat_ofNat']; omega
    simp only [List.cons_append, decompressElements, ht]
    simp [hn, show data.length - 1 + 1 = data.length by omega,
      show ¬ declared < o.length + data.length by omega,
      show ¬ data.length + s.length < data.length by omega]
  -- The length takes 1 to 4 bytes after the tag.
  · rename_i hn
    have hk : 1 ≤ literalLengthBytes (data.length - 1) ∧ literalLengthBytes (data.length - 1) ≤ 4 ∧
        data.length - 1 < 256 ^ literalLengthBytes (data.length - 1) := by
      unfold literalLengthBytes
      split <;> (try split) <;> (try split) <;> simp only [Nat.reducePow] at * <;> omega
    obtain ⟨hk1, hk4, hlt⟩ := hk
    generalize literalLengthBytes (data.length - 1) = k at *
    have ht : (UInt8.ofNat ((59 + k) * 4)).toNat = (59 + k) * 4 := by
      rw [UInt8.toNat_ofNat']; omega
    have hv : (uintToBytes k (data.length - 1)).toList.foldr
        (fun byte acc => byte.toNat + 256 * acc) 0 = data.length - 1 := by
      simpa using EthLib.Base.foldr_uintToBytes_of_lt hlt
    have hk' : (uintToBytes k (data.length - 1)).toList.length = k := by simp
    simp only [List.cons_append, List.append_assoc]
    simp only [decompressElements, ht, EthLib.Base.bytesToUint_toVector]
    simp [show ¬ 59 + k < 60 by omega, show 59 + k - 59 = k by omega, hv, hk',
      show data.length - 1 + 1 = data.length by omega,
      show ¬ declared < o.length + data.length by omega,
      show ¬ data.length + s.length < data.length by omega,
      show ¬ k + (data.length + s.length) < k by omega]

/-- The bytes of a literal take the output to the output followed by the data. -/
theorem reads_literal {declared : Nat} {o data : List UInt8} (hne : data ≠ [])
    (h : data.length ≤ 2 ^ 32) (hd : o.length + data.length ≤ declared) :
    Reads declared (literal data) o (o ++ data) := by
  refine reads_of_step ?_ fun s fuel => decompressElements_literal_append hne h hd fuel
  dsimp only [literal]
  split <;> exact List.cons_ne_nil _ _


/-! ## Copies (§2.2) -/

/-- One byte, read as a number, is its value. -/
theorem bytesToUint_single (b : UInt8) : EthLib.Base.bytesToUint #[b].toVector = b.toNat := by
  simpa using EthLib.Base.bytesToUint_toVector [b]

/-- Bytes that repeat the byte `offset` places before them make a prefix of the list they repeat. -/
theorem eq_take_of_repeat {L r : List UInt8} {p n offset : Nat} (hoff : 0 < offset)
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

/-- A copy element reads as the copy it was written for, when it repeats bytes of a list.

Here the first `p` bytes of `L` are the output so far.

Each byte of the copy is the byte `offset` places before it in `L`.
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
  split
  -- A copy with a one-byte offset.
  · rename_i hc
    obtain ⟨hc1, hc2, hc3⟩ := hc
    simp only [copyOneOffsetBound] at hc3
    have ht : (UInt8.ofNat (1 + (len - 4) * 4 + offset / 256 * 32)).toNat =
        1 + (len - 4) * 4 + offset / 256 * 32 := by
      rw [UInt8.toNat_ofNat']; omega
    have hb : (UInt8.ofNat (offset % 256)).toNat = offset % 256 := by
      rw [UInt8.toNat_ofNat']; omega
    simp only [copyOne, List.cons_append, List.nil_append, decompressElements, ht]
    simp [show (1 + (len - 4) * 4 + offset / 256 * 32) % 4 = 1 by omega,
      show (1 + (len - 4) * 4 + offset / 256 * 32) / 4 % 8 = len - 4 by omega,
      show (1 + (len - 4) * 4 + offset / 256 * 32) / 4 / 8 = offset / 256 by omega,
      bytesToUint_single, hb, show 4 + (len - 4) = len by omega,
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
    simp only [copyTwo, List.cons_append, List.nil_append, decompressElements, ht]
    simp [show (2 + (len - 1) * 4) % 4 = 2 by omega,
      show (2 + (len - 1) * 4) / 4 = len - 1 by omega,
      EthLib.Base.bytesToUint_toVector, hb0, hb1, show len - 1 + 1 = len by omega,
      show offset % 256 + 256 * (offset / 256) = offset by omega,
      Nat.min_eq_left (show p ≤ L.length by omega), show offset ≠ 0 by omega,
      show ¬ declared < p + len by omega, show ¬ s.length + 1 + 1 < 2 by omega, hr]

/-! ## The encoder -/

/-- The copies that `emitCopies` appends read as a copy of the next `len` bytes of a list.

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
      split
      · rename_i h0
        subst h0
        exact ⟨[], by simp, Reads.nil declared _⟩
      · rename_i h0
        have hn : min len maxCopyLength ≤ len := Nat.min_le_left _ _
        have hn1 : 1 ≤ min len maxCopyLength := by simp only [maxCopyLength]; omega
        have hn2 : min len maxCopyLength ≤ maxCopyLength := Nat.min_le_right _ _
        have h₁ := reads_copyElement (declared := declared) (L := L) (p := p) hoff hle hn1 hn2
          hbound (by omega) (by omega)
          (fun j hj hjn h1 h2 => hmatch j hj (by omega) h1 h2)
        obtain ⟨e, he, hr⟩ := ih (len - min len maxCopyLength) (by omega)
          (p + min len maxCopyLength)
          (out ++ ⟨(copyElement offset (min len maxCopyLength)).toArray⟩)
          (by omega) (by omega) (by omega)
          (fun j hj hjn h1 h2 => hmatch j (by omega) (by omega) h1 h2)
        refine ⟨copyElement offset (min len maxCopyLength) ++ e, ?_, ?_⟩
        · rw [he]; simp
        · rw [show p + len = p + min len maxCopyLength + (len - min len maxCopyLength) by omega]
          exact h₁.trans hr

/-- The literal that `emitLiteral` appends reads as the bytes of `src` from `lo` up to `hi`. -/
theorem emitLiteral_reads {declared : Nat} {src : ByteArray} {lo hi : Nat} (out : ByteArray)
    (hlh : lo ≤ hi) (hhi : hi ≤ src.size) (hlen : hi - lo ≤ 2 ^ 32) (hfit : hi ≤ declared) :
    ∃ e, (emitLiteral out src lo hi).data.toList = out.data.toList ++ e ∧
      Reads declared e (src.data.toList.take lo) (src.data.toList.take hi) := by
  unfold emitLiteral
  split
  · rename_i hlt
    have hd : (src.extract lo hi).data.toList = (src.data.toList.drop lo).take (hi - lo) := by
      rw [ByteArray.data_extract, Array.toList_extract]
    have hsz : src.data.toList.length = src.size := Array.length_toList
    have hlo : (src.data.toList.take lo).length = lo := by simp; omega
    have hdl : ((src.data.toList.drop lo).take (hi - lo)).length = hi - lo := by simp; omega
    refine ⟨literal (src.extract lo hi).data.toList, by simp, ?_⟩
    rw [hd, show hi = lo + (hi - lo) by omega, List.take_add, Nat.add_sub_cancel_left]
    refine reads_literal (fun h => ?_) (by omega) (by omega)
    rw [h] at hdl
    simp at hdl
    omega
  · rename_i hge
    obtain rfl : lo = hi := by omega
    exact ⟨[], by simp, Reads.nil declared _⟩

end EthLib.Networking.Proofs.Snappy.Encode
