module

public import EthLib.Networking.Quic.VarInt
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: QUIC integers

Reading an integer written at any width that holds it returns that integer and the trailing bytes.
-/

@[expose] public section

namespace EthLib.Networking.Quic.VarInt

open EthLib.Base

/-- A chosen width writes exactly the byte count selected by its two-bit prefix. -/
theorem length_encodeWith (w : Width) (v : VarInt) (h : v.val < capacity w) :
    (encodeWith w v h).length = 2 ^ w.val := by
  simp only [encodeWith, List.length_cons, natToBytes_length, tailLength]
  have : 0 < 2 ^ w.val := Nat.two_pow_pos _
  omega

/-- The high bits of the first byte select the writer's width. -/
private theorem head_parts (w : Width) (v : VarInt) (h : v.val < capacity w) :
    (UInt8.ofNat (w.val * 64 + v.val / 256 ^ tailLength w)).toNat / 64 = w.val ∧
    (UInt8.ofNat (w.val * 64 + v.val / 256 ^ tailLength w)).toNat % 64 =
      v.val / 256 ^ tailLength w := by
  have hp : 0 < 256 ^ tailLength w := Nat.pow_pos (by decide)
  have hq : v.val / 256 ^ tailLength w < 64 := by
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [capacity, Nat.mul_comm] using h)
  have hw := w.isLt
  have hhead : w.val * 64 + v.val / 256 ^ tailLength w < UInt8.size := by
    simp only [UInt8.size]
    omega
  simp only [UInt8.toNat_ofNat_of_lt' hhead]
  generalize v.val / 256 ^ tailLength w = q at hq ⊢
  constructor <;> omega

/-- Decoding undoes encoding at every width that holds the value, with any trailing bytes. -/
theorem decode_encodeWith (w : Width) (v : VarInt) (h : v.val < capacity w)
    (rest : List UInt8) : decode (encodeWith w v h ++ rest) = .ok (v, rest) := by
  obtain ⟨hdiv, hmod⟩ := head_parts w v h
  have hselector : (⟨(UInt8.ofNat (w.val * 64 +
      v.val / 256 ^ tailLength w)).toNat / 64, by omega⟩ : Width) = w :=
    Fin.ext hdiv
  simp only [encodeWith, List.cons_append, decode, hselector]
  have hlen := natToBytes_length (tailLength w) v.val
  have htake : (natToBytes (tailLength w) v.val ++ rest).take (tailLength w) =
      natToBytes (tailLength w) v.val := by
    simpa only [hlen] using (List.take_left (l₁ := natToBytes (tailLength w) v.val) (l₂ := rest))
  have hdrop : (natToBytes (tailLength w) v.val ++ rest).drop (tailLength w) = rest := by
    simpa only [hlen] using (List.drop_left (l₁ := natToBytes (tailLength w) v.val) (l₂ := rest))
  have hvalue : v.val / 256 ^ tailLength w * 256 ^ tailLength w +
      bytesToNat (natToBytes (tailLength w) v.val) = v.val := by
    rw [bytesToNat_natToBytes]
    exact Nat.div_add_mod' _ _
  simp only [List.length_append, hlen, Nat.not_lt.mpr (Nat.le_add_right ..), ↓reduceIte,
    htake, hmod, hvalue, v.isLt, ↓reduceDIte, hdrop]

/-- Decoding reads back the shortest encoding, with any trailing bytes. -/
theorem decode_encode (v : VarInt) (rest : List UInt8) :
    decode (encode v ++ rest) = .ok (v, rest) :=
  decode_encodeWith _ _ _ _

/-- An input shorter than the selected width is rejected. -/
theorem decode_truncated (head : UInt8) (rest : List UInt8)
    (h : rest.length < 2 ^ (head.toNat / 64) - 1) :
    decode (head :: rest) = .error .truncated := by
  simp [decode, tailLength, h]

/-- Every width carries at most 62 payload bits. -/
private theorem capacity_le (w : Width) : capacity w ≤ 2 ^ 62 := by
  rcases w with ⟨w, hw⟩
  have : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    dsimp only [capacity, tailLength] <;> decide

/-- Every complete integer is accepted, including longer representations of small values. -/
theorem decode_ok_of_length (head : UInt8) (rest : List UInt8)
    (h : 2 ^ (head.toNat / 64) - 1 ≤ rest.length) :
    ∃ v, decode (head :: rest) = .ok (v, rest.drop (2 ^ (head.toNat / 64) - 1)) := by
  let w : Width := ⟨head.toNat / 64, by have := head.toNat_lt; omega⟩
  have hlen : (rest.take (tailLength w)).length = tailLength w := by
    simp only [List.length_take]
    exact Nat.min_eq_left h
  have hbytes := bytesToNat_lt (rest.take (tailLength w))
  rw [hlen] at hbytes
  have hhead : head.toNat % 64 + 1 ≤ 64 := by omega
  have hv : head.toNat % 64 * 256 ^ tailLength w +
      bytesToNat (rest.take (tailLength w)) < capacity w := by
    calc
      _ < (head.toNat % 64 + 1) * 256 ^ tailLength w := by
        rw [Nat.succ_mul]
        omega
      _ ≤ capacity w := Nat.mul_le_mul_right _ hhead
  have hbound := Nat.lt_of_lt_of_le hv (capacity_le w)
  dsimp only [tailLength, w] at hbound
  simp only [decode, tailLength, Nat.not_lt.mpr h, ↓reduceIte, hbound, ↓reduceDIte]
  exact ⟨_, rfl⟩

/-- A nonempty input is rejected exactly when it is shorter than its selected width. -/
theorem decode_error_iff (head : UInt8) (rest : List UInt8) (error : Error) :
    decode (head :: rest) = .error error ↔
      rest.length < 2 ^ (head.toNat / 64) - 1 ∧ error = .truncated := by
  by_cases h : rest.length < 2 ^ (head.toNat / 64) - 1
  · simp [decode_truncated head rest h, h, eq_comm]
  · obtain ⟨v, hv⟩ := decode_ok_of_length head rest (by omega)
    simp [hv, h]

end EthLib.Networking.Quic.VarInt
