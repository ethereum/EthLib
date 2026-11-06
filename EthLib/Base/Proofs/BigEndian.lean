module

public import EthLib.Base.BigEndian

/-!
# Proofs: `BigEndian`

Reading and writing big-endian bytes undo each other.

- A list of `k` bytes holds a value below `256 ^ k`.
- Writing `n` on `len` bytes gives bytes that read back as `n % 256 ^ len`.
- On `a + b` bytes, `n` is `n / 256 ^ b` on the first `a` bytes, then `n` on the last `b`.
- Zero on `len` bytes is `len` zero bytes.
- Reading `k` bytes and writing the value back on `k` bytes gives the same bytes.
-/

@[expose] public section

namespace EthLib.Base

/-- Folding from any start value shifts it by one factor of 256 per byte. -/
theorem foldl_bytesToNat (bytes : List UInt8) (acc : Nat) :
    bytes.foldl (fun acc b => acc * 256 + b.toNat) acc
      = acc * 256 ^ bytes.length + bytesToNat bytes := by
  induction bytes generalizing acc with
  | nil => simp [bytesToNat]
  | cons b rest ih =>
    -- Unfold one byte on both sides, then use the induction hypothesis twice.
    have h0 := ih (b.toNat)
    have h1 := ih (acc * 256 + b.toNat)
    simp only [bytesToNat, List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add] at *
    rw [h1, h0, Nat.pow_succ, Nat.add_mul, Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm 256]

/-- Appending bytes on the right shifts the earlier value left by their count. -/
theorem bytesToNat_append (a b : List UInt8) :
    bytesToNat (a ++ b) = bytesToNat a * 256 ^ b.length + bytesToNat b := by
  rw [bytesToNat, List.foldl_append, foldl_bytesToNat]
  rfl

/-- A list of `k` bytes is worth less than `256 ^ k`. -/
theorem bytesToNat_lt (bytes : List UInt8) : bytesToNat bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [bytesToNat]
  | cons b rest ih =>
    -- The first byte is the most significant one, worth `256 ^ rest.length` per unit.
    have hcons : bytesToNat (b :: rest) = b.toNat * 256 ^ rest.length + bytesToNat rest := by
      simpa [bytesToNat] using foldl_bytesToNat rest b.toNat
    have hb : b.toNat + 1 ≤ 256 := b.toNat_lt
    rw [hcons, List.length_cons, Nat.pow_succ, Nat.mul_comm _ 256]
    -- `b * 256^r + v < (b + 1) * 256^r ≤ 256 * 256^r`.
    calc b.toNat * 256 ^ rest.length + bytesToNat rest
        < (b.toNat + 1) * 256 ^ rest.length := by rw [Nat.succ_mul]; omega
      _ ≤ 256 * 256 ^ rest.length := Nat.mul_le_mul_right _ hb

/-- Writing `n` on `len` bytes and reading it back gives `n % 256 ^ len`. -/
theorem bytesToNat_natToBytes (len n : Nat) :
    bytesToNat (natToBytes len n) = n % 256 ^ len := by
  induction len generalizing n with
  | zero => simp [natToBytes_zero, bytesToNat, Nat.mod_one]
  | succ len ih =>
    -- Split off the lowest byte, which is written last.
    rw [natToBytes_succ, bytesToNat_append, ih, List.length_singleton]
    have hlow : bytesToNat [UInt8.ofNat (n % 256)] = n % 256 := by
      simp [bytesToNat]
    rw [hlow, Nat.pow_one]
    -- `n % 256^(len+1) = n % 256 + 256 * (n / 256 % 256^len)`.
    rw [Nat.pow_succ', Nat.mod_mul, Nat.mul_comm, Nat.add_comm]

/-- Writing on `a + b` bytes puts `n / 256 ^ b` on the first `a` bytes and `n` on the last `b`. -/
theorem natToBytes_add (a b n : Nat) :
    natToBytes (a + b) n = natToBytes a (n / 256 ^ b) ++ natToBytes b n := by
  induction b generalizing n with
  | zero => simp [natToBytes_zero]
  | succ b ih =>
    -- Both sides end with the lowest byte, and the higher bytes are `n / 256` written on `a + b`.
    rw [← Nat.add_assoc, natToBytes_succ, ih, natToBytes_succ, List.append_assoc,
      Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 256]

/-- Zero on `len` bytes is `len` zero bytes. -/
theorem natToBytes_zero_right (len : Nat) : natToBytes len 0 = List.replicate len 0 := by
  induction len with
  | zero => rfl
  | succ len ih => rw [natToBytes_succ, Nat.zero_div, ih, List.replicate_succ']; rfl

/-- A number below `256 ^ len` survives the round trip through `len` bytes. -/
theorem bytesToNat_natToBytes_of_lt {len n : Nat} (h : n < 256 ^ len) :
    bytesToNat (natToBytes len n) = n := by
  rw [bytesToNat_natToBytes, Nat.mod_eq_of_lt h]

/-- A list of bytes survives the round trip through its value, written back on as many bytes. -/
theorem natToBytes_bytesToNat (bytes : List UInt8) :
    natToBytes bytes.length (bytesToNat bytes) = bytes := by
  generalize hn : bytes.length = len
  induction len generalizing bytes with
  | zero => simp [List.length_eq_zero_iff.mp hn, natToBytes_zero]
  | succ len ih =>
    -- Split off the last byte, the lowest digit.
    obtain ⟨front, b, rfl⟩ := (List.eq_nil_or_concat bytes).resolve_left (by rintro rfl; simp at hn)
    rw [List.concat_eq_append] at hn ⊢
    have hf : front.length = len := by simpa using hn
    have hb : b.toNat < 256 := b.toNat_lt
    have hv : bytesToNat (front ++ [b]) = bytesToNat front * 256 + b.toNat := by
      rw [bytesToNat_append]
      simp [bytesToNat]
    -- The front is the value divided by 256, and the last byte its remainder.
    have hdiv : (bytesToNat front * 256 + b.toNat) / 256 = bytesToNat front := by omega
    have hmod : (bytesToNat front * 256 + b.toNat) % 256 = b.toNat := by omega
    rw [hv, natToBytes_succ, hdiv, hmod, ih front hf]
    simp

/-- Two byte lists of one length that hold the same number are equal. -/
theorem bytesToNat_inj {a b : List UInt8} (length : a.length = b.length)
    (same : bytesToNat a = bytesToNat b) : a = b := by
  rw [← natToBytes_bytesToNat a, ← natToBytes_bytesToNat b, length, same]

/-- The first byte is worth `256` to the power of the number of bytes after it. -/
theorem bytesToNat_cons (b : UInt8) (rest : List UInt8) :
    bytesToNat (b :: rest) = b.toNat * 256 ^ rest.length + bytesToNat rest := by
  simpa [bytesToNat] using foldl_bytesToNat rest b.toNat

/-- Two bytes compare as the numbers they hold. -/
theorem _root_.UInt8.compare_eq_compare_toNat (a b : UInt8) :
    compare a b = compare a.toNat b.toNat := by
  simp only [compare, compareOfLessAndEq, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj]

/-- Two lists of bytes of one length compare, byte after byte, as the numbers they write. -/
theorem compare_eq_compare_bytesToNat {a b : List UInt8} (h : a.length = b.length) :
    compare a b = compare (bytesToNat a) (bytesToNat b) := by
  induction a generalizing b with
  | nil =>
    rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at h
    subst h
    rfl
  | cons x a ih =>
    obtain ⟨y, b, rfl⟩ := List.exists_cons_of_length_eq_add_one h.symm
    have hlen : a.length = b.length := by simpa using h
    have ha := bytesToNat_lt a
    have hb := bytesToNat_lt b
    rw [← hlen] at hb
    rw [List.compare_cons_cons, ih hlen, bytesToNat_cons, bytesToNat_cons, ← hlen,
      UInt8.compare_eq_compare_toNat]
    -- The first bytes decide, since each tail is worth less than one unit of the first byte.
    generalize 256 ^ a.length = unit at ha hb ⊢
    rcases Nat.lt_trichotomy x.toNat y.toNat with hxy | hxy | hxy
    · have : x.toNat * unit + bytesToNat a < y.toNat * unit + bytesToNat b := by
        have := Nat.mul_le_mul_right unit (Nat.succ_le_of_lt hxy)
        rw [Nat.succ_mul] at this
        omega
      rw [Nat.compare_eq_lt.mpr hxy, Nat.compare_eq_lt.mpr this]
      rfl
    · rw [hxy, Nat.compare_eq_eq.mpr rfl]
      simp only [Ordering.then, Nat.compare_eq_ite_lt, Nat.add_lt_add_iff_left]
    · have : y.toNat * unit + bytesToNat b < x.toNat * unit + bytesToNat a := by
        have := Nat.mul_le_mul_right unit (Nat.succ_le_of_lt hxy)
        rw [Nat.succ_mul] at this
        omega
      rw [Nat.compare_eq_gt.mpr hxy, Nat.compare_eq_gt.mpr this]
      rfl

end EthLib.Base
