module

public import EthLib.Base.BigEndian

/-!
# Proofs: `BigEndian`

Reading and writing big-endian bytes undo each other.

- A list of `k` bytes holds a value below `256 ^ k`.
- Writing `n` on `len` bytes gives bytes that read back as `n % 256 ^ len`.
- On `a + b` bytes, `n` is `n / 256 ^ b` on the first `a` bytes, then `n` on the last `b`.
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
  | zero => simp [natToBytes, bytesToNat, Nat.mod_one]
  | succ len ih =>
    -- Split off the lowest byte, which is written last.
    rw [natToBytes, bytesToNat_append, ih, List.length_singleton]
    have hlow : bytesToNat [UInt8.ofNat (n % 256)] = n % 256 := by
      simp [bytesToNat]
    rw [hlow, Nat.pow_one]
    -- `n % 256^(len+1) = n % 256 + 256 * (n / 256 % 256^len)`.
    rw [Nat.pow_succ', Nat.mod_mul, Nat.mul_comm, Nat.add_comm]

/-- Writing on `a + b` bytes puts `n / 256 ^ b` on the first `a` bytes and `n` on the last `b`. -/
theorem natToBytes_add (a b n : Nat) :
    natToBytes (a + b) n = natToBytes a (n / 256 ^ b) ++ natToBytes b n := by
  induction b generalizing n with
  | zero => simp [natToBytes]
  | succ b ih =>
    -- Both sides end with the lowest byte, and the higher bytes are `n / 256` written on `a + b`.
    rw [← Nat.add_assoc, natToBytes, ih, natToBytes, List.append_assoc, Nat.div_div_eq_div_mul,
      Nat.pow_succ, Nat.mul_comm 256]

/-- A number below `256 ^ len` survives the round trip through `len` bytes. -/
theorem bytesToNat_natToBytes_of_lt {len n : Nat} (h : n < 256 ^ len) :
    bytesToNat (natToBytes len n) = n := by
  rw [bytesToNat_natToBytes, Nat.mod_eq_of_lt h]

/-- A list of bytes survives the round trip through its value, written back on as many bytes. -/
theorem natToBytes_bytesToNat (bytes : List UInt8) :
    natToBytes bytes.length (bytesToNat bytes) = bytes := by
  generalize hn : bytes.length = len
  induction len generalizing bytes with
  | zero => simp [List.length_eq_zero_iff.mp hn, natToBytes]
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
    rw [hv, natToBytes, hdiv, hmod, ih front hf]
    simp

end EthLib.Base
