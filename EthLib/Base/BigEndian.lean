module

/-!
# `Base.BigEndian`

Big-endian integers: a list of bytes read as a number, and a number written back as bytes.

Appendix H of the Yellow Paper reads a word this way.

The first byte is the most significant one:

```text
    [0x01, 0x00]  reads as  1 * 256 + 0 = 256
```
-/

@[expose] public section

namespace EthLib.Base

/-- The integer that the bytes write, the first byte the most significant.

An empty list reads as 0. -/
def bytesToNat (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

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

/-- `n` as exactly `len` big-endian bytes, keeping only `n mod 256 ^ len`.

A number that does not fit loses its higher bytes.

The bytes are exact whenever `n < 256 ^ len`. -/
def natToBytes (len n : Nat) : List UInt8 :=
  go len n []
where
  /-- The bytes are written from the lowest one up, each in front of those already written.

  So each byte costs one step.

  The byte of `n` is `n % 256`, which `UInt8.ofNat` keeps without a division. -/
  go : Nat → Nat → List UInt8 → List UInt8
    | 0, _, written => written
    | len + 1, n, written => go len (n / 256) (UInt8.ofNat n :: written)

/-- Bytes written before the loop starts stay at the end. -/
theorem natToBytes.go_append (len n : Nat) (written : List UInt8) :
    natToBytes.go len n written = natToBytes len n ++ written := by
  induction len generalizing n written with
  | zero => rfl
  | succ len ih =>
    rw [natToBytes, go, go, ih, ih (written := [_]), List.append_assoc]
    rfl

/-- Zero bytes write nothing. -/
theorem natToBytes_zero (n : Nat) : natToBytes 0 n = [] := rfl

/-- On `len + 1` bytes, the higher bytes come first and the lowest byte last. -/
theorem natToBytes_succ (len n : Nat) :
    natToBytes (len + 1) n = natToBytes len (n / 256) ++ [UInt8.ofNat (n % 256)] := by
  rw [natToBytes, natToBytes.go, natToBytes.go_append]
  exact congrArg (natToBytes len (n / 256) ++ [·]) UInt8.ofNat_mod_size.symm

/-- Writing on `len` bytes gives exactly `len` bytes. -/
theorem natToBytes_length (len n : Nat) : (natToBytes len n).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih => simp [natToBytes_succ, ih]

/-- `n` as four big-endian bytes, keeping only `n mod 2^32`, such as a 32-bit block counter. -/
def natToBytes4 (n : Nat) : ByteArray :=
  ⟨(natToBytes 4 n).toArray⟩

/-- The counter is always four bytes. -/
theorem natToBytes4_size (n : Nat) : (natToBytes4 n).size = 4 := by
  simp [natToBytes4, ByteArray.size, natToBytes_length]

end EthLib.Base
