module

/-!
# `Base.ByteOrder`

An integer written in base 256, one digit per byte.

A little-endian encoding puts the least significant byte first.

A big-endian encoding puts the most significant byte first.

The little-endian reader takes a vector, since its callers hold fixed-width keys, hashes and words.

The big-endian reader takes a list, since its callers hold buffers and slices of any length.
-/

@[expose] public section

namespace EthLib.Base.ByteOrder

/-- The `n` low bytes of `x`, least significant first.

A number below `256 ^ n` is written exactly, and a larger one keeps only `x % 256 ^ n`.

For example, the two low bytes of `0x1234` are `[0x34, 0x12]`. -/
def toLE (n x : Nat) : Vector UInt8 n :=
  -- Byte `i` holds bits `8i` to `8i + 7`.
  Vector.ofFn fun i => UInt8.ofNat (x >>> (8 * i.val))

/-- The `n` low bytes of `x`, most significant first, written in front of the bytes `written`.

The bytes are written from the lowest one up, each in front of those already written.

So each byte costs one step, and each step writes `x % 256`, the part of `x` that one byte holds. -/
def toBE.go : Nat → Nat → List UInt8 → List UInt8
  | 0, _, written => written
  | n + 1, x, written => go n (x / 256) (UInt8.ofNat x :: written)

/-- Writing `n` more bytes in front of `written` adds `n` bytes. -/
theorem toBE.length_go (n x : Nat) (written : List UInt8) :
    (toBE.go n x written).length = n + written.length := by
  induction n generalizing x written with
  | zero => simp [toBE.go]
  | succ n ih =>
    rw [toBE.go, ih, List.length_cons]
    omega

/-- The `n` low bytes of `x`, most significant first: the little-endian bytes in reverse order.

A number below `256 ^ n` is written exactly, and a larger one keeps only `x % 256 ^ n`.

For example, the two low bytes of `0x1234` are `[0x12, 0x34]`.

It is written by its own loop rather than as a reversal of the little-endian bytes.

Proofs then compute its bytes as a list one step at a time, as they do for the encodings. -/
def toBE (n x : Nat) : Vector UInt8 n :=
  ⟨(toBE.go n x []).toArray, by simp [toBE.length_go]⟩

/-- The number of bytes of `x` in base 256 with no leading zero byte; zero has none.

The highest set bit of `x` is bit `x.log2`, and it lies in byte `x.log2 / 8`.

The bytes are counted from 0, from the least significant one.

So the bytes of `x` with no leading zero are the `x.log2 / 8 + 1` low ones.

For example, `0xff` takes one byte, and `0x100` takes two. -/
def byteLength (x : Nat) : Nat := if x = 0 then 0 else x.log2 / 8 + 1

/-- The number whose `n` bytes these are, the least significant first.

It is below `256 ^ n`.

For example, `[0x34, 0x12]` reads as `0x1234`. -/
def ofLE {n : Nat} (bytes : Vector UInt8 n) : Nat :=
  -- Horner's rule from the most significant byte, the last one, down.
  bytes.toArray.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The number whose bytes these are, the most significant first.

Any number of bytes is allowed, and no bytes read as 0.

Appendix H of the Yellow Paper reads a word this way.

For example, `[0x12, 0x34]` reads as `0x1234`. -/
def ofBE (bytes : List UInt8) : Nat :=
  -- Horner's rule from the most significant byte, the first one, down.
  bytes.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- Reading big-endian bytes from any start value shifts it by one factor of 256 per byte. -/
theorem foldl_ofBE (bytes : List UInt8) (acc : Nat) :
    bytes.foldl (fun acc b => 256 * acc + b.toNat) acc = 256 ^ bytes.length * acc + ofBE bytes := by
  induction bytes generalizing acc with
  | nil => simp [ofBE]
  | cons b rest ih =>
    -- Unfold one byte on both sides, then use the induction hypothesis twice.
    simp only [ofBE, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih, ih (256 * 0 + b.toNat), Nat.pow_succ, Nat.mul_zero, Nat.zero_add]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- A list of bytes reads big-endian as a number below 256 to the power of its length. -/
theorem ofBE_lt (bytes : List UInt8) : ofBE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [ofBE]
  | cons b rest ih =>
    -- The first byte is the most significant one, worth `256 ^ rest.length` per unit.
    have hcons : ofBE (b :: rest) = 256 ^ rest.length * b.toNat + ofBE rest := by
      simpa [ofBE] using foldl_ofBE rest b.toNat
    have hb : b.toNat + 1 ≤ 256 := b.toNat_lt
    rw [hcons, List.length_cons, Nat.pow_succ]
    -- `256^r * b + v < 256^r * (b + 1) ≤ 256^r * 256`.
    calc 256 ^ rest.length * b.toNat + ofBE rest
        < 256 ^ rest.length * (b.toNat + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ 256 ^ rest.length * 256 := Nat.mul_le_mul_left _ hb

end EthLib.Base.ByteOrder
