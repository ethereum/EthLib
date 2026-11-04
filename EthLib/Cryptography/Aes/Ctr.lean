module

public import EthLib.Cryptography.Aes.Block

/-!
# `Aes.Ctr`

The counter mode of [NIST SP 800-38A](https://doi.org/10.6028/NIST.SP.800-38A) §6.5.

Each data block is XORed with the forward cipher of its own counter block.

Decryption in §6.5 uses the same formulas as encryption, so one function does both.

The mode is secure only if no counter block repeats under one key, across all messages (§6.5).

Choosing the initial counter blocks is left to the caller.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes

/-! ## Counter blocks -/

/-- The integer that a block spells, first byte most significant.

SP 800-38A §4.1 reads a bit string as an integer with the first bit most significant. -/
def blockToNat (T : Block) : Nat :=
  T.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The block that spells `x mod 2^128`, first byte most significant. -/
def blockOfNat (x : Nat) : Block :=
  Vector.ofFn fun i => (x / 256 ^ (15 - i.val)).toUInt8

/-- The standard incrementing function of SP 800-38A Appendix B.1.

It adds one, modulo `2^m`, to the `m` least significant bits, and keeps the other bits.

Appendix B.1 asks for `m ≤ 128`, and a larger `m` acts as `m = 128`. -/
def inc (m : Nat) (T : Block) : Block :=
  let x := blockToNat T
  blockOfNat (x / 2 ^ m * 2 ^ m + (x % 2 ^ m + 1) % 2 ^ m)

/-! ## The mode -/

/-- XOR `n` blocks of data with the outputs `O_j = CIPH_K(T_j)` of the counters from `T`.

The last block can be partial, of `u` bytes.

Then the XOR uses `MSB_u(O_n)`, because XOR of two lists stops at the shorter one. -/
def xorKeystream (ciph : Block → Block) (m n : Nat) (T : Block) (data : List UInt8) :
    List UInt8 :=
  (go n T data #[]).toList
where
  /-- Append the XOR of `n` more blocks to the output so far.

  The loop keeps the output in an array, so it runs in constant stack for any length. -/
  go : Nat → Block → List UInt8 → Array UInt8 → Array UInt8
    | 0, _, _, out => out
    | n + 1, T, data, out =>
      go n (inc m T) (data.drop 16) (out ++ List.zipWith (· ^^^ ·) (data.take 16) (ciph T).toList)

/-- CTR encryption and decryption of SP 800-38A §6.5.

The cipher argument is the forward cipher `CIPH_K`, so it carries a secret key.

The first counter is given, and each next one is the standard increment of the one before.

The data has `n = ceil(len / 16)` blocks, and the output has the length of the data. -/
def ctr (ciph : Block → Block) (m : Nat) (initialCounter : Block) (data : ByteArray) : ByteArray :=
  ⟨(xorKeystream ciph m ((data.size + 15) / 16) initialCounter data.data.toList).toArray⟩

end EthLib.Cryptography.Aes
