import EthLib.Cryptography.Hash.Keccak
import EthLib.Cryptography.Sphincs.Address

/-!
# `Sphincs.TweakableHash`

The hash every other definition is built from.

```text
    Th(P, A, M) = H_0(P | A | M)
```

- `H` is Keccak-256, Ethereum's hash: FIPS 202's 256-bit hash with Keccak's original padding.
- `H_0` and `H_1` are the first and last 16 bytes of its output.
- `P` and `A` are 16 bytes each, so the payload `M` always starts at byte 32.

One seed derivation keeps both halves: they are two secrets for the price of one hash.

An output read as a number is read little-endian, so its first 16 bytes are its low 128 bits.

Source: `tweakableHashInput`, `truncateHash` and `hashHalf` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- `H`: the scheme's 32-byte hash. -/
def hash (input : ByteArray) : HashOutput :=
  Hash.Keccak.keccak256 input

/-- `H_0` or `H_1` of a hash value: its first or its last 16 bytes. -/
def halfOf (half : Fin 2) (full : HashOutput) : Digest :=
  -- Half 0 is bytes 0 to 15, half 1 is bytes 16 to 31.
  Vector.ofFn fun i => full[16 * half.val + i.val]'(by
    have := half.isLt
    have := i.isLt
    simp only [N, HASH_LEN] at *
    omega)

/-- The bytes one tweakable hash call hashes: `P | A | M`. -/
def thInput (pp : PublicParam) (address : Address) (payload : ByteArray) : ByteArray :=
  -- Fixed-length prefixes, so the input splits back into its three parts one way.
  packBytes pp ++ packBytes address ++ payload

/-- `H(P | A | M)`: the whole 32-byte output of one call.

Seed derivations and the message digest keep all of it. -/
def thFull (pp : PublicParam) (address : Address) (payload : ByteArray) : HashOutput :=
  hash (thInput pp address payload)

/-- `Th(P, A, M)`: hash a payload under one address of one key, cut to 16 bytes. -/
def th (pp : PublicParam) (address : Address) (payload : ByteArray) : Digest :=
  halfOf 0 (thFull pp address payload)

end EthLib.Cryptography.Sphincs
