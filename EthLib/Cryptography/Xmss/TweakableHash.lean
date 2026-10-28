import EthLib.Cryptography.Hash.Keccak
import EthLib.Cryptography.Xmss.Address

/-!
# `Xmss.TweakableHash`

The hash every other definition is built from.

```text
    Th(P, A, M) = H_0(P | A | M)
```

- `H` is Keccak-256, Ethereum's hash: FIPS 202's 256-bit hash with Keccak's original padding.
- `H_0` and `H_1` are the first and last 16 bytes of its output.
- `P` and `A` are 16 bytes each, so the payload `M` always starts at byte 32.

Source: the leanXMSS specification draft, section "Hashing and parameters".
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- `H`: the scheme's 32-byte hash. -/
def hash (input : ByteArray) : Vector UInt8 32 :=
  Hash.Keccak.keccak256 input

/-- The first or the last 16 bytes of a 32-byte hash value. -/
def halfOf (half : Fin 2) (full : Vector UInt8 32) : Digest :=
  -- Half 0 is bytes 0 to 15, half 1 is bytes 16 to 31.
  Vector.ofFn fun i => full[16 * half.val + i.val]'(by
    have := half.isLt
    have := i.isLt
    simp only [DIGEST_LEN] at *
    omega)

/-- `H_0` or `H_1`: the first or the last 16 bytes of the hash. -/
def hashHalf (half : Fin 2) (input : ByteArray) : Digest :=
  halfOf half (hash input)

/-- The bytes one tweakable hash call hashes: `P | A | M`. -/
def thInput (pp : PublicParam) (address : Address) (payload : ByteArray) : ByteArray :=
  -- Fixed-length prefixes, so the input splits back into its three parts one way.
  packBytes pp ++ packBytes address ++ payload

/-- `Th(P, A, M)`: hash a payload under one address of one key. -/
def th (pp : PublicParam) (address : Address) (payload : ByteArray) : Digest :=
  hashHalf 0 (thInput pp address payload)

end EthLib.Cryptography.Xmss
