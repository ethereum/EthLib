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

Every definition that hashes takes the hash `H` as an argument, in a monad `m`.

- `hashId` is the hash EthLib computes: Keccak-256, in the identity monad.
- A proof in the random oracle model passes a query to the oracle instead.

So the definitions that run are the definitions that the security proof is about.

Source: the leanXMSS specification draft, sections "Hashing and parameters" and "Security".
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- Keccak-256, the scheme's 32-byte hash. -/
def hash (input : ByteArray) : Vector UInt8 32 :=
  Hash.Keccak.keccak256 input

/-- A hash function, as a computation in the identity monad. -/
def pureHash (f : ByteArray → Vector UInt8 32) (input : ByteArray) : Id (Vector UInt8 32) :=
  pure (f input)

/-- `H` as EthLib computes it: Keccak-256, in the identity monad.

An abbreviation, so a theorem about `pureHash f` applies to it with `f = hash`. -/
abbrev hashId : ByteArray → Id (Vector UInt8 32) :=
  pureHash hash

/-- The first or the last 16 bytes of a 32-byte hash value. -/
def halfOf (half : Fin 2) (full : Vector UInt8 32) : Digest :=
  -- Half 0 is bytes 0 to 15, half 1 is bytes 16 to 31.
  Vector.ofFn fun i => full[16 * half.val + i.val]'(by
    have := half.isLt
    have := i.isLt
    simp only [DIGEST_LEN] at *
    omega)

/-- The bytes one tweakable hash call hashes: `P | A | M`. -/
def thInput (pp : PublicParam) (address : Address) (payload : ByteArray) : ByteArray :=
  -- Fixed-length prefixes, so the input splits back into its three parts one way.
  packBytes pp ++ packBytes address ++ payload

/-- `Th(P, A, M)`: hash a payload under one address of one key, with one call of `H`. -/
def th {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam)
    (address : Address) (payload : ByteArray) : m Digest := do
  return halfOf 0 (← H (thInput pp address payload))

end EthLib.Cryptography.Xmss
