module

public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Cryptography.Sphincs.Address
public import EthLib.Cryptography.HashSig

/-!
# The leanSPHINCS tweakable hash

The hash every other definition is built from.

```text
    Th(PK.seed, ADRS, M)       = Trunc_n(H(PK.seed | ADRS | M))
    PRF(PK.seed, SK.seed, ADRS) = Th(PK.seed, ADRS, SK.seed)
```

- `H` is Keccak-256: the 256-bit hash of FIPS 202, with Keccak's original padding byte `0x01`.
- `Trunc_n` keeps the first `n = 16` bytes of its output.
- `PK.seed` has 16 bytes and `ADRS` 32, so the payload `M` always starts at byte 48.

`Th` is FIPS 205's `F`, `H` and `T_l` alike, as the SHAKE instances of FIPS 205 §11.1 lay them out.

Every definition that hashes takes the hash `H` as an argument, in a monad `m`.

- The hash that EthLib computes is Keccak-256, in the identity monad.
- A proof in the random oracle model passes a query to the oracle instead.

So the definitions that run are the definitions that the security proof is about.

Source: [main.tex][main] §2.

[main]: https://github.com/leanEthereum/leanVM/blob/5e3ade21d339a45e1b3b0dba97ad9300ab50e49b/doc/lean_sphincs/main.tex
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## The hash -/

export EthLib.Cryptography.HashSig (pureHash)

/-- `H`: the scheme's 32-byte hash, Keccak-256. -/
def hash (input : ByteArray) : HashOutput :=
  Hash.Keccak.keccak256 input

/-- `H` as EthLib computes it: Keccak-256, in the identity monad.

An abbreviation, so a theorem about `pureHash f` applies to it with `f = hash`. -/
abbrev hashId : ByteArray → Id (Vector UInt8 32) :=
  pureHash hash

/-- `Trunc_r`: the first `r` bytes of a byte string. -/
def trunc {k : Nat} (r : Nat) (x : Vector UInt8 k) (h : r ≤ k := by decide) : Vector UInt8 r :=
  Vector.ofFn fun i => x[i.val]'(by have := i.isLt; omega)

/-! ## Tweakable hash calls -/

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- The bytes one tweakable hash call hashes: `PK.seed | ADRS | M`. -/
def thInput (pkSeed : PkSeed) (adrs : Adrs) (payload : ByteArray) : ByteArray :=
  -- Fixed-length prefixes, so the input splits back into its three parts one way.
  packBytes pkSeed ++ packBytes adrs ++ payload

/-- `Th(PK.seed, ADRS, M)`: hash a payload under one address of one key, cut to `n` bytes.

It is FIPS 205's `F`, `H` and `T_l`. -/
def th (pkSeed : PkSeed) (adrs : Adrs) (payload : ByteArray) : m Digest := do
  return trunc N (← H (thInput pkSeed adrs payload))

/-! ## Secret values -/

/-- A source of secret values: `PRF(PK.seed, SK.seed, ADRS)` as a function of the address.

The signer derives every chain start and every FORS secret through one such source.

So a proof can replace the derivations from `SK.seed` as a whole. -/
abbrev Prf (m : Type → Type) := Adrs → m Digest

/-- `PRF(PK.seed, SK.seed, ADRS) = Th(PK.seed, ADRS, SK.seed)`, FIPS 205's `PRF`.

`SK.seed` has 32 bytes, so the input has 80 bytes. -/
def prf (pkSeed : PkSeed) (skSeed : Seed) : Prf m := fun adrs =>
  th H pkSeed adrs (packBytes skSeed)

end EthLib.Cryptography.Sphincs
