module

public import EthLib.Cryptography.Sphincs.Verify

/-!
# leanSPHINCS key generation

Key generation.

The secret key is `SK.seed`, 32 bytes, and nothing more.

Two hashes of it under the scheme's 11-byte ASCII name give `PK.seed` and `SK.prf`:

```text
    PK.seed = Trunc_n(H("leanSPHINCS" | SK.seed | BE_8(0)))
    SK.prf  = H("leanSPHINCS" | SK.seed | BE_8(1))
```

`SK.prf` keeps all 32 bytes, so predicting a randomizer is as hard as guessing `SK.seed`.

So `SK.seed` alone regenerates every chain, every FORS secret and the public key.

FIPS 205 draws `SK.prf` and `PK.seed` independently of `SK.seed`.

Source: [main.tex][main] §2 and §6.1, and FIPS 205's `slh_keygen_internal` (Algorithm 18).

[main]: https://github.com/leanEthereum/leanVM/blob/5e3ade21d339a45e1b3b0dba97ad9300ab50e49b/doc/lean_sphincs/main.tex
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Keys -/

/-- A secret key: `SK.seed`. -/
structure SecretKey where
  /-- `SK.seed`, the 32 uniform bytes every secret derives from. -/
  seed : Seed

/-- What `SK.seed` expands to: `PK.seed` and `SK.prf`. -/
structure ExpandedKey where
  /-- `PK.seed`, the first 16 bytes of the hash under domain 0. -/
  pkSeed : PkSeed
  /-- `SK.prf`, the whole hash under domain 1, the key of `PRF_msg`. -/
  skPrf : HashOutput

/-! ## Key expansion -/

/-- The 44 bytes the key expansion hashes: `"leanSPHINCS" | SK.seed | BE_8(domain)`.

The input has no `PK.seed` and no address, and no addressed call has 44 bytes. -/
def expandInput (seed : Seed) (domain : UInt8) : ByteArray :=
  ByteArray.mk SEED_TAG.toArray ++ packBytes seed ++ ByteArray.mk #[domain]

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- The key expansion of `SK.seed`: `PK.seed` from domain 0, then `SK.prf` from domain 1. -/
def expandKey (seed : Seed) : m ExpandedKey := do
  let pkSeed := trunc N (← H (expandInput seed 0))
  let skPrf ← H (expandInput seed 1)
  return { pkSeed, skPrf }

/-! ## Key generation -/

/-- The public key of `PK.seed` and a source of secrets: `PK.seed`, then the top tree's root.

Computing the root builds the whole top tree: `2^10` one-time keys. -/
def publicKeyOf (pkSeed : PkSeed) (prf : Prf m) : m PublicKey := do
  let root ← treeRoot H pkSeed prf .top 0
  return { pkSeed, root }

/-- `Gen` over a hash `H`: the key pair of `SK.seed`, FIPS 205's `slh_keygen_internal`.

1. `PK.seed` and `SK.prf`, from `SK.seed`.
2. `PK.root`, the root of the top tree, whose secrets are `PRF(PK.seed, SK.seed, ADRS)`.

The seed must be 32 uniform bytes, kept secret.

`SK.prf` is not part of the public key, but `Gen` derives it, as main.tex §6.1 does. -/
def keyGenWith (seed : Seed) : m (SecretKey × PublicKey) := do
  let key ← expandKey H seed
  return (⟨seed⟩, ← publicKeyOf H key.pkSeed (prf H key.pkSeed seed))

/-- `Gen`: the key pair of `SK.seed`.

The seed must be 32 uniform bytes, kept secret. -/
def keyGen (seed : Seed) : SecretKey × PublicKey :=
  (keyGenWith hashId seed).run

end EthLib.Cryptography.Sphincs
