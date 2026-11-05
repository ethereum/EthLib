module

public import EthLib.Cryptography.Sphincs.Verify

/-!
# leanSPHINCS key generation

Key generation.

The secret key is a 32-byte seed `S_0`, nothing more.

Every secret derives from the scheme's seed `S = H("leanSPHINCS" | S_0)`.

So the seed alone regenerates every chain, every FORS secret and the public key.

The scheme's name separates these derivations from those of every other scheme, leanXMSS included.

Source: `keygenFromSeed` in FORS/Scheme.lean.
<https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean>

That model derives from `S_0` directly.

This module hashes the scheme's name first, as leanXMSS does.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-! ## Derivations from the seed -/

/-- `S = H("leanSPHINCS" | S_0)`: the seed every secret derives from.

The scheme's name comes first, so no other scheme derives from the same bytes. -/
def schemeSeed (seed : Seed) : m Seed :=
  H (ByteArray.mk SEED_TAG.toArray ++ packBytes seed)

/-- `P = H_0(0^128 | A_param | S)`: the public parameter, a derivation from the seed.

The all-zero parameter stands in for the one being derived, and the suffix is empty. -/
def publicParamOf (prf : SeedPrf m) : m PublicParam := do
  return halfOf 0 (← prf (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam .empty)

/-! ## Keys -/

/-- A secret key: the seed `S_0`. -/
structure SecretKey where
  /-- The 32 uniform bytes the scheme's seed derives from. -/
  seed : Seed

/-! ## Key generation -/

/-- The public key of the derivations from a seed: the parameter `P`, then the top tree's root.

Computing the root builds the whole top tree: `2^10` one-time keys. -/
def publicKeyOf (prf : SeedPrf m) : m PublicKey := do
  let pp ← publicParamOf prf
  let root ← treeRoot H pp prf .top 0
  return { root, publicParam := pp }

/-- `Gen` over a hash `H`: the key pair grown from a seed.

1. The scheme seed `S`, from the seed.
2. The public key of the derivations from `S`.

The seed must be 32 uniform bytes, kept secret. -/
def keyGenWith (seed : Seed) : m (SecretKey × PublicKey) := do
  let s ← schemeSeed H seed
  return (⟨seed⟩, ← publicKeyOf H (seedPrf H s))

/-- `Gen`: the key pair grown from a seed.

The seed must be 32 uniform bytes, kept secret. -/
def keyGen (seed : Seed) : SecretKey × PublicKey :=
  (keyGenWith hashId seed).run

end EthLib.Cryptography.Sphincs
