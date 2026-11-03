module

public import EthLib.Cryptography.Sphincs.Verify

/-!
# `Sphincs.KeyGen`

Key generation.

The secret key is a 32-byte seed `S_0`, nothing more.

Every secret derives from the scheme's seed `S = H("leanSPHINCS" | S_0)`.

So the seed alone regenerates every chain, every FORS secret and the public key.

The scheme's name separates these derivations from those of every other scheme, leanXMSS included.

Source: `keygenFromSeed` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).

That model derives from `S_0` directly, and this module hashes the scheme's name first, as leanXMSS does.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- `S = H("leanSPHINCS" | S_0)`: the seed every secret derives from.

The scheme's name comes first, so no other scheme derives from the same bytes. -/
def schemeSeed (seed : Seed) : Seed :=
  hash (ByteArray.mk SEED_TAG.toArray ++ packBytes seed)

/-- `P = Th(0^128, A_param, S)`: the public parameter.

The all-zero parameter stands in for the one being derived. -/
def publicParamOf (seed : Seed) : PublicParam :=
  th (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam (packBytes seed)

/-- A secret key: the seed `S_0`. -/
structure SecretKey where
  /-- The 32 uniform bytes the scheme's seed derives from. -/
  seed : Seed

/-- The secret key's scheme seed `S`, which every secret derives from. -/
def SecretKey.master (sk : SecretKey) : Seed :=
  schemeSeed sk.seed

/-- The secret key's public parameter `P`. -/
def SecretKey.publicParam (sk : SecretKey) : PublicParam :=
  publicParamOf sk.master

/-- The public key: the root of the top tree, with the public parameter.

Computing it builds the whole top tree: `2^10` one-time keys. -/
def SecretKey.publicKey (sk : SecretKey) : PublicKey where
  root := treeRoot sk.publicParam sk.master .top 0
  publicParam := sk.publicParam

/-- `Gen`: the key pair grown from a seed.

The seed must be 32 uniform bytes, kept secret. -/
def keyGen (seed : Seed) : SecretKey × PublicKey :=
  let sk : SecretKey := ⟨seed⟩
  (sk, sk.publicKey)

end EthLib.Cryptography.Sphincs
