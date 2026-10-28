import EthLib.Cryptography.Xmss.Verify

/-!
# `Xmss.KeyGen`

Key generation.

The secret key is a 32-byte seed `S_0`, nothing more.

Every secret derives from the scheme's seed `S = H("leanXMSS" | S_0)`.

So the seed alone regenerates every chain, every node and the public key.

Source: the leanXMSS specification draft, sections "Hashing and parameters" and "The scheme".
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## Derivations from the seed -/

/-- `S = H("leanXMSS" | S_0)`: the seed every secret derives from.

The scheme's name comes first, so no other scheme derives from the same bytes. -/
def schemeSeed (seed : Seed) : Seed :=
  hash (ByteArray.mk SEED_TAG.toArray ++ packBytes seed)

/-- `P = Th(0^128, A_param, S)`: the public parameter.

The all-zero parameter stands in for the one being derived. -/
def publicParamOf (s : Seed) : PublicParam :=
  th (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam (packBytes s)

/-! ## Keys -/

/-- A secret key: the seed `S_0`. -/
structure SecretKey where
  /-- The 32 uniform bytes every secret derives from. -/
  seed : Seed

/-- The secret key's scheme seed `S`. -/
def SecretKey.schemeSeed (sk : SecretKey) : Seed :=
  Xmss.schemeSeed sk.seed

/-- The secret key's public parameter `P`. -/
def SecretKey.publicParam (sk : SecretKey) : PublicParam :=
  publicParamOf sk.schemeSeed

/-- The public key: the root of the top tree, with the public parameter.

Computing it builds the whole top tree: `2^16` one-time keys. -/
def SecretKey.publicKey (sk : SecretKey) : PublicKey where
  root := node sk.publicParam sk.schemeSeed .top LAYER_HEIGHT (Nat.le_refl _) 0
  publicParam := sk.publicParam

/-! ## Key generation -/

/-- The key pair grown from a seed.

The seed must be 32 uniform bytes, kept secret. -/
def keyGen (seed : Seed) : SecretKey × PublicKey :=
  let sk : SecretKey := ⟨seed⟩
  (sk, sk.publicKey)

end EthLib.Cryptography.Xmss
