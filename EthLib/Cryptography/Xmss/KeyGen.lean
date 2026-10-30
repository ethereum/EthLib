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

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-! ## Derivations from the seed -/

/-- `S = H("leanXMSS" | S_0)`: the seed every secret derives from.

The scheme's name comes first, so no other scheme derives from the same bytes. -/
def schemeSeed (seed : Seed) : m Seed :=
  H (ByteArray.mk SEED_TAG.toArray ++ packBytes seed)

/-- `P = Th(0^128, A_param, S)`: the public parameter.

The all-zero parameter stands in for the one being derived. -/
def publicParamOf (s : Seed) : m PublicParam :=
  th H (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam (packBytes s)

/-! ## Keys -/

/-- A secret key: the seed `S_0`. -/
structure SecretKey where
  /-- The 32 uniform bytes every secret derives from. -/
  seed : Seed

/-! ## Key generation -/

/-- The public key of the scheme seed `S`: the parameter `P`, then the root of the top tree.

Computing the root builds all `2^16` one-time keys of the top tree. -/
def publicKeyOf (s : Seed) : m PublicKey := do
  let pp ← publicParamOf H s
  let root ← node H pp s .top LAYER_HEIGHT (Nat.le_refl _) 0
  return { root, publicParam := pp }

/-- `Gen` over a hash `H`: the key pair grown from a seed.

1. The scheme seed `S`, from the seed.
2. The public key of `S`.

The seed must be 32 uniform bytes, kept secret. -/
def keyGenWith (seed : Seed) : m (SecretKey × PublicKey) := do
  let s ← schemeSeed H seed
  return (⟨seed⟩, ← publicKeyOf H s)

/-- `Gen`, with Keccak-256. -/
def keyGen (seed : Seed) : SecretKey × PublicKey :=
  (keyGenWith hashId seed).run

end EthLib.Cryptography.Xmss
