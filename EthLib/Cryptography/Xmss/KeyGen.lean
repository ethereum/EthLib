module

public import EthLib.Cryptography.Xmss.Errors
public import EthLib.Cryptography.Xmss.Verify

/-!
# leanXMSS key generation

Key generation.

Every secret derives from the scheme's seed `S = H("leanXMSS" | S_0)`, for a 32-byte seed `S_0`.

In the note, the secret key is `S_0` alone, and signing rebuilds every tree it reads.

Here the secret key also keeps the trees it has built.

Key generation builds the top tree to compute the root, so the key keeps it at no extra cost.

The key also keeps the bottom trees it signed in last, each with the top signature of its root.

Signing is deterministic, so a kept tree gives the bytes a rebuilt one would give.

Source: the leanXMSS specification draft, sections "Hashing and parameters" and "The scheme".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)

/-! ## Derivations from the seed -/

/-- `S = H("leanXMSS" | S_0)`: the seed every secret derives from.

The scheme's name comes first, so no other scheme derives from the same bytes.

The name is 8 bytes, one lane, so the input is the name's lane and the seed's four. -/
def schemeSeed (seed : Seed) : m Seed :=
  H (#[SEED_TAG_LANE] ++ seed.toArray)

/-- `P`: the public parameter, the first half of the derivation at `0^128` and `A_param`.

The all-zero parameter stands in for the one being derived, and the suffix is empty.

With the derivations from the scheme seed `S`, it is `Th(0^128, A_param, S)`. -/
def publicParamOf (prf : SeedPrf m) : m PublicParam := do
  return halfOf 0 (← prf ⟨0, 0⟩ addrParam #[])

/-! ## Keys -/

/-- How many bottom trees a secret key keeps: the ones it signed in last.

A kept tree holds `2^17 - 1` digests, and its `2^16` leaf indices sign without rebuilding it. -/
def MAX_CACHED_BOTTOM_TREES : Nat := 8

/-- A bottom tree, built, with the top layer's signature of its root. -/
structure CachedTree where
  /-- The index `b` of the bottom tree. -/
  index : Nat
  /-- Every node of bottom tree `b`. -/
  tree : Merkle.Built Digest
  /-- The signature of the tree's root by the top key `b`, or the error of that layer. -/
  top : Except XmssError LayerSignature

/-- A secret key: the scheme seed `S`, the parameter `P`, and the trees built from them.

`S` is secret for the key's whole life, and so is every one-time secret derived from it.

The tree nodes are not secret: a signature reveals some of them.

A key from key generation and signing holds exactly what the note's signer rebuilds from `S`.

With other trees, a top key could sign two different roots. -/
structure SecretKey where
  /-- The scheme seed `S`, which every secret derives from. -/
  schemeSeed : Seed
  /-- The public parameter `P`. -/
  publicParam : PublicParam
  /-- Every node of the top tree. -/
  top : Merkle.Built Digest
  /-- The bottom trees the key keeps, the one it signed in last first. -/
  cache : List CachedTree

/-! ## Key generation -/

namespace Internal

/-- The key pair grown from a scheme seed `S`, with its secrets from the given derivations.

Key generation passes the derivations of `S`.

1. The public parameter `P`, derived from `S`.
2. The top tree, from the `2^16` one-time keys of the top layer.

The secret key keeps `S`, `P` and the top tree. -/
def keyGenFrom (prf : SeedPrf m) (s : Seed) : m (PublicKey × SecretKey) := do
  let pp ← publicParamOf prf
  let top ← build H pp prf .top LAYER_HEIGHT 0
  return ({ root := top.value, publicParam := pp },
    { schemeSeed := s, publicParam := pp, top, cache := [] })

end Internal

/-- `Gen` over a hash `H`: the key pair grown from a seed.

1. The scheme seed `S`, from the seed.
2. The public parameter `P`, derived from `S`.
3. The top tree, from the `2^16` one-time keys of the top layer.

The public key is the top tree's root and `P`.

The seed must be 32 uniform bytes, kept secret. -/
def keyGenWith (seed : Seed) : m (PublicKey × SecretKey) := do
  let s ← schemeSeed H seed
  Internal.keyGenFrom H (seedPrf H s) s

/-- `Gen`, with Keccak-256. -/
def keyGen (seed : Seed) : PublicKey × SecretKey :=
  (keyGenWith hashId seed).run

end EthLib.Cryptography.Xmss
