module

public import EthLib.Cryptography.Vrf.Hash
public import EthLib.Cryptography.Merkle.Tree

/-!
# VRF key generation

The tree over the `2^32` leaf secrets, and the secrets from one 32-byte seed.

Verification never sees the seed, so the derivation of the secrets is not consensus-critical.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-! ## The tree of the secrets -/

section Oracle

variable {m : Type → Type} [Monad m] (H : ByteArray → m Digest)

/-- Leaf `j` over the secrets `s_j`, with `H` in place of Keccak-256: it commits to secret `j`. -/
def leafWith (secrets : UInt32 → Digest) (j : Nat) : m Digest :=
  H (leafInput (secrets (UInt32.ofNat j)))

/-- The root of the tree over the secrets, with `H` in place of Keccak-256. -/
def rootWith (secrets : UInt32 → Digest) : m Digest :=
  -- Every node is a node hash.
  Merkle.root (nodeWith H) (leafWith H secrets) VRF_TREE_HEIGHT

/-- The opening at index `i`, with `H` in place of Keccak-256: its secret and its path. -/
def openingWith (secrets : UInt32 → Digest) (i : UInt32) : m Opening := do
  let path ← Merkle.path (nodeWith H) (leafWith H secrets) VRF_TREE_HEIGHT i.toNat
  return ⟨secrets i, path⟩

end Oracle

/-- The root of the tree over the secrets. -/
def root (secrets : UInt32 → Digest) : Digest :=
  (rootWith (m := Id) (fun x => pure (hash x)) secrets).run

/-- The opening at index `i`: its secret and its path. -/
def opening (secrets : UInt32 → Digest) (i : UInt32) : Opening :=
  (openingWith (m := Id) (fun x => pure (hash x)) secrets i).run

/-! ## The secrets of a seed -/

/-- The bytes a secret hash reads: the secret prefix, the seed, then the index.

The index is `LE32(i)`, its four bytes least significant first. -/
def secretInput (seed : Seed) (i : UInt32) : ByteArray :=
  packBytes VRF_SECRET_DST ++ packBytes seed ++ packBytes (Base.ByteOrder.toLE 4 i.toNat)

/-- `s_i`: the secret of leaf `i`. -/
def secret (seed : Seed) (i : UInt32) : Digest :=
  -- `s_i = keccak256(PQ_VRF_SECRET | seed | LE32(i))`.
  --
  -- Keccak-256 acts as a pseudorandom function of the index.
  --
  -- The seed is its key, and the prefix separates it from the other hashes.
  hash (secretInput seed i)

/-- The root of the tree of a seed: what the holder publishes.

The seed must be 32 uniformly random bytes, kept secret. -/
def keyGen (seed : Seed) : Digest :=
  -- So a verifier cannot tell whether the secrets came from a seed, or were chosen by the holder.
  --
  -- The derivation is specified so that any implementation rebuilds the same tree from one seed.
  root (secret seed)

/-- The opening at index `i` of the tree of a seed. -/
def prove (seed : Seed) (i : UInt32) : Opening :=
  -- The holder stores the seed, not the `2^32` secrets.
  --
  -- It recomputes a secret, or a subtree, when it opens an index.
  opening (secret seed) i

/-- The output at index `i` of the tree of a seed. -/
def evaluate (seed : Seed) (i : UInt32) : Digest :=
  outputHash i (secret seed i)

end EthLib.Cryptography.Vrf
