import EthLib.Cryptography.Vrf.Verify
import EthLib.Cryptography.Vrf.KeyGen
import EthLib.Cryptography.Proofs.Hash.KeccakKernel

/-!
# Proofs: the VRF tree over the kernel's fast hash

The known answers evaluate 34 Keccak permutations in the kernel.

So they run on a fast form of verification, proved equal to the specification.

- The hash is the record form of Keccak-f, over an input written as one list.
- The verifier is the specification's, step for step, over that hash.
-/

namespace EthLib.Cryptography.Vrf.Kernel

open EthLib.Cryptography.Vrf
open EthLib.Cryptography.Vrf.Constants

/-! ## The hashes -/

/-- Keccak-256 over the record form of Keccak-f, of an input written as one list. -/
def hash (input : List UInt8) : Digest :=
  Hash.Keccak.Kernel.keccak256 ⟨⟨input⟩⟩

/-- The leaf hash, over the fast hash. -/
def leafHash (secret : Digest) : Digest :=
  hash (VRF_LEAF_DST.toList ++ secret.toList)

/-- The node hash, over the fast hash. -/
def nodeHash (left right : Digest) : Digest :=
  hash (VRF_NODE_DST.toList ++ left.toList ++ right.toList)

/-- The output hash, over the fast hash. -/
def outputHash (secret : Digest) : Digest :=
  hash (VRF_OUTPUT_DST.toList ++ secret.toList)

/-- The leaf hash is the leaf hash over the fast hash. -/
theorem leafHash_eq (secret : Digest) : Vrf.leafHash secret = leafHash secret := by
  rw [Vrf.leafHash, Vrf.hash, Hash.Keccak.Kernel.keccak256_eq, leafHash, hash, leafInput]
  -- The two inputs are the same bytes, by definition.
  congr 1

/-- The node hash is the node hash over the fast hash. -/
theorem nodeHash_eq (left right : Digest) : Vrf.nodeHash left right = nodeHash left right := by
  rw [Vrf.nodeHash, Vrf.hash, Hash.Keccak.Kernel.keccak256_eq, nodeHash, hash, nodeInput]
  -- The two inputs are the same bytes, by definition.
  congr 1

/-- The output hash is the output hash over the fast hash. -/
theorem outputHash_eq (secret : Digest) : Vrf.outputHash secret = outputHash secret := by
  rw [Vrf.outputHash, Vrf.hash, Hash.Keccak.Kernel.keccak256_eq, outputHash, hash, outputInput]
  -- The two inputs are the same bytes, by definition.
  congr 1

/-- A leaf secret, over the fast hash. -/
def secret (seed : Seed) (i : UInt32) : Digest :=
  hash (VRF_SECRET_DST.toList ++ seed.toList ++ (indexBytes i).toList)

/-- A leaf secret is the leaf secret over the fast hash. -/
theorem secret_eq (seed : Seed) (i : UInt32) : Vrf.secret seed i = secret seed i := by
  rw [Vrf.secret, Vrf.hash, Hash.Keccak.Kernel.keccak256_eq, secret, hash, secretInput]
  -- The two inputs are the same bytes, by definition.
  congr 1

/-! ## Verifying -/

/-- Verification over the fast hash, step for step the specification's. -/
def verify (root : Digest) (i : UInt32) (o : Opening) : Option Digest :=
  if Tree.climb nodeHash i.toNat (leafHash o.secret) o.path.toList = root then
    some (outputHash o.secret)
  else none

/-- Verification is verification over the fast hash. -/
theorem verify_eq (root : Digest) (i : UInt32) (o : Opening) :
    Vrf.verify root i o = verify root i o := by
  -- The node hash is the fast one, as a function.
  have hnode : Vrf.nodeHash = nodeHash := funext fun l => funext fun r => nodeHash_eq l r
  simp only [Vrf.verify, verify, hnode, leafHash_eq, outputHash_eq]

end EthLib.Cryptography.Vrf.Kernel
