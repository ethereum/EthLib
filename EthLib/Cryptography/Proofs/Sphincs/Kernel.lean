module

public import EthLib.Cryptography.Sphincs
public import EthLib.Cryptography.Proofs.Hash.KeccakKernel

/-!
# Proofs: leanSPHINCS over the kernel's fast hash

The known answer evaluates hundreds of Keccak permutations in the kernel.

The kernel reads an array by walking a list, and appends to one an element at a time.

So the known answer runs on a fast form instead, proved equal to the specification:

- The hash is the record form of Keccak-f, over its input written as one list.
- `Th(P, A, M)` is that hash of the list `P ++ A ++ M`.
- A chain walk is the same walk over that `Th`.
- A path fold and a FORS climb are the climbs of the shared Merkle tree, with that `Th` as the node hash.

A known answer rewrites its statement with these equalities, then lets the kernel evaluate it.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Kernel

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

/-! ## Bytes as lists -/

/-- An object's bytes, as a list. -/
@[simp] theorem toList_packBytes {n : Nat} (v : Vector UInt8 n) :
    (packBytes v).data.toList = v.toList := rfl

/-- A list of digests' bytes, as a list. -/
@[simp] theorem toList_packDigests {n : Nat} (ds : Vector Digest n) :
    (packDigests ds).data.toList = (ds.toList.map Vector.toList).flatten := by
  simp [packDigests, Xmss.packBytes, Vector.flatten, Array.toList_flatten, Vector.toList]
  rfl

/-- Concatenated bytes, as a list. -/
@[simp] theorem toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

/-! ## The hash -/

/-- The fast form of the scheme's hash: Keccak-256 over the record form of Keccak-f. -/
def hash (input : List UInt8) : HashOutput :=
  Hash.Keccak.Kernel.keccak256 ⟨⟨input⟩⟩

/-- `H(P | A | M)` over the fast hash, its input written as one list. -/
def thFull (pp : PublicParam) (address : Address) (payload : List UInt8) : HashOutput :=
  hash (pp.toList ++ address.toList ++ payload)

/-- `Th` over the fast hash. -/
def th (pp : PublicParam) (address : Address) (payload : List UInt8) : Digest :=
  halfOf 0 (thFull pp address payload)

/-- The whole output of one call is the fast hash of the payload's bytes. -/
theorem thFull_eq (pp : PublicParam) (address : Address) (payload : ByteArray) :
    Sphincs.thFull pp address payload = thFull pp address payload.data.toList := by
  simp only [Sphincs.thFull, Sphincs.hash, Hash.Keccak.Kernel.keccak256_eq, thFull, hash]
  -- The two inputs are the same bytes, by definition.
  rfl

/-- `Th` is `Th` over the fast hash, of the payload's bytes. -/
theorem th_eq (pp : PublicParam) (address : Address) (payload : ByteArray) :
    Sphincs.th pp address payload = th pp address payload.data.toList := by
  simp only [Sphincs.th, thFull_eq, th]

/-! ## Chains -/

/-- A chain walk over the fast hash, step for step the specification's. -/
def chain (pp : PublicParam) (key : OtsKey) (i : Fin V) (start steps : Nat)
    (h : start + steps < CHAIN_LENGTH) (value : Digest) : Digest :=
  match steps, h with
  | 0, _ => value
  | s + 1, h => th pp (addrChain key i ⟨start + s, by simp only [CHAIN_LENGTH] at *; omega⟩)
      (chain pp key i start s (by omega) value).toList

/-- A chain walk is the walk over the fast hash. -/
theorem chain_eq (pp : PublicParam) (key : OtsKey) (i : Fin V) (start : Nat) :
    ∀ steps h value,
      Sphincs.chain pp key i start steps h value = chain pp key i start steps h value := by
  intro steps
  induction steps with
  | zero => intro h value; rfl
  | succ s ih =>
    intro h value
    -- One step on each side, the walks below it equal by induction.
    simp only [Sphincs.chain, chainStep, chain, th_eq, ih, toList_packBytes]

/-! ## Paths -/

/-- A parent node over the fast hash, its children written as lists. -/
def nodeHash (pp : PublicParam) (layer : Layer) (tree level j : Nat) (left right : Digest) : Id Digest :=
  th pp (addrNode layer tree (Fin.ofNat _ level) j) (left.toList ++ right.toList)

/-- A parent node is the parent over the fast hash. -/
theorem nodeHash_eq (pp : PublicParam) (layer : Layer) (tree : Nat) :
    Sphincs.nodeHash pp layer tree = nodeHash pp layer tree := by
  funext level j left right
  simp only [Sphincs.nodeHash, nodeHash, th_eq, toList_append, toList_packBytes]

/-- A path fold is the same climb over the fast hash. -/
theorem fold_eq (pp : PublicParam) (layer : Layer) (tree e : Nat) (leaf : Digest)
    (pi : Vector Digest layer.height) :
    fold pp layer tree e leaf pi = (Merkle.climb (nodeHash pp layer tree) 0 e leaf pi.toList).run := by
  rw [fold, nodeHash_eq]

/-! ## FORS -/

/-- A FORS parent node over the fast hash, its children written as lists. -/
def forsNodeHash (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (level j : Nat)
    (left right : Digest) : Id Digest :=
  th pp (addrForsNode idx kappa (Fin.ofNat _ level) (forsIndex j)) (left.toList ++ right.toList)

/-- A FORS parent node is the parent over the fast hash. -/
theorem forsNodeHash_eq (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) :
    Sphincs.forsNodeHash pp idx kappa = forsNodeHash pp idx kappa := by
  funext level j left right
  simp only [Sphincs.forsNodeHash, forsNodeHash, th_eq, toList_append, toList_packBytes]

/-- The two level-9 nodes an opening leads to, over the fast hash. -/
def treeRecover (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT))
    (opening : TreeOpening) : Digest × Digest :=
  let leaf := th pp (addrForsLeaf idx kappa l) opening.secret.toList
  let reached :=
    (Merkle.climb (forsNodeHash pp idx kappa) 0 l leaf (opening.path.toList.take (FORS_HEIGHT - 1))).run
  Merkle.ordered (l.val >>> (FORS_HEIGHT - 1)) reached (opening.path[FORS_HEIGHT - 1]'(by decide))

/-- The two level-9 nodes that an opening recovers are the ones it recovers over the fast hash. -/
theorem treeRecover_eq (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) (opening : TreeOpening) :
    Sphincs.treeRecover pp idx kappa l opening = treeRecover pp idx kappa l opening := by
  simp only [Sphincs.treeRecover, forsLeafHash, th_eq, forsNodeHash_eq, treeRecover, toList_packBytes]

end EthLib.Cryptography.Sphincs.Kernel
