import EthLib.Cryptography.Sphincs
import EthLib.Cryptography.Proofs.Hash.KeccakKernel

/-!
# Proofs: leanSPHINCS over the kernel's fast hash

The known answer evaluates hundreds of Keccak permutations in the kernel.

The kernel reads an array by walking a list, and appends to one an element at a time.

So the known answer runs on a fast form instead, proved equal to the specification:

- the hash is the record form of Keccak-f, over its input written as one list;
- `Th(P, A, M)` is that hash of the list `P ++ A ++ M`;
- a chain walk, a path fold and a FORS climb are the same walks over that `Th`.

A known answer rewrites its statement with these equalities, then lets the kernel evaluate it.
-/

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

/-- Climbing a hypertree path over the fast hash, level for level the specification's. -/
def climbUpto (pp : PublicParam) (layer : Layer) (tree e : Nat) (pi : Vector Digest layer.height)
    (leaf : Digest) : (levels : Nat) → levels ≤ layer.height → Digest
  | 0, _ => leaf
  | l + 1, h =>
    let current := climbUpto pp layer tree e pi leaf l (by omega)
    let sibling := pi[l]'(by omega)
    let address := addrNode layer tree ⟨l + 1, by have := layer.height_le; omega⟩ (e >>> (l + 1))
    -- Bit `l` of the key's index says which child the held node is.
    if (e >>> l) % 2 == 0 then th pp address (current.toList ++ sibling.toList)
    else th pp address (sibling.toList ++ current.toList)

/-- Climbing a path is climbing it over the fast hash. -/
theorem climbUpto_eq (pp : PublicParam) (layer : Layer) (tree e : Nat)
    (pi : Vector Digest layer.height) (leaf : Digest) :
    ∀ levels h,
      Internal.climbUpto pp layer tree e pi leaf levels h
        = climbUpto pp layer tree e pi leaf levels h := by
  intro levels
  induction levels with
  | zero => intro h; rfl
  | succ l ih =>
    intro h
    -- One level on each side, the climbs below it equal by induction.
    simp only [Internal.climbUpto, Internal.climbStep, nodeHash, climbUpto, th_eq, ih,
      toList_append, toList_packBytes]

/-- A path fold is the fold over the fast hash. -/
theorem fold_eq (pp : PublicParam) (layer : Layer) (tree e : Nat) (leaf : Digest)
    (pi : Vector Digest layer.height) :
    fold pp layer tree e leaf pi = climbUpto pp layer tree e pi leaf layer.height (Nat.le_refl _) :=
  climbUpto_eq pp layer tree e pi leaf _ _

/-! ## FORS -/

/-- Climbing a FORS path over the fast hash, level for level the specification's. -/
def forsClimbUpto (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (l : Nat)
    (pi : Vector Digest FORS_HEIGHT) (leaf : Digest) :
    (levels : Nat) → levels ≤ FORS_HEIGHT - 1 → Digest
  | 0, _ => leaf
  | k + 1, h =>
    let current := forsClimbUpto pp idx kappa l pi leaf k (by omega)
    let sibling := pi[k]'(by have := h; simp only [FORS_HEIGHT] at this ⊢; omega)
    let address := addrForsNode idx kappa ⟨k + 1, by have := h; simp only [FORS_HEIGHT] at this; omega⟩
      (forsIndex (l >>> (k + 1)))
    -- Bit `k` of the leaf index says which child the held node is.
    if (l >>> k) % 2 == 0 then th pp address (current.toList ++ sibling.toList)
    else th pp address (sibling.toList ++ current.toList)

/-- Climbing a FORS path is climbing it over the fast hash. -/
theorem forsClimbUpto_eq (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (l : Nat)
    (pi : Vector Digest FORS_HEIGHT) (leaf : Digest) :
    ∀ levels h,
      Internal.forsClimbUpto pp idx kappa l pi leaf levels h
        = forsClimbUpto pp idx kappa l pi leaf levels h := by
  intro levels
  induction levels with
  | zero => intro h; rfl
  | succ k ih =>
    intro h
    -- One level on each side, the climbs below it equal by induction.
    simp only [Internal.forsClimbUpto, Internal.forsClimbStep, forsNodeHash, forsClimbUpto, th_eq, ih,
      toList_append, toList_packBytes]
    rfl

/-- The two level-9 nodes an opening leads to, over the fast hash. -/
def treeRecover (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT))
    (opening : TreeOpening) : Digest × Digest :=
  let leaf := th pp (addrForsLeaf idx kappa l) opening.secret.toList
  let reached := forsClimbUpto pp idx kappa l opening.path leaf (FORS_HEIGHT - 1) (Nat.le_refl _)
  let other := opening.path[FORS_HEIGHT - 1]'(by decide)
  if (l.val >>> (FORS_HEIGHT - 1)) % 2 == 0 then (reached, other) else (other, reached)

/-- Recovering a tree's two level-9 nodes is recovering them over the fast hash. -/
theorem treeRecover_eq (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) (opening : TreeOpening) :
    Sphincs.treeRecover pp idx kappa l opening = treeRecover pp idx kappa l opening := by
  simp only [Sphincs.treeRecover, forsLeafHash, th_eq, forsClimbUpto_eq, treeRecover, toList_packBytes]

end EthLib.Cryptography.Sphincs.Kernel
