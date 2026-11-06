module

public import EthLib.Cryptography.Proofs.Xmss.Tree
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.CacheRefinement
import Mathlib.Data.Nat.Bitwise

/-!
# Root reconstruction from an actual settled XMSS path

A successful reading of the path program settles every query reached by its sibling subtrees.

The selected leaf and its climb then retain the full root's result and complete cache.

The cache may contain other entries, and node indices retain their global offsets.

The equality says nothing about query counts.

Source: the leanXMSS specification draft, section "Trees".

The draft gives the sibling indices, the leaf-to-root path order and the left/right child order.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV

open OracleComp OracleSpec EthLib.Cryptography

variable {m : Type → Type} [Monad m] {Y : Type}

/-- Both root programs call the left child, right child and parent in that order. -/
private theorem node_eq_merkleRootM (hash : Nat → Nat → Y → Y → m Y) (leaf : Nat → m Y) :
    ∀ h j, Merkle.node hash leaf h j = PerfectMerkleTree.merkleRootM leaf hash h j
  | 0, _ => rfl
  | h + 1, j => by
    simp only [Merkle.node, PerfectMerkleTree.merkleRootM, node_eq_merkleRootM hash leaf h]

/-- A climb starting above level zero shifts only the generic hash's level argument. -/
private theorem climb_eq_climbM [LawfulMonad m] (hash : Nat → Nat → Y → Y → m Y) :
    ∀ (siblings : List Y) level j current,
      Merkle.climb hash level j current siblings =
        PerfectMerkleTree.climbM (fun h k l r => hash (level + h) k l r) j current siblings
  | [], _, _, _ => by simp [Merkle.climb]
  | a :: rest, level, j, current => by
    rw [Merkle.climb, PerfectMerkleTree.climbM_cons]
    simp only [Merkle.ordered]
    -- Both programs choose the same child order before the next parent hash.
    split_ifs <;> simp only [climb_eq_climbM hash rest]
    all_goals
      congr 1
      funext parent
      congr 1
      funext h k l r
      congr 1
      omega

/-- Flipping the low index bit selects the other child of the same parent. -/
private theorem sibling_eq_xor (i : Nat) : PerfectMerkleTree.sibling i = i ^^^ 1 := by
  unfold PerfectMerkleTree.sibling
  split
  next h => exact (Nat.xor_one_of_even (Nat.even_iff.mpr h)).symm
  next h => exact (Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))).symm

/-- The two vector collectors run each callback from index zero upward. -/
private theorem ofFnInOrder_eq_ofFnM [LawfulMonad m] : ∀ (n : Nat) (f : Fin n → m Y),
    Xmss.ofFnInOrder n f = Vector.ofFnM f
  | 0, _ => by simp [Xmss.ofFnInOrder]
  | n + 1, f => by
    rw [Xmss.ofFnInOrder, Vector.ofFnM_succ', ofFnInOrder_eq_ofFnM n]

/-- The generic path is the same ordered collection of sibling-subtree computations. -/
private theorem intrinsicAuthPathM_eq_ofFnM [LawfulMonad m]
    (hash : Nat → Nat → Y → Y → m Y) (leaf : Nat → m Y) (j : Nat) : ∀ n,
    PerfectMerkleTree.intrinsicAuthPathM leaf hash j n =
      Vector.ofFnM (fun i : Fin n => PerfectMerkleTree.merkleRootM leaf hash i.val
        (PerfectMerkleTree.sibling (j / 2 ^ i.val)))
  | 0 => by simp [PerfectMerkleTree.intrinsicAuthPathM]
  | n + 1 => by
    rw [PerfectMerkleTree.intrinsicAuthPathM, Vector.ofFnM_succ,
      intrinsicAuthPathM_eq_ofFnM hash leaf j n]
    -- The last vector index is the new level, and earlier indices keep their values.
    rfl

/-- The actual path and generic path retain every callback in leaf-to-root order. -/
private theorem path_eq_intrinsicAuthPathM [LawfulMonad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (seed : Seed)
    (layer : Layer) (j : Nat) :
    Xmss.path H pp seed layer j =
      PerfectMerkleTree.intrinsicAuthPathM (Xmss.leaves H pp seed layer)
        (Xmss.nodeHash H pp layer) j Constants.LAYER_HEIGHT := by
  rw [Xmss.path_eq_ofFnInOrder, ofFnInOrder_eq_ofFnM, intrinsicAuthPathM_eq_ofFnM]
  congr 1
  funext i
  rw [sibling_eq_xor]
  exact node_eq_merkleRootM _ _ _ _

universe v

/-- A settled actual path permits root reconstruction with the same result and entire cache.

The premise evaluates the actual path program through the known partial cache.

The initial live cache may extend that cache.

Node indices keep their global subtree offsets.

The miss handler is arbitrary, and its target monad is lawful.

No equality of physical query counts is asserted.
-/
theorem run_node_eq_run_selected_fold_of_path_settled
    {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    {target : Type → Type v} [Monad target] [LawfulMonad target]
    (so : QueryImpl spec target) (H : ByteArray → OracleComp spec (Vector UInt8 32))
    (pp : PublicParam) (seed : Seed) (layer : Layer) (idx : Nat)
    {known live : spec.QueryCache} (hle : known ≤ live)
    (pi : Vector Digest Constants.LAYER_HEIGHT)
    (hpath : simulateQ known.toPartialImpl (Xmss.path H pp seed layer idx) = some pi) :
    (simulateQ so.withCaching
      (Xmss.node H pp seed layer Constants.LAYER_HEIGHT
        (idx / 2 ^ Constants.LAYER_HEIGHT))).run live =
    (simulateQ so.withCaching (do
      let leaf ← Xmss.leaves H pp seed layer idx
      Xmss.fold H pp layer idx leaf pi)).run live := by
  -- Settled sibling programs frame every live cache extending the known one.
  have joint := PerfectMerkleTree.run_simulateQ_merkleRootM_eq_run_climbM_of_path_settled
    so (Xmss.leaves H pp seed layer) (Xmss.nodeHash H pp layer)
    idx Constants.LAYER_HEIGHT hle pi (by rw [← path_eq_intrinsicAuthPathM]; exact hpath)
  -- The adapters preserve the complete effectful programs, not just their values in Id.
  simpa only [Xmss.node, Xmss.fold, node_eq_merkleRootM, climb_eq_climbM, Nat.zero_add] using joint

end EthLib.Cryptography.Xmss.Unforgeability.VCV
