module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerValues
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# Chain-only computations preserve the local derivation state

Only the 29 paired secret starts enter a leaf, path or built Merkle tree.

State used for other private addresses can therefore stay in the caller during these operations.

This permits the randomizer reads on either side of a tree construction to share their own cache.

The leanXMSS draft specifies the paired starts in "WOTS+C" and the tree construction in "Trees".
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open EthLib.Cryptography HashSig OracleSpec OracleComp Constants

variable {R : Type}
abbrev WithLocal (R : Type) := StateT R (OracleComp SharedSpec)

/-- The genuine start pairs are graph reads that leave the residual derivation cache alone. -/
@[expose] def LocalPairs (pp : PublicParam) (l : Layer) (cb : SeedPrf (WithLocal R))
    (base : SeedPrf (OracleComp SharedSpec)) : Prop :=
  ∀ e : UInt32, ∀ j : Fin (V / 2), cb pp (addrPrf l e j) .empty
      = liftM (base pp (addrPrf l e j) .empty)

local notation "LH" => (fun b => (liftM (hash b) : WithLocal R (Vector UInt8 32)))

private theorem leaves_same (pp : PublicParam) (l : Layer) (cb : SeedPrf (WithLocal R))
    (base : SeedPrf (OracleComp SharedSpec)) (pairs : LocalPairs pp l cb base) :
    leaves LH pp cb l = leaves LH pp (fun p a b => liftM (base p a b)) l := by
  unfold LocalPairs at pairs
  funext j
  simp only [leaves, otsPublicLeaf, chainStarts, pairs]

/-- Building the root reads no residual derivations and keeps the complete local cache. -/
theorem node_lift (pp : PublicParam) (l : Layer) (cb : SeedPrf (WithLocal R))
    (base : SeedPrf (OracleComp SharedSpec)) (pairs : LocalPairs pp l cb base) (h j : Nat) :
    node LH pp cb l h j = liftM (node hash pp base l h j) := by
  rw [node_map_monad (fun {_} p => (liftM p : WithLocal R _)) (fun _ => liftM_pure _) (fun _ _ =>
      liftM_bind _ _)]
  simp only [node, leaves_same pp l cb base pairs]

/-- Building a tree once preserves the residual state as well as its full path information. -/
theorem build_lift (pp : PublicParam) (l : Layer) (cb : SeedPrf (WithLocal R))
    (base : SeedPrf (OracleComp SharedSpec)) (pairs : LocalPairs pp l cb base) (h j : Nat) :
    build LH pp cb l h j = liftM (build hash pp base l h j) := by
  rw [build_map_monad (fun {_} p => (liftM p : WithLocal R _)) (fun _ => liftM_pure _) (fun _ _ =>
      liftM_bind _ _)]
  simp only [build, leaves_same pp l cb base pairs]

/-- Computing all siblings reads the same 29 paired starts at each visited leaf. -/
theorem path_lift (pp : PublicParam) (l : Layer) (cb : SeedPrf (WithLocal R))
    (base : SeedPrf (OracleComp SharedSpec)) (pairs : LocalPairs pp l cb base) (e : Nat) :
    path LH pp cb l e = liftM (path hash pp base l e) := by
  rw [path_map_monad (fun {_} p => (liftM p : WithLocal R _)) (fun _ => liftM_pure _) (fun _ _ =>
      liftM_bind _ _)]
  simp only [path, leaves_same pp l cb base pairs]

/-- The 58 chain walks at an already chosen codeword leave the residual table alone. -/
theorem chainValues_lift (pp : PublicParam) (l : Layer) (cb : SeedPrf (WithLocal R))
    (base : SeedPrf (OracleComp SharedSpec)) (pairs : LocalPairs pp l cb base) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) :
    chainValues LH cb pp l e x = liftM (chainValues hash base pp l e x) := by
  unfold LocalPairs at pairs
  simp only [chainValues, liftM_bind]
  rw [chainStarts_map_monad (fun {_} p => (liftM p : WithLocal R _)) (fun _ =>
      liftM_pure _) (fun _ _ => liftM_bind _ _)]
  simp only [chainStarts, pairs]
  apply bind_congr
  intro starts
  rw [ofFnInOrder_map_monad (fun {_} p => (liftM p : WithLocal R _)) (fun _ =>
      liftM_pure _) (fun _ _ => liftM_bind _ _)]
  congr 1
  funext i
  exact (chain_map_monad (fun {_} p => (liftM p : WithLocal R _)) (fun _ =>
      liftM_pure _) (fun _ _ => liftM_bind _ _)
    _ _ _ _ _ _ _ _ _).symm

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
