module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedNative
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedSignature
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedPhases
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# Admitted native structural operations on the shared graph

A complete chain walk or tree construction issues only unmarked physical queries.

The quota, private tables and graph are therefore those of the free structural schedule.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp TwoLayerGraph Honest
  LayerGraph.Hidden

private noncomputable abbrev freeMark := mark (fun _ => False)

private theorem freeHash (b : ByteArray) :
    simulateQ freeMark (hashOf sourcePass b) = markedChainHash b := hash_unchosen _ _ id

private theorem freePrf (p : PublicParam) (a : Address) (b : ByteArray) :
    simulateQ freeMark (sourcePrf p a b) = phasePrf p a b := (phasePrf_free ..).symm

private theorem free_build (pp : PublicParam) (l : Layer) (h j : Nat) :
    simulateQ freeMark (build (hashOf sourcePass) pp sourcePrf l h j) =
      build markedChainHash pp phasePrf l h j := by
  rw [build_map_monad (fun {_} p => simulateQ freeMark p) (fun _ => simulateQ_pure _ _)
    (fun _ _ => simulateQ_bind _ _ _)]
  simp only [freeHash, freePrf]

private theorem free_path (pp : PublicParam) (l : Layer) (e : Nat) :
    simulateQ freeMark (path (hashOf sourcePass) pp sourcePrf l e) =
      path markedChainHash pp phasePrf l e := by
  rw [path_map_monad (fun {_} p => simulateQ freeMark p) (fun _ => simulateQ_pure _ _)
    (fun _ _ => simulateQ_bind _ _ _)]
  simp only [freeHash, freePrf]

private theorem values_nat {n : Type → Type} [Monad n] [LawfulMonad n]
    {m : Type → Type} [Monad m] [LawfulMonad m] (f : ∀ {a : Type}, m a → n a)
    (unit : ∀ {a : Type} (x : a), f (pure x) = pure x)
    (bind : ∀ {a b : Type} (p : m a) (next : a → m b),
      f (p >>= next) = f p >>= fun x => f (next x))
    (H : ByteArray → m (Vector UInt8 32)) (cb : SeedPrf m) (pp : PublicParam) (l : Layer)
    (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V) :
    f (chainValues H cb pp l e x) = chainValues (fun b => f (H b)) (fun p a b =>
      f (cb p a b)) pp l e x := by
  simp only [chainValues, bind, chainStarts_map_monad f unit bind,
      HashSig.ofFnInOrder_map_monad f unit bind,
    chain_map_monad f unit bind]

private theorem free_values (pp : PublicParam) (l : Layer) (e : UInt32) (x : Vector
    (Fin CHAIN_LENGTH) V) :
    simulateQ freeMark (chainValues (hashOf sourcePass) sourcePrf pp l e x) =
      chainValues markedChainHash phasePrf pp l e x := by
  rw [values_nat (fun {_} p => simulateQ freeMark p) (fun _ => simulateQ_pure _ _)
    (fun _ _ => simulateQ_bind _ _ _)]
  simp only [freeHash, freePrf]

theorem selected_values (pp : PublicParam) (l : Layer) (e : UInt32) (x : Vector
    (Fin CHAIN_LENGTH) V) :
    SameCap pp (simulateQ (selectedImpl pp) (chainValues markedChainHash phasePrf pp l e x))
      (liftM (simulateQ (selection pp l).liftQuery (beforeValues pp l e x >>= fun _ =>
        revealValues e x)) :
        Selected pp _) := by
  rw [← free_values, unmarked_phase]
  apply sameCap_lift
  rw [values_nat (fun {_} p => inGraph pp p) (inGraph_pure pp) (inGraph_bind pp)]
  simp only [inGraph_hash]
  let b := prf pp l emptyPrf
  change SameLocal pp (chainValues _ (graphPrf pp) pp l e x) _
  rw [chainValues_lift pp l (graphPrf pp) b (graphPrf_pairs pp l) e x]
  exact sameLocal_lift (values_schedule pp l b (prf_pair pp l emptyPrf) e x)

theorem selected_path (pp : PublicParam) (l : Layer) (e : Nat) :
    SameCap pp (simulateQ (selectedImpl pp) (path markedChainHash pp phasePrf l e))
      (liftM (pathSchedule pp l e) : Selected pp _) := by
  rw [← free_path, unmarked_phase]
  apply sameCap_lift
  rw [path_map_monad (fun {_} p => inGraph pp p) (inGraph_pure pp) (inGraph_bind pp)]
  simp only [inGraph_hash]
  let b := prf pp l emptyPrf
  change SameLocal pp (path _ pp (graphPrf pp) l e) _
  rw [path_lift pp l (graphPrf pp) b (graphPrf_pairs pp l) e]
  exact sameLocal_lift (path_pairs pp l b (prf_pair pp l emptyPrf) e)

attribute [local irreducible] Xmss.build builtPathSchedule LayerGraph.Hidden.beforeNode
  LayerGraph.Hidden.revealPath selection simulateQ inGraph

private theorem lift_twice {R α : Type} (p : OracleComp SharedSpec α) :
    (liftM (liftM p : WithLocal R α) : WithCap R α) = liftM p := by
  ext q r : 3
  simp [OptionT.run_monadLift, StateT.run_monadLift, StateT.run_map, Functor.map_map]

/-- The bottom root and authentication path come from the one native tree build. -/
theorem selected_built (pp : PublicParam) (idx : LeafIndex) :
    SameCap pp ((fun tree : Merkle.Built Digest =>
      (tree.value, tree.path LAYER_HEIGHT idx.toNat)) <$>
        simulateQ (selectedImpl pp)
          (build markedChainHash pp phasePrf .bottom LAYER_HEIGHT (bottomTree idx)))
      (liftM (builtPathSchedule pp .bottom LAYER_HEIGHT
        (bottomTree idx) idx.toNat) : Selected pp _) := by
  rw [← free_build, unmarked_phase]
  have native : inGraph pp (build (hashOf sourcePass) pp sourcePrf .bottom LAYER_HEIGHT
      (bottomTree idx)) =
      liftM (build Honest.hash pp (prf pp .bottom emptyPrf) .bottom LAYER_HEIGHT
        (bottomTree idx)) := by
    rw [build_map_monad (fun {_} p => inGraph pp p) (inGraph_pure pp) (inGraph_bind pp)]
    simp only [inGraph_hash]
    exact build_lift pp .bottom (graphPrf pp) _ (graphPrf_pairs pp .bottom) _ _
  rw [native]
  have pair := sameLocal_lift (R := ResidualCache pp) (build_path_pairs pp .bottom _
    (prf_pair pp .bottom emptyPrf) LAYER_HEIGHT (bottomTree idx) idx.toNat le_rfl rfl)
  have capped := sameCap_lift pair
  simpa only [liftM_map, lift_twice] using capped

/-- The physical randomizer uses the genuine private lookup without consuming a public query. -/
theorem selected_base (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    simulateQ (selectedImpl pp) (randomizerBase pp phasePrf l e msg) =
      (liftM (randomizerBase pp (graphPrf pp) l e msg) : Selected pp _) := by
  have source := randomizerBase_map_monad (fun {_} p => simulateQ freeMark p)
    (fun _ => simulateQ_pure _ _) (fun _ _ => simulateQ_bind _ _ _) sourcePrf pp l e msg
  simp only [freePrf] at source
  rw [← source, unmarked_phase, randomizerBase_map_monad (fun {_} p => inGraph pp p)
    (inGraph_pure pp) (inGraph_bind pp)]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
