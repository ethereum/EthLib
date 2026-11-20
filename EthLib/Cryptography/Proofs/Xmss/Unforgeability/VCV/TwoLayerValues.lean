module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerSchedule

/-!
# The shared signing oracle's private chain reads

The leanXMSS draft, section "WOTS+C", returns one value at the selected position of each chain.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants HashSig OracleComp OracleSpec LayerGraph.Hidden
open ChainGraph (indexAt Public)

/-- A seed oracle returns the two private starts of each physical pair in this layer. -/
def Pairs (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec)) : Prop :=
  ∀ (e : UInt32) (j : Fin (V / 2)), cb pp (addrPrf l e j) .empty = (do
    let lo ← readCell (pub := Public) (K := Row) (some (.inl (l, e, indexAt j 0)))
    let hi ← readCell (pub := Public) (K := Row) (some (.inl (l, e, indexAt j 1)))
    pure (ofOutput (PairedHashWord.halves.symm (lo, hi))))

private theorem pair_starts (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec))
    (paired : Pairs pp l cb) (other : SeedPrf (OracleComp LayerGraph.Spec)) (e : UInt32) :
    chainStarts pp cb l e = chainStarts pp (prf pp l other) l e := by
  have agree (j : Fin (V / 2)) : cb pp (addrPrf l e j) .empty =
      prf pp l other pp (addrPrf l e j) .empty := (paired e j).trans (prf_pair pp l other e j).symm
  simp only [chainStarts, agree]

/-- The WOTS values returned after the finder's successful trial. -/
def chainValues {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
    (cb : SeedPrf m) (pp : PublicParam) (l : Layer) (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V) :
    m (Vector Digest V) := do
  let starts ← chainStarts pp cb l e
  ofFnInOrder V fun i => Xmss.chain H pp l e i 0 (x[i]).val (by simp) starts[i]

attribute [local irreducible] ofFnInOrder chainStarts Xmss.chain

private theorem values_image (pp : PublicParam) (l : Layer)
    (other : SeedPrf (OracleComp LayerGraph.Spec))
    (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V) :
    simulateQ (selection pp l).liftQuery
      (chainValues LayerGraph.hash (LayerGraph.startPrf pp l other) pp l e x) =
      chainValues hash (prf pp l other) pp l e x := by
  let v := selection pp l
  let φ := fun {α : Type} (op : OracleComp LayerGraph.Spec α) => simulateQ v.liftQuery op
  change φ (chainValues LayerGraph.hash (LayerGraph.startPrf pp l other) pp l e x) = _
  unfold chainValues
  rw [show ∀ {α β} (p : OracleComp LayerGraph.Spec α)
    (k : α → OracleComp LayerGraph.Spec β),
    φ (p >>= k) = φ p >>= fun a => φ (k a) from fun _ _ => simulateQ_bind _ _ _]
  rw [Xmss.chainStarts_map_monad (fun {_} p => φ p) (simulateQ_pure _) (simulateQ_bind _)]
  apply bind_congr
  intro xs
  rw [ofFnInOrder_map_monad (fun {_} p => φ p) (simulateQ_pure _) (simulateQ_bind _)]
  congr 1
  funext i
  rw [Xmss.chain_map_monad (fun {_} p => φ p) (simulateQ_pure _) (simulateQ_bind _)]
  simp only [φ, v, hash_image]

theorem exact_collect (pp : PublicParam) (l : Layer) {α : Type}
    (n : Nat) (f : Fin n → OracleComp LayerGraph.Spec α)
    (entries : ∀ i, (selection pp l).Exact (f i)) :
    (selection pp l).Exact (ofFnInOrder n f) := by
  let v := selection pp l
  induction n with
  | zero => rw [ofFnInOrder]; exact v.exact_pure _
  | succ n ih =>
    rw [ofFnInOrder]
    exact v.exact_bind (entries 0) fun _ => v.exact_bind
      (ih (fun i => f i.succ) (fun i => entries i.succ)) fun _ => v.exact_pure _

/-- Only the selected 58 get read in the common graph; all touches happen first. -/
theorem values_schedule (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec))
    (paired : Pairs pp l cb) (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V) :
    simulateQ (graph pp).eagerImpl (chainValues hash cb pp l e x) =
      simulateQ (graph pp).eagerImpl (simulateQ (selection pp l).liftQuery
        (beforeValues pp l e x >>= fun _ => revealValues e x)) := by
  let v := selection pp l
  let aux : SeedPrf (OracleComp LayerGraph.Spec) := fun _ _ _ => pure (Vector.replicate 32 0)
  have actual : chainValues hash cb pp l e x = chainValues hash (prf pp l aux) pp l e x := by
    unfold chainValues
    rw [pair_starts pp l cb paired aux e]
  rw [actual, ← values_image pp l aux e x]
  ext s : 1
  apply v.run_eq_of_exact
  · exact v.exact_bind (starts_selected pp l aux e).2 fun xs =>
      exact_collect pp l _ _ (fun i => (chain_selected pp l e i _ _ _ xs[i]).2)
  · apply v.exact_bind (beforeValues_pred (fun p => v.Exact p) (v.exact_pure ())
      (fun _ _ a b => v.exact_bind a fun _ => b) v.exact_touchCell pp l e x)
    intro _
    exact exact_collect pp l _ _ fun i => v.exact_map _ (v.exact_readCell _)
  · exact fun t => congrArg (fun m => StateT.run m t) (LayerGraph.Hidden.values pp l aux e x)

/-- The common oracle performs the actual randomizer search before touching any private start. -/
noncomputable def signSchedule (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec))
    (e : UInt32) (msg : ByteArray) :
    OracleComp SharedSpec (Option (Randomizer × Vector Digest V)) := do
  let base ← randomizerBase pp cb l e msg
  let some (rho, x) ← Xmss.Internal.findCodeword hash pp l e msg base 0 MAX_RANDOMIZER_TRIALS
    | return none
  let ys ← simulateQ (selection pp l).liftQuery
    (beforeValues pp l e x >>= fun _ => revealValues e x)
  return some (rho, ys)

attribute [local irreducible] Xmss.Internal.findCodeword

/-- No assumptions on the randomizer or finder queries are needed for the signing equality. -/
theorem ots_schedule (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec))
    (paired : Pairs pp l cb) (e : UInt32) (msg : ByteArray) :
    simulateQ (graph pp).eagerImpl (otsSign hash pp cb l e msg) =
      simulateQ (graph pp).eagerImpl (signSchedule pp l cb e msg) := by
  unfold otsSign signSchedule
  simp only [simulateQ_bind]
  apply bind_congr
  intro base
  apply bind_congr
  rintro (_ | ⟨rho, x⟩)
  · rfl
  · have law := congrArg (fun p : StateT SharedState ProbComp (Vector Digest V) =>
      p >>= fun ys => pure (some (rho, ys))) (values_schedule pp l cb paired e x)
    simpa only [chainValues, simulateQ_bind, simulateQ_pure, bind_assoc] using law

theorem leaves_pairs (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec))
    (paired : Pairs pp l cb) (other : SeedPrf (OracleComp LayerGraph.Spec)) :
    leaves hash pp cb l = leaves hash pp (prf pp l other) l := by
  funext j
  unfold leaves otsPublicLeaf
  rw [pair_starts pp l cb paired other]

/-- Any actual seed handler with the correct pair responses can run both layers in one graph. -/
theorem node_pairs (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec))
    (paired : Pairs pp l cb) (h j : Nat) (bound : h ≤ LAYER_HEIGHT) :
    simulateQ (graph pp).eagerImpl (Xmss.node hash pp cb l h j) =
      simulateQ (graph pp).eagerImpl (simulateQ (selection pp l).liftQuery
        (beforeNode pp l h j >>= fun _ => LayerGraph.readOutput (LayerGraph.treeRole h j))) := by
  let aux : SeedPrf (OracleComp LayerGraph.Spec) := fun _ _ _ => pure (Vector.replicate 32 0)
  rw [Xmss.node, leaves_pairs pp l cb paired aux]
  exact node_schedule pp l aux h j bound

/-- The current signer uses the actual shared private handler to generate its sixteen siblings. -/
theorem path_pairs (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec))
    (paired : Pairs pp l cb) (e : Nat) :
    simulateQ (graph pp).eagerImpl (Xmss.path hash pp cb l e) =
      simulateQ (graph pp).eagerImpl (pathSchedule pp l e) := by
  let aux : SeedPrf (OracleComp LayerGraph.Spec) := fun _ _ _ => pure (Vector.replicate 32 0)
  rw [Xmss.path, leaves_pairs pp l cb paired aux]
  exact path_schedule pp l aux e

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
