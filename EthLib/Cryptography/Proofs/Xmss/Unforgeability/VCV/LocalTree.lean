module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LocalDelay

/-!
# Authentication data of a stateful signing request

Key generation and the bottom signer each build the native tree.

The top finder signs its actual bottom root.

Its failure can consume local randomness without disclosing a bottom authentication path.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open EthLib.Cryptography HashSig OracleSpec OracleComp Constants LayerGraph.Hidden
variable {R α : Type}

local notation "LH" => (fun b => (liftM (hash b) : WithLocal R (Vector UInt8 32)))

/-- The public root exposed by building the bottom tree; private nodes are only touched. -/
noncomputable abbrev bottomRootSchedule (pp : PublicParam) (idx : LeafIndex) :=
  let h := LAYER_HEIGHT
  let j := bottomTree idx
  simulateQ (selection pp .bottom).liftQuery
    (beforeNode pp .bottom h j >>= fun _ => LayerGraph.readOutput (LayerGraph.treeRole h j))

/-- Read the bottom path after the complete signing result is known. -/
noncomputable abbrev bottomPathSchedule (pp : PublicParam) (idx : LeafIndex) :=
  simulateQ (selection pp .bottom).liftQuery (revealPath LAYER_HEIGHT idx.toNat)

private theorem build_then {cb : SeedPrf (WithLocal R)} (pp : PublicParam)
    (base : SeedPrf (OracleComp SharedSpec)) (pairs : LocalPairs pp .bottom cb base)
    (selected : Pairs pp .bottom base)
    (idx : LeafIndex) (k : Digest × Vector Digest LAYER_HEIGHT → WithLocal R α) :
    SameLocal pp (Xmss.build LH pp cb .bottom LAYER_HEIGHT (bottomTree idx) >>=
      fun t => k (t.value, t.path LAYER_HEIGHT idx.toNat))
      (liftM (builtPathSchedule pp .bottom LAYER_HEIGHT (bottomTree idx) idx.toNat) >>= k) := by
  rw [build_lift pp .bottom cb base pairs]
  have both := sameLocal_lift (R := R) (build_path_pairs pp .bottom base selected
    LAYER_HEIGHT (bottomTree idx) idx.toNat le_rfl rfl)
  simpa only [liftM_map, bind_map_left] using (both.bind (f := k) (g := k) (fun _ _ => rfl))

/-- The top signature and bottom path are returned together only on successful completion. -/
@[expose] noncomputable def localTree (pp : PublicParam) (cb : SeedPrf (WithLocal R))
    (idx : LeafIndex) :
    WithLocal R (Except XmssError (Vector Digest LAYER_HEIGHT × LayerSignature)) := do
  let root ← liftM (bottomRootSchedule pp idx)
  match ← localLayer pp cb .top (bottomTree idx) (packBytes root) with
  | .error err => return .error err
  | .ok top => return .ok (← liftM (bottomPathSchedule pp idx), top)

attribute [local irreducible] Xmss.build Xmss.signLayer localLayer beforeNode revealPath
  builtPathSchedule localTree

/-- Building once and returning its path agrees with reading that path only on top-layer success. -/
theorem build_layer_local (pp : PublicParam) (cb : SeedPrf (WithLocal R))
    (base : Layer → SeedPrf (OracleComp SharedSpec)) (pairs : ∀ l, LocalPairs pp l cb (base l))
    (selected : ∀ l, Pairs pp l (base l)) (idx : LeafIndex) :
    SameLocal pp (do
      let tree ← Xmss.build LH pp cb .bottom LAYER_HEIGHT (bottomTree idx)
      let top ← Xmss.signLayer LH pp cb .top (bottomTree idx) (packBytes tree.value)
      return top.map (fun s => (tree.path LAYER_HEIGHT idx.toNat, s))) (localTree pp cb idx) := by
  let next := fun (both : Digest × Vector Digest LAYER_HEIGHT) => do
    let top ← Xmss.signLayer LH pp cb .top (bottomTree idx) (packBytes both.1)
    pure (top.map (fun s => (both.2, s)))
  apply (build_then pp (base .bottom) (pairs .bottom) (selected .bottom) idx next).trans
  have old : SameLocal pp
      (liftM (builtPathSchedule pp .bottom LAYER_HEIGHT (bottomTree idx) idx.toNat) >>= next)
      (do
        let root ← liftM (bottomRootSchedule pp idx)
        let path ← liftM (bottomPathSchedule pp idx)
        let answer ← localLayer pp cb .top (bottomTree idx) (packBytes root)
        return answer.map (fun top => (path, top))) := by
    simp only [builtPathSchedule, bottomRootSchedule, bottomPathSchedule,
      simulateQ_bind, simulateQ_pure, liftM_bind, liftM_pure, bind_assoc, pure_bind, next]
    apply SameLocal.bind (fun _ => rfl)
    intro _
    apply SameLocal.bind (fun _ => rfl)
    intro root
    apply SameLocal.bind (fun _ => rfl)
    intro path
    exact (signLayer_local pp cb .top (base .top) (pairs .top)
      (selected .top) _ _).bind (fun _ _ => rfl)
  have stable : StableRead pp (bottomRootSchedule pp idx) (bottomPathSchedule pp idx) :=
    fun s z ran => root_stores_path pp .bottom LAYER_HEIGHT (bottomTree idx)
      idx.toNat le_rfl rfl s z ran
  have delayed := delayLocal pp (bottomRootSchedule pp idx) (bottomPathSchedule pp idx)
    (fun root => localLayer pp cb .top (bottomTree idx) (packBytes root))
    (fun path top => (path, top)) stable
  refine old.trans (delayed.trans ?_)
  unfold localTree
  apply SameLocal.bind (fun _ => rfl)
  intro root
  apply SameLocal.bind (fun _ => rfl)
  rintro (_ | top) _ <;> rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
