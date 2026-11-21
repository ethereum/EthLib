module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LocalSignature
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ResidualRandomizer
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerSignerReplay
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerSignerLog

/-!
# A realized stateful signing trace

The lower randomizer receives the residual table on entry to signing.

The upper randomizer receives the table left by the lower lookup.

All operations after the upper lookup preserve that residual table.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography OracleComp OracleSpec HashSig Constants TwoLayerGraph
open TwoLayerGraph.Honest LayerGraph.Hidden
open scoped Classical

private theorem logged_map {α β : Type} {pp : PublicParam} {op : OracleComp SharedSpec α}
    {s a log t} (ran : Logged pp op s a log t) (f : α → β) :
    Logged pp (f <$> op) s (f a) log t := by
  unfold Logged at ran ⊢
  simp only [simulateQ_map, WriterT.run_map', StateT.run_map, support_map]
  exact ⟨((a, log), t), ran, rfl⟩

private theorem logged_bind {α β : Type} {pp : PublicParam} {p : OracleComp SharedSpec α}
    {f : α → OracleComp SharedSpec β} {s a xs m b ys t}
    (head : Logged pp p s a xs m) (tail : Logged pp (f a) m b ys t) :
    Logged pp (p >>= f) s b (xs ++ ys) t := by
  unfold Logged at head tail ⊢
  simp only [simulateQ_bind, WriterT.run_bind', simulateQ_map, StateT.run_bind, StateT.run_map,
    mem_support_bind_iff, support_map]
  exact ⟨((a, xs), m), head, ((b, ys), t), tail, rfl⟩

private theorem project_map {R α β : Type} (r : R) (p : StateT R (OracleComp SharedSpec) α)
    (f : α → β) :
    Prod.fst <$> (p >>= fun x => pure (f x)).run r = (Prod.fst <$> p.run r) >>=
      fun x => pure (f x) := by
  simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure, bind_map_left]

private theorem project_lift {R α β : Type} (r : R) (p : StateT R (OracleComp SharedSpec) α)
    (next : α → OracleComp SharedSpec β) :
    Prod.fst <$> (p >>= fun x => (liftM (next x) : StateT R (OracleComp SharedSpec) β)).run r =
      (Prod.fst <$> p.run r) >>= next := by
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind,
    map_pure, bind_map_left, bind_pure]

private theorem rnd_bottom (pp : PublicParam) (low high : ResidualCache pp)
    (e : UInt32) (m : ByteArray) :
    Prod.fst <$> (randomizerBase pp (graphPrf pp) .bottom e m).run low =
      randomizerBase pp (signingPrf pp low high) .bottom e m := by
  unfold randomizerBase
  rw [signingPrf_bottom]
  exact project_map low _ _

private theorem rnd_top (pp : PublicParam) (low high : ResidualCache pp)
    (e : UInt32) (m : ByteArray) :
    Prod.fst <$> (randomizerBase pp (graphPrf pp) .top e m).run high =
      randomizerBase pp (signingPrf pp low high) .top e m := by
  unfold randomizerBase
  rw [signingPrf_top]
  exact project_map high _ _

attribute [local irreducible] graphPrf signingPrf randomizerBase Honest.hash
attribute [local irreducible] Xmss.Internal.findCodeword
  selection beforeValues revealValues pathSchedule beforeNode revealPath LayerGraph.readOutput

/-- Once the upper randomizer returns, the finder, chain values and path use only the graph. -/
private noncomputable def upperRest (pp : PublicParam) (e : Nat) (m : ByteArray)
    (base : Randomizer) :
    OracleComp SharedSpec (Except XmssError LayerSignature) := do
  let mutSig ← (do
    let some (rho, x) ← Xmss.Internal.findCodeword Honest.hash pp .top
        (UInt32.ofNat e) m base 0 MAX_RANDOMIZER_TRIALS
      | return none
    let ys ← simulateQ (selection pp .top).liftQuery
      (beforeValues pp .top (UInt32.ofNat e) x >>= fun _ => revealValues (UInt32.ofNat e) x)
    return some (rho, ys))
  match mutSig with
  | none => return .error (.noAdmissibleEncoding .top e)
  | some (rho, ys) => return .ok ⟨rho, ys, ← pathSchedule pp .top e⟩

private theorem top_local (pp : PublicParam) (e : Nat) (m : ByteArray) :
    localLayer pp (graphPrf pp) .top e m =
      (randomizerBase pp (graphPrf pp) .top (UInt32.ofNat e) m >>=
        fun b => liftM (upperRest pp e m b)) := by
  unfold localLayer localOts upperRest
  simp only [liftM_bind, bind_assoc]
  apply bind_congr
  intro _
  apply bind_congr
  rintro (_ | ⟨rho,x⟩)
  · rfl
  · simp only [liftM_bind, liftM_pure, bind_assoc, pure_bind]

private theorem top_graph (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (e : Nat) (m : ByteArray) :
    layerSchedule pp cb .top e m =
      (randomizerBase pp cb .top (UInt32.ofNat e) m >>= upperRest pp e m) := by
  unfold layerSchedule signSchedule upperRest
  simp only [bind_assoc]
  apply bind_congr
  intro _
  apply bind_congr
  rintro (_ | ⟨rho,x⟩)
  · rfl
  · simp only [bind_assoc, pure_bind]

attribute [local irreducible] upperRest

private theorem layer_project (pp : PublicParam) (low high : ResidualCache pp)
    (e : Nat) (m : ByteArray) :
    Prod.fst <$> (localLayer pp (graphPrf pp) .top e m).run high =
      layerSchedule pp (signingPrf pp low high) .top e m := by
  rw [top_local, top_graph, ← rnd_top pp low high]
  exact project_lift high _ _

private theorem tree_project (pp : PublicParam) (low high : ResidualCache pp) (idx : LeafIndex) :
    Prod.fst <$> (localTree pp (graphPrf pp) idx).run high =
      releasedTree pp (signingPrf pp low high) idx := by
  unfold localTree releasedTree
  simp only [bottomRootSchedule, bottomPathSchedule, StateT.run_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, map_bind]
  apply bind_congr
  intro root
  rw [← layer_project pp low high]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨(_ | top), r⟩
  · rfl
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_pure,
      bind_assoc, pure_bind, map_bind, map_pure]


/-- The part of signing after the first randomizer can be run in either monad. -/
private noncomputable def afterLower {m : Type → Type} [Monad m] (embed : ∀ {a : Type},
    OracleComp SharedSpec a → m a)
    (pp : PublicParam) (idx : LeafIndex) (msg : Message) (rnd : Randomizer)
    (top : m (Except XmssError (Vector Digest LAYER_HEIGHT × LayerSignature))) :
      m (Except XmssError Signature) := do
  let e := UInt32.ofNat idx.toNat
  let some (rho, x) ← embed (Xmss.Internal.findCodeword Honest.hash pp .bottom e
      (packBytes msg) rnd 0 MAX_RANDOMIZER_TRIALS)
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  let v := selection pp .bottom
  embed (simulateQ v.liftQuery (beforeValues pp .bottom e x))
  match ← top with
  | .error err => return .error err
  | .ok b =>
    let ys ← embed (simulateQ v.liftQuery (revealValues e x))
    return .ok (packSignature idx rho ys b)

private theorem after_project (pp : PublicParam) (low high : ResidualCache pp)
    (idx : LeafIndex) (msg : Message) (rnd : Randomizer) :
    Prod.fst <$> (afterLower (fun {_} p => (liftM p : WithLocal (ResidualCache pp) _))
      pp idx msg rnd (localTree pp (graphPrf pp) idx)).run high =
      afterLower (fun {_} p => p) pp idx msg rnd (releasedTree pp
        (signingPrf pp low high) idx) := by
  unfold afterLower
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, map_bind]
  apply bind_congr
  rintro (_ | ⟨rho, x⟩)
  · rfl
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc,
        pure_bind, map_bind]
    apply bind_congr
    intro _
    rw [← tree_project pp low high]
    simp only [bind_map_left]
    apply bind_congr
    rintro ⟨(_ | top), state⟩
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_pure,
        bind_assoc, pure_bind, map_bind, map_pure]

/-- Both saved states are from one realized signing prefix.

The pure callback retains the same graph log, raw result and pending cells. -/
theorem local_released_log (pp : PublicParam) (low : ResidualCache pp) (idx : LeafIndex)
    (msg : Message) {s ans out log t}
    (ran : Logged pp ((localReleased pp (graphPrf pp) idx msg).run low) s (ans, out) log t) :
    ∃ high : ResidualCache pp,
      Logged pp (releasedSchedule pp (signingPrf pp low high) idx msg) s ans log t := by
  change Logged pp ((randomizerBase pp (graphPrf pp) .bottom (UInt32.ofNat idx.toNat)
    (packBytes msg) >>=
    fun rnd => afterLower (fun {_} p => (liftM p : WithLocal (ResidualCache pp) _)) pp idx msg rnd
      (localTree pp (graphPrf pp) idx)).run low) s (ans, out) log t at ran
  rw [StateT.run_bind] at ran
  obtain ⟨⟨rnd, high⟩, pre, mid, tail, ha, hb, rfl⟩ := ran.bind
  refine ⟨high, ?_⟩
  have first := logged_map ha Prod.fst
  rw [rnd_bottom pp low high] at first
  have rest := logged_map hb Prod.fst
  rw [after_project pp low high] at rest
  exact logged_bind (f := fun base => afterLower (fun {_} p => p) pp idx msg base
    (releasedTree pp (signingPrf pp low high) idx)) first rest

/-- Every direct chain read uses a position disclosed by this signing reply. -/
theorem local_signature_release (pp : PublicParam) (low : ResidualCache pp) (idx : LeafIndex)
    (msg : Message) {s ans out log t}
    (ran : Logged pp ((localReleased pp (graphPrf pp) idx msg).run low) s (ans, out) log t) :
    SignatureRelease pp idx msg ans log t.1 := by
  obtain ⟨high, actual⟩ := local_released_log pp low idx msg ran
  exact releasedSchedule_logged pp _ (signingPrf_residual pp low high) idx msg actual


end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
