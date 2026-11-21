module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedDelay
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LocalSignature

/-!
# Delaying the two-layer signature under a selected cutoff

The public finder may refuse before returning a word.

Only a successful complete signature releases lower chain values and the lower authentication path.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open EthLib.Cryptography HashSig OracleComp OracleSpec Constants LayerGraph.Hidden

attribute [local irreducible] beforeNode revealPath beforeValues revealValues LayerGraph.readOutput
  selection simulateQ

variable {R : Type}

protected theorem SameCap.trans {pp : PublicParam} {α : Type} {a b c : WithCap R α}
    (first : SameCap pp a b) (second : SameCap pp b c) : SameCap pp a c :=
  fun q => (first q).trans (second q)

theorem sameCap_lift {pp : PublicParam} {α : Type} {a b : WithLocal R α} (h : SameLocal pp a b) :
    SameCap pp (liftM a : WithCap R α) (liftM b) := by
  intro q
  simp only [OptionT.run_monadLift, StateT.run_map, StateT.run_monadLift, monadLift_self]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  exact h.bind (fun _ _ => rfl)

/-- The upper signer receives the actual root and can spend budget or update its private table. -/
theorem delayed_selected_path (pp : PublicParam) (idx : LeafIndex)
    (next : Digest → WithCap R (Except XmssError LayerSignature)) :
    SameCap pp (do
      let root ← liftM (bottomRootSchedule pp idx)
      let path ← liftM (bottomPathSchedule pp idx)
      let top ← next root
      return top.map (fun t => (path, t))) (do
      let root ← liftM (bottomRootSchedule pp idx)
      match ← next root with
      | .error err => return .error err
      | .ok top => return .ok (← liftM (bottomPathSchedule pp idx), top)) := by
  have ready : StableRead pp (bottomRootSchedule pp idx) (bottomPathSchedule pp idx) :=
    fun s z ran => root_stores_path pp .bottom LAYER_HEIGHT
      (bottomTree idx) idx.toNat le_rfl rfl s z ran
  have delayed := delayCap pp (bottomRootSchedule pp idx) (bottomPathSchedule pp idx) next
    (fun path top => (path, top)) ready
  apply delayed.trans
  apply SameCap.bind (fun _ _ => rfl)
  intro root
  apply SameCap.bind (fun _ _ => rfl)
  rintro (_ | top) _ _ <;> rfl

/-- The lower values are touched before the upper signer runs and read only when it succeeds. -/
theorem delayed_selected_values (pp : PublicParam) (idx : LeafIndex) (rho : Randomizer)
    (x : Vector (Fin CHAIN_LENGTH) V)
    (upper : WithCap R (Except XmssError (Vector Digest LAYER_HEIGHT × LayerSignature))) :
    let e := UInt32.ofNat idx.toNat
    let sel := selection pp .bottom
    SameCap pp (do
      liftM (simulateQ sel.liftQuery (beforeValues pp .bottom e x))
      let ys ← liftM (simulateQ sel.liftQuery (revealValues e x))
      let result ← upper
      return result.map (packSignature idx rho ys)) (do
      liftM (simulateQ sel.liftQuery (beforeValues pp .bottom e x))
      match ← upper with
      | .error err => return .error err
      | .ok top => return .ok (packSignature idx rho (←
        liftM (simulateQ sel.liftQuery (revealValues e x))) top)) := by
  let e := UInt32.ofNat idx.toNat
  have delayed := delayCap pp (simulateQ (selection pp .bottom).liftQuery
      (beforeValues pp .bottom e x))
    (simulateQ (selection pp .bottom).liftQuery (revealValues e x)) (fun _ => upper)
    (packSignature idx rho) (stable_values pp .bottom e x)
  apply delayed.trans
  apply SameCap.bind (fun _ _ => rfl)
  intro _
  apply SameCap.bind (fun _ _ => rfl)
  rintro (_ | top) _ _ <;> rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
