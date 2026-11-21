module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedStructure

/-!
# The guarded signer discloses only after both finders succeed

Each finder runs on the original charged physical port.

The deferred order reuses the native bottom root for the top finder.

A refusal in either finder stops all later disclosures.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants Merkle OracleSpec OracleComp TwoLayerGraph Honest
open LayerGraph.Hidden

/-- Draw the private randomizer before running the paid finder. -/
@[expose] noncomputable def guardedFind (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) :
    Selected pp (Option (Randomizer × Vector (Fin CHAIN_LENGTH) V)) := do
  let base ← liftM (randomizerBase pp (graphPrf pp) l e msg)
  simulateQ (selectedImpl pp) (Xmss.Internal.findCodeword markedFindHash pp l e msg base 0
    MAX_RANDOMIZER_TRIALS)

@[expose] noncomputable def guardedOts (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) :
    Selected pp (Option (Randomizer × Vector Digest V)) := do
  let some (rho, x) ← guardedFind pp l e msg | return none
  let ys ← liftM (simulateQ (selection pp l).liftQuery (beforeValues pp l e x >>= fun _ =>
    revealValues e x))
  return some (rho, ys)

attribute [local irreducible] chainValues randomizerBase Xmss.Internal.findCodeword
  beforeValues revealValues selection selectedImpl graphPrf simulateQ Xmss.build Xmss.path

private theorem ots (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    SameCap pp (simulateQ (selectedImpl pp) (markedOts pp l e msg)) (guardedOts pp l e msg) := by
  unfold markedOts guardedOts guardedFind
  simp only [simulateQ_bind, selected_base, bind_assoc]
  apply SameCap.bind (fun _ _ => rfl)
  intro base
  apply SameCap.bind (fun _ _ => rfl)
  rintro (_ | ⟨rho, x⟩)
  · rw [simulateQ_pure]
    exact fun _ _ => rfl
  · simp only [simulateQ_bind, simulateQ_pure]
    have transfer := selected_values pp l e x
    rw [simulateQ_bind] at transfer
    exact transfer.bind (fun _ _ _ => rfl)

@[expose] noncomputable def guardedTop (pp : PublicParam) (e : Nat) (bytes : ByteArray) :
    Selected pp (Except XmssError LayerSignature) := do
  let some (rho, ys) ← guardedOts pp .top (UInt32.ofNat e) bytes
    | return .error (.noAdmissibleEncoding .top e)
  return .ok ⟨rho, ys, ← liftM (pathSchedule pp .top e)⟩

private theorem top (pp : PublicParam) (e : Nat) (msg : ByteArray) :
    SameCap pp (simulateQ (selectedImpl pp) (markedLayer pp e msg)) (guardedTop pp e msg) := by
  unfold markedLayer guardedTop
  simp only [simulateQ_bind]
  apply SameCap.bind (ots pp .top _ msg)
  rintro (_ | ⟨rho, ys⟩)
  · rw [simulateQ_pure]
    exact fun _ _ => rfl
  · simp only [simulateQ_bind, simulateQ_pure]
    exact (selected_path pp .top e).bind (fun _ _ _ => rfl)

@[expose] noncomputable def guardedTree (pp : PublicParam) (idx : LeafIndex) :
    Selected pp (Except XmssError (Vector Digest LAYER_HEIGHT × LayerSignature)) := do
  let root ← liftM (bottomRootSchedule pp idx)
  match ← guardedTop pp (bottomTree idx) (packBytes root) with
  | .error err => return .error err
  | .ok sig => return .ok (← liftM (bottomPathSchedule pp idx), sig)

attribute [local irreducible] builtPathSchedule guardedTop beforeNode revealPath

private theorem tree (pp : PublicParam) (idx : LeafIndex) :
    SameCap pp (do
      let t ← simulateQ (selectedImpl pp) (build markedChainHash pp phasePrf .bottom LAYER_HEIGHT
        (bottomTree idx))
      let ans ← simulateQ (selectedImpl pp) (markedLayer pp (bottomTree idx) (packBytes t.value))
      return ans.map (fun top => (t.path LAYER_HEIGHT idx.toNat, top))) (guardedTree pp idx) := by
  let next := fun (pair : Digest × Vector Digest LAYER_HEIGHT) => do
    let ans ← simulateQ (selectedImpl pp) (markedLayer pp (bottomTree idx) (packBytes pair.1))
    return ans.map (fun t => (pair.2, t))
  have first := (selected_built pp idx).bind (f := next) (g := next) (fun _ _ _ => rfl)
  simp only [bind_map_left, next] at first
  apply first.trans
  unfold builtPathSchedule
  simp only [simulateQ_bind, simulateQ_pure, liftM_bind, liftM_pure, bind_assoc, pure_bind]
  refine (SameCap.trans ?_ (delayed_selected_path pp idx (fun root =>
    guardedTop pp (bottomTree idx) (packBytes root)))).trans ?_
  · simp only [bottomRootSchedule, bottomPathSchedule, simulateQ_bind, liftM_bind, bind_assoc]
    apply SameCap.bind (fun _ _ => rfl)
    intro _
    apply SameCap.bind (fun _ _ => rfl)
    intro root
    apply SameCap.bind (fun _ _ => rfl)
    intro path
    exact (top pp _ _).bind (fun _ _ _ => rfl)
  · unfold guardedTree
    apply SameCap.bind (fun _ _ => rfl)
    intro root
    apply SameCap.bind (fun _ _ => rfl)
    rintro (_ | val) _ _ <;> rfl

/-- The full signer keeps each physical finder and releases the lower values only on success. -/
@[expose] noncomputable def guardedSignature (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    Selected pp (Except XmssError Signature) := do
  let e := UInt32.ofNat idx.toNat
  let some (rho, x) ← guardedFind pp .bottom e (packBytes msg)
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  let sel := selection pp .bottom
  liftM (simulateQ sel.liftQuery (beforeValues pp .bottom e x))
  match ← guardedTree pp idx with
  | .error err => return .error err
  | .ok upper =>
    let ys ← liftM (simulateQ sel.liftQuery (revealValues e x))
    return .ok (packSignature idx rho ys upper)

private theorem after_values (pp : PublicParam) (idx : LeafIndex) (rho : Randomizer)
    (ys : Vector Digest V) :
    SameCap pp (do
      let tree ← simulateQ (selectedImpl pp)
        (build markedChainHash pp phasePrf .bottom LAYER_HEIGHT (bottomTree idx))
      match ← simulateQ (selectedImpl pp) (markedLayer pp (bottomTree idx)
        (packBytes tree.value)) with
      | .error err => return .error err
      | .ok top => return .ok (packSignature idx rho ys (tree.path LAYER_HEIGHT idx.toNat, top)))
      (do let upper ← guardedTree pp idx; return upper.map (packSignature idx rho ys)) := by
  have h := (tree pp idx).bind (f := fun ans => pure (ans.map (packSignature idx rho ys)))
    (g := fun ans => pure (ans.map (packSignature idx rho ys))) (fun _ _ _ => rfl)
  apply SameCap.trans _ h
  simp only [bind_assoc, pure_bind]
  apply SameCap.bind (fun _ _ => rfl)
  intro root
  apply SameCap.bind (fun _ _ => rfl)
  rintro (_ | val) _ _ <;> rfl

/-- The native single-build signing program agrees on all four tables, budget and raw answer. -/
theorem guarded_signature (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    SameCap pp (simulateQ (selectedImpl pp) (simulateQ (mark IsTrial)
      (signDerived (hashOf sourcePass) sourcePrf pp idx msg))) (guardedSignature pp idx msg) := by
  rw [marked_signature_native]
  let middle := do
    let some (rho, ys) ← guardedOts pp .bottom (UInt32.ofNat idx.toNat) (packBytes msg)
      | return Except.error (.noAdmissibleEncoding .bottom idx.toNat)
    let tree ← guardedTree pp idx
    return tree.map (packSignature idx rho ys)
  have first : SameCap pp (simulateQ (selectedImpl pp) (markedSignature pp idx msg)) middle := by
    unfold markedSignature middle
    simp only [simulateQ_bind]
    apply SameCap.bind (ots pp .bottom _ _)
    rintro (_ | ⟨rho, ys⟩)
    · rw [simulateQ_pure]
      exact fun _ _ => rfl
    · simp only [simulateQ_bind]
      apply SameCap.trans _ (after_values pp idx rho ys)
      apply SameCap.bind (fun _ _ => rfl)
      intro tree
      apply SameCap.bind (fun _ _ => rfl)
      rintro (_ | top) <;> rw [simulateQ_pure] <;> exact fun _ _ => rfl
  apply first.trans
  unfold middle guardedOts guardedSignature
  simp only [bind_assoc]
  apply SameCap.bind (fun _ _ => rfl)
  rintro (_ | ⟨rho, x⟩)
  · exact fun _ _ => rfl
  · simp only [simulateQ_bind, liftM_bind, bind_assoc, pure_bind]
    apply (delayed_selected_values pp idx rho x (guardedTree pp idx)).trans
    apply SameCap.bind (fun _ _ => rfl)
    intro _
    apply SameCap.bind (fun _ _ => rfl)
    rintro (_ | top) _ _ <;> rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
