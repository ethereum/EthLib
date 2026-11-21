module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LocalTree

/-!
# The two-layer signer with its residual derivation state

Both successful finders must run before the bottom chain values are disclosed.

The upper finder can use state left by the lower randomizer even when it returns an error.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open EthLib.Cryptography OracleComp OracleSpec HashSig Constants LayerGraph.Hidden

variable {R : Type}
local notation "LH" => (fun b => (liftM (hash b) : WithLocal R (Vector UInt8 32)))

private abbrev PairBase := Layer → SeedPrf (OracleComp SharedSpec)

/-- The lower signer reveals chain values only after its bounded finder succeeds. -/
@[expose] noncomputable def localReleased (pp : PublicParam) (cb : SeedPrf (WithLocal R))
    (idx : LeafIndex) (msg : Message) : WithLocal R (Except XmssError Signature) := do
  let e := UInt32.ofNat idx.toNat
  let bytes := packBytes msg
  let rnd ← randomizerBase pp cb .bottom e bytes
  let some (rho, x) ← liftM (Xmss.Internal.findCodeword hash pp .bottom e bytes
      rnd 0 MAX_RANDOMIZER_TRIALS)
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  let v := selection pp .bottom
  liftM (simulateQ v.liftQuery (beforeValues pp .bottom e x))
  match ← localTree pp cb idx with
  | .error err => return .error err
  | .ok b =>
    let ys ← liftM (simulateQ v.liftQuery (revealValues e x))
    return .ok (packSignature idx rho ys b)

attribute [local irreducible] Xmss.build Xmss.signLayer Xmss.Internal.findCodeword localLayer
  beforeValues revealValues localTree

private theorem after_values (pp : PublicParam) (cb : SeedPrf (WithLocal R)) (base : PairBase)
    (pairs : ∀ l, LocalPairs pp l cb (base l)) (selected : ∀ l, Pairs pp l (base l))
    (idx : LeafIndex) (rho : Randomizer) (ys : Vector Digest V) :
    SameLocal pp (do
      let tree ← Xmss.build LH pp cb .bottom LAYER_HEIGHT (bottomTree idx)
      let top ← match ← signLayer LH pp cb .top (bottomTree idx) (packBytes tree.value) with
        | .ok sig => pure sig
        | .error err => return .error err
      return .ok (⟨idx, ⟨rho, ys, tree.path LAYER_HEIGHT idx.toNat⟩, top⟩ : Signature))
      (do let answer ← localTree pp cb idx; return answer.map (packSignature idx rho ys)) := by
  let native := (build_layer_local pp cb base pairs selected idx).bind
    (f := fun answer => pure (answer.map (packSignature idx rho ys)))
    (g := fun answer => pure (answer.map (packSignature idx rho ys))) (fun _ _ => rfl)
  refine (SameLocal.trans ?_ native)
  simp only [bind_assoc, pure_bind]
  apply SameLocal.bind (fun _ => rfl)
  intro tree
  apply SameLocal.bind (fun _ => rfl)
  rintro (_ | top) _ <;> rfl

/-- Both native randomizer calls and both complete local tables survive the replacement.

The graph law holds for every initial local and graph state. -/
theorem signDerived_local (pp : PublicParam) (cb : SeedPrf (WithLocal R))
    (base : Layer → SeedPrf (OracleComp SharedSpec)) (pairs : ∀ l, LocalPairs pp l cb (base l))
    (selected : ∀ l, Pairs pp l (base l)) (idx : LeafIndex) (msg : Message) :
    SameLocal pp (signDerived LH cb pp idx msg) (localReleased pp cb idx msg) := by
  let native := do
    let some (rho, ys) ← localOts pp cb .bottom (UInt32.ofNat idx.toNat) (packBytes msg)
      | return Except.error (.noAdmissibleEncoding .bottom idx.toNat)
    let answer ← localTree pp cb idx
    return answer.map (packSignature idx rho ys)
  have first : SameLocal pp (signDerived LH cb pp idx msg) native := by
    unfold signDerived native
    apply SameLocal.bind (ots_local pp cb .bottom (base .bottom) (pairs .bottom)
      (selected .bottom) _ _)
    rintro (_ | ⟨rho, ys⟩)
    · exact fun _ => rfl
    · exact after_values pp cb base pairs selected idx rho ys
  apply first.trans
  unfold native localReleased localOts
  simp only [bind_assoc]
  apply SameLocal.bind (fun _ => rfl)
  intro rnd
  apply SameLocal.bind (fun _ => rfl)
  rintro (_ | ⟨rho, x⟩)
  · exact fun _ => rfl
  · simp only [simulateQ_bind, liftM_bind, bind_assoc, pure_bind]
    let e := UInt32.ofNat idx.toNat
    have delayed := delayLocal pp (simulateQ (selection pp .bottom).liftQuery
        (beforeValues pp .bottom e x))
      (simulateQ (selection pp .bottom).liftQuery (revealValues e x)) (fun _ => localTree pp cb idx)
      (packSignature idx rho) (stable_values pp .bottom e x)
    apply delayed.trans
    apply SameLocal.bind (fun _ => rfl)
    intro _
    apply SameLocal.bind (fun _ => rfl)
    rintro (_ | b) _ <;> rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
