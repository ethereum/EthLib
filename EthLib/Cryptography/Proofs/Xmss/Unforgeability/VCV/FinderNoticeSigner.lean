module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNotice

/-!
# Signing notices for the normalized two-layer signer

The first attempt at a key precedes its private randomizer query, including on failure.

Only a complete successful signature records the selected bottom and top digests.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp TwoLayerGraph
    Honest LayerGraph.Hidden

/-- Emit a notice and retain the full randomizer and finder result. -/
@[expose] noncomputable def find (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    Program pp (Option (Randomizer × Vector (Fin CHAIN_LENGTH) V)) := do
  emit (.attempt l e msg)
  carry (mixedFind pp l e msg)

@[simp] theorem forget_find (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    forget (find pp l e msg) = mixedFind pp l e msg := by simp [find]

/-- After upper selection, only the returned chain and sibling cells remain to be read. -/
@[expose] noncomputable def afterUpper (pp : PublicParam) (idx : LeafIndex)
    (lower upper : ByteArray) (rho tau : Randomizer) (x y : Vector (Fin CHAIN_LENGTH) V) :
    Program pp (Except XmssError Signature) := do
  let e := UInt32.ofNat idx.toNat
  let j := bottomTree idx
  let tops ← carry (emitted emitStructure pp (simulateQ (selection pp .top).liftQuery
    (beforeValues pp .top (UInt32.ofNat j) y >>= fun _ => revealValues (UInt32.ofNat j) y)))
  let auth ← carry (emitted emitStructure pp (pathSchedule pp .top j))
  let bottom ← carry (emitted emitStructure pp (bottomPathSchedule pp idx))
  let ys ← carry (emitted emitStructure pp (simulateQ (selection pp .bottom).liftQuery
    (revealValues e x)))
  emit (selectedNotice pp .bottom e lower rho x)
  emit (selectedNotice pp .top (UInt32.ofNat j) upper tau y)
  return .ok (packSignature idx rho ys (bottom, ⟨tau, tops, auth⟩))

/-- The upper finder uses the bottom root computed after the lower finder returned. -/
@[expose] noncomputable def afterLower (pp : PublicParam) (idx : LeafIndex)
    (lower : ByteArray) (rho : Randomizer) (x : Vector (Fin CHAIN_LENGTH) V) :
    Program pp (Except XmssError Signature) := do
  let e := UInt32.ofNat idx.toNat
  let sel := selection pp .bottom
  carry (emitted emitStructure pp (simulateQ sel.liftQuery (beforeValues pp .bottom e x)))
  let root ← carry (emitted emitStructure pp (bottomRootSchedule pp idx))
  let j := bottomTree idx
  let upper := packBytes root
  let some (tau, y) ← find pp .top (UInt32.ofNat j) upper
    | return .error (.noAdmissibleEncoding .top j)
  afterUpper pp idx lower upper rho tau x y

/-- Both finder calls retain their actual message and digit vector up to the successful reply. -/
@[expose] noncomputable def signature (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    Program pp (Except XmssError Signature) := do
  let lower := packBytes msg
  let some (rho, x) ← find pp .bottom (UInt32.ofNat idx.toNat) lower
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  afterLower pp idx lower rho x

@[simp] theorem forget_map {pp : PublicParam} {α β : Type} (f : α → β) (p : Program pp α) :
    forget (f <$> p) = f <$> forget p := by
  simp only [map_eq_pure_bind, forget_bind, forget_pure]

private theorem bind_eq {m : Type → Type} [Monad m] {α β : Type} {p : m α}
    {f g : α → m β} (same : ∀ a, f a = g a) : (p >>= f) = (p >>= g) := by
  rw [funext same]

attribute [local irreducible] mixedFind emitStructure beforeValues revealValues pathSchedule

/-- The observer sees the same signer, including both raw finder errors and all private state. -/
theorem forget_signature (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    forget (signature pp idx msg) = mixedSignature emitStructure pp idx msg := by
  unfold signature afterLower afterUpper mixedSignature mixedTree mixedTop mixedOts
  simp only [forget_bind, forget_find, bind_assoc]
  apply bind_eq
  rintro (_ | ⟨rho, x⟩)
  · simp
  · simp only [forget_bind, forget_find, forget_carry]
    apply bind_eq
    intro _
    apply bind_eq
    intro root
    apply bind_eq
    rintro (_ | ⟨tau, y⟩)
    · simp
    · simp

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
