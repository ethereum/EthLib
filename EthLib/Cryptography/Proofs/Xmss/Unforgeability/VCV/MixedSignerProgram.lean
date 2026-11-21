module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LocalSignature
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedFree
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedCalls

/-!
# A normalized signer in the physical mixed query language

Recursive structural programs are interpreted as internal graph operations.

The public full-word port carries only the original message digest trials.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig OracleComp OracleSpec Constants TwoLayerGraph Honest
open LayerGraph.Hidden

/-- The computations that touch and reveal the honest tree, in the mixed query language. -/
abbrev Structural := ∀ {a : Type}, OracleComp SharedSpec a → OracleComp MixedWorld a

noncomputable abbrev emitted (emit : Structural) (pp : PublicParam) {α : Type}
    (op : OracleComp SharedSpec α) : MixedLocal pp α := liftM (emit op)

@[expose] noncomputable def mixedFind (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) :
    MixedLocal pp (Option (Randomizer × Vector (Fin CHAIN_LENGTH) V)) := do
  let base ← mixedRandomizer pp l e msg
  liftM (Xmss.Internal.findCodeword mixedHash pp l e msg (halfOf 0 base) 0 MAX_RANDOMIZER_TRIALS)

@[expose] noncomputable def mixedOts (emit : Structural) (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) : MixedLocal pp (Option (Randomizer × Vector Digest V)) := do
  let some (rho, x) ← mixedFind pp l e msg | return none
  let ys ← emitted emit pp (simulateQ (selection pp l).liftQuery (beforeValues pp l e x >>=
      fun _ => revealValues e x))
  return some (rho, ys)

@[expose] noncomputable def mixedTop (emit : Structural) (pp : PublicParam)
    (e : Nat) (msg : ByteArray) :
    MixedLocal pp (Except XmssError LayerSignature) := do
  let some (rho, ys) ← mixedOts emit pp .top (UInt32.ofNat e) msg
    | return .error (.noAdmissibleEncoding .top e)
  return .ok ⟨rho, ys, ← emitted emit pp (pathSchedule pp .top e)⟩

@[expose] noncomputable def mixedTree (emit : Structural) (pp : PublicParam) (idx : LeafIndex) :
    MixedLocal pp (Except XmssError (Vector Digest LAYER_HEIGHT × LayerSignature)) := do
  let root ← emitted emit pp (bottomRootSchedule pp idx)
  match ← mixedTop emit pp (bottomTree idx) (packBytes root) with
  | .error err => return .error err
  | .ok top => return .ok (← emitted emit pp (bottomPathSchedule pp idx), top)

@[expose] noncomputable def mixedSignature (emit : Structural) (pp : PublicParam)
    (idx : LeafIndex) (msg : Message) :
    MixedLocal pp (Except XmssError Signature) := do
  let e := UInt32.ofNat idx.toNat
  let some (rho, x) ← mixedFind pp .bottom e (packBytes msg)
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  let sel := selection pp .bottom
  emitted emit pp (simulateQ sel.liftQuery (beforeValues pp .bottom e x))
  match ← mixedTree emit pp idx with
  | .error err => return .error err
  | .ok top =>
    let ys ← emitted emit pp (simulateQ sel.liftQuery (revealValues e x))
    return .ok (packSignature idx rho ys top)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
