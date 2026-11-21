module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedSignerRoles
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerDelayed
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# The native two-layer signer with explicit physical roles

The lower and upper finders use the charged port.

Both chains, the lower tree and the upper authentication path use the free port.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig OracleComp OracleSpec Constants TwoLayerGraph.Honest

noncomputable abbrev phasePrf (p : PublicParam) (a : Address) (b : ByteArray) :=
  simulateQ (mark IsTrial) (sourcePrf p a b)

/-- The private derivation port is identical in an unmarked phase. -/
theorem phasePrf_free (p : PublicParam) (a : Address) (b : ByteArray) :
    phasePrf p a b = simulateQ (mark (fun _ => False)) (sourcePrf p a b) := by
  simp [phasePrf, sourcePrf, mark]

/-- The one-time signature obtains its codeword before making any structural query. -/
@[expose] noncomputable def markedOts (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) :
    OracleComp Marked (Option (Randomizer × Vector Digest V)) := do
  let base ← randomizerBase pp phasePrf l e msg
  let some (rho, x) ← Xmss.Internal.findCodeword markedFindHash pp l e msg base
      0 MAX_RANDOMIZER_TRIALS
    | return none
  let ys ← chainValues markedChainHash phasePrf pp l e x
  return some (rho, ys)

private theorem ots_roles (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    otsSign signingHash pp phasePrf l e msg = markedOts pp l e msg := by
  unfold otsSign Internal.otsSignTrials markedOts
  simp only [signing_finder]
  apply bind_congr
  intro _
  apply bind_congr
  rintro (_ | ⟨rho, x⟩)
  · rfl
  · simp only [chainValues, signing_chain, bind_assoc]

@[expose] noncomputable def markedLayer (pp : PublicParam) (e : Nat) (msg : ByteArray) :
    OracleComp Marked (Except XmssError LayerSignature) := do
  let some (rho, ys) ← markedOts pp .top (UInt32.ofNat e) msg
    | return .error (.noAdmissibleEncoding .top e)
  return .ok ⟨rho, ys, ← path markedChainHash pp phasePrf .top e⟩

private theorem layer_roles (pp : PublicParam) (e : Nat) (msg : ByteArray) :
    signLayer signingHash pp phasePrf .top e msg = markedLayer pp e msg := by
  unfold signLayer markedLayer
  rw [ots_roles]
  apply bind_congr
  rintro (_ | ⟨rho,x⟩)
  · rfl
  · rw [signing_path]

/-- This is the complete source program of one signing request after its selected parameter. -/
@[expose] noncomputable def markedSignature (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    OracleComp Marked (Except XmssError Signature) := do
  let some (rho, ys) ← markedOts pp .bottom (UInt32.ofNat idx.toNat) (packBytes msg)
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  let tree ← build markedChainHash pp phasePrf .bottom LAYER_HEIGHT (bottomTree idx)
  match ← markedLayer pp (bottomTree idx) (packBytes tree.value) with
  | .error err => return .error err
  | .ok top => return .ok (packSignature idx rho ys (tree.path LAYER_HEIGHT idx.toNat, top))

attribute [local irreducible] Xmss.build signLayer markedLayer otsSign markedOts

theorem marked_signature_native (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    simulateQ (mark IsTrial) (signDerived (hashOf sourcePass) sourcePrf pp idx msg) =
      markedSignature pp idx msg := by
  rw [signDerived_map_monad (fun {_} p => simulateQ (mark IsTrial) p) (fun _ => simulateQ_pure _ _)
    (fun _ _ => simulateQ_bind _ _ _)]
  change signDerived signingHash phasePrf pp idx msg = _
  unfold signDerived markedSignature
  rw [ots_roles]
  apply bind_congr
  rintro (_ | ⟨rho,ys⟩)
  · rfl
  · rw [signing_build]
    apply bind_congr
    intro tree
    rw [layer_roles]
    apply bind_congr
    rintro (_ | top) <;> rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
