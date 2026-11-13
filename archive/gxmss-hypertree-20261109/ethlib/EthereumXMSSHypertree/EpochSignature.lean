/-
Copyright (c) 2026 Matthias Meijers.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.Representation

/-!
# Source signatures at a fixed outer epoch

The source signature carries its own index. At a fixed coherent outer epoch, its
remaining data are exactly the bottom and top layer representations. Packing
reconstructs the embedded index from that epoch. The resulting bijection retains
both randomizers, every revealed chain value and both leaf-first paths.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- The two complete layer representations of a source signature, in bottom/top order. -/
@[expose]
def stripSourceSignature (sig : Signature) :
    LayerSignatureRepresentation × LayerSignatureRepresentation :=
  (signatureEquiv sig).2

/-- Pack the two source layers, reconstructing the embedded index from the outer epoch. -/
@[expose]
def packSourceSignature (epoch : Epoch)
    (layers : LayerSignatureRepresentation × LayerSignatureRepresentation) : Signature :=
  signatureEquiv.symm (epoch, layers)

/-- Packing reconstructs precisely the source word represented by the outer epoch. -/
@[simp]
theorem packSourceSignature_leafIndex (epoch : Epoch)
    (layers : LayerSignatureRepresentation × LayerSignatureRepresentation) :
    (packSourceSignature epoch layers).leafIndex = leafIndexEquiv.symm epoch := rfl

/-- Every packed source signature is coherent with its outer epoch. -/
@[simp]
theorem packSourceSignature_coherent (epoch : Epoch)
    (layers : LayerSignatureRepresentation × LayerSignatureRepresentation) :
    leafIndexEquiv (packSourceSignature epoch layers).leafIndex = epoch :=
  leafIndexEquiv.apply_symm_apply epoch

/-- Stripping retains the complete bottom layer. -/
@[simp]
theorem stripSourceSignature_bottom (sig : Signature) :
    (stripSourceSignature sig).1 = layerSignatureEquiv sig.bottom := rfl

/-- Stripping retains the complete top layer. -/
@[simp]
theorem stripSourceSignature_top (sig : Signature) :
    (stripSourceSignature sig).2 = layerSignatureEquiv sig.top := rfl

/-- Stripping a packed signature recovers both complete layer representations. -/
@[simp]
theorem stripSourceSignature_packSourceSignature (epoch : Epoch)
    (layers : LayerSignatureRepresentation × LayerSignatureRepresentation) :
    stripSourceSignature (packSourceSignature epoch layers) = layers := by
  change (signatureEquiv (signatureEquiv.symm (epoch, layers))).2 = layers
  rw [Equiv.apply_symm_apply]

/-- Packing a coherent signature's layers recovers that exact source signature. -/
theorem packSourceSignature_stripSourceSignature (epoch : Epoch) (sig : Signature)
    (coherent : leafIndexEquiv sig.leafIndex = epoch) :
    packSourceSignature epoch (stripSourceSignature sig) = sig := by
  apply signatureEquiv.injective
  change signatureEquiv (signatureEquiv.symm (epoch, (signatureEquiv sig).2)) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact coherent.symm
  · rfl

/-- Coherent source signatures at one outer epoch are exactly their two complete layers. -/
@[expose]
def sourceSignatureAtEpochEquiv (epoch : Epoch) :
    {sig : Signature // leafIndexEquiv sig.leafIndex = epoch} ≃
      LayerSignatureRepresentation × LayerSignatureRepresentation where
  toFun sig := stripSourceSignature sig.val
  invFun layers := ⟨packSourceSignature epoch layers, packSourceSignature_coherent epoch layers⟩
  left_inv sig := Subtype.ext (packSourceSignature_stripSourceSignature epoch sig.val sig.property)
  right_inv layers := stripSourceSignature_packSourceSignature epoch layers

/-- At a fixed coherent epoch, stripping cannot identify different source signatures. -/
theorem stripSourceSignature_injective_at_epoch (epoch : Epoch) (first second : Signature)
    (hfirst : leafIndexEquiv first.leafIndex = epoch)
    (hsecond : leafIndexEquiv second.leafIndex = epoch)
    (hlayers : stripSourceSignature first = stripSourceSignature second) : first = second := by
  calc
    first = packSourceSignature epoch (stripSourceSignature first) :=
      (packSourceSignature_stripSourceSignature epoch first hfirst).symm
    _ = packSourceSignature epoch (stripSourceSignature second) := congrArg _ hlayers
    _ = second := packSourceSignature_stripSourceSignature epoch second hsecond

/-- At a fixed coherent epoch, layer equality is exact source-signature equality. -/
theorem stripSourceSignature_eq_iff (epoch : Epoch) (first second : Signature)
    (hfirst : leafIndexEquiv first.leafIndex = epoch)
    (hsecond : leafIndexEquiv second.leafIndex = epoch) :
    stripSourceSignature first = stripSourceSignature second ↔ first = second :=
  ⟨stripSourceSignature_injective_at_epoch epoch first second hfirst hsecond,
    congrArg stripSourceSignature⟩

/-- The message/signature equality used for strong freshness is exact at a coherent fixed epoch. -/
theorem message_stripSourceSignature_eq_iff (epoch : Epoch)
    (firstMessage secondMessage : Message) (first second : Signature)
    (hfirst : leafIndexEquiv first.leafIndex = epoch)
    (hsecond : leafIndexEquiv second.leafIndex = epoch) :
    (firstMessage, stripSourceSignature first) = (secondMessage, stripSourceSignature second) ↔
      (firstMessage, first) = (secondMessage, second) := by
  constructor
  · intro h
    apply Prod.ext
    · exact congrArg (fun pair : Message ×
        (LayerSignatureRepresentation × LayerSignatureRepresentation) => pair.1) h
    · exact stripSourceSignature_injective_at_epoch epoch first second hfirst hsecond
        (congrArg (fun pair : Message ×
          (LayerSignatureRepresentation × LayerSignatureRepresentation) => pair.2) h)
  · intro h
    exact congrArg (fun pair : Message × Signature => (pair.1, stripSourceSignature pair.2)) h

/-- Equal packed source signatures have the same outer epoch and the same layer data. -/
theorem packSourceSignature_eq_iff (epoch otherEpoch : Epoch)
    (layers otherLayers : LayerSignatureRepresentation × LayerSignatureRepresentation) :
    packSourceSignature epoch layers = packSourceSignature otherEpoch otherLayers ↔
      epoch = otherEpoch ∧ layers = otherLayers := by
  constructor
  · intro h
    have hrepr := congrArg signatureEquiv h
    change signatureEquiv (signatureEquiv.symm (epoch, layers)) =
      signatureEquiv (signatureEquiv.symm (otherEpoch, otherLayers)) at hrepr
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hrepr
    exact ⟨congrArg Prod.fst hrepr, congrArg Prod.snd hrepr⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A packed source signature passes the outer-epoch coherence check before source verification. -/
theorem verifyAtEpochWith_packSourceSignature {m : Type → Type} [Monad m]
    (hash : ByteArray → m (Vector UInt8 32)) (pk : PublicKey) (epoch : Epoch)
    (msg : Message) (layers : LayerSignatureRepresentation × LayerSignatureRepresentation) :
    verifyAtEpochWith hash pk epoch msg (packSourceSignature epoch layers) =
      verifyWith hash pk msg (packSourceSignature epoch layers) :=
  verifyAtEpochWith_eq hash pk epoch msg _ (packSourceSignature_coherent epoch layers)

/-- An unchanged coherent source signature is rejected at every different outer epoch. -/
theorem verifyAtEpochWith_relabel_reject {m : Type → Type} [Monad m]
    (hash : ByteArray → m (Vector UInt8 32)) (pk : PublicKey) (epoch otherEpoch : Epoch)
    (msg : Message) (sig : Signature) (coherent : leafIndexEquiv sig.leafIndex = epoch)
    (different : epoch ≠ otherEpoch) :
    verifyAtEpochWith hash pk otherEpoch msg sig = pure false := by
  apply verifyAtEpochWith_mismatch
  simpa only [coherent] using different

end EthereumXMSSHypertree
