/- Authors: Matthias Meijers -/

module

public import EthereumXMSSHypertree.EpochSignature
public import EthereumXMSSHypertree.HypertreeCoordinates
public import HashSig.GXMSS.Hypertree.Scheme

/-!
# Actual two-layer hypertree signature representation

At a coherent fixed outer epoch the complete source signature is equivalent to
the reviewed generic signature's bottom component and its single upper component.
Both layer randomizers, all chain values and both leaf-first paths are retained.
-/

public section

namespace EthereumXMSSHypertree.ConcreteHypertree

open EthLib.Cryptography.Xmss

/-- The source public-key fields are exactly the actual generic root and public seed. -/
@[expose]
def publicKeyToGeneric (pk : PublicKey) : GXMSS.PublicKey PublicParam Digest :=
  ⟨pk.root, pk.publicParam⟩

/-- Recover the source public-key field names from the actual generic public key. -/
@[expose]
def publicKeyToSource (pk : GXMSS.PublicKey PublicParam Digest) : PublicKey := ⟨pk.root, pk.seed⟩

/-- The complete source and generic public-key domains are equivalent. -/
@[expose]
def genericPublicKeyEquiv : PublicKey ≃ GXMSS.PublicKey PublicParam Digest where
  toFun := publicKeyToGeneric
  invFun := publicKeyToSource
  left_inv pk := by cases pk; rfl
  right_inv pk := by cases pk; rfl

/-- The source's complete layer fields are the actual generic component-signature fields. -/
@[expose]
def componentSignatureEquiv :
    LayerSignatureRepresentation ≃ GXMSS.Signature Randomizer Digest shape.h shape.v where
  toFun fields := ⟨fields.1, fields.2.1, fields.2.2⟩
  invFun sig := (sig.randomizer, sig.ots, sig.path)
  left_inv fields := by cases fields; rfl
  right_inv sig := by cases sig; rfl

/-- The two source layers are the actual bottom and unique upper signature components. -/
@[expose]
def signatureLayersEquiv :
    (LayerSignatureRepresentation × LayerSignatureRepresentation) ≃
      GXMSS.Hypertree.Signature Randomizer Digest shape where
  toFun layers := ⟨componentSignatureEquiv layers.1, fun _ => componentSignatureEquiv layers.2⟩
  invFun sig := (componentSignatureEquiv.symm sig.bottom,
    componentSignatureEquiv.symm (sig.upper ⟨0, by decide⟩))
  left_inv layers := by
    simp only [Equiv.symm_apply_apply]
  right_inv sig := by
    simp only [Equiv.apply_symm_apply]
    cases sig with
    | mk bottom upper =>
      congr 1
      funext i
      have hi : i = ⟨0, by decide⟩ := by
        apply Fin.ext
        have := i.isLt
        change i.val < 1 at this
        omega
      rw [hi]

/-- The exact source-signature bijection at one fixed coherent external epoch. -/
@[expose]
def sourceSignatureEquiv (epoch : Epoch) :
    {sig : Signature // leafIndexEquiv sig.leafIndex = epoch} ≃
      GXMSS.Hypertree.Signature Randomizer Digest shape :=
  (sourceSignatureAtEpochEquiv epoch).trans signatureLayersEquiv

/-- Read the two source layers into the actual generic signature representation. -/
@[expose]
def signatureToGeneric (sig : Signature) : GXMSS.Hypertree.Signature Randomizer Digest shape :=
  signatureLayersEquiv (stripSourceSignature sig)

/-- Reconstruct the embedded source index from the external epoch and both generic layers. -/
@[expose]
def signatureToSource (epoch : Epoch)
    (sig : GXMSS.Hypertree.Signature Randomizer Digest shape) : Signature :=
  packSourceSignature epoch (signatureLayersEquiv.symm sig)

/-- Reconstructed source signatures have exactly the requested external epoch. -/
@[simp]
theorem signatureToSource_coherent (epoch : Epoch)
    (sig : GXMSS.Hypertree.Signature Randomizer Digest shape) :
    leafIndexEquiv (signatureToSource epoch sig).leafIndex = epoch :=
  packSourceSignature_coherent epoch _

/-- Converting a generic signature to the source and back preserves all signature fields. -/
@[simp]
theorem signatureToGeneric_signatureToSource (epoch : Epoch)
    (sig : GXMSS.Hypertree.Signature Randomizer Digest shape) :
    signatureToGeneric (signatureToSource epoch sig) = sig := by
  simp [signatureToGeneric, signatureToSource]

/-- Converting a coherent source signature to the generic representation and back is exact. -/
theorem signatureToSource_signatureToGeneric (epoch : Epoch) (sig : Signature)
    (coherent : leafIndexEquiv sig.leafIndex = epoch) :
    signatureToSource epoch (signatureToGeneric sig) = sig := by
  simp only [signatureToSource, signatureToGeneric, Equiv.symm_apply_apply]
  exact packSourceSignature_stripSourceSignature epoch sig coherent

/-- The bottom component keeps the source's complete layer representation. -/
@[simp]
theorem signatureToGeneric_bottom (sig : Signature) :
    (signatureToGeneric sig).bottom = componentSignatureEquiv (layerSignatureEquiv sig.bottom) :=
  rfl

/-- The unique upper component keeps the source's complete top layer representation. -/
@[simp]
theorem signatureToGeneric_upper (sig : Signature) (i : Fin (shape.d - 1)) :
    (signatureToGeneric sig).upper i = componentSignatureEquiv (layerSignatureEquiv sig.top) := rfl

end EthereumXMSSHypertree.ConcreteHypertree
