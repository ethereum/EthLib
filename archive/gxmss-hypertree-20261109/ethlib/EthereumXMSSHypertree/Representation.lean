/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trail of Bits
-/

module
public import EthereumXMSSHypertree.Coordinates

/-!
# Exact concrete representations of source keys and signatures

These products describe the source's concrete domains. They keep both layer
randomizers, all 58 chain values in each layer, the leaf-first paths, and the
signature's embedded index. They do not instantiate a generic GXMSS interface.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- Source public-key fields, in root/public-parameter order. -/
abbrev PublicKeyRepresentation := Digest × PublicParam

/-- Source layer fields with their original chain and leaf-first path indices. -/
abbrev LayerSignatureRepresentation :=
  Randomizer × (Fin V → Digest) × (Fin LAYER_HEIGHT → Digest)

/-- Source full-signature fields, retaining the embedded epoch before both layers. -/
abbrev SignatureRepresentation :=
  Epoch × LayerSignatureRepresentation × LayerSignatureRepresentation

/-- Exact representation of the source public-key domain. -/
@[expose] def publicKeyEquiv : PublicKey ≃ PublicKeyRepresentation where
  toFun pk := (pk.root, pk.publicParam)
  invFun p := ⟨p.1, p.2⟩
  left_inv pk := by cases pk; rfl
  right_inv p := by cases p; rfl

/-- Exact representation of a source layer signature, with no field omitted. -/
@[expose] def layerSignatureEquiv : LayerSignature ≃ LayerSignatureRepresentation where
  toFun sig := (sig.randomizer, (fun i => sig.chainValues[i]), fun i => sig.path[i])
  invFun p := ⟨p.1, Vector.ofFn p.2.1, Vector.ofFn p.2.2⟩
  left_inv sig := by
    have hc : Vector.ofFn (fun i : Fin V => sig.chainValues[i]) = sig.chainValues := by
      apply Vector.ext
      intro i hi
      simp
    have hp : Vector.ofFn (fun i : Fin LAYER_HEIGHT => sig.path[i]) = sig.path := by
      apply Vector.ext
      intro i hi
      simp
    change LayerSignature.mk sig.randomizer _ _ = sig
    rw [hc, hp]
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        simp
      · funext i
        simp

/-- Exact representation of the source signature domain, including its index. -/
@[expose] def signatureEquiv : Signature ≃ SignatureRepresentation where
  toFun sig :=
    (leafIndexEquiv sig.leafIndex, layerSignatureEquiv sig.bottom, layerSignatureEquiv sig.top)
  invFun p :=
    ⟨leafIndexEquiv.symm p.1, layerSignatureEquiv.symm p.2.1,
      layerSignatureEquiv.symm p.2.2⟩
  left_inv sig := by
    simp only [Equiv.symm_apply_apply]
  right_inv p := by
    simp only [Equiv.apply_symm_apply]

/-- The public-key root is preserved verbatim. -/
@[simp] theorem publicKeyEquiv_root (pk : PublicKey) : (publicKeyEquiv pk).1 = pk.root := rfl

/-- The public parameter is preserved verbatim. -/
@[simp] theorem publicKeyEquiv_publicParam (pk : PublicKey) :
    (publicKeyEquiv pk).2 = pk.publicParam := rfl

/-- A layer randomizer is preserved verbatim. -/
@[simp] theorem layerSignatureEquiv_randomizer (sig : LayerSignature) :
    (layerSignatureEquiv sig).1 = sig.randomizer := rfl

/-- Every one of the 58 revealed chain values keeps its source index. -/
@[simp] theorem layerSignatureEquiv_chainValues (sig : LayerSignature) (i : Fin V) :
    (layerSignatureEquiv sig).2.1 i = sig.chainValues[i] := rfl

/-- Every authentication sibling keeps its source leaf-first position. -/
@[simp] theorem layerSignatureEquiv_path (sig : LayerSignature) (i : Fin LAYER_HEIGHT) :
    (layerSignatureEquiv sig).2.2 i = sig.path[i] := rfl

/-- The full representation preserves the original embedded index. -/
@[simp] theorem signatureEquiv_epoch (sig : Signature) :
    (signatureEquiv sig).1 = leafIndexEquiv sig.leafIndex := rfl

/-- The bottom randomizer is retained in its own layer. -/
@[simp] theorem signatureEquiv_bottom_randomizer (sig : Signature) :
    (signatureEquiv sig).2.1.1 = sig.bottom.randomizer := rfl

/-- The top randomizer is retained in its own layer. -/
@[simp] theorem signatureEquiv_top_randomizer (sig : Signature) :
    (signatureEquiv sig).2.2.1 = sig.top.randomizer := rfl

/-- Decoding a representation reconstructs its original embedded numerical index. -/
@[simp] theorem signatureEquiv_symm_leafIndex_toNat (p : SignatureRepresentation) :
    (signatureEquiv.symm p).leafIndex.toNat = p.1.val :=
  leafIndexEquiv_symm_toNat p.1

/-- Source verification at an outer epoch checks the embedded source index first. -/
@[expose] def verifyAtEpochWith {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pk : PublicKey) (e : Epoch)
    (msg : Message) (sig : Signature) : m Bool :=
  if leafIndexEquiv sig.leafIndex = e then verifyWith H pk msg sig else pure false

/-- Matching epochs pass the original source signature to its verifier unchanged. -/
theorem verifyAtEpochWith_eq {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pk : PublicKey) (e : Epoch)
    (msg : Message) (sig : Signature) (h : leafIndexEquiv sig.leafIndex = e) :
    verifyAtEpochWith H pk e msg sig = verifyWith H pk msg sig := by
  simp [verifyAtEpochWith, h]

/-- An embedded index mismatch is rejected before source verification. -/
theorem verifyAtEpochWith_mismatch {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pk : PublicKey) (e : Epoch)
    (msg : Message) (sig : Signature) (h : leafIndexEquiv sig.leafIndex ≠ e) :
    verifyAtEpochWith H pk e msg sig = pure false := by
  simp [verifyAtEpochWith, h]

/-- A numerical mismatch of the original source index rejects at an outer epoch. -/
theorem verifyAtEpochWith_index_mismatch {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pk : PublicKey) (e : Epoch)
    (msg : Message) (sig : Signature) (h : sig.leafIndex.toNat ≠ e.val) :
    verifyAtEpochWith H pk e msg sig = pure false := by
  apply verifyAtEpochWith_mismatch
  exact fun he => h ((leafIndexEquiv_eq_iff sig.leafIndex e).mp he)

/-- A reconstructed signature is checked at the epoch its representation carries. -/
theorem verifyAtEpochWith_signatureEquiv_symm {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pk : PublicKey)
    (msg : Message) (p : SignatureRepresentation) :
    verifyAtEpochWith H pk p.1 msg (signatureEquiv.symm p) =
      verifyWith H pk msg (signatureEquiv.symm p) := by
  apply verifyAtEpochWith_eq
  exact leafIndexEquiv.apply_symm_apply p.1

end EthereumXMSSHypertree
