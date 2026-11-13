/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import EthereumXMSSHypertree.HypertreeCorrespondence

/-!
# All-input source recovery and verification

The actual reviewed hypertree verifier is compared with source recovery on complete arbitrary
signature fields, preserving every returned decoder failure.
-/

public section

namespace EthereumXMSSHypertree.HypertreeCorrespondence

open EthLib.Cryptography Xmss Xmss.Constants
open ConcreteHypertree HypertreeStrategies HypertreePRF

/-- A source layer root is the exact optional decoder output followed by source recovery. -/
private theorem source_layerRoot_map (H : Pure.Hash) (pp : PublicParam) (layer : Layer)
    (index : Nat) (msg : ByteArray) (sig : LayerSignature) :
    Pure.layerRoot H pp layer index msg sig =
      (codeword? (Pure.messageHash H pp layer (UInt32.ofNat index) msg sig.randomizer)).map
        (fun (digits : Vector (Fin CHAIN_LENGTH) V) => Pure.climb H pp layer 0 index
          (Pure.leafHash H pp layer (UInt32.ofNat index) (Vector.ofFn fun i =>
            Pure.chain H pp layer (UInt32.ofNat index) i (digits[i] : Fin CHAIN_LENGTH).val
              (CHAIN_LENGTH - 1 - (digits[i] : Fin CHAIN_LENGTH).val)
              (by have := digits[i].isLt; omega)
              sig.chainValues[i])) sig.path.toList) := by
  cases hd : codeword? (Pure.messageHash H pp layer (UInt32.ofNat index) msg sig.randomizer) with
  | none => simp only [Pure.layerRoot, Pure.otsLeaf, hd, Option.map_none]
  | some digits => simp only [Pure.layerRoot, Pure.otsLeaf, hd, Option.map_some]

/-- The generic word representation with the source decoder's own constant-indexed domain. -/
private def sourceWord (digits : Vector (Fin CHAIN_LENGTH) V) :
    GXMSS.Encoding.Codeword shape.v (2 ^ shape.w) := GenericEncoding.sourceCodewordEquiv digits

/-- Coordinate-indexed generic component recovery preserves arbitrary source signature data. -/
theorem recoverComponent_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (pp : PublicParam)
    (position : GXMSS.Hypertree.OTSPosition shape)
    (message : GXMSS.Hypertree.Message shape Message Digest position)
    (sig : GXMSS.Signature Randomizer Digest shape.h shape.v) :
    GXMSS.Hypertree.recoverComponent (hashInstance H seedGen) (sourceEncodingFamily H)
      pp position message sig =
      Pure.layerRoot H pp (sourceLayer position.1) (globalIndex position)
        (sourceMessageBytes position message) (componentToSource sig) := by
  rw [GXMSS.Hypertree.recoverComponent, sourceEncodingFamily_value_source, source_layerRoot_map]
  change Option.bind ((codeword? ((messageDigest (pureHash H) pp (sourceLayer position.1)
    (sourceKey position) (sourceMessageBytes position message) sig.randomizer).run)).map
      sourceWord) (fun word => some (((hashInstance H seedGen).componentHash position.1).recoverRoot
        pp position.2 (fun i => ((hashInstance H seedGen).componentHash position.1).chain pp
          position.2 i (word i).val (2 ^ shape.w - 1 - (word i).val) (sig.ots i)) sig.path)) = _
  rw [Option.bind_map, Option.map_eq_bind]
  apply congrArg (Option.bind (codeword? (Pure.messageHash H pp
    (sourceLayer position.1) (sourceKey position) (sourceMessageBytes position message)
    sig.randomizer)))
  funext digits
  dsimp only [Function.comp_apply]
  rw [component_recover_eq]
  have hc : (fun i => ((hashInstance H seedGen).componentHash position.1).chain pp position.2 i
      (sourceWord digits i)
      (2 ^ shape.w - 1 - (sourceWord digits i).val) (sig.ots i)) =
      (fun i => Pure.chain H pp (sourceLayer position.1) (sourceKey position) i
        (digits[i] : Fin CHAIN_LENGTH).val
        (CHAIN_LENGTH - 1 - (digits[i] : Fin CHAIN_LENGTH).val)
        (by have := digits[i].isLt; omega) (sig.ots i)) := by
    funext i
    exact component_chain_eq H seedGen pp position.1 position.2 i (digits[i] : Fin CHAIN_LENGTH).val
      (CHAIN_LENGTH - 1 - (digits[i] : Fin CHAIN_LENGTH).val)
      (by have := digits[i].isLt; omega) (sig.ots i)
  rw [hc]
  have hv (i : Fin V) : (componentToSource sig).chainValues[i] = sig.ots i := by
    change (Vector.ofFn sig.ots)[i.val] = sig.ots i
    exact Vector.getElem_ofFn i.isLt
  have hp : (componentToSource sig).path.toList = List.ofFn sig.path := by
    change (Vector.ofFn sig.path).toList = List.ofFn sig.path
    exact Vector.toList_ofFn
  simp_rw [hv]
  rw [hp]
  simp only [sourceKey, globalIndex]


/-- Full two-layer recovery preserves both source decoder failures on arbitrary signatures. -/
theorem recoverRoot_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (pp : PublicParam)
    (msg : Message) (sig : Signature) :
    GXMSS.Hypertree.recoverRoot (hashInstance H seedGen) (sourceEncodingFamily H) pp
      (sourceEpoch sig.leafIndex) msg (signatureToGeneric sig) =
      (Pure.layerRoot H pp .bottom sig.leafIndex.toNat (packBytes msg) sig.bottom).bind
        (fun root => Pure.layerRoot H pp .top (bottomTree sig.leafIndex)
          (packBytes root) sig.top) := by
  change (GXMSS.Hypertree.recoverComponent (hashInstance H seedGen) (sourceEncodingFamily H)
    pp (GXMSS.Hypertree.bottomPosition shape (sourceEpoch sig.leafIndex))
      (GXMSS.Hypertree.bottomMessage _ msg) (signatureToGeneric sig).bottom >>= fun root =>
    GXMSS.Hypertree.recoverComponent (hashInstance H seedGen) (sourceEncodingFamily H) pp
      (GXMSS.Hypertree.upperPositionAt shape (sourceEpoch sig.leafIndex) ⟨0, by decide⟩).1
      (GXMSS.Hypertree.internalMessage
        (GXMSS.Hypertree.upperPositionAt shape (sourceEpoch sig.leafIndex) ⟨0, by decide⟩) root)
      ((signatureToGeneric sig).upper ⟨0, by decide⟩)) = _
  simp only [recoverComponent_eq, sourceMessageBytes_bottom, sourceMessageBytes_internal]
  have hb : componentToSource (signatureToGeneric sig).bottom = sig.bottom :=
    componentToSource_toGeneric sig.bottom
  have ht : componentToSource ((signatureToGeneric sig).upper ⟨0, by decide⟩) = sig.top :=
    componentToSource_toGeneric sig.top
  rw [hb, ht]
  have bottomLayer : sourceLayer
      (GXMSS.Hypertree.bottomPosition shape (sourceEpoch sig.leafIndex)).1 = .bottom := rfl
  have topLayer : sourceLayer
      (GXMSS.Hypertree.upperPositionAt shape (sourceEpoch sig.leafIndex)
        ⟨0, by decide⟩).1.1 = .top := rfl
  rw [bottomLayer, topLayer]
  change (Pure.layerRoot H pp .bottom
    (globalIndex (GXMSS.Hypertree.positionAt shape (sourceEpoch sig.leafIndex) 0))
      (packBytes msg) sig.bottom >>= fun root => Pure.layerRoot H pp .top
        (globalIndex (GXMSS.Hypertree.positionAt shape (sourceEpoch sig.leafIndex) 1))
        (packBytes root) sig.top) = _
  rw [positionAt_bottom_globalIndex, positionAt_top_globalIndex]
  rfl

/-- The actual reviewed verifier agrees on every complete source signature representation. -/
theorem source_verify_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (pk : PublicKey)
    (msg : Message) (sig : Signature) :
    GXMSS.Hypertree.verify (hashInstance H seedGen) (sourceEncodingFamily H)
      (publicKeyToGeneric pk) (sourceEpoch sig.leafIndex) msg (signatureToGeneric sig) =
      Pure.verify H pk msg sig := by
  rw [GXMSS.Hypertree.verify, recoverRoot_eq]
  change decide (((Pure.layerRoot H pk.publicParam .bottom sig.leafIndex.toNat
    (packBytes msg) sig.bottom).bind (fun root => Pure.layerRoot H pk.publicParam .top
      (bottomTree sig.leafIndex) (packBytes root) sig.top)) = some pk.root) = _
  cases hb : Pure.layerRoot H pk.publicParam .bottom sig.leafIndex.toNat
      (packBytes msg) sig.bottom with
  | none => simp only [Pure.verify, hb, Option.bind_none, reduceCtorEq, decide_false]
  | some bottom =>
    cases ht : Pure.layerRoot H pk.publicParam .top (bottomTree sig.leafIndex)
        (packBytes bottom) sig.top with
    | none => simp only [Pure.verify, hb, ht, Option.bind_some, reduceCtorEq, decide_false]
    | some root => simp only [Pure.verify, hb, ht, Option.bind_some, Option.some.injEq]

end EthereumXMSSHypertree.HypertreeCorrespondence
