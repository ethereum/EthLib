/- Authors: Matthias Meijers -/

module

public import EthereumXMSSHypertree.HypertreeCorrespondence

/-!
# Source signing in the reviewed generic hypertree

The component equations use the exact source counter output, chain prefixes and
leaf-first authentication path. Returned encoding exhaustion remains optional
failure throughout the source-to-generic signature observation.
-/

public section

namespace EthereumXMSSHypertree.HypertreeSigning

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants
open ConcreteHypertree HypertreeStrategies HypertreePRF HypertreeCorrespondence

/-- Explicit source chain material in the actual reviewed forest secret-key record. -/
@[expose]
def sourceSecretMaterial {Coins : Type} (hash : Pure.Hash) (seedGen : ProbComp PublicParam)
    (pp : PublicParam) (prf : Pure.Derivation)
    (coins : GXMSS.Hypertree.UpperPosition shape → Coins) :
    GXMSS.Hypertree.SecretKey PublicParam Digest Coins shape :=
  ⟨pp, sourceStarts pp prf, GXMSS.Hypertree.endpoints (hashInstance hash seedGen) pp
    (sourceStarts pp prf), coins⟩

private def sourceWord (digits : Vector (Fin CHAIN_LENGTH) V) :
    GXMSS.Encoding.Codeword shape.v (2 ^ shape.w) := GenericEncoding.sourceCodewordEquiv digits

private theorem layerSignature_ofFn (randomizer : Randomizer) (values : Fin V → Digest)
    (path : Vector Digest LAYER_HEIGHT) :
    componentSignatureEquiv (layerSignatureEquiv ⟨randomizer, Vector.ofFn values, path⟩) =
      GXMSS.Signature.mk randomizer values (fun z => path[z]) := by
  change GXMSS.Signature.mk randomizer (fun i => (Vector.ofFn values)[i]) _ = _
  apply congrArg₂ (GXMSS.Signature.mk randomizer)
  · funext i
    exact Vector.getElem_ofFn i.isLt
  · rfl

/-- Materializing one successful word retains exactly the source chain reveals and path. -/
theorem componentSignature_eq_source {Coins : Type} (hash : Pure.Hash)
    (seedGen : ProbComp PublicParam) (pp : PublicParam) (prf : Pure.Derivation)
    (coins : GXMSS.Hypertree.UpperPosition shape → Coins)
    (position : GXMSS.Hypertree.OTSPosition shape) (digits : Vector (Fin CHAIN_LENGTH) V)
    (randomizer : Randomizer) :
    GXMSS.Hypertree.componentSignature (hashInstance hash seedGen)
      (sourceSecretMaterial hash seedGen pp prf coins) position
      (GenericEncoding.sourceCodewordEquiv digits, randomizer) =
      componentSignatureEquiv (layerSignatureEquiv
        ⟨randomizer, Vector.ofFn (fun i => Pure.chain hash pp (sourceLayer position.1)
          (sourceKey position) i 0 digits[i] (by simp)
            (Pure.starts pp prf (sourceLayer position.1) (sourceKey position))[i]),
          Pure.path hash pp prf (sourceLayer position.1) (globalIndex position)⟩) := by
  change GXMSS.Hypertree.componentSignature (hashInstance hash seedGen)
    (sourceSecretMaterial hash seedGen pp prf coins) position (sourceWord digits, randomizer) = _
  have hchain :
      (fun i => ((hashInstance hash seedGen).componentHash position.1).chain pp position.2 i
        0 (sourceWord digits i).val (sourceStarts pp prf position i)) =
      (fun i => Pure.chain hash pp (sourceLayer position.1) (sourceKey position) i
        0 (digits[i] : Fin CHAIN_LENGTH).val (by simp [CHAIN_LENGTH])
        (Pure.starts pp prf (sourceLayer position.1) (sourceKey position))[i]) := by
    funext i
    exact component_chain_eq hash seedGen pp position.1 position.2 i 0
      (digits[i] : Fin CHAIN_LENGTH).val (by simp [CHAIN_LENGTH]) _
  have hpath := component_path_eq hash seedGen pp prf position.1 position.2
  rw [layerSignature_ofFn]
  change GXMSS.Signature.mk randomizer _ _ = GXMSS.Signature.mk randomizer _ _
  exact congrArg₂ (GXMSS.Signature.mk randomizer) hchain hpath

/-- The source layer's exact optional signature is the materialized actual generic retry result. -/
theorem componentSign_eq_source {Coins : Type} (hash : Pure.Hash)
    (seedGen : ProbComp PublicParam) (pp : PublicParam) (prf : Pure.Derivation)
    (coins : GXMSS.Hypertree.UpperPosition shape → Coins)
    (position : GXMSS.Hypertree.OTSPosition shape)
    (message : GXMSS.Hypertree.Message shape Message Digest position) :
    (GXMSS.Hypertree.componentResult (sourceEncodingFamily hash) sourceRetryPlan
      (sourceSecretMaterial hash seedGen pp prf coins) position message
        (Pure.randomizerBase pp prf (sourceLayer position.1) (sourceKey position)
          (sourceMessageBytes position message))).output.map
      (GXMSS.Hypertree.componentSignature (hashInstance hash seedGen)
        (sourceSecretMaterial hash seedGen pp prf coins) position) =
      (Pure.signLayer hash pp prf (sourceLayer position.1) (globalIndex position)
        (sourceMessageBytes position message)).toOption.map
          (fun sig => componentSignatureEquiv (layerSignatureEquiv sig)) := by
  change (sourceRetryPlan.run
    ((sourceEncodingFamily hash).atEpoch position (Fin shape.branching)) pp message position.2
      (Pure.randomizerBase pp prf (sourceLayer position.1) (sourceKey position)
        (sourceMessageBytes position message))).output.map _ = _
  rw [sourceRetryPlan_output, Option.map_map]
  change (Pure.search hash pp (sourceLayer position.1) (sourceKey position)
    (sourceMessageBytes position message)
    (Pure.randomizerBase pp prf (sourceLayer position.1) (sourceKey position)
      (sourceMessageBytes position message))).map _ = _
  cases hs : Pure.search hash pp (sourceLayer position.1) (sourceKey position)
      (sourceMessageBytes position message)
      (Pure.randomizerBase pp prf (sourceLayer position.1) (sourceKey position)
        (sourceMessageBytes position message)) with
  | none =>
    change Pure.search hash pp (sourceLayer position.1) (UInt32.ofNat (globalIndex position))
      (sourceMessageBytes position message)
      (Pure.randomizerBase pp prf (sourceLayer position.1) (UInt32.ofNat (globalIndex position))
        (sourceMessageBytes position message)) = none at hs
    simp [Pure.signLayer, Pure.otsSign, hs, Except.toOption]
  | some result =>
    rcases result with ⟨randomizer, digits⟩
    change Pure.search hash pp (sourceLayer position.1) (UInt32.ofNat (globalIndex position))
      (sourceMessageBytes position message)
      (Pure.randomizerBase pp prf (sourceLayer position.1) (UInt32.ofNat (globalIndex position))
        (sourceMessageBytes position message)) = some (randomizer, digits) at hs
    simp only [Option.map_some, Function.comp_apply]
    rw [componentSignature_eq_source]
    simp [Pure.signLayer, Pure.otsSign, sourceKey, hs, Except.toOption]

/-- The exact fixed source child root certified by one complete upper signing coordinate. -/
@[expose]
def certifiedRoot (hash : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (position : GXMSS.Hypertree.UpperPosition shape) : Digest :=
  Pure.node hash pp prf (sourceLayer (GXMSS.Hypertree.childTree shape position))
    16 (GXMSS.Hypertree.childTree shape position).2.val

/-- Fixed source upper coins derive from the key's immutable child-root message. -/
@[expose]
def sourceUpperCoins (hash : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (position : GXMSS.Hypertree.UpperPosition shape) : Randomizer :=
  Pure.randomizerBase pp prf (sourceLayer position.val.1) (sourceKey position.val)
    (packBytes (certifiedRoot hash pp prf position))

/-- The actual derived secret material is the full source forest with its fixed source bases. -/
theorem coreSecretKey_eq_sourceMaterial (hash : Pure.Hash) (seedGen : ProbComp PublicParam)
    (raw : Seed) :
    let prf := Pure.derivedResponse hash (Pure.schemeSeed hash raw)
    let pp := Pure.publicParam prf
    GXMSS.Hypertree.PRFDerived.coreSecretKey (hashInstance hash seedGen) .pairedCounter
      sourceRetrySampling (sourceEvaluator hash) sourceInterpretation
        sourceRetryInterpretation raw =
      sourceSecretMaterial hash seedGen pp prf (sourceUpperCoins hash pp prf) := by
  let prf := Pure.derivedResponse hash (Pure.schemeSeed hash raw)
  let pp := Pure.publicParam prf
  have hpp : GXMSS.Hypertree.PRFDerived.publicSeed (sourceEvaluator hash)
      sourceInterpretation raw = pp := publicSeed_eq_pure hash raw
  have hstarts : GXMSS.Hypertree.PRFDerived.starts .pairedCounter
      (GXMSS.Hypertree.PRFDerived.retryBudget sourceRetrySampling)
      (sourceEvaluator hash) sourceInterpretation raw pp = sourceStarts pp prf := by
    funext position i
    exact starts_eq_source hash raw pp position i
  dsimp only
  simp only [GXMSS.Hypertree.PRFDerived.coreSecretKey]
  rw [hpp, hstarts]
  apply congrArg (fun coins => sourceSecretMaterial hash seedGen pp prf coins)
  funext position
  rw [component_root_eq, internalCoins_eq_source]
  rfl

/-- A fixed reviewed certificate has the exact optional source layer signature at its child root. -/
theorem certificate_eq_source (hash : Pure.Hash) (seedGen : ProbComp PublicParam)
    (pp : PublicParam) (prf : Pure.Derivation) (position : GXMSS.Hypertree.UpperPosition shape) :
    GXMSS.Hypertree.certificate (hashInstance hash seedGen) (sourceEncodingFamily hash)
      sourceRetryPlan (sourceSecretMaterial hash seedGen pp prf (sourceUpperCoins hash pp prf))
        position =
      (Pure.signLayer hash pp prf (sourceLayer position.val.1) (globalIndex position.val)
        (packBytes (certifiedRoot hash pp prf position))).toOption.map
          (fun sig => componentSignatureEquiv (layerSignatureEquiv sig)) := by
  unfold GXMSS.Hypertree.certificate GXMSS.Hypertree.certificateResult
  dsimp only [sourceSecretMaterial]
  rw [component_root_eq]
  have hcomponent := componentSign_eq_source hash seedGen pp prf (sourceUpperCoins hash pp prf)
    position.val (GXMSS.Hypertree.internalMessage position (certifiedRoot hash pp prf position))
  simpa only [sourceMessageBytes_internal, sourceSecretMaterial, sourceUpperCoins, certifiedRoot]
    using hcomponent

private theorem upperIndex_eq_zero (i : Fin (shape.d - 1)) : i = ⟨0, by decide⟩ := by
  apply Fin.ext
  change i.val = 0
  have hi := i.isLt
  change i.val < 1 at hi
  omega

/-- The unique upper certificate signs the source root of the selected bottom tree. -/
theorem certifiedRoot_at_epoch (hash : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (idx : LeafIndex) (i : Fin (shape.d - 1)) :
    certifiedRoot hash pp prf (GXMSS.Hypertree.upperPositionAt shape (sourceEpoch idx) i) =
      Pure.node hash pp prf .bottom LAYER_HEIGHT (bottomTree idx) := by
  have hi := upperIndex_eq_zero i
  subst i
  have hchild : GXMSS.Hypertree.childTree shape
      (GXMSS.Hypertree.upperPositionAt shape (sourceEpoch idx) ⟨0, by decide⟩) =
      (GXMSS.Hypertree.bottomPosition shape (sourceEpoch idx)).1 := by
    simpa [GXMSS.Hypertree.upperPositionAt, GXMSS.Hypertree.upperLayer,
      GXMSS.Hypertree.bottomPosition] using
      GXMSS.Hypertree.childTree_positionAt shape (sourceEpoch idx) ⟨1, by decide⟩ (by decide)
  unfold certifiedRoot
  rw [hchild]
  change Pure.node hash pp prf .bottom 16
    (GXMSS.Hypertree.positionAt shape (sourceEpoch idx) 0).1.2.val = _
  rw [positionAt_bottom_tree]
  rfl

/-- The bottom complete-coordinate source word equals the original signature index. -/
theorem sourceKey_bottomPosition (idx : LeafIndex) :
    sourceKey (GXMSS.Hypertree.bottomPosition shape (sourceEpoch idx)) = idx := by
  apply UInt32.toNat_inj.mp
  rw [sourceKey_toNat]
  exact positionAt_bottom_globalIndex idx

/-- Every upper array index selects the same source top signing key. -/
theorem globalIndex_upperPositionAt (idx : LeafIndex) (i : Fin (shape.d - 1)) :
    globalIndex (GXMSS.Hypertree.upperPositionAt shape (sourceEpoch idx) i).val =
      bottomTree idx := by
  have hi := upperIndex_eq_zero i
  subst i
  exact positionAt_top_globalIndex idx

/-- Every upper array index retains the source top layer tag. -/
theorem sourceLayer_upperPositionAt (idx : LeafIndex) (i : Fin (shape.d - 1)) :
    sourceLayer (GXMSS.Hypertree.upperPositionAt shape (sourceEpoch idx) i).val.1 = .top := by
  have hi := upperIndex_eq_zero i
  subst i
  rfl

private theorem sourceSigning_map (hash : Pure.Hash) (seedGen : ProbComp PublicParam)
    (sk : GXMSS.Hypertree.SecretKey PublicParam Digest Randomizer shape)
    (ep : GXMSS.Hypertree.Epoch shape) (message : Message) (base : Randomizer) :
    GXMSS.Hypertree.signWithCoins (hashInstance hash seedGen) (sourceEncodingFamily hash)
      sourceRetrySampling sk ep message base =
    (do
      let first ← (GXMSS.Hypertree.componentResult (sourceEncodingFamily hash) sourceRetryPlan sk
        (GXMSS.Hypertree.bottomPosition shape ep)
        (GXMSS.Hypertree.bottomMessage (H := Digest) ep message) base).output.map
          (GXMSS.Hypertree.componentSignature (hashInstance hash seedGen) sk
            (GXMSS.Hypertree.bottomPosition shape ep))
      let upper ← Fin.mOfFn (shape.d - 1) fun i =>
        GXMSS.Hypertree.certificate (hashInstance hash seedGen) (sourceEncodingFamily hash)
          sourceRetryPlan sk (GXMSS.Hypertree.upperPositionAt shape ep i)
      pure ⟨first, upper⟩) := by
  unfold GXMSS.Hypertree.signWithCoins
  change Option.bind _ _ = Option.bind (Option.map _ _) _
  rw [Option.bind_map]
  rfl

/-- Complete explicit-coin signing preserves both layer failures and all source signature fields. -/
theorem signWithCoins_eq_source (hash : Pure.Hash) (seedGen : ProbComp PublicParam)
    (pp : PublicParam) (prf : Pure.Derivation) (idx : LeafIndex) (message : Message) :
    GXMSS.Hypertree.signWithCoins (hashInstance hash seedGen) (sourceEncodingFamily hash)
      sourceRetrySampling
      (sourceSecretMaterial hash seedGen pp prf (sourceUpperCoins hash pp prf))
      (sourceEpoch idx) message (Pure.randomizerBase pp prf .bottom idx (packBytes message)) =
      (Pure.signDerived hash prf pp idx message).toOption.map signatureToGeneric := by
  let sk := sourceSecretMaterial hash seedGen pp prf (sourceUpperCoins hash pp prf)
  let bottom := GXMSS.Hypertree.bottomPosition shape (sourceEpoch idx)
  have hbottom := componentSign_eq_source hash seedGen pp prf (sourceUpperCoins hash pp prf)
    bottom (GXMSS.Hypertree.bottomMessage (H := Digest) (sourceEpoch idx) message)
  have hlayer : sourceLayer bottom.1 = .bottom := rfl
  have hglobal : globalIndex bottom = idx.toNat := positionAt_bottom_globalIndex idx
  dsimp only [bottom] at hbottom hlayer hglobal
  simp only [sourceMessageBytes_bottom, sourceKey_bottomPosition, hlayer, hglobal] at hbottom
  have hupper (i : Fin (shape.d - 1)) :
      GXMSS.Hypertree.certificate (hashInstance hash seedGen) (sourceEncodingFamily hash)
        sourceRetryPlan sk (GXMSS.Hypertree.upperPositionAt shape (sourceEpoch idx) i) =
      (Pure.signLayer hash pp prf .top (bottomTree idx)
        (packBytes (Pure.node hash pp prf .bottom LAYER_HEIGHT (bottomTree idx)))).toOption.map
          (fun sig => componentSignatureEquiv (layerSignatureEquiv sig)) := by
    rw [certificate_eq_source, sourceLayer_upperPositionAt, globalIndex_upperPositionAt,
      certifiedRoot_at_epoch]
  have hrewrite :
      GXMSS.Hypertree.signWithCoins (hashInstance hash seedGen) (sourceEncodingFamily hash)
        sourceRetrySampling sk (sourceEpoch idx) message
          (Pure.randomizerBase pp prf .bottom idx (packBytes message)) =
      (do
        let first ← (GXMSS.Hypertree.componentResult (sourceEncodingFamily hash) sourceRetryPlan sk
          bottom (GXMSS.Hypertree.bottomMessage (H := Digest) (sourceEpoch idx) message)
          (Pure.randomizerBase pp prf .bottom idx (packBytes message))).output.map
            (GXMSS.Hypertree.componentSignature (hashInstance hash seedGen) sk bottom)
        let upper ← Fin.mOfFn (shape.d - 1) fun i =>
          GXMSS.Hypertree.certificate (hashInstance hash seedGen) (sourceEncodingFamily hash)
            sourceRetryPlan sk (GXMSS.Hypertree.upperPositionAt shape (sourceEpoch idx) i)
        pure ⟨first, upper⟩) := by
    exact sourceSigning_map hash seedGen sk (sourceEpoch idx) message _
  rw [hrewrite, hbottom]
  simp_rw [hupper]
  cases hb : Pure.signLayer hash pp prf .bottom idx.toNat (packBytes message) with
  | error err => simp [Pure.signDerived, hb, Except.toOption]
  | ok bottomSig =>
    cases ht : Pure.signLayer hash pp prf .top (bottomTree idx)
        (packBytes (Pure.node hash pp prf .bottom LAYER_HEIGHT (bottomTree idx))) with
    | error err => simp [Pure.signDerived, hb, ht, Except.toOption, Fin.mOfFn]
    | ok topSig =>
      simp only [Except.toOption, Option.map_some, Nat.add_one_sub_one, Fin.mOfFn,
        Nat.reduceAdd, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Pure.signDerived, hb, ht, Option.some.injEq]
      change (⟨componentSignatureEquiv (layerSignatureEquiv bottomSig),
        Fin.cons (componentSignatureEquiv (layerSignatureEquiv topSig)) Fin.elim0⟩ :
        GXMSS.Hypertree.Signature Randomizer Digest shape) =
        ⟨componentSignatureEquiv (layerSignatureEquiv bottomSig),
          fun _ => componentSignatureEquiv (layerSignatureEquiv topSig)⟩
      apply congrArg (GXMSS.Hypertree.Signature.mk
        (componentSignatureEquiv (layerSignatureEquiv bottomSig)))
      funext i
      rw [upperIndex_eq_zero i]
      rfl

/-- The actual reviewed PRF-derived signer is the exact optional pure source signer. -/
theorem source_sign_eq (hash : Pure.Hash) (seedGen : ProbComp PublicParam) (raw : Seed)
    (idx : LeafIndex) (message : Message) :
    GXMSS.Hypertree.PRFDerived.sign (hashInstance hash seedGen) (sourceEncodingFamily hash)
      .pairedCounter sourceRetrySampling (sourceEvaluator hash) sourceInterpretation
      sourceRetryInterpretation raw (sourceEpoch idx) message =
      pure ((Pure.sign hash ⟨raw⟩ idx message).map signatureToGeneric) := by
  unfold GXMSS.Hypertree.PRFDerived.sign
  rw [coreSecretKey_eq_sourceMaterial]
  have hcoins : GXMSS.Hypertree.PRFDerived.bottomCoins .pairedCounter sourceRetrySampling
      (sourceEvaluator hash) sourceInterpretation sourceRetryInterpretation raw
      (sourceEpoch idx) message =
      Pure.randomizerBase (Pure.publicParam (Pure.derivedResponse hash (Pure.schemeSeed hash raw)))
        (Pure.derivedResponse hash (Pure.schemeSeed hash raw)) .bottom idx (packBytes message) := by
    unfold GXMSS.Hypertree.PRFDerived.bottomCoins
    change sourceInterpretation.retryRandomizer (sourceEvaluator hash raw
      (.retry _ (GXMSS.Hypertree.bottomPosition shape (sourceEpoch idx))
        (GXMSS.Hypertree.bottomMessage (H := Digest) (sourceEpoch idx) message) ())) = _
    rw [retryBase_eq_source, publicSeed_eq_pure, sourceMessageBytes_bottom,
      sourceKey_bottomPosition]
    rfl
  rw [hcoins]
  exact congrArg pure (signWithCoins_eq_source hash seedGen _ _ idx message)

end EthereumXMSSHypertree.HypertreeSigning
