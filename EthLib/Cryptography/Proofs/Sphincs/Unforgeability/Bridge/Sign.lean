module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Signature
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Landing
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Correctness

/-!
# Proofs: under fixed answers, EthLib's signer is the model's

Both signers compute the randomizer, the digest, the FORS openings and one signature per layer.

Both sign the layers from the bottom up, and they make different calls.

- EthLib derives `PK.seed` and `SK.prf` again and rebuilds the top tree on each request.
- EthLib computes each layer's message from scratch, and the model takes it from the layer below.
- The model makes one more digest call, for its randomizer search.

Under a fixed answer function each call is a value, whatever its order or repetition.

So under every answer function EthLib's signature is the model's, and both fail together.

The model signs with the secret key that its key generation returns under the same answers.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open OracleComp SphincsSecurity.Completeness
open SphincsSecurity.Concrete (sequenceFin)

variable (f : QueryImpl HashSig.HashSpec Id)

/-- A model layer signature, or its absence, as EthLib's result for that layer. -/
def toLayerResult (lay : SphincsSecurity.Layer) :
    Option (SphincsSecurity.LayerSignature lay) →
      Except SphincsError (LayerSignature (layerOf lay))
  | none => .error (.noAdmissibleEncoding (layerOf lay))
  | some s => .ok (ofLayerSignature lay s)

/-- Under fixed answers, a layer signs a message as the model's layer signs the same bytes.

The model's layer reads only the seed and `PK.seed` of its key. -/
theorem signLayer_answers (sk : SphincsSecurity.Seeded.SecretKey) (index : SphincsSecurity.Index)
    (lay : SphincsSecurity.Layer) (msg : Digest)
    (hmsg : msg.toList = layerMessageValue f sk index lay) :
    evalWithAnswerFn f (signLayer (queryH (m := OracleComp HashSig.HashSpec)) (ofParam sk.parameter)
        (secretsOf sk.seed sk.parameter) (layerOf lay) index.val msg)
      = toLayerResult lay (evalWithAnswerFn f
          (SphincsSecurity.Seeded.signLayer sk index lay : OracleComp HashSig.HashSpec _)) := by
  unfold signLayer
  rw [ofIndex_eq]
  simp only [SphincsSecurity.Seeded.signLayer, SphincsSecurity.Seeded.signLayerWith,
    evalWithAnswerFn_bind]
  rw [show evalWithAnswerFn f (SphincsSecurity.Seeded.layerMessage sk index lay
      : OracleComp HashSig.HashSpec _) = layerMessageValue f sk index lay from rfl,
    ← hmsg, otsSign_queryH, evalWithAnswerFn_map]
  cases evalWithAnswerFn f (SphincsSecurity.Seeded.otsSign sk.parameter lay
      (SphincsSecurity.Concrete.treeIndexAt index lay)
      (SphincsSecurity.Concrete.leafIndexAt index lay)
      sk.seed msg.toList : OracleComp HashSig.HashSpec _) with
  | none => rfl
  | some ots =>
    obtain ⟨counter, values⟩ := ots
    simp only [Option.map_some, ofOts, keyOf, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rw [path_queryH, evalWithAnswerFn_map, eval_sequenceFin, SphincsSecurity.Seeded.treePath,
      eval_sequenceFin]
    simp only [toLayerResult, ofLayerSignature, keptHeight_eq, Fin.is_lt, ↓reduceIte]
    rfl

/-- Under fixed answers, a layer's message is the model's: what the layer below it gives.

That is the FORS public key at the bottom, and the root of the tree below on higher layers. -/
theorem layerMessage_answers (sk : SphincsSecurity.Seeded.SecretKey)
    (index : SphincsSecurity.Index) (lay : SphincsSecurity.Layer) :
    evalWithAnswerFn f (layerMessage (queryH (m := OracleComp HashSig.HashSpec))
        (ofParam sk.parameter) (secretsOf sk.seed sk.parameter) (layerOf lay) index.val)
      = ofDigest (belowValue f sk index lay) := by
  obtain ⟨v, hv⟩ := lay
  change v < 3 at hv
  interval_cases v
  · -- The top key signs the root of the middle tree of the index.
    have hkey : (OtsKey.ofIndex .middle index.val).tree
        = (SphincsSecurity.Concrete.treeIndexAt index middleLayer).val :=
      congrArg OtsKey.tree (ofIndex_eq index middleLayer)
    have hroot : treeRoot (queryH (m := OracleComp HashSig.HashSpec)) (ofParam sk.parameter)
        (secretsOf sk.seed sk.parameter) .middle
        (SphincsSecurity.Concrete.treeIndexAt index middleLayer).val
        = ofDigest <$> SphincsSecurity.Seeded.treeRoot sk.parameter middleLayer
            (SphincsSecurity.Concrete.treeIndexAt index middleLayer) sk.seed :=
      treeRoot_queryH sk.seed sk.parameter middleLayer _
    rw [belowValue, dite_eq_left (show 0 + 1 < SphincsSecurity.numLayers by decide)]
    simp only [layerMessage, layerOf, hkey, hroot, evalWithAnswerFn_map]
  · -- The middle key signs the root of the bottom tree of the index.
    have hkey : (OtsKey.ofIndex .bottom index.val).tree
        = (SphincsSecurity.Concrete.treeIndexAt index bottomLayer).val :=
      congrArg OtsKey.tree (ofIndex_eq index bottomLayer)
    have hroot : treeRoot (queryH (m := OracleComp HashSig.HashSpec)) (ofParam sk.parameter)
        (secretsOf sk.seed sk.parameter) .bottom
        (SphincsSecurity.Concrete.treeIndexAt index bottomLayer).val
        = ofDigest <$> SphincsSecurity.Seeded.treeRoot sk.parameter bottomLayer
            (SphincsSecurity.Concrete.treeIndexAt index bottomLayer) sk.seed :=
      treeRoot_queryH sk.seed sk.parameter bottomLayer _
    rw [belowValue, dite_eq_left (show 1 + 1 < SphincsSecurity.numLayers by decide)]
    simp only [layerMessage, layerOf, hkey, hroot, evalWithAnswerFn_map]
  · -- The bottom key signs the FORS public key of the index.
    rw [belowValue, dite_eq_right (show ¬(2 + 1 < SphincsSecurity.numLayers) by decide)]
    exact forsKey_answers f sk.seed sk.parameter index

/-- The bytes of a layer's message are what the model's layer signs. -/
theorem toList_belowValue (sk : SphincsSecurity.Seeded.SecretKey) (index : SphincsSecurity.Index)
    (lay : SphincsSecurity.Layer) :
    (ofDigest (belowValue f sk index lay)).toList = layerMessageValue f sk index lay := by
  rw [toList_ofDigest, ← rootPayload_belowValue]
  rfl

attribute [local irreducible] SphincsSecurity.Seeded.signLayer SphincsSecurity.Seeded.forsOpen
  SphincsSecurity.Seeded.treePath SphincsSecurity.Seeded.treeNode sequenceFin
  SphincsSecurity.Seeded.forsKey SphincsSecurity.Seeded.treeRoot SphincsSecurity.Seeded.spineNode
  forsSign signLayer layerMessage

/-- One absent value makes the whole family absent. -/
theorem allSome_eq_none {n : Nat} {α : Fin n → Type} (values : (i : Fin n) → Option (α i))
    (i : Fin n) (h : values i = none) : allSome values = none :=
  dite_eq_right fun hall => by simpa [h] using hall i

/-- When the three layers' values are present, the family holds them. -/
theorem allSome_layers {α : SphincsSecurity.Layer → Type}
    (values : (lay : SphincsSecurity.Layer) → Option (α lay)) {top : α SphincsSecurity.topLayer}
    {middle : α middleLayer} {bottom : α bottomLayer}
    (htop : values SphincsSecurity.topLayer = some top) (hmiddle : values middleLayer = some middle)
    (hbottom : values bottomLayer = some bottom) :
    ∃ layers, allSome values = some layers ∧ layers SphincsSecurity.topLayer = top
      ∧ layers middleLayer = middle ∧ layers bottomLayer = bottom := by
  have hall : ∀ lay, (values lay).isSome := by
    rintro ⟨i, hi⟩
    change i < 3 at hi
    interval_cases i
    · exact (Option.isSome_iff_exists.2 ⟨_, htop⟩)
    · exact (Option.isSome_iff_exists.2 ⟨_, hmiddle⟩)
    · exact (Option.isSome_iff_exists.2 ⟨_, hbottom⟩)
  exact ⟨_, dite_eq_left hall, (Option.eq_some_iff_get_eq.1 htop).2,
    (Option.eq_some_iff_get_eq.1 hmiddle).2, (Option.eq_some_iff_get_eq.1 hbottom).2⟩

/-- Under fixed answers, the model signs with its first randomizer `rho`, at its digest's index.

It returns a signature exactly when every layer signs. -/
theorem eval_sign (sk : SphincsSecurity.Seeded.SecretKey) (msg : SphincsSecurity.Message)
    (rho : SphincsSecurity.Randomness)
    (hrho : (evalWithAnswerFn f (SphincsSecurity.deriveRandomizer sk.prf sk.parameter msg
      : OracleComp HashSig.HashSpec _)).1 = rho) :
    evalWithAnswerFn f (SphincsSecurity.Seeded.sign sk msg : OracleComp HashSig.HashSpec _)
      = (allSome fun lay => evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer sk
          (SphincsSecurity.Concrete.digestIndex (digestValue f sk msg rho)) lay
          : OracleComp HashSig.HashSpec _)).map fun layers =>
        ⟨rho, evalWithAnswerFn f (SphincsSecurity.Seeded.forsOpen sk.parameter
            (SphincsSecurity.Concrete.digestIndex (digestValue f sk msg rho))
            (SphincsSecurity.Concrete.digestLeaves (digestValue f sk msg rho)) sk.seed
            : OracleComp HashSig.HashSpec _), layers⟩ := by
  rw [SphincsSecurity.Seeded.sign, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    show SphincsSecurity.digestAttemptLimit = 2 ^ 32 - 1 + 1 from rfl, signDigestLoop_succ,
    evalWithAnswerFn_map, hrho]
  rw [evalWithAnswerFn_bind, show evalWithAnswerFn f (SphincsSecurity.Concrete.messageDigest
      sk.parameter sk.root msg rho : OracleComp HashSig.HashSpec _)
      = digestValue f sk msg rho from rfl]
  generalize digestValue f sk msg rho = digest
  -- The recovered FORS public key is the honest one, from which the layers thread up.
  simp only [evalWithAnswerFn_bind, eval_forsPublicKey_forsRecover]
  rw [eval_signLayers f sk _ (SphincsSecurity.landed_full _ _)]
  cases allSome fun lay => evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer sk
      (SphincsSecurity.Concrete.digestIndex digest) lay : OracleComp HashSig.HashSpec _) <;> rfl

/-- Under fixed answers, EthLib signs from a key's secrets, public key and randomizer as the model.

The randomizer is the model's, and the public key is the model's `PK.seed` and `PK.root`. -/
theorem signDerived_answers (sk : SphincsSecurity.Seeded.SecretKey)
    (msg : SphincsSecurity.Message) :
    Except.toOption (evalWithAnswerFn f (signDerived (queryH (m := OracleComp HashSig.HashSpec))
        (secretsOf sk.seed sk.parameter) (ofPublicKey ⟨sk.root, sk.parameter⟩)
        (ofRandomizer (evalWithAnswerFn f (SphincsSecurity.deriveRandomizer sk.prf sk.parameter
          msg : OracleComp HashSig.HashSpec _)).1) (ofMessage msg)))
      = Option.map ofSignature (evalWithAnswerFn f
          (SphincsSecurity.Seeded.sign sk msg : OracleComp HashSig.HashSpec _)) := by
  generalize hrho : (evalWithAnswerFn f (SphincsSecurity.deriveRandomizer sk.prf sk.parameter msg
    : OracleComp HashSig.HashSpec _)).1 = rho
  conv_rhs => rw [eval_sign f sk msg rho hrho]
  unfold signDerived
  simp only [ofPublicKey]
  rw [evalWithAnswerFn_bind, messageDigest_queryH (root := sk.root), evalWithAnswerFn_map,
    eval_sequenceFin]
  have hdigest : digestValue f sk msg rho
      = SphincsSecurity.truncateMessageDigest fun call =>
          evalWithAnswerFn f (SphincsSecurity.Concrete.messageDigestCall sk.parameter sk.root msg
            rho call) := by
    rw [digestValue, SphincsSecurity.Concrete.messageDigest, evalWithAnswerFn_bind,
      eval_sequenceFin, evalWithAnswerFn_pure]
  rw [hdigest]
  generalize (fun call => evalWithAnswerFn f
    (SphincsSecurity.Concrete.messageDigestCall sk.parameter sk.root msg rho call
      : OracleComp HashSig.HashSpec _)) = outs
  rw [digestIndex_ofOutputs, digestLeaves_ofOutputs]
  generalize SphincsSecurity.Concrete.digestIndex (SphincsSecurity.truncateMessageDigest outs)
    = index
  rw [evalWithAnswerFn_bind, forsSign_answers]
  generalize evalWithAnswerFn f (SphincsSecurity.Seeded.forsOpen sk.parameter index
    (SphincsSecurity.Concrete.digestLeaves (SphincsSecurity.truncateMessageDigest outs)) sk.seed
      : OracleComp HashSig.HashSpec _) = opening
  -- Each layer signs the model's message, so it signs as the model's layer does.
  have hlayer : ∀ lay : SphincsSecurity.Layer,
      evalWithAnswerFn f (signLayer (queryH (m := OracleComp HashSig.HashSpec))
        (ofParam sk.parameter) (secretsOf sk.seed sk.parameter) (layerOf lay) index.val
        (evalWithAnswerFn f (layerMessage (queryH (m := OracleComp HashSig.HashSpec))
          (ofParam sk.parameter) (secretsOf sk.seed sk.parameter) (layerOf lay) index.val)))
      = toLayerResult lay (evalWithAnswerFn f
          (SphincsSecurity.Seeded.signLayer sk index lay : OracleComp HashSig.HashSpec _)) :=
    fun lay => by
      rw [layerMessage_answers]
      exact signLayer_answers f sk index lay _ (toList_belowValue f sk index lay)
  have hb := hlayer bottomLayer
  have hm := hlayer middleLayer
  have ht := hlayer SphincsSecurity.topLayer
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind]
  erw [hb]
  cases hbottom : evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer sk index
      bottomLayer : OracleComp HashSig.HashSpec _) with
  | none =>
    rw [allSome_eq_none _ bottomLayer hbottom]
    rfl
  | some bottom =>
    dsimp only [toLayerResult]
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind]
    erw [hm]
    cases hmiddle : evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer sk index
        middleLayer : OracleComp HashSig.HashSpec _) with
    | none =>
      rw [allSome_eq_none _ middleLayer hmiddle]
      rfl
    | some middle =>
      dsimp only [toLayerResult]
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind]
      erw [ht]
      cases htop : evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer sk index
          SphincsSecurity.topLayer : OracleComp HashSig.HashSpec _) with
      | none =>
        rw [allSome_eq_none _ SphincsSecurity.topLayer htop]
        rfl
      | some top =>
        obtain ⟨layers, hlayers, htop', hmiddle', hbottom'⟩ := allSome_layers
          (fun lay => evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer sk index lay
            : OracleComp HashSig.HashSpec _)) htop hmiddle hbottom
        dsimp only [toLayerResult]
        rw [hlayers]
        simp only [Option.map_some, ofSignature, htop', hmiddle', hbottom']
        rfl

/-! ## The signer from the seed -/

/-- The model's public key of `PK.seed` and a root, which EthLib's key computes. -/
theorem publicKeyOf_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter) :
    publicKeyOf (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P) (secretsOf S P)
      = (fun root => ofPublicKey ⟨root, P⟩) <$> SphincsSecurity.Seeded.treeRoot P
          SphincsSecurity.topLayer SphincsSecurity.Concrete.rootTree S := by
  have hroot : treeRoot (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
      (secretsOf S P) .top 0
      = ofDigest <$> SphincsSecurity.Seeded.treeRoot P SphincsSecurity.topLayer
          SphincsSecurity.Concrete.rootTree S :=
    treeRoot_queryH S P SphincsSecurity.topLayer SphincsSecurity.Concrete.rootTree
  rw [publicKeyOf, hroot, bind_map_left, map_eq_bind_pure_comp]
  rfl

/-- Under fixed answers, the model's key generation returns `PK.seed`, `SK.prf` and the top root. -/
theorem eval_keygen (S0 : SphincsSecurity.MasterSeed) :
    evalWithAnswerFn f (SphincsSecurity.Seeded.keygen S0)
      = (⟨evalWithAnswerFn f (SphincsSecurity.Seeded.treeRoot
            (evalWithAnswerFn f
              (SphincsSecurity.derivePublicSeed S0 : OracleComp HashSig.HashSpec _))
            SphincsSecurity.topLayer SphincsSecurity.Concrete.rootTree S0
              : OracleComp HashSig.HashSpec _),
          evalWithAnswerFn f (SphincsSecurity.derivePublicSeed S0 : OracleComp HashSig.HashSpec _)⟩,
        ⟨S0, evalWithAnswerFn f (SphincsSecurity.derivePrf S0 : OracleComp HashSig.HashSpec _),
          evalWithAnswerFn f (SphincsSecurity.derivePublicSeed S0 : OracleComp HashSig.HashSpec _),
          evalWithAnswerFn f (SphincsSecurity.Seeded.treeRoot
            (evalWithAnswerFn f
              (SphincsSecurity.derivePublicSeed S0 : OracleComp HashSig.HashSpec _))
            SphincsSecurity.topLayer SphincsSecurity.Concrete.rootTree S0
              : OracleComp HashSig.HashSpec _)⟩) := by
  simp only [SphincsSecurity.Seeded.keygen, SphincsSecurity.Seeded.keygenFromSeed,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure]

/-- Under fixed answers, EthLib's signer on `SK.seed` is the model's signer on its secret key.

That key is what the model's key generation returns on the seed, under the same answers.

EthLib derives `PK.seed` and `SK.prf` again and rebuilds `PK.root`, and gets the key's values. -/
theorem signWith_answers (S0 : SphincsSecurity.MasterSeed) (msg : SphincsSecurity.Message) :
    evalWithAnswerFn f (Except.toOption <$> signWith (queryH (m := OracleComp HashSig.HashSpec))
        ⟨ofSeed S0⟩ (ofMessage msg))
      = Option.map ofSignature (evalWithAnswerFn f
          (SphincsSecurity.Seeded.sign
            (evalWithAnswerFn f (SphincsSecurity.Seeded.keygen S0)).2 msg
              : OracleComp HashSig.HashSpec _)) := by
  rw [eval_keygen, ← signDerived_answers]
  rw [evalWithAnswerFn_map, signWith, expandKey_queryH, bind_assoc, evalWithAnswerFn_bind,
    bind_assoc, evalWithAnswerFn_bind, pure_bind]
  simp only [ofExpanded]
  rw [evalWithAnswerFn_bind, publicKeyOf_queryH, evalWithAnswerFn_map, evalWithAnswerFn_bind,
    prfMsg_queryH, evalWithAnswerFn_map]

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
