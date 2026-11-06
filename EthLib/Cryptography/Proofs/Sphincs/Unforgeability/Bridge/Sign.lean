module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Signature
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Landing
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Correctness

/-!
# Proofs: under fixed answers, EthLib's signer is the model's

Both signers compute the randomizer, the digest, the FORS openings and one signature per layer.

They make different calls.

Both sign the layers from the bottom up.

The model makes one more digest call, for its randomizer search.

EthLib derives the scheme seed and the public parameter again on each request.

Under a fixed answer function each call is a value, whatever its order or repetition.

So under every answer function EthLib's signature is the model's, and both fail together.
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

/-- Under fixed answers, a layer signs a message as the model's layer signs the same bytes. -/
theorem signLayer_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (root : SphincsSecurity.Digest) (index : SphincsSecurity.Index) (lay : SphincsSecurity.Layer)
    (msg : ByteArray)
    (hmsg : msg.data.toList = layerMessageValue f ⟨S, P, root⟩ index lay) :
    evalWithAnswerFn f (signLayer (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) (layerOf lay) index.val msg)
      = toLayerResult lay (evalWithAnswerFn f
          (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index lay
            : OracleComp HashSig.HashSpec _)) := by
  unfold signLayer
  rw [ofIndex_eq]
  simp only [SphincsSecurity.Seeded.signLayer, evalWithAnswerFn_bind]
  rw [show evalWithAnswerFn f (SphincsSecurity.Seeded.layerMessage ⟨S, P, root⟩ index lay
      : OracleComp HashSig.HashSpec _) = layerMessageValue f ⟨S, P, root⟩ index lay from rfl,
    ← hmsg, otsSign_queryH, evalWithAnswerFn_map]
  cases evalWithAnswerFn f (SphincsSecurity.Seeded.otsSign P lay
      (SphincsSecurity.Concrete.treeIndexAt index lay)
      (SphincsSecurity.Concrete.leafIndexAt index lay)
      S msg.data.toList : OracleComp HashSig.HashSpec _) with
  | none => rfl
  | some ots =>
    obtain ⟨counter, values⟩ := ots
    simp only [Option.map_some, ofOts, keyOf, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rw [path_queryH, evalWithAnswerFn_map, eval_sequenceFin, SphincsSecurity.Seeded.treePath,
      eval_sequenceFin]
    simp only [toLayerResult, ofLayerSignature, keptHeight_eq, Fin.is_lt, ↓reduceIte]
    rfl

/-- Under fixed answers, the bottom layer signs the model's message: the FORS key. -/
theorem layerMessage_bottom_answers (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (index : SphincsSecurity.Index) :
    (evalWithAnswerFn f (layerMessage (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) .bottom index.val)).data.toList
      = layerMessageValue f ⟨S, P, root⟩ index bottomLayer := by
  simp only [layerMessage, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [forsKey_answers, toList_forsKeyBytes]
  exact (layerMessageValue_bottom f ⟨S, P, root⟩ index).symm

/-- Under fixed answers, the middle layer signs the model's message: the bottom tree's root. -/
theorem layerMessage_middle_answers (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (index : SphincsSecurity.Index) :
    (evalWithAnswerFn f (layerMessage (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) .middle index.val)).data.toList
      = layerMessageValue f ⟨S, P, root⟩ index middleLayer := by
  have hkey : OtsKey.ofIndex .bottom index.val
      = keyOf bottomLayer (SphincsSecurity.Concrete.treeIndexAt index bottomLayer)
          (SphincsSecurity.Concrete.leafIndexAt index bottomLayer) :=
    ofIndex_eq index bottomLayer
  have hroot : treeRoot (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
      (seedPrf queryH (ofSeed S)) .bottom
      (SphincsSecurity.Concrete.treeIndexAt index bottomLayer).val
      = ofDigest <$> SphincsSecurity.Seeded.treeRoot P bottomLayer
          (SphincsSecurity.Concrete.treeIndexAt index bottomLayer) S :=
    treeRoot_queryH S P bottomLayer _
  simp only [layerMessage, hkey, keyOf, hroot, bind_map_left, evalWithAnswerFn_bind,
    evalWithAnswerFn_pure, toList_data_packBytes_ofDigest]
  rw [layerMessageValue_above f ⟨S, P, root⟩ index middleLayer (by decide)]
  rfl

/-- Under fixed answers, the top layer signs the model's message: the middle tree's root. -/
theorem layerMessage_top_answers (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (index : SphincsSecurity.Index) :
    (evalWithAnswerFn f (layerMessage (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) .top index.val)).data.toList
      = layerMessageValue f ⟨S, P, root⟩ index SphincsSecurity.topLayer := by
  have hkey : OtsKey.ofIndex .middle index.val
      = keyOf middleLayer (SphincsSecurity.Concrete.treeIndexAt index middleLayer)
          (SphincsSecurity.Concrete.leafIndexAt index middleLayer) :=
    ofIndex_eq index middleLayer
  have hroot : treeRoot (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
      (seedPrf queryH (ofSeed S)) .middle
      (SphincsSecurity.Concrete.treeIndexAt index middleLayer).val
      = ofDigest <$> SphincsSecurity.Seeded.treeRoot P middleLayer
          (SphincsSecurity.Concrete.treeIndexAt index middleLayer) S :=
    treeRoot_queryH S P middleLayer _
  simp only [layerMessage, hkey, keyOf, hroot, bind_map_left, evalWithAnswerFn_bind,
    evalWithAnswerFn_pure, toList_data_packBytes_ofDigest]
  rw [layerMessageValue_above f ⟨S, P, root⟩ index SphincsSecurity.topLayer (by decide)]
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

/-- Under fixed answers, the model's layers give every signature, or nothing when one fails. -/
theorem eval_sequenceLayers {α : SphincsSecurity.Layer → Type}
    (computation : (lay : SphincsSecurity.Layer) →
      OracleComp HashSig.HashSpec (Option (α lay))) :
    evalWithAnswerFn f (SphincsSecurity.Concrete.sequenceLayers computation)
      = allSome fun lay => evalWithAnswerFn f (computation lay) :=
  eval_sequenceDep f computation

/-- Under fixed answers, the model signs with its first randomizer `rho`, at its digest's index.

It returns a signature exactly when every layer signs. -/
theorem eval_sign (secretKey : SphincsSecurity.Seeded.SecretKey) (msg : SphincsSecurity.Message)
    (rho : SphincsSecurity.Randomness)
    (hrho : (evalWithAnswerFn f (SphincsSecurity.deriveRandomizer secretKey.parameter
      secretKey.seed msg : OracleComp HashSig.HashSpec _)).1 = rho) :
    evalWithAnswerFn f (SphincsSecurity.Seeded.sign secretKey msg : OracleComp HashSig.HashSpec _)
      = (allSome fun lay => evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer secretKey
          (SphincsSecurity.Concrete.digestIndex (digestValue f secretKey msg rho)) lay
          : OracleComp HashSig.HashSpec _)).map fun layers =>
        ⟨rho, evalWithAnswerFn f (SphincsSecurity.Seeded.forsOpen secretKey.parameter
            (SphincsSecurity.Concrete.digestIndex (digestValue f secretKey msg rho))
            (SphincsSecurity.Concrete.digestLeaves (digestValue f secretKey msg rho)) secretKey.seed
            : OracleComp HashSig.HashSpec _), layers⟩ := by
  rw [SphincsSecurity.Seeded.sign, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    show SphincsSecurity.digestAttemptLimit = 2 ^ 32 - 1 + 1 from rfl, signDigestLoop_succ,
    evalWithAnswerFn_map, hrho]
  dsimp only
  rw [evalWithAnswerFn_bind, show evalWithAnswerFn f (SphincsSecurity.Concrete.messageDigest
      secretKey.parameter secretKey.root msg rho : OracleComp HashSig.HashSpec _)
      = digestValue f secretKey msg rho from rfl]
  generalize digestValue f secretKey msg rho = digest
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_sequenceLayers]
  cases allSome fun lay => evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer secretKey
      (SphincsSecurity.Concrete.digestIndex digest) lay : OracleComp HashSig.HashSpec _) <;> rfl

/-- Under fixed answers, EthLib signs from `S` and `P` as the model signs with the key `S`, `P`.

The model's key also holds a root, which its signer never reads. -/
theorem signDerived_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (root : SphincsSecurity.Digest) (msg : SphincsSecurity.Message) :
    Except.toOption (evalWithAnswerFn f (signDerived (queryH (m := OracleComp HashSig.HashSpec))
        (seedPrf queryH (ofSeed S)) (ofParam P) (ofMessage msg)))
      = Option.map ofSignature (evalWithAnswerFn f
          (SphincsSecurity.Seeded.sign ⟨S, P, root⟩ msg : OracleComp HashSig.HashSpec _)) := by
  unfold signDerived
  rw [evalWithAnswerFn_bind, randomizer_queryH, evalWithAnswerFn_map, evalWithAnswerFn_bind,
    messageDigest_queryH (root := root), evalWithAnswerFn_map, eval_sequenceFin]
  generalize hrho : (evalWithAnswerFn f (SphincsSecurity.deriveRandomizer P S msg
    : OracleComp HashSig.HashSpec _)).1 = rho
  conv_rhs => rw [eval_sign f ⟨S, P, root⟩ msg rho hrho]
  have hdigest : digestValue f ⟨S, P, root⟩ msg rho
      = SphincsSecurity.truncateMessageDigest fun call =>
          evalWithAnswerFn f (SphincsSecurity.Concrete.messageDigestCall P root msg rho call) := by
    rw [digestValue, SphincsSecurity.Concrete.messageDigest, evalWithAnswerFn_bind,
      eval_sequenceFin, evalWithAnswerFn_pure]
  rw [hdigest]
  generalize (fun call => evalWithAnswerFn f
    (SphincsSecurity.Concrete.messageDigestCall P root msg rho call
      : OracleComp HashSig.HashSpec _)) = outs
  dsimp only
  rw [digestIndex_ofOutputs, digestLeaves_ofOutputs]
  generalize SphincsSecurity.Concrete.digestIndex (SphincsSecurity.truncateMessageDigest outs)
    = index
  rw [evalWithAnswerFn_bind, forsSign_answers]
  generalize evalWithAnswerFn f (SphincsSecurity.Seeded.forsOpen P index
    (SphincsSecurity.Concrete.digestLeaves (SphincsSecurity.truncateMessageDigest outs)) S
      : OracleComp HashSig.HashSpec _) = opening
  have hb : evalWithAnswerFn f (signLayer (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
      (seedPrf queryH (ofSeed S)) .bottom index.val (evalWithAnswerFn f (layerMessage
        (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P) (seedPrf queryH (ofSeed S))
        .bottom index.val)))
      = toLayerResult bottomLayer (evalWithAnswerFn f
          (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index bottomLayer
            : OracleComp HashSig.HashSpec _)) :=
    signLayer_answers f S P root index bottomLayer _ (layerMessage_bottom_answers f S P root index)
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, hb]
  cases hbottom : evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index
      bottomLayer : OracleComp HashSig.HashSpec _) with
  | none =>
    rw [allSome_eq_none _ bottomLayer hbottom]
    rfl
  | some bottom =>
    have hm : evalWithAnswerFn f (signLayer (queryH (m := OracleComp HashSig.HashSpec))
        (ofParam P) (seedPrf queryH (ofSeed S)) .middle index.val (evalWithAnswerFn f
          (layerMessage (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
            (seedPrf queryH (ofSeed S)) .middle index.val)))
        = toLayerResult middleLayer (evalWithAnswerFn f
            (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index middleLayer
              : OracleComp HashSig.HashSpec _)) :=
      signLayer_answers f S P root index middleLayer _
        (layerMessage_middle_answers f S P root index)
    dsimp only [toLayerResult]
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind, hm]
    cases hmiddle : evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index
        middleLayer : OracleComp HashSig.HashSpec _) with
    | none =>
      rw [allSome_eq_none _ middleLayer hmiddle]
      rfl
    | some middle =>
      have ht : evalWithAnswerFn f (signLayer (queryH (m := OracleComp HashSig.HashSpec))
          (ofParam P) (seedPrf queryH (ofSeed S)) .top index.val (evalWithAnswerFn f
            (layerMessage (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
              (seedPrf queryH (ofSeed S)) .top index.val)))
          = toLayerResult SphincsSecurity.topLayer (evalWithAnswerFn f
              (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index SphincsSecurity.topLayer
                : OracleComp HashSig.HashSpec _)) :=
        signLayer_answers f S P root index SphincsSecurity.topLayer _
          (layerMessage_top_answers f S P root index)
      dsimp only [toLayerResult]
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind, ht]
      cases htop : evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index
          SphincsSecurity.topLayer : OracleComp HashSig.HashSpec _) with
      | none =>
        rw [allSome_eq_none _ SphincsSecurity.topLayer htop]
        rfl
      | some top =>
        obtain ⟨layers, hlayers, htop', hmiddle', hbottom'⟩ := allSome_layers
          (fun lay => evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index lay
            : OracleComp HashSig.HashSpec _)) htop hmiddle hbottom
        dsimp only [toLayerResult]
        rw [hlayers]
        simp only [Option.map_some, ofSignature, htop', hmiddle', hbottom']
        rfl

/-- Under fixed answers, EthLib's signer on the seed `S0` is the model's signer on its key.

The key holds the scheme seed and the public parameter that EthLib derives again from `S0`.

Its root is any digest, since the model's signer never reads it. -/
theorem signWith_answers (S0 : SphincsSecurity.MasterSeed) (root : SphincsSecurity.Digest)
    (msg : SphincsSecurity.Message) :
    evalWithAnswerFn f (Except.toOption <$> signWith (queryH (m := OracleComp HashSig.HashSpec))
        ⟨ofSeed S0⟩ (ofMessage msg))
      = Option.map ofSignature (evalWithAnswerFn f
          (SphincsSecurity.Seeded.sign
            ⟨evalWithAnswerFn f (SphincsSecurity.schemeSeed S0 : OracleComp HashSig.HashSpec _),
              evalWithAnswerFn f (SphincsSecurity.deriveKey 0 .parameter
                (evalWithAnswerFn f (SphincsSecurity.schemeSeed S0 : OracleComp HashSig.HashSpec _))
                  : OracleComp HashSig.HashSpec _),
              root⟩ msg : OracleComp HashSig.HashSpec _)) := by
  rw [evalWithAnswerFn_map, signWith, schemeSeed_queryH, bind_map_left, evalWithAnswerFn_bind,
    publicParamOf_queryH, bind_map_left, evalWithAnswerFn_bind]
  exact signDerived_answers f _ _ root msg

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
