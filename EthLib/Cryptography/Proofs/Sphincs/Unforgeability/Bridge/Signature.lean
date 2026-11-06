module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Digest

/-!
# Proofs: EthLib's keys, signatures and verifier are the model's

A model signature becomes EthLib's field by field.

The model numbers its layers from the top, so its layer 2 is EthLib's bottom layer.

Both verifiers recover the FORS key, then walk the layers from the bottom up.

They make the same calls in the same order, so EthLib's verifier with the query is the model's.

Key generation makes the same calls too: the scheme seed, the public parameter, then the top root.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open SphincsSecurity.Concrete (sequenceFin)

/-! ## Keys and signatures -/

/-- A model public key as EthLib's. -/
def ofPublicKey (pk : SphincsSecurity.PublicKey) : PublicKey :=
  { root := ofDigest pk.root, publicParam := ofParam pk.parameter }

/-- A model layer signature as EthLib's, on the same layer. -/
def ofLayerSignature (lay : SphincsSecurity.Layer) (s : SphincsSecurity.LayerSignature lay) :
    LayerSignature (layerOf lay) :=
  { counter := ofCounter s.counter
    chainValues := ofChains s.chainValues
    path := Vector.ofFn fun i => ofDigest (s.path (Fin.cast (height_layerOf lay) i)) }

/-- The model's bottom layer, layer 2. -/
abbrev bottomLayer : SphincsSecurity.Layer := ⟨2, by decide⟩

/-- The model's middle layer, layer 1. -/
abbrev middleLayer : SphincsSecurity.Layer := ⟨1, by decide⟩

/-- A model signature as EthLib's. -/
def ofSignature (sig : SphincsSecurity.Signature) : Signature :=
  { randomizer := ofRandomizer sig.randomness
    fors := ofOpenings sig.fors
    bottom := ofLayerSignature bottomLayer (sig.layers bottomLayer)
    middle := ofLayerSignature middleLayer (sig.layers middleLayer)
    top := ofLayerSignature SphincsSecurity.topLayer (sig.layers SphincsSecurity.topLayer) }

/-- The one-time key of a layer on the way from an index up is the model's. -/
theorem ofIndex_eq (index : SphincsSecurity.Index) (lay : SphincsSecurity.Layer) :
    OtsKey.ofIndex (layerOf lay) index.val
      = keyOf lay (SphincsSecurity.Concrete.treeIndexAt index lay)
          (SphincsSecurity.Concrete.leafIndexAt index lay) := by
  obtain ⟨v, hv⟩ := lay
  change v < 3 at hv
  interval_cases v <;>
    simp only [OtsKey.ofIndex, keyOf, layerOf, SphincsSecurity.Concrete.treeIndexAt,
      SphincsSecurity.Concrete.leafIndexAt, Nat.shiftRight_eq_div_pow, OtsKey.mk.injEq,
      true_and] <;>
    exact ⟨rfl, rfl⟩

/-- A counter read back from EthLib's 32 bits is the model's. -/
theorem ofNat_ofCounter (c : SphincsSecurity.Counter) :
    BitVec.ofNat 32 (ofCounter c).toNat = c := by
  apply BitVec.eq_of_toNat_eq
  have := c.isLt
  simp only [ofCounter, UInt32.toNat_ofNat', BitVec.toNat_ofNat]
  simp only [SphincsSecurity.counterBits] at this ⊢
  omega

/-- A layer's path, read as a list, is the model's path read up to the layer's height. -/
theorem toList_path_ofLayerSignature (sig : SphincsSecurity.Signature)
    (lay : SphincsSecurity.Layer) :
    (Vector.ofFn fun i : Fin (layerOf lay).height =>
        ofDigest ((sig.layers lay).path (Fin.cast (height_layerOf lay) i))).toList
      = List.ofFn fun i : Fin (SphincsSecurity.layerHeight lay) =>
          ofDigest (SphincsSecurity.Concrete.signaturePath sig lay i.val) := by
  apply List.ext_getElem
  · simp [height_layerOf]
  · intro i h1 h2
    simp only [List.length_ofFn] at h2
    simp [SphincsSecurity.Concrete.signaturePath]

/-- EthLib's FORS tree as the model's. -/
def treeAt (κ : Fin FORS_TREES) : SphincsSecurity.FTree :=
  ⟨κ.val, lt_of_lt_of_eq κ.isLt rfl⟩

/-- Lists in pairs, flattened twice, are the pairs joined and flattened once. -/
theorem flatten_flatten_pairs {α : Type} {n : Nat} (f g : Fin n → List α) :
    (List.ofFn fun x => [f x, g x]).flatten.flatten = (List.ofFn fun x => f x ++ g x).flatten := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ, ih]

/-- The bytes of digests in pairs, in order, as one list. -/
theorem toList_packDigests_pairs {n : Nat} (a b : Fin n → Digest) :
    (packDigests ((Vector.ofFn fun κ => #v[a κ, b κ]).flatten.cast (Nat.mul_comm n 2))).data.toList
      = (List.ofFn fun κ => (a κ).toList ++ (b κ).toList).flatten := by
  simp only [packDigests, packBytes, Vector.flatten, Vector.cast_mk, Array.toList_flatten,
    Vector.toArray_ofFn, Array.toList_map, Array.toList_ofFn, List.map_ofFn, Function.comp_def]
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def, List.map_cons, List.map_nil]
  exact flatten_flatten_pairs (fun x => (a x).toList) (fun x => (b x).toList)

/-- The bytes of a FORS key, as the message the bottom layer signs, are the model's. -/
theorem toList_forsKeyBytes (k : SphincsSecurity.ForsKey) :
    (forsKeyBytes (ofForsKey k)).data.toList = SphincsSecurity.Concrete.rootsPayload k := by
  have hvec : (Vector.ofFn fun i : Fin (2 * FORS_TREES) =>
      let pair := (ofForsKey k)[i.val / 2]'(by have := i.isLt; omega)
      if i.val % 2 = 0 then pair.1 else pair.2)
      = (Vector.ofFn fun κ : Fin FORS_TREES =>
          #v[ofDigest (k (treeAt κ)).1, ofDigest (k (treeAt κ)).2]).flatten.cast
          (Nat.mul_comm _ _) := by
    apply Vector.ext
    intro i hi
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;>
      simp [ofForsKey, ofTops, treeAt, h, Vector.getElem_cast, Vector.getElem_flatten]
  unfold forsKeyBytes
  rw [hvec, toList_packDigests_pairs]
  simp only [toList_ofDigest, SphincsSecurity.Concrete.rootsPayload, List.flatMap_def,
    List.map_ofFn]
  rfl

section Query

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSig.HashSpec m]

/-- The root that a layer's signature leads to is the model's. -/
theorem layerRoot_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (sig : SphincsSecurity.Signature) (lay : SphincsSecurity.Layer) (msg : ByteArray) :
    layerRoot (queryH (m := m)) (ofParam P) (layerOf lay) index.val msg
        (ofLayerSignature lay (sig.layers lay))
      = Option.map ofDigest <$> (do
          let tree := SphincsSecurity.Concrete.treeIndexAt index lay
          let leaf := SphincsSecurity.Concrete.leafIndexAt index lay
          let some value ← SphincsSecurity.Concrete.otsLeaf (m := m) P lay tree leaf
              msg.data.toList (sig.layers lay).counter (sig.layers lay).chainValues
            | pure none
          some <$> SphincsSecurity.Concrete.treeFold P lay tree leaf
            (SphincsSecurity.Concrete.signaturePath sig lay) (SphincsSecurity.layerHeight lay)
            value) := by
  have hclimb := climb_queryH (m := m) P lay (SphincsSecurity.Concrete.treeIndexAt index lay)
    (SphincsSecurity.Concrete.leafIndexAt index lay)
    (SphincsSecurity.Concrete.signaturePath sig lay)
  unfold layerRoot
  rw [ofIndex_eq]
  simp only [ofLayerSignature]
  rw [otsLeaf_queryH, ofNat_ofCounter, bind_map_left, map_bind]
  refine bind_congr fun r => ?_
  rcases r with _ | value
  · simp
  · have h := hclimb value (SphincsSecurity.layerHeight lay) 0
      ((Nat.zero_add _).trans_le (SphincsSecurity.Concrete.layerHeight_le lay))
    simp only [Nat.zero_add, SphincsSecurity.Concrete.treeFold, pure_bind, pow_zero,
      Nat.div_one] at h
    simp only [Option.map_some, fold, keyOf]
    rw [toList_path_ofLayerSignature, ← h]
    simp

/-- EthLib's verifier is the model's, on the translated key, message and signature. -/
theorem verifyWith_queryH (pk : SphincsSecurity.PublicKey) (msg : SphincsSecurity.Message)
    (sig : SphincsSecurity.Signature) :
    verifyWith (queryH (m := m)) (ofPublicKey pk) (ofMessage msg) (ofSignature sig)
      = SphincsSecurity.Concrete.verify (m := m) pk msg sig := by
  unfold verifyWith SphincsSecurity.Concrete.verify SphincsSecurity.Concrete.messageDigest
  simp only [ofPublicKey, ofSignature]
  rw [messageDigest_queryH (root := pk.root), bind_map_left, bind_assoc]
  refine bind_congr fun outs => ?_
  rw [pure_bind, digestIndex_ofOutputs, digestLeaves_ofOutputs, forsRecover_queryH,
    bind_map_left]
  refine bind_congr fun key => ?_
  generalize SphincsSecurity.Concrete.digestIndex (SphincsSecurity.truncateMessageDigest outs)
    = index
  have hb : layerRoot (queryH (m := m)) (ofParam pk.parameter) .bottom index.val
      (forsKeyBytes (ofForsKey key)) (ofLayerSignature bottomLayer (sig.layers bottomLayer)) = _ :=
    layerRoot_queryH pk.parameter index sig bottomLayer _
  rw [hb, toList_forsKeyBytes]
  erw [SphincsSecurity.Concrete.verifyLayers.eq_2]
  simp only [dite_eq_left (show 2 < SphincsSecurity.numLayers by decide), map_bind, bind_assoc]
  refine bind_congr fun r => ?_
  rcases r with _ | bottomRoot
  · simp
  simp only [Option.map_some, bind_map_left, bind_assoc]
  refine bind_congr fun bottomRoot => ?_
  have hm : layerRoot (queryH (m := m)) (ofParam pk.parameter) .middle index.val
      (packBytes (ofDigest bottomRoot)) (ofLayerSignature middleLayer (sig.layers middleLayer))
      = _ :=
    layerRoot_queryH pk.parameter index sig middleLayer _
  rw [ite_eq_right (by decide), hm, toList_data_packBytes_ofDigest]
  erw [SphincsSecurity.Concrete.verifyLayers.eq_2]
  simp only [dite_eq_left (show 1 < SphincsSecurity.numLayers by decide), map_bind, bind_assoc,
    SphincsSecurity.Concrete.rootPayload]
  refine bind_congr fun r => ?_
  rcases r with _ | middleRoot
  · simp
  simp only [Option.map_some, bind_map_left, bind_assoc]
  refine bind_congr fun middleRoot => ?_
  have ht : layerRoot (queryH (m := m)) (ofParam pk.parameter) .top index.val
      (packBytes (ofDigest middleRoot))
      (ofLayerSignature SphincsSecurity.topLayer (sig.layers SphincsSecurity.topLayer))
      = _ :=
    layerRoot_queryH pk.parameter index sig SphincsSecurity.topLayer _
  rw [ite_eq_right (by decide), ht, toList_data_packBytes_ofDigest]
  erw [SphincsSecurity.Concrete.verifyLayers.eq_2]
  simp only [dite_eq_left (show 0 < SphincsSecurity.numLayers by decide), map_bind, bind_assoc,
    SphincsSecurity.Concrete.rootPayload]
  refine bind_congr fun r => ?_
  rcases r with _ | topRoot
  · simp
  simp only [Option.map_some, bind_map_left, bind_assoc]
  refine bind_congr fun root => ?_
  simp only [ite_true, pure_bind]
  have hiff : ofDigest root = ofDigest pk.root ↔ root = pk.root :=
    ⟨HashSig.ofBV_inj (by decide), congrArg ofDigest⟩
  simp only [hiff]

end Query

/-! ## Key generation -/

/-- EthLib's key generation is the model's, with the seed as the secret key. -/
theorem keyGenWith_queryH (S0 : SphincsSecurity.MasterSeed) :
    keyGenWith (queryH (m := OracleComp HashSig.HashSpec)) (ofSeed S0)
      = (fun kp => ((⟨ofSeed S0⟩ : SecretKey), ofPublicKey kp.1)) <$>
          SphincsSecurity.Seeded.keygen S0 := by
  unfold keyGenWith publicKeyOf SphincsSecurity.Seeded.keygen
    SphincsSecurity.Seeded.keygenFromSeed
  rw [schemeSeed_queryH, bind_map_left, map_bind]
  refine bind_congr fun S => ?_
  rw [publicParamOf_queryH, bind_map_left, bind_assoc, map_bind]
  refine bind_congr fun P => ?_
  have hroot : treeRoot (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
      (seedPrf queryH (ofSeed S)) .top 0
      = ofDigest <$> SphincsSecurity.Seeded.treeRoot P SphincsSecurity.topLayer
          SphincsSecurity.Concrete.rootTree S :=
    treeRoot_queryH S P SphincsSecurity.topLayer SphincsSecurity.Concrete.rootTree
  rw [hroot, bind_map_left, map_bind]
  simp only [bind_assoc, pure_bind, map_pure]
  rfl

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
