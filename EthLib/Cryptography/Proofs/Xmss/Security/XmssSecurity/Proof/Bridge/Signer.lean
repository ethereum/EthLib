module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Real
public import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# EthLib's signer under the prepared cache

EthLib's signer from the scheme's seed `S` and the parameter `P` is the model's table signer.

That holds under the prepared cache.

It derives the same randomizer base and makes the same trials.

Everything it computes after a codeword is cached.

That is the chains, the bottom tree and the whole top signature.

The bottom tree's build resolves to a tree with the stored root and the stored path of the key.

So it erases to the values the model's key stores.
-/

@[expose] public section

open OracleComp OracleSpec
open EthLib.Cryptography
open EthLib.Cryptography.Xmss.Constants (V CHAIN_LENGTH LAYER_HEIGHT MAX_RANDOMIZER_TRIALS)
open EthLib.Cryptography.Xmss.Unforgeability (queryH ofParam ofSeed ofDigest ofOutput ofChains
  ofLeafIndex ofTopIndex ofMessage ofRandomizer ofEncoding ofPath ofLayerSig ofSignature chainOf)

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

/-- A query to the oracle, as the query and the four lanes of its answer. -/
theorem queryH_eq (x : Array UInt64) :
    (queryH x : OracleComp HashSpec Hash.Keccak.Lanes4)
      = liftM (HashSpec.query (Hash.Keccak.lanesBytes x)) >>= fun y => pure (ofOutput y) := by
  unfold queryH HashSig.queryLanes
  rw [map_eq_bind_pure_comp]
  rfl

/-- The first half of an answer, read as a randomizer. -/
theorem halfOf_zero_ofOutput_randomizer (y : HashOutput) :
    (Xmss.halfOf 0 (ofOutput y) : Xmss.Randomizer)
      = ofRandomizer (y.extractLsb' 0 randomnessBits) := by
  rw [Xmss.Unforgeability.halfOf_zero_ofOutput]
  rfl

/-- The randomizer base is one query, its answer's first half read as a randomizer.

Stated at the randomizer's type, so later binds associate with it. -/
theorem randomizerBase_queryH (pp : Xmss.PublicParam) (s : Xmss.Seed) (layer : Xmss.Layer)
    (e : UInt32) (msg : Array UInt64) :
    (Xmss.randomizerBase pp (Xmss.seedPrf queryH s) layer e msg :
      OracleComp HashSpec Xmss.Randomizer)
      = liftM (HashSpec.query
          (Hash.Keccak.lanesBytes (Xmss.thInput pp (Xmss.addrRnd layer e) (s.toArray ++ msg)))) >>=
        fun y => pure (ofRandomizer (y.extractLsb' 0 randomnessBits)) := by
  rw [Xmss.randomizerBase_seedPrf]
  unfold Xmss.th
  simp only [queryH_eq, bind_assoc, pure_bind]
  refine bind_congr fun y => ?_
  exact congrArg pure (halfOf_zero_ofOutput_randomizer y)

/-- The bottom randomizer base `R0(idx, m)` is the bottom derivation's input. -/
theorem rndInput_toList (P : PublicParameter) (seed : MasterSeed) (index : LeafIndex)
    (message : Message) :
    Hash.Keccak.lanesBytes (Xmss.thInput (ofParam P) (Xmss.addrRnd .bottom (ofLeafIndex index))
      ((ofSeed seed).toArray ++ (ofMessage message).toArray))
      = rndInput P seed ⟨index, message⟩ := by
  rw [rndInput_eq]
  simp only [Xmss.thInput_eq_append,
    EthLib.Cryptography.Hash.Keccak.lanesBytes_append, Xmss.Unforgeability.toList_ofParam,
    Xmss.Unforgeability.toList_ofSeed, Xmss.Unforgeability.toList_ofMessage,
    Xmss.Unforgeability.toList_addrRnd, Xmss.Unforgeability.toNat_ofLeafIndex]
  -- The bottom layer adds no flag to `hi`.
  exact congrArg (fun x => bytesLE 16 P ++ fieldBytes (tweakFields 7 0 x index.val) ++
    (bytesLE 32 seed ++ bytesLE 32 message)) (by simp [Xmss.Layer.toNat])

/-- The top randomizer base `R0_top(b, r)` is the top derivation's input. -/
theorem topRndInput_toList (P : PublicParameter) (seed : MasterSeed) (key : TopIndex)
    (root : Digest) :
    Hash.Keccak.lanesBytes (Xmss.thInput (ofParam P) (Xmss.addrRnd .top (ofTopIndex key))
      ((ofSeed seed).toArray ++ (ofDigest root).toArray))
      = topRndInput P seed (key, root) := by
  rw [topRndInput_eq]
  simp only [Xmss.thInput_eq_append,
    EthLib.Cryptography.Hash.Keccak.lanesBytes_append, Xmss.Unforgeability.toList_ofParam,
    Xmss.Unforgeability.toList_ofSeed, Xmss.Unforgeability.toList_ofDigest,
    Xmss.Unforgeability.toList_addrRnd, Xmss.Unforgeability.toNat_ofTopIndex]
  -- The top layer adds its flag to `hi`.
  exact congrArg (fun x => bytesLE 16 P ++ fieldBytes (tweakFields 7 0 x key.val) ++
    (bytesLE 32 seed ++ bytesLE 16 root)) (by simp [Xmss.Layer.toNat, topFlag])

/-- The bottom search is the table signer's trials, whatever follows each. -/
theorem erases_findCodeword_bottom {β : Type} (cache : QueryCache HashSpec)
    (sk : XmssSecurity.SecretKey) (index : LeafIndex) (message : Message) (base : Randomness)
    (K : Option (Xmss.Randomizer × Vector (Fin CHAIN_LENGTH) V) → OracleComp HashSpec β)
    (K' : Option Signature → OracleComp HashSpec β) (hnone : Erases cache (K none) (K' none))
    (hsome : ∀ rho enc, Erases cache (K (some (ofRandomizer rho, ofEncoding enc)))
      (K' (some (Concrete.precomputedSignWithEncoding sk index rho enc)))) :
    ∀ fuel trial, Erases cache
      (Xmss.Internal.findCodeword queryH (ofParam sk.parameter) .bottom (ofLeafIndex index)
        ((ofMessage message).toArray) (ofRandomizer base) trial fuel >>= K)
      (tableSignFrom base sk index message fuel trial >>= K')
  | 0, _ => by simpa [Xmss.Internal.findCodeword_eq, Wots.findFirst, tableSignFrom] using hnone
  | fuel + 1, trial => by
    rw [Xmss.Internal.findCodeword_eq]
    unfold Wots.findFirst tableSignFrom
    simp only [Xmss.Unforgeability.trialRandomizer_ofRandomizer,
      Xmss.Unforgeability.messageDigest_bottom, Concrete.precomputedSignAttempt, bind_assoc,
      bind_map_left]
    refine (Erases.refl _ _).bind _ _ fun digest => ?_
    rw [Xmss.Unforgeability.codeword?_ofDigest]
    cases TargetSum.decodeDigest digest with
    | none =>
      simpa [Xmss.Internal.findCodeword_eq] using
        erases_findCodeword_bottom cache sk index message base K K' hnone hsome fuel (trial + 1)
    | some enc => simpa using hsome _ enc

/-- A resolved node gives a resolved build of the same position, with the node's value on top. -/
theorem resolves_build {α : Type} {cache : QueryCache HashSpec}
    (hash : Merkle.Position → α → α → OracleComp HashSpec α)
    (leaves : Nat → OracleComp HashSpec α) :
    ∀ (p : Merkle.Position) (v : α), Resolves cache (Merkle.node hash leaves p) v →
      ∃ t, Resolves cache (Merkle.build hash leaves p) t ∧ t.value = v := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero =>
    intro v h
    exact ⟨.leaf v, by rw [Merkle.build_zero]; exact h.bind (.pure _), rfl⟩
  | succ level ih =>
    intro v h
    -- The node resolves its two children, then its hash.
    rw [Merkle.node_succ] at h
    obtain ⟨a, ha, h⟩ := h.of_bind
    obtain ⟨b, hb, h⟩ := h.of_bind
    obtain ⟨left, hleft, rfl⟩ := ih (2 * j) a ha
    obtain ⟨right, hright, rfl⟩ := ih (2 * j + 1) b hb
    exact ⟨.node v left right, by
      rw [Merkle.build_succ]
      exact hleft.bind (hright.bind (h.bind (.pure _))), rfl⟩

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec}

theorem xor_one_lt {n k : Nat} (hn : n < 2 ^ k) (hk : 1 ≤ k) : Nat.xor n 1 < 2 ^ k :=
  Nat.xor_lt_two_pow hn (Nat.one_lt_two_pow (by omega))

/-- The top search of a bottom root resolves to the key's top signature. -/
theorem realTopFind (h : Prepared seed d result cache) (key : TopIndex) (base : Randomness)
    (res : Option (Randomness × Encoding)) :
    ∀ fuel trial,
      Resolves cache (Concrete.topSignFrom d.parameter key (h.root key) base fuel trial) res →
      Resolves cache (Xmss.Internal.findCodeword queryH (ofParam d.parameter) .top (ofTopIndex key)
          ((ofDigest (h.root key)).toArray) (ofRandomizer base) trial fuel :
          OracleComp HashSpec _)
        (res.map fun p => (ofRandomizer p.1, ofEncoding p.2))
  | 0, _, hmodel => by
    rw [← hmodel.pure_inv]
    exact .pure _
  | fuel + 1, trial, hmodel => by
    rw [Concrete.topSignFrom] at hmodel
    rw [Xmss.Internal.findCodeword_eq]
    unfold Wots.findFirst
    simp only [Xmss.Unforgeability.trialRandomizer_ofRandomizer,
      Xmss.Unforgeability.messageDigest_top, bind_map_left]
    obtain ⟨digest, hdigest, hrest⟩ := hmodel.of_bind
    refine hdigest.bind ?_
    rw [Xmss.Unforgeability.codeword?_ofDigest]
    cases hdec : TargetSum.decodeDigest digest with
    | none =>
      rw [hdec] at hrest
      have next := realTopFind h key base res fuel (trial + 1) hrest
      rwa [Xmss.Internal.findCodeword_eq] at next
    | some encoding =>
      rw [hdec] at hrest
      rw [← hrest.pure_inv]
      exact .pure _

/-- A top key's chains, opened at a codeword, resolve to the key's stored values. -/
theorem realTopChains (h : Prepared seed d result cache) (key : TopIndex) (encoding : Encoding) :
    Resolves cache (Xmss.ofFnInOrder V fun i => Xmss.chain queryH (ofParam d.parameter) .top
        (ofTopIndex key) i 0 (ofEncoding encoding)[i] (by simp)
        (ofChains (d.topSecret key))[i] : OracleComp HashSpec _)
      (ofChains fun chain => (modelSecretKey d result).topChainValue key chain (encoding chain)) :=
  Resolves.ofFnInOrder fun i => by
    rw [show (ofChains (d.topSecret key))[i] = ofDigest (d.topSecret key (chainOf i)) from
      Vector.getElem_ofFn _, Xmss.Unforgeability.chain_top]
    rw [show ((ofEncoding encoding)[i] : Nat) = (encoding (chainOf i)).val from
      congrArg Fin.val (Vector.getElem_ofFn _)]
    exact (h.topChain key (chainOf i) (encoding (chainOf i))).map _

/-- A bottom key's chains, opened at a codeword, resolve to the key's stored values. -/
theorem realBottomChains (h : Prepared seed d result cache) (index : LeafIndex)
    (encoding : Encoding) :
    Resolves cache (Xmss.ofFnInOrder V fun i => Xmss.chain queryH (ofParam d.parameter) .bottom
        (ofLeafIndex index) i 0 (ofEncoding encoding)[i] (by simp)
        (ofChains (d.secret index))[i] : OracleComp HashSpec _)
      (ofChains fun chain => (modelSecretKey d result).chainValue index chain (encoding chain)) :=
  Resolves.ofFnInOrder fun i => by
    rw [show (ofChains (d.secret index))[i] = ofDigest (d.secret index (chainOf i)) from
      Vector.getElem_ofFn _, Xmss.Unforgeability.chain_bottom]
    rw [show ((ofEncoding encoding)[i] : Nat) = (encoding (chainOf i)).val from
      congrArg Fin.val (Vector.getElem_ofFn _)]
    exact (h.chain index (chainOf i) (encoding (chainOf i))).map _

/-- A top key's path resolves to the key's stored nodes. -/
theorem realTopPath (h : Prepared seed d result cache) (key : TopIndex) :
    Resolves cache (Xmss.path queryH (ofParam d.parameter) (realPrf seed) .top key.val :
        OracleComp HashSpec _)
      (ofPath fun level =>
        (modelSecretKey d result).topTreeValue level.castSucc
          (Concrete.topPathNode key level)) := by
  rw [Xmss.path_eq_ofFnInOrder]
  refine Resolves.ofFnInOrder fun level => ?_
  have hlevel : level.val < 16 := level.isLt
  have hb : key.val / 2 ^ level.val < 2 ^ (16 - level.val) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
      show 16 - level.val + level.val = 16 by omega]
    exact lt_of_lt_of_eq key.isLt (by norm_num [topLifetime, treeHeight])
  exact h.realTopNode level.val (by omega) _ (xor_one_lt hb (by omega))

/-- A bottom key's path resolves to the key's stored nodes. -/
theorem realBottomPath (h : Prepared seed d result cache) (index : LeafIndex) :
    Resolves cache (Xmss.path queryH (ofParam d.parameter) (realPrf seed) .bottom index.val :
        OracleComp HashSpec _)
      (ofPath fun level => (modelSecretKey d result).treeValue level.castSucc
        (Concrete.authenticationPathNode index level)) := by
  rw [Xmss.path_eq_ofFnInOrder]
  refine Resolves.ofFnInOrder fun level => ?_
  have hlevel : level.val < 16 := level.isLt
  have hb : index.val / 2 ^ level.val < 2 ^ (32 - level.val) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
      show 32 - level.val + level.val = 32 by omega]
    exact lt_of_lt_of_eq index.isLt (by norm_num [lifetime, treeHeight])
  exact h.realBottomNode level.val (by omega) _ (xor_one_lt hb (by omega))

/-- The top layer's signature of bottom tree `b`, or its error, as the key stores it. -/
theorem realTopLayer (h : Prepared seed d result cache) (key : TopIndex) :
    Resolves cache (Xmss.signLayer queryH (ofParam d.parameter) (realPrf seed) .top key.val
        ((ofDigest (h.root key)).toArray) : OracleComp HashSpec _)
      (match (modelSecretKey d result).topSigned key with
        | some _ => .ok (ofLayerSig (Concrete.topPart (modelSecretKey d result) key))
        | none => .error (.noAdmissibleEncoding .top key.val)) := by
  unfold Xmss.signLayer Xmss.otsSign Xmss.Internal.otsSignTrials
  rw [Xmss.Unforgeability.ofNat_val_topIndex, randomizerBase_queryH]
  simp only [bind_assoc]
  have hbase : cache (topRndInput d.parameter seed (key, h.root key))
      = some (d.topRnd (key, h.root key)) :=
    h.prog_le (progCache_topRnd seed d (key, h.root key))
  refine .query _ (d.topRnd (key, h.root key)) ?_ _ _ ?_
  · rw [topRndInput_toList]
    exact hbase
  simp only [pure_bind]
  have hgrind := h.realTopFind key _ _ signingAttemptLimit 0 (h.topSign key)
  refine hgrind.bind ?_
  cases hsigned : result.1.2 key with
  | none =>
    have : (modelSecretKey d result).topSigned key = none := hsigned
    simp only [Option.map_none, this]
    exact .pure _
  | some signed =>
    obtain ⟨randomness, encoding⟩ := signed
    have hsk : (modelSecretKey d result).topSigned key = some (randomness, encoding) := hsigned
    simp only [Option.map_some, bind_assoc, pure_bind]
    refine ((chainStarts_top seed d key).mono h.prog_le).bind ?_
    refine (h.realTopChains key encoding).bind ?_
    refine (h.realTopPath key).bind ?_
    simp only [hsk, Concrete.topPart]
    exact .pure _

theorem bottomKey_lt (index : LeafIndex) : (topKeyOf index).val < 2 ^ (32 - 16) :=
  lt_of_lt_of_eq (topKeyOf index).isLt (by norm_num [topLifetime, treeHeight])

/-- The root of bottom tree `b` resolves to the one the key stores. -/
theorem root_resolves (h : Prepared seed d result cache) (index : LeafIndex) :
    Resolves cache (Xmss.node queryH (ofParam d.parameter) (realPrf seed) .bottom LAYER_HEIGHT
        (topKeyOf index).val : OracleComp HashSpec Xmss.Digest)
      (ofDigest (h.root (topKeyOf index))) := by
  have hroot := h.realBottomNode 16 le_rfl (topKeyOf index).val (bottomKey_lt index)
  unfold Prepared.root
  rw [Prepared.bottomRootNode_eq]
  exact hroot

/-- The build of bottom tree `b` resolves to a tree with the stored root and the key's path. -/
theorem realBottomBuild (h : Prepared seed d result cache) (index : LeafIndex) :
    ∃ t, Resolves cache (Xmss.build queryH (ofParam d.parameter) (realPrf seed) .bottom
        LAYER_HEIGHT (topKeyOf index).val : OracleComp HashSpec _) t ∧
      t.value = ofDigest (h.root (topKeyOf index)) ∧
      t.path LAYER_HEIGHT index.val = ofPath fun level =>
        (modelSecretKey d result).treeValue level.castSucc
          (Concrete.authenticationPathNode index level) := by
  obtain ⟨t, ht, hroot⟩ := resolves_build _ _ _ _ (h.root_resolves index)
  replace ht : Resolves cache (Xmss.build queryH (ofParam d.parameter) (realPrf seed) .bottom
      LAYER_HEIGHT (topKeyOf index).val : OracleComp HashSpec _) t := ht
  refine ⟨t, ht, hroot, ?_⟩
  -- Answer every query from the cache: the build and the path then evaluate to their values.
  let f : QueryImpl HashSpec Id := fun x => (cache x).getD default
  have hf : ∀ x a, cache x = some a → f x = a := fun x a hx => by simp [f, hx]
  rw [← ht.eval f hf, ← (h.realBottomPath index).eval f hf]
  have hbuild := Xmss.build_map_monad (m := OracleComp HashSpec) (m' := Id)
    (fun {β} (c : OracleComp HashSpec β) => (evalWithAnswerFn f c : Id β)) (fun _ => rfl)
    (fun x g => evalWithAnswerFn_bind f x g) queryH (realPrf seed) (ofParam d.parameter) .bottom
    LAYER_HEIGHT (topKeyOf index).val
  have hpath := Xmss.path_map_monad (m := OracleComp HashSpec) (m' := Id)
    (fun {β} (c : OracleComp HashSpec β) => (evalWithAnswerFn f c : Id β)) (fun _ => rfl)
    (fun x g => evalWithAnswerFn_bind f x g) queryH (realPrf seed) (ofParam d.parameter) .bottom
    index.val
  rw [hbuild, hpath, show (topKeyOf index).val = index.val / 2 ^ LAYER_HEIGHT from rfl]
  exact Xmss.path_build_run index.val

/-- EthLib's signer from `S` and `P` erases to the table signer, its signatures translated. -/
theorem erases_sign (h : Prepared seed d result cache) (index : LeafIndex) (message : Message) :
    Erases cache (Except.toOption <$> Xmss.signDerived queryH (realPrf seed) (ofParam d.parameter)
        (ofLeafIndex index) (ofMessage message))
      (Option.map (ofSignature index) <$> (tableSign d.rnd (modelSecretKey d result) index message :
        OracleComp HashSpec (Option Signature))) := by
  unfold Xmss.signDerived tableSign
  -- Only the bottom key is unfolded: the top layer resolves as a whole.
  rw [Xmss.otsSign.eq_1, Xmss.Internal.otsSignTrials.eq_1, Xmss.Unforgeability.toNat_ofLeafIndex,
    Xmss.Unforgeability.ofNat_val_leafIndex, randomizerBase_queryH]
  simp only [bind_assoc, map_bind]
  have hR0 : cache (rndInput d.parameter seed ⟨index, message⟩) = some (d.rnd ⟨index, message⟩) :=
    h.prog_le (progCache_rnd seed d ⟨index, message⟩)
  refine Erases.skip (spec := HashSpec) _ (d.rnd ⟨index, message⟩) ?_ _ _ ?_
  · rw [rndInput_toList]
    exact hR0
  simp only [pure_bind]
  refine erases_findCodeword_bottom cache (modelSecretKey d result) index message _ _ _ ?_ ?_
    signingAttemptLimit 0
  · simp [Except.toOption]
    exact .pure _
  · intro randomness encoding
    apply erases_pure_of_resolves
    dsimp only
    simp only [bind_assoc, pure_bind]
    refine ((chainStarts_bottom seed d index).mono h.prog_le).bind ?_
    refine (h.realBottomChains index encoding).bind ?_
    rw [Xmss.Unforgeability.bottomTree_ofLeafIndex]
    simp only [map_bind]
    obtain ⟨tree, htree, hroot, hpath⟩ := h.realBottomBuild index
    refine htree.bind ?_
    rw [hroot, hpath]
    refine (h.realTopLayer (topKeyOf index)).bind ?_
    cases hsigned : (modelSecretKey d result).topSigned (topKeyOf index) with
    | none =>
      have hat : Concrete.topSignedAt (modelSecretKey d result) index = false := by
        simp [Concrete.topSignedAt, hsigned]
      simp [hat, Except.toOption]
      exact .pure _
    | some signed =>
      have hat : Concrete.topSignedAt (modelSecretKey d result) index = true := by
        simp [Concrete.topSignedAt, hsigned]
      simp [hat, Except.toOption, ofSignature, Concrete.precomputedSignWithEncoding]
      exact .pure _

end Prepared

end XmssSecurity.Bridge
