module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Resolution
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Translate
public import EthLib.Cryptography.Proofs.Xmss.Tree

/-!
# EthLib's key generation under the programmed cache

EthLib's key generation, with `H` a query to the oracle, makes `K = 13,434,881` hash calls.

They are the seed hash, then `K - 1` calls from the scheme's seed `S`.

With every derivation programmed, a tree node EthLib computes from `S` is the model's node.

Only the derivation queries differ, and the cache answers them.
-/

@[expose] public section

open OracleComp OracleSpec
open EthLib.Cryptography
open EthLib.Cryptography.Xmss.Constants (V CHAIN_LENGTH LAYER_HEIGHT PUBLIC_PARAM_LEN)
open EthLib.Cryptography.Xmss.Unforgeability (queryH ofParam ofSeed ofDigest ofOutput ofChains
  ofLeafIndex ofTopIndex ofPublicKey chainOf)

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

/-- The hash calls of key generation: the seed hash, the parameter and the top tree. -/
def keygenQueries : Nat := 2 + 2 ^ 16 * (29 + 174 + 1) + 2 ^ 16 - 1

theorem keygenQueries_eq : keygenQueries = 13434881 := by decide

/-- EthLib's key generation from the scheme's seed `S`, after the seed hash. -/
def realKeygen (seed : MasterSeed) : OracleComp HashSpec Xmss.PublicKey :=
  Xmss.publicKeyOf queryH (ofSeed seed)

/-! ## Counts -/

theorem queryCount_oracleHash (x : HashInput) :
    QueryCount (Concrete.oracleHash x : OracleComp HashSpec HashOutput) 1 := by
  change QueryCount (liftM (HashSpec.query x) : OracleComp HashSpec HashOutput) 1
  rw [← bind_pure (liftM (HashSpec.query x) : OracleComp HashSpec HashOutput)]
  exact .query x _ 0 fun a => .pure a

theorem queryCount_queryH (x : ByteArray) :
    QueryCount (queryH x : OracleComp HashSpec (Vector UInt8 32)) 1 :=
  (queryCount_oracleHash _).map _

/-- `n` computations in order make the sum of their calls. -/
theorem QueryCount.ofFnInOrder {α : Type} {k n : Nat} {c : Fin k → OracleComp HashSpec α}
    (h : ∀ i, QueryCount (c i) n) : QueryCount (Xmss.ofFnInOrder k c) (k * n) := by
  rw [HashSig.ofFnInOrder_eq_map_sequenceFin]
  exact (QueryCount.sequenceFin h).map _

theorem queryCount_th (pp : Xmss.PublicParam) (A : Xmss.Address) (payload : ByteArray) :
    QueryCount (Xmss.th queryH pp A payload : OracleComp HashSpec Xmss.Digest) 1 := by
  unfold Xmss.th
  exact (queryCount_queryH _).bind fun _ => .pure _

theorem queryCount_chain (pp : Xmss.PublicParam) (layer : Xmss.Layer) (e : UInt32) (i : Fin V)
    (start : Nat) : ∀ (steps : Nat) (h : start + steps < CHAIN_LENGTH) (v : Xmss.Digest),
    QueryCount (Xmss.chain queryH pp layer e i start steps h v : OracleComp HashSpec Xmss.Digest)
      steps
  | 0, _, _ => .pure _
  | s + 1, h, v => by
    rw [Xmss.chain]
    exact (queryCount_chain pp layer e i start s (by omega) v).bind fun _ => queryCount_th _ _ _

theorem queryCount_chainStarts (pp : Xmss.PublicParam) (s : Xmss.Seed) (layer : Xmss.Layer)
    (e : UInt32) :
    QueryCount (Xmss.chainStarts queryH pp s layer e : OracleComp HashSpec _) 29 := by
  unfold Xmss.chainStarts
  exact (QueryCount.ofFnInOrder fun _ => queryCount_queryH _).bind fun _ => .pure _

/-- The hash calls of a node at `level`, its subtree's one-time keys included. -/
def nodeQueries (level : Nat) : Nat := 2 ^ level * (29 + 174 + 1) + 2 ^ level - 1

theorem queryCount_otsPublicLeaf (pp : Xmss.PublicParam) (s : Xmss.Seed) (layer : Xmss.Layer)
    (e : UInt32) :
    QueryCount (Xmss.otsPublicLeaf queryH pp s layer e : OracleComp HashSpec Xmss.Digest)
      (nodeQueries 0) := by
  unfold Xmss.otsPublicLeaf
  rw [show nodeQueries 0 = 29 + (V * 3 + 1) by decide]
  refine (queryCount_chainStarts pp s layer e).bind fun starts => ?_
  exact (QueryCount.ofFnInOrder fun i => queryCount_chain pp layer e i 0 3 (by decide) _).bind
    fun _ => queryCount_th _ _ _

theorem queryCount_node (pp : Xmss.PublicParam) (s : Xmss.Seed) (layer : Xmss.Layer) :
    ∀ (level : Nat) (j : Nat),
      QueryCount (Xmss.node queryH pp s layer level j : OracleComp HashSpec Xmss.Digest)
        (nodeQueries level)
  | 0, j => by
    rw [Xmss.node_zero]
    exact queryCount_otsPublicLeaf pp s layer _
  | l + 1, j => by
    rw [Xmss.node_succ]
    have hcount : nodeQueries (l + 1) = nodeQueries l + (nodeQueries l + 1) := by
      simp only [nodeQueries, pow_succ]
      have : 1 ≤ 2 ^ l := Nat.one_le_two_pow
      omega
    rw [hcount]
    exact (queryCount_node pp s layer l _).bind fun _ =>
      (queryCount_node pp s layer l _).bind fun _ => queryCount_th _ _ _

theorem queryCount_realKeygen (seed : MasterSeed) :
    QueryCount (realKeygen seed) (keygenQueries - 1) := by
  unfold realKeygen Xmss.publicKeyOf Xmss.publicParamOf
  rw [show keygenQueries - 1 = 1 + (nodeQueries 16 + 0) by decide]
  exact (queryCount_th _ _ _).bind fun _ =>
    (queryCount_node _ _ _ 16 0).bind fun _ => .pure _

/-! ## Erasing the derivations -/

/-- A query whose answer the cache holds resolves to it. -/
theorem resolves_queryH {cache : QueryCache HashSpec} {x : ByteArray} {y : HashOutput}
    (h : cache x.data.toList = some y) :
    Resolves cache (queryH x : OracleComp HashSpec (Vector UInt8 32)) (ofOutput y) := by
  change Resolves cache (ofOutput <$> (liftM (HashSpec.query x.data.toList) :
    OracleComp HashSpec HashOutput)) _
  rw [← bind_pure (liftM (HashSpec.query _) : OracleComp HashSpec HashOutput), map_bind]
  exact .query _ _ h _ _ (.pure _)

/-- A vector computed in order resolves entry by entry. -/
theorem Resolves.ofFnInOrder {α : Type} {cache : QueryCache HashSpec} {n : Nat}
    {c : Fin n → OracleComp HashSpec α} {v : Fin n → α} (h : ∀ i, Resolves cache (c i) (v i)) :
    Resolves cache (Xmss.ofFnInOrder n c) (Vector.ofFn v) := by
  rw [HashSig.ofFnInOrder_eq_map_sequenceFin]
  exact (Resolves.sequenceFin h).map _

/-- The hash that starts chains `2j` and `2j + 1` of a bottom key is the bottom derivation's. -/
theorem bottomPrfInput (seed : MasterSeed) (d : Derivations) (index : LeafIndex) (j : Fin (V / 2)) :
    (Xmss.thInput (ofParam d.parameter) (Xmss.addrPrf .bottom (ofLeafIndex index) j)
      (Xmss.packBytes (ofSeed seed))).data.toList
      = bottomInput d.parameter seed (index, ⟨j.val, j.isLt⟩) := by
  rw [bottomInput_eq]
  simp only [Xmss.thInput, EthLib.Cryptography.HashSig.toList_data_append,
    EthLib.Cryptography.HashSig.toList_data_packBytes, Xmss.Unforgeability.toList_ofParam,
    Xmss.Unforgeability.toList_ofSeed, Xmss.Unforgeability.toList_addrPrf]
  rw [Xmss.Unforgeability.toNat_ofLeafIndex]
  -- The bottom layer adds no flag to `hi`.
  exact congrArg (fun x => bytesLE 16 d.parameter ++ fieldBytes (tweakFields 0 0 x index.val) ++
    bytesLE 32 seed) (by simp [Xmss.Layer.toNat])

/-- The hash that starts chains `2j` and `2j + 1` of a top key is the top derivation's. -/
theorem topPrfInput (seed : MasterSeed) (d : Derivations) (key : TopIndex) (j : Fin (V / 2)) :
    (Xmss.thInput (ofParam d.parameter) (Xmss.addrPrf .top (ofTopIndex key) j)
      (Xmss.packBytes (ofSeed seed))).data.toList
      = topInput d.parameter seed (key, ⟨j.val, j.isLt⟩) := by
  rw [topInput_eq]
  simp only [Xmss.thInput, EthLib.Cryptography.HashSig.toList_data_append,
    EthLib.Cryptography.HashSig.toList_data_packBytes, Xmss.Unforgeability.toList_ofParam,
    Xmss.Unforgeability.toList_ofSeed, Xmss.Unforgeability.toList_addrPrf]
  rw [Xmss.Unforgeability.toNat_ofTopIndex]
  -- The top layer adds its flag to `hi`.
  exact congrArg (fun x => bytesLE 16 d.parameter ++ fieldBytes (tweakFields 0 0 x key.val) ++
    bytesLE 32 seed) (by simp [Xmss.Layer.toNat, topFlag])

/-- Chain `i` starts at half `i mod 2` of the derivation of its pair. -/
theorem halves_eq (f : ChainPair → HashOutput) (pairs : Fin (V / 2) → HashOutput)
    (hpairs : ∀ j, pairs j = f ⟨j.val, j.isLt⟩) :
    (Vector.ofFn fun i : Fin V => Xmss.halfOf ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
      ((Vector.ofFn fun j => ofOutput (pairs j))[i.val / 2]'(by
        have := i.isLt; simp only [V] at *; omega)))
      = ofChains fun chain => hashHalf chain.val (f (chainPair chain)) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, ofChains, hpairs]
  rw [Xmss.Unforgeability.halfOf_mod_two_ofOutput]
  rfl

/-- A bottom key's chain starts are the derivations' answers. -/
theorem chainStarts_bottom (seed : MasterSeed) (d : Derivations) (index : LeafIndex) :
    Resolves (progCache seed d) (Xmss.chainStarts queryH (ofParam d.parameter) (ofSeed seed)
        .bottom (ofLeafIndex index) : OracleComp HashSpec (Vector Xmss.Digest V))
      (ofChains (d.secret index)) := by
  unfold Xmss.chainStarts
  refine (Resolves.ofFnInOrder
    (v := fun j : Fin (V / 2) => ofOutput (d.bottom (index, ⟨j.val, j.isLt⟩)))
    fun j => resolves_queryH ?_).bind ?_
  · rw [bottomPrfInput]
    exact progCache_bottom seed d _
  · rw [halves_eq (fun pair => d.bottom (index, pair)) _ fun _ => rfl]
    exact .pure _

/-- A top key's chain starts are the derivations' answers. -/
theorem chainStarts_top (seed : MasterSeed) (d : Derivations) (key : TopIndex) :
    Resolves (progCache seed d) (Xmss.chainStarts queryH (ofParam d.parameter) (ofSeed seed)
        .top (ofTopIndex key) : OracleComp HashSpec (Vector Xmss.Digest V))
      (ofChains (d.topSecret key)) := by
  unfold Xmss.chainStarts
  refine (Resolves.ofFnInOrder (v := fun j : Fin (V / 2) => ofOutput (d.top (key, ⟨j.val, j.isLt⟩)))
    fun j => resolves_queryH ?_).bind ?_
  · rw [topPrfInput]
    exact progCache_top seed d _
  · rw [halves_eq (fun pair => d.top (key, pair)) _ fun _ => rfl]
    exact .pure _

/-- A bottom leaf from its chain starts is the model's leaf. -/
theorem leaf_bottom (P : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (index : LeafIndex) :
    (do
      let ends ← Xmss.ofFnInOrder V fun i => Xmss.chain queryH (ofParam P) .bottom
        (ofLeafIndex index) i 0 (CHAIN_LENGTH - 1) (by decide) (ofChains (secret index))[i]
      Xmss.otsLeafHash queryH (ofParam P) .bottom (ofLeafIndex index) ends :
        OracleComp HashSpec Xmss.Digest)
      = ofDigest <$> Concrete.leafAt P secret index := by
  rewrite [Xmss.Unforgeability.ofFnInOrder_congr (c' := fun i : Fin V => ofDigest <$>
    Concrete.chainWalk (m := OracleComp HashSpec) P index (chainOf i) 0 (CHAIN_LENGTH - 1)
      (secret index (chainOf i))) fun i => by
    rw [show (ofChains (secret index))[i] = ofDigest (secret index (chainOf i)) from
      Vector.getElem_ofFn _, Xmss.Unforgeability.chain_bottom]]
  rw [HashSig.ofFnInOrder_eq_sequenceFin, bind_map_left]
  unfold Concrete.leafAt Concrete.oneTimePublicKey
  rw [map_bind]
  refine bind_congr fun (ends : ChainIndex → Digest) => ?_
  exact Xmss.Unforgeability.otsLeafHash_bottom P index ends

/-- A top leaf from its chain starts is the model's leaf. -/
theorem leaf_top (P : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key : TopIndex) :
    (do
      let ends ← Xmss.ofFnInOrder V fun i => Xmss.chain queryH (ofParam P) .top
        (ofTopIndex key) i 0 (CHAIN_LENGTH - 1) (by decide) (ofChains (topSecret key))[i]
      Xmss.otsLeafHash queryH (ofParam P) .top (ofTopIndex key) ends :
        OracleComp HashSpec Xmss.Digest)
      = ofDigest <$> Concrete.topLeafAt P topSecret key := by
  rewrite [Xmss.Unforgeability.ofFnInOrder_congr (c' := fun i : Fin V => ofDigest <$>
    Concrete.topChainWalk (m := OracleComp HashSpec) P key (chainOf i) 0 (CHAIN_LENGTH - 1)
      (topSecret key (chainOf i))) fun i => by
    rw [show (ofChains (topSecret key))[i] = ofDigest (topSecret key (chainOf i)) from
      Vector.getElem_ofFn _, Xmss.Unforgeability.chain_top]]
  rw [HashSig.ofFnInOrder_eq_sequenceFin, bind_map_left]
  unfold Concrete.topLeafAt Concrete.topOneTimePublicKey
  rw [map_bind]
  refine bind_congr fun (ends : ChainIndex → Digest) => ?_
  exact Xmss.Unforgeability.otsLeafHash_top P key ends

theorem ofNat_merkleNodeOfNat {j : Nat} (hj : j < 2 ^ 32) :
    UInt32.ofNat j = ofLeafIndex (Concrete.merkleNodeOfNat j) := by
  apply UInt32.toNat.inj
  rw [Xmss.Unforgeability.toNat_ofLeafIndex]
  simp [Concrete.merkleNodeOfNat, lifetime, treeHeight,
    Nat.mod_eq_of_lt (show j < 4294967296 by omega)]

theorem ofNat_topNodeOfNat {j : Nat} (hj : j < 2 ^ 16) :
    UInt32.ofNat j = ofTopIndex (Concrete.topNodeOfNat j) := by
  apply UInt32.toNat.inj
  rw [Xmss.Unforgeability.toNat_ofTopIndex]
  simp [Concrete.topNodeOfNat, topLifetime, treeHeight, Nat.mod_eq_of_lt (show j < 65536 by omega),
    Nat.mod_eq_of_lt (show j < 4294967296 by omega)]

/-- A node of a layer from `S` is the model's with its derivations erased, when its leaves are.

The hypothesis covers the first `2^bits` leaves, and the layer has at least that many leaves. -/
theorem erases_node (seed : MasterSeed) (d : Derivations) (layer : Xmss.Layer) (bits : Nat)
    (hheight : LAYER_HEIGHT ≤ bits) (hbits : 2 ^ bits ≤ Concrete.layerLeaves layer)
    (leaves : Nat → OracleComp HashSpec Digest)
    (hleaves : ∀ j < 2 ^ bits, Erases (progCache seed d)
      (Xmss.node queryH (ofParam d.parameter) (ofSeed seed) layer 0 j :
        OracleComp HashSpec Xmss.Digest) (ofDigest <$> leaves j)) :
    ∀ (level : Nat), level ≤ LAYER_HEIGHT → ∀ (j : Nat), j < 2 ^ (bits - level) →
      Erases (progCache seed d) (Xmss.node queryH (ofParam d.parameter) (ofSeed seed) layer
          level j : OracleComp HashSpec Xmss.Digest)
        (ofDigest <$> EthLib.Cryptography.Merkle.node (Concrete.nodeAt d.parameter layer) leaves
          level j)
  | 0, _, j, hj => by
    simpa [EthLib.Cryptography.Merkle.node_zero] using hleaves j (by simpa using hj)
  | l + 1, hlevel, j, hj => by
    have hl : l + 1 ≤ 16 := hlevel
    have hj2 : 2 * j + 1 < 2 ^ (bits - l) := by
      rw [show bits - l = bits - (l + 1) + 1 by omega, pow_succ]
      omega
    have hjN : j < Concrete.layerLeaves layer :=
      (hj.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))).trans_le hbits
    rw [Xmss.node_succ, EthLib.Cryptography.Merkle.node_succ]
    -- The children of node `j` are nodes `2j` and `2j + 1`, in both.
    refine Erases.trans ((erases_node seed d layer bits hheight hbits leaves hleaves l (by omega)
      (2 * j) (by omega)).bind _ _ fun left => (erases_node seed d layer bits hheight hbits leaves
        hleaves l (by omega) (2 * j + 1) hj2).bind _ _ fun right => .refl _ _) ?_
    rw [map_bind, bind_map_left]
    refine (Erases.refl _ _).bind _ _ fun left => ?_
    rw [map_bind, bind_map_left]
    refine (Erases.refl _ _).bind _ _ fun right => ?_
    -- On the tree, the model's node hash is EthLib's.
    simp only [Concrete.nodeAt, show l < treeHeight by simp only [treeHeight]; omega, ↓reduceIte,
      Nat.mod_eq_of_lt hjN, Xmss.Unforgeability.map_ofDigest_toDigest]
    exact .refl _ _

/-- A bottom node from `S` is the model's with its derivations erased. -/
theorem erases_node_bottom (seed : MasterSeed) (d : Derivations) (level : Nat)
    (hlevel : level ≤ LAYER_HEIGHT) (j : Nat) (hj : j < 2 ^ (32 - level)) :
    Erases (progCache seed d) (Xmss.node queryH (ofParam d.parameter) (ofSeed seed) .bottom
        level j : OracleComp HashSpec Xmss.Digest)
      (ofDigest <$> Concrete.treeNode d.parameter d.secret level (Concrete.merkleNodeOfNat j)) := by
  have hjN : j < lifetime := hj.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  rw [Concrete.treeNode, show (Concrete.merkleNodeOfNat j).val = j from Nat.mod_eq_of_lt hjN]
  refine erases_node seed d .bottom 32 (by decide) le_rfl _ (fun j hj => ?_) level hlevel j hj
  rw [Xmss.node_zero, ofNat_merkleNodeOfNat hj, ← leaf_bottom]
  unfold Xmss.otsPublicLeaf
  exact (erases_pure_of_resolves (chainStarts_bottom seed d _)).bind_known _ _ (.refl _ _)

/-- A top node from `S` is the model's with its derivations erased. -/
theorem erases_node_top (seed : MasterSeed) (d : Derivations) (level : Nat)
    (hlevel : level ≤ LAYER_HEIGHT) (j : Nat) (hj : j < 2 ^ (16 - level)) :
    Erases (progCache seed d) (Xmss.node queryH (ofParam d.parameter) (ofSeed seed) .top
        level j : OracleComp HashSpec Xmss.Digest)
      (ofDigest <$> Concrete.topTreeNode d.parameter d.topSecret level
        (Concrete.topNodeOfNat j)) := by
  have hjN : j < topLifetime := hj.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  rw [Concrete.topTreeNode, show (Concrete.topNodeOfNat j).val = j from Nat.mod_eq_of_lt hjN]
  refine erases_node seed d .top 16 (by decide) le_rfl _ (fun j hj => ?_) level hlevel j hj
  rw [Xmss.node_zero, ofNat_topNodeOfNat hj, ← leaf_top]
  unfold Xmss.otsPublicLeaf
  exact (erases_pure_of_resolves (chainStarts_top seed d _)).bind_known _ _ (.refl _ _)

/-! ## Under the prepared cache -/

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec}

theorem realBottomNode (h : Prepared seed d result cache) (level : Nat)
    (hlevel : level ≤ LAYER_HEIGHT)
    (j : Nat) (hj : j < 2 ^ (32 - level)) :
    Resolves cache (Xmss.node queryH (ofParam d.parameter) (ofSeed seed) .bottom level j :
        OracleComp HashSpec Xmss.Digest)
      (ofDigest ((modelSecretKey d result).treeValue ⟨level, by
        have : level ≤ 16 := hlevel; simp only [treeHeight]; omega⟩
        (Concrete.merkleNodeOfNat j))) :=
  (erases_node_bottom seed d level hlevel j hj).resolves h.prog_le
    ((h.tree level hlevel j hj).map _)

theorem realTopNode (h : Prepared seed d result cache) (level : Nat)
    (hlevel : level ≤ LAYER_HEIGHT)
    (j : Nat) (hj : j < 2 ^ (16 - level)) :
    Resolves cache (Xmss.node queryH (ofParam d.parameter) (ofSeed seed) .top level j :
        OracleComp HashSpec Xmss.Digest)
      (ofDigest ((modelSecretKey d result).topTreeValue ⟨level, by
        have : level ≤ 16 := hlevel; simp only [treeHeight]; omega⟩
        (Concrete.topNodeOfNat j))) :=
  (erases_node_top seed d level hlevel j hj).resolves h.prog_le
    ((h.topTree level hlevel j hj).map _)

/-- The parameter `P = Th(0^128, A_param, S)` resolves to the programmed one. -/
theorem realParam (h : Prepared seed d result cache) :
    Resolves cache (Xmss.publicParamOf queryH (ofSeed seed) : OracleComp HashSpec _)
      (ofParam d.parameter) := by
  unfold Xmss.publicParamOf Xmss.th
  have hparam : cache (paramInput seed) = some d.param := h.prog_le (progCache_param seed d)
  -- The all-zero parameter is the bytes of the zero bit vector.
  have hzero : Vector.replicate PUBLIC_PARAM_LEN (0 : UInt8)
      = ofParam (0 : PublicParameter) := by
    rw [Xmss.Unforgeability.ofParam, Xmss.Unforgeability.ofBV_eq_uintToBytes]
    apply Vector.ext
    intro i hi
    simp [Xmss.uintToBytes]
  -- The input is `0^128 | A_param | S`, the programmed parameter's.
  have hinput : (Xmss.thInput (ofParam (0 : PublicParameter)) Xmss.addrParam
      (Xmss.packBytes (ofSeed seed))).data.toList
      = paramInput seed := by
    rw [paramInput_eq]
    simp only [Xmss.thInput, EthLib.Cryptography.HashSig.toList_data_append,
      EthLib.Cryptography.HashSig.toList_data_packBytes, Xmss.Unforgeability.toList_ofParam,
      Xmss.Unforgeability.toList_ofSeed, Xmss.Unforgeability.toList_addrParam]
    rfl
  refine (resolves_queryH (y := d.param) ?_).bind ?_
  · rw [hzero, hinput]
    exact hparam
  · rw [Xmss.Unforgeability.halfOf_zero_ofOutput]
    exact .pure _

/-- EthLib's key generation from `S` resolves to the model's public key. -/
theorem realKeygen (h : Prepared seed d result cache) :
    Resolves cache (Bridge.realKeygen seed) (ofPublicKey ⟨result.1.1, d.parameter⟩) := by
  unfold Bridge.realKeygen Xmss.publicKeyOf
  refine h.realParam.bind ?_
  have hroot := h.realTopNode 16 le_rfl 0 (by decide)
  have hnode : Concrete.topNodeOfNat 0 = Concrete.rootNode := rfl
  rw [hnode, h.rootValue] at hroot
  exact hroot.bind (.pure _)

end Prepared

end XmssSecurity.Bridge
