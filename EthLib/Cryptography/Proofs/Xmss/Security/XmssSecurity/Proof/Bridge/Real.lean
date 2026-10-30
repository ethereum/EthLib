import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Resolution
import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Translate

/-!
# EthLib's key generation under the programmed cache

EthLib's key generation, with `H` a query to the oracle, makes `K = 13,434,881` hash calls.

They are the seed hash, then `K - 1` calls from the scheme's seed `S`.

With every derivation programmed, a tree node EthLib computes from `S` is the model's node.

Only the derivation queries differ, and the cache answers them.
-/

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
  rw [Xmss.Unforgeability.ofFnInOrder_eq_map_sequenceFin]
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
    ∀ (level : Nat) (h : level ≤ LAYER_HEIGHT) (j : Nat),
      QueryCount (Xmss.node queryH pp s layer level h j : OracleComp HashSpec Xmss.Digest)
        (nodeQueries level)
  | 0, _, j => by
    unfold Xmss.node
    exact queryCount_otsPublicLeaf pp s layer _
  | l + 1, h, j => by
    unfold Xmss.node
    have hcount : nodeQueries (l + 1) = nodeQueries l + (nodeQueries l + 1) := by
      simp only [nodeQueries, pow_succ]
      have : 1 ≤ 2 ^ l := Nat.one_le_two_pow
      omega
    rw [hcount]
    exact (queryCount_node pp s layer l (by omega) _).bind fun _ =>
      (queryCount_node pp s layer l (by omega) _).bind fun _ => queryCount_th _ _ _

theorem queryCount_realKeygen (seed : MasterSeed) :
    QueryCount (realKeygen seed) (keygenQueries - 1) := by
  unfold realKeygen Xmss.publicKeyOf Xmss.publicParamOf
  rw [show keygenQueries - 1 = 1 + (nodeQueries 16 + 0) by decide]
  exact (queryCount_th _ _ _).bind fun _ =>
    (queryCount_node _ _ _ 16 le_rfl 0).bind fun _ => .pure _

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
  rw [Xmss.Unforgeability.ofFnInOrder_eq_map_sequenceFin]
  exact (Resolves.sequenceFin h).map _

/-- The hash that starts chains `2j` and `2j + 1` of a bottom key is the bottom derivation's. -/
theorem bottomPrfInput (seed : MasterSeed) (d : Derivations) (index : LeafIndex) (j : Fin (V / 2)) :
    (Xmss.thInput (ofParam d.parameter) (Xmss.addrPrf .bottom (ofLeafIndex index) j)
      (Xmss.packBytes (ofSeed seed))).data.toList
      = bottomInput d.parameter seed (index, ⟨j.val, j.isLt⟩) := by
  rw [bottomInput_eq]
  simp only [Xmss.thInput, Xmss.Unforgeability.toList_data_append,
    Xmss.Unforgeability.toList_data_packBytes, Xmss.Unforgeability.toList_ofParam,
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
  simp only [Xmss.thInput, Xmss.Unforgeability.toList_data_append,
    Xmss.Unforgeability.toList_data_packBytes, Xmss.Unforgeability.toList_ofParam,
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
  rw [Xmss.Unforgeability.ofFnInOrder_eq_sequenceFin, bind_map_left]
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
  rw [Xmss.Unforgeability.ofFnInOrder_eq_sequenceFin, bind_map_left]
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

/-- A bottom node from `S` is the model's with its derivations erased. -/
theorem erases_node_bottom (seed : MasterSeed) (d : Derivations) :
    ∀ (level : Nat) (hlevel : level ≤ LAYER_HEIGHT) (j : Nat), j < 2 ^ (32 - level) →
      Erases (progCache seed d) (Xmss.node queryH (ofParam d.parameter) (ofSeed seed) .bottom
          level hlevel j : OracleComp HashSpec Xmss.Digest)
        (ofDigest <$> Concrete.treeNode d.parameter d.secret level (Concrete.merkleNodeOfNat j))
  | 0, _, j, hj => by
    rw [Xmss.node.eq_1, Concrete.treeNode_zero_eq, ofNat_merkleNodeOfNat (by simpa using hj),
      ← leaf_bottom]
    unfold Xmss.otsPublicLeaf
    exact (erases_pure_of_resolves (chainStarts_bottom seed d _)).bind_known _ _ (.refl _ _)
  | l + 1, hlevel, j, hj => by
    have hl : l + 1 ≤ 16 := hlevel
    have hj2 : 2 * j + 1 < 2 ^ (32 - l) := by
      rw [show 32 - l = 32 - (l + 1) + 1 by omega, pow_succ]
      omega
    have hjlt : j < 4294967296 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 32 - (l + 1) ≤ 32 by omega)
      have : (2 : Nat) ^ 32 = 4294967296 := by norm_num
      omega
    rw [Xmss.node.eq_2, Concrete.treeNode_succ_eq]
    simp only [show l < treeHeight by simp only [treeHeight]; omega, ↓reduceDIte]
    -- The children of node `j` are nodes `2j` and `2j + 1`, in both.
    have hleft : Concrete.childNode (Concrete.merkleNodeOfNat j) false
        = Concrete.merkleNodeOfNat (2 * j) := by
      apply Fin.ext
      simp [Concrete.childNode, Concrete.merkleNodeOfNat, lifetime, treeHeight,
        Nat.mod_eq_of_lt hjlt]
    have hright : Concrete.childNode (Concrete.merkleNodeOfNat j) true
        = Concrete.merkleNodeOfNat (2 * j + 1) := by
      apply Fin.ext
      simp [Concrete.childNode, Concrete.merkleNodeOfNat, lifetime, treeHeight,
        Nat.mod_eq_of_lt hjlt]
    have hval : (Concrete.merkleNodeOfNat j).val = j := by
      simp [Concrete.merkleNodeOfNat, lifetime, treeHeight, Nat.mod_eq_of_lt hjlt]
    rw [hleft, hright]
    refine Erases.trans ((erases_node_bottom seed d l (by omega) (2 * j) (by omega)).bind _ _
      fun left => (erases_node_bottom seed d l (by omega) (2 * j + 1) hj2).bind _ _
        fun right => .refl _ _) ?_
    rw [map_bind, bind_map_left]
    refine (Erases.refl _ _).bind _ _ fun left => ?_
    rw [map_bind, bind_map_left]
    refine (Erases.refl _ _).bind _ _ fun right => ?_
    have hnode := Xmss.Unforgeability.nodeHash_bottom (m := OracleComp HashSpec) d.parameter
      ⟨l, by simp only [treeHeight]; omega⟩ (Concrete.merkleNodeOfNat j) left right
    rw [hval] at hnode
    rw [hnode]
    exact .refl _ _

/-- A top node from `S` is the model's with its derivations erased. -/
theorem erases_node_top (seed : MasterSeed) (d : Derivations) :
    ∀ (level : Nat) (hlevel : level ≤ LAYER_HEIGHT) (j : Nat), j < 2 ^ (16 - level) →
      Erases (progCache seed d) (Xmss.node queryH (ofParam d.parameter) (ofSeed seed) .top
          level hlevel j : OracleComp HashSpec Xmss.Digest)
        (ofDigest <$> Concrete.topTreeNode d.parameter d.topSecret level (Concrete.topNodeOfNat j))
  | 0, _, j, hj => by
    rw [Xmss.node.eq_1, Concrete.topTreeNode, ofNat_topNodeOfNat (by simpa using hj), ← leaf_top]
    unfold Xmss.otsPublicLeaf
    exact (erases_pure_of_resolves (chainStarts_top seed d _)).bind_known _ _ (.refl _ _)
  | l + 1, hlevel, j, hj => by
    have hl : l + 1 ≤ 16 := hlevel
    have hj2 : 2 * j + 1 < 2 ^ (16 - l) := by
      rw [show 16 - l = 16 - (l + 1) + 1 by omega, pow_succ]
      omega
    have hjlt : j < 65536 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 16 - (l + 1) ≤ 16 by omega)
      have : (2 : Nat) ^ 16 = 65536 := by norm_num
      omega
    rw [Xmss.node.eq_2, Concrete.topTreeNode]
    simp only [show l < treeHeight by simp only [treeHeight]; omega, ↓reduceDIte]
    -- The children of node `j` are nodes `2j` and `2j + 1`, in both.
    have hleft : Concrete.topChildNode (Concrete.topNodeOfNat j) false
        = Concrete.topNodeOfNat (2 * j) := by
      apply Fin.ext
      simp [Concrete.topChildNode, Concrete.topNodeOfNat, topLifetime, treeHeight,
        Nat.mod_eq_of_lt hjlt]
    have hright : Concrete.topChildNode (Concrete.topNodeOfNat j) true
        = Concrete.topNodeOfNat (2 * j + 1) := by
      apply Fin.ext
      simp [Concrete.topChildNode, Concrete.topNodeOfNat, topLifetime, treeHeight,
        Nat.mod_eq_of_lt hjlt]
    have hval : (Concrete.topNodeOfNat j).val = j := by
      simp [Concrete.topNodeOfNat, topLifetime, treeHeight, Nat.mod_eq_of_lt hjlt]
    rw [hleft, hright]
    refine Erases.trans ((erases_node_top seed d l (by omega) (2 * j) (by omega)).bind _ _
      fun left => (erases_node_top seed d l (by omega) (2 * j + 1) hj2).bind _ _
        fun right => .refl _ _) ?_
    rw [map_bind, bind_map_left]
    refine (Erases.refl _ _).bind _ _ fun left => ?_
    rw [map_bind, bind_map_left]
    refine (Erases.refl _ _).bind _ _ fun right => ?_
    have hnode := Xmss.Unforgeability.nodeHash_top (m := OracleComp HashSpec) d.parameter
      ⟨l, by simp only [treeHeight]; omega⟩ (Concrete.topNodeOfNat j) left right
    rw [hval] at hnode
    rw [hnode]
    exact .refl _ _

/-! ## Under the prepared cache -/

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec}

theorem realBottomNode (h : Prepared seed d result cache) (level : Nat)
    (hlevel : level ≤ LAYER_HEIGHT)
    (j : Nat) (hj : j < 2 ^ (32 - level)) :
    Resolves cache (Xmss.node queryH (ofParam d.parameter) (ofSeed seed) .bottom level hlevel j :
        OracleComp HashSpec Xmss.Digest)
      (ofDigest ((modelSecretKey d result).treeValue ⟨level, by
        have : level ≤ 16 := hlevel; simp only [treeHeight]; omega⟩
        (Concrete.merkleNodeOfNat j))) :=
  (erases_node_bottom seed d level hlevel j hj).resolves h.prog_le
    ((h.tree level hlevel j hj).map _)

theorem realTopNode (h : Prepared seed d result cache) (level : Nat)
    (hlevel : level ≤ LAYER_HEIGHT)
    (j : Nat) (hj : j < 2 ^ (16 - level)) :
    Resolves cache (Xmss.node queryH (ofParam d.parameter) (ofSeed seed) .top level hlevel j :
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
    rw [Xmss.Unforgeability.ofParam, Xmss.Unforgeability.ofBV_eq_littleEndian]
    apply Vector.ext
    intro i hi
    simp [Xmss.littleEndian]
  -- The input is `0^128 | A_param | S`, the programmed parameter's.
  have hinput : (Xmss.thInput (ofParam (0 : PublicParameter)) Xmss.addrParam
      (Xmss.packBytes (ofSeed seed))).data.toList
      = paramInput seed := by
    rw [paramInput_eq]
    simp only [Xmss.thInput, Xmss.Unforgeability.toList_data_append,
      Xmss.Unforgeability.toList_data_packBytes, Xmss.Unforgeability.toList_ofParam,
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
