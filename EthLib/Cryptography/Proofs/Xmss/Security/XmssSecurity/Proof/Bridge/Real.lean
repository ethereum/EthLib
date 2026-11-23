module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Resolution
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Translate
public import EthLib.Cryptography.Proofs.Xmss.Tree
public import EthLib.Cryptography.Proofs.Xmss.KeyGen
public import EthLib.Cryptography.Proofs.Xmss.Ots
public import EthLib.Cryptography.Proofs.Merkle.Build

/-!
# EthLib's key generation under the programmed cache

EthLib's key generation, with `H` a query to the oracle, makes `K = 13,434,881` hash calls.

They are the seed hash, then `K - 1` calls from the scheme's seed `S`.

Those are the parameter and the top tree.

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

/-- The derivations from the scheme's seed `S`, each a query to the oracle. -/
abbrev realPrf (seed : MasterSeed) : Xmss.SeedPrf (OracleComp HashSpec) :=
  Xmss.seedPrf queryH (ofSeed seed)

/-- EthLib's key generation from the scheme's seed `S`, after the seed hash.

It derives the parameter, then builds the top tree. -/
abbrev realKeygen (seed : MasterSeed) : OracleComp HashSpec (Xmss.PublicKey × Xmss.SecretKey) :=
  Xmss.Internal.keyGenFrom queryH (realPrf seed) (ofSeed seed)

/-! ## Counts -/

theorem queryCount_oracleHash (x : HashInput) :
    QueryCount (Concrete.oracleHash x : OracleComp HashSpec HashOutput) 1 := by
  change QueryCount (liftM (HashSpec.query x) : OracleComp HashSpec HashOutput) 1
  rw [← bind_pure (liftM (HashSpec.query x) : OracleComp HashSpec HashOutput)]
  exact .query x _ 0 fun a => .pure a

theorem queryCount_queryH (x : Array UInt64) :
    QueryCount (queryH x : OracleComp HashSpec Hash.Keccak.Lanes4) 1 :=
  (queryCount_oracleHash _).map _

/-- `n` computations in order make the sum of their calls. -/
theorem QueryCount.ofFnInOrder {α : Type} {k n : Nat} {c : Fin k → OracleComp HashSpec α}
    (h : ∀ i, QueryCount (c i) n) : QueryCount (Xmss.ofFnInOrder k c) (k * n) := by
  rw [HashSig.ofFnInOrder_eq_map_sequenceFin]
  exact (QueryCount.sequenceFin h).map _

theorem queryCount_th (publicParam : Xmss.PublicParam) (site : Xmss.CallSite)
    (payload : Array UInt64) :
    QueryCount (Xmss.th queryH publicParam site payload : OracleComp HashSpec Xmss.Digest) 1 := by
  unfold Xmss.th
  exact (queryCount_queryH _).bind fun _ => .pure _

theorem queryCount_chain (publicParam : Xmss.PublicParam) (layer : Xmss.Layer)
    (e : UInt32) (i : Fin V)
    (start : Nat) : ∀ (steps : Nat) (h : start + steps < CHAIN_LENGTH) (v : Xmss.Digest),
    QueryCount
      (Xmss.chain queryH publicParam layer e i start steps h v : OracleComp HashSpec Xmss.Digest)
      steps
  | 0, _, _ => .pure _
  | s + 1, h, v => by
    rw [Xmss.chain]
    exact (queryCount_chain publicParam layer e i start s
      (by omega) v).bind fun _ => queryCount_th _ _ _

theorem queryCount_chainStarts (publicParam : Xmss.PublicParam) (s : Xmss.Seed) (layer : Xmss.Layer)
    (e : UInt32) :
    QueryCount (Xmss.chainStarts publicParam
      (Xmss.seedPrf queryH s) layer e : OracleComp HashSpec _)
      29 := by
  rw [Xmss.chainStarts_seedPrf]
  exact (QueryCount.ofFnInOrder fun _ => queryCount_queryH _).bind fun _ => .pure _

/-- The hash calls of a node at `level`, its subtree's one-time keys included. -/
def nodeQueries (level : Nat) : Nat := 2 ^ level * (29 + 174 + 1) + 2 ^ level - 1

theorem queryCount_otsPublicLeaf (publicParam : Xmss.PublicParam) (s : Xmss.Seed)
    (layer : Xmss.Layer)
    (e : UInt32) :
    QueryCount (Xmss.otsPublicLeaf queryH publicParam (Xmss.seedPrf queryH s) layer e :
      OracleComp HashSpec Xmss.Digest)
      (nodeQueries 0) := by
  unfold Xmss.otsPublicLeaf
  rw [show nodeQueries 0 = 29 + (V * 3 + 1) by decide]
  refine (queryCount_chainStarts publicParam s layer e).bind fun starts => ?_
  exact (QueryCount.ofFnInOrder fun i => queryCount_chain publicParam layer e i 0
    3 (by decide) _).bind
    fun _ => queryCount_th _ _ _

theorem queryCount_node (publicParam : Xmss.PublicParam) (s : Xmss.Seed) (layer : Xmss.Layer) :
    ∀ (level : Nat) (j : Nat),
      QueryCount (Xmss.node queryH publicParam (Xmss.seedPrf queryH s) layer level j :
        OracleComp HashSpec Xmss.Digest)
        (nodeQueries level)
  | 0, j => by
    rw [Xmss.node_zero]
    exact queryCount_otsPublicLeaf publicParam s layer _
  | l + 1, j => by
    rw [Xmss.node_succ]
    have hcount : nodeQueries (l + 1) = nodeQueries l + (nodeQueries l + 1) := by
      simp only [nodeQueries, pow_succ]
      have : 1 ≤ 2 ^ l := Nat.one_le_two_pow
      omega
    rw [hcount]
    exact (queryCount_node publicParam s layer l _).bind fun _ =>
      (queryCount_node publicParam s layer l _).bind fun _ => queryCount_th _ _ _

/-- A build at `level` makes the calls of its node: each node of the subtree is computed once. -/
theorem queryCount_build (publicParam : Xmss.PublicParam) (s : Xmss.Seed) (layer : Xmss.Layer) :
    ∀ (level : Nat) (j : Nat),
      QueryCount (Xmss.build queryH publicParam (Xmss.seedPrf queryH s) layer level j :
        OracleComp HashSpec (Merkle.Built Xmss.Digest))
        (nodeQueries level)
  | 0, j => by
    have h := (queryCount_otsPublicLeaf publicParam s layer (UInt32.ofNat j)).bind
      (f := fun value => (pure (Merkle.Built.leaf value) :
        OracleComp HashSpec (Merkle.Built Xmss.Digest))) fun _ => .pure _
    rw [Nat.add_zero] at h
    unfold Xmss.build
    rw [Merkle.build_zero]
    exact h
  | l + 1, j => by
    have hcount : nodeQueries (l + 1) = nodeQueries l + (nodeQueries l + (1 + 0)) := by
      simp only [nodeQueries, pow_succ]
      have : 1 ≤ 2 ^ l := Nat.one_le_two_pow
      omega
    rw [hcount]
    unfold Xmss.build
    rw [Merkle.build_succ]
    exact (queryCount_build publicParam s layer l _).bind fun _ =>
      (queryCount_build publicParam s layer l _).bind fun _ =>
        (queryCount_th _ _ _).bind fun _ => .pure _

theorem queryCount_realKeygen (seed : MasterSeed) :
    QueryCount (realKeygen seed) (keygenQueries - 1) := by
  unfold realKeygen Xmss.Internal.keyGenFrom
  rw [Xmss.publicParamOf_seedPrf]
  rw [show keygenQueries - 1 = 1 + (nodeQueries 16 + 0) by decide]
  exact (queryCount_th _ _ _).bind fun _ =>
    (queryCount_build _ _ _ 16 0).bind fun _ => .pure _

/-! ## Resolved builds -/

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

/-! ## Erasing the derivations -/

/-- A query whose answer the cache holds resolves to it. -/
theorem resolves_queryH {cache : QueryCache HashSpec} {x : Array UInt64} {y : HashOutput}
    (h : cache (Hash.Keccak.lanesBytes x) = some y) :
    Resolves cache (queryH x : OracleComp HashSpec Hash.Keccak.Lanes4) (ofOutput y) := by
  change Resolves cache (ofOutput <$> (liftM (HashSpec.query (Hash.Keccak.lanesBytes x)) :
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
    Hash.Keccak.lanesBytes (Xmss.thInput (ofParam d.parameter)
      (Xmss.CallSite.prf .bottom (ofLeafIndex index) j) (ofSeed seed).toArray)
      = bottomInput d.parameter seed (index, ⟨j.val, j.isLt⟩) := by
  rw [bottomInput_eq]
  simp only [Xmss.thInput_eq_append,
    EthLib.Cryptography.Hash.Keccak.lanesBytes_append, Xmss.Unforgeability.toList_ofParam,
    Xmss.Unforgeability.toList_ofSeed, Xmss.Unforgeability.toList_encode_prf]
  rw [Xmss.Unforgeability.toNat_ofLeafIndex]
  -- The bottom layer adds no flag to `hi`.
  exact congrArg (fun x => bytesLE 16 d.parameter ++ fieldBytes (tweakFields 0 0 x index.val) ++
    bytesLE 32 seed) (by simp [Xmss.Layer.toNat])

/-- The hash that starts chains `2j` and `2j + 1` of a top key is the top derivation's. -/
theorem topPrfInput (seed : MasterSeed) (d : Derivations) (key : TopIndex) (j : Fin (V / 2)) :
    Hash.Keccak.lanesBytes
      (Xmss.thInput (ofParam d.parameter) (Xmss.CallSite.prf .top (ofTopIndex key) j)
        ((ofSeed seed).toArray))
      = topInput d.parameter seed (key, ⟨j.val, j.isLt⟩) := by
  rw [topInput_eq]
  simp only [Xmss.thInput_eq_append,
    EthLib.Cryptography.Hash.Keccak.lanesBytes_append, Xmss.Unforgeability.toList_ofParam,
    Xmss.Unforgeability.toList_ofSeed, Xmss.Unforgeability.toList_encode_prf]
  rw [Xmss.Unforgeability.toNat_ofTopIndex]
  -- The top layer adds its flag to `hi`.
  exact congrArg (fun x => bytesLE 16 d.parameter ++ fieldBytes (tweakFields 0 0 x key.val) ++
    bytesLE 32 seed) (by simp [Xmss.Layer.toNat, topFlag])

/-- Chain `i` starts at half `i mod 2` of the derivation of its pair. -/
theorem halves_eq (f : ChainPair → HashOutput) (pairs : Fin (V / 2) → HashOutput)
    (hpairs : ∀ j, pairs j = f ⟨j.val, j.isLt⟩) :
    ((Vector.ofFn fun j => ofOutput (pairs j)).flatMap
        fun p => #v[Xmss.halfOf 0 p, Xmss.halfOf 1 p]).cast (by decide)
      = ofChains fun chain => hashHalf chain.val (f (chainPair chain)) := by
  apply Vector.ext
  intro i hi
  simp only [Xmss.getElem_cast_flatMap_halves, Vector.getElem_ofFn, ofChains, hpairs]
  rw [Xmss.Unforgeability.halfOf_mod_two_ofOutput]
  rfl

/-- A bottom key's chain starts are the derivations' answers. -/
theorem chainStarts_bottom (seed : MasterSeed) (d : Derivations) (index : LeafIndex) :
    Resolves (progCache seed d) (Xmss.chainStarts (ofParam d.parameter) (realPrf seed)
        .bottom (ofLeafIndex index) : OracleComp HashSpec (Vector Xmss.Digest V))
      (ofChains (d.secret index)) := by
  rw [Xmss.chainStarts_seedPrf]
  refine (Resolves.ofFnInOrder
    (v := fun j : Fin (V / 2) => ofOutput (d.bottom (index, ⟨j.val, j.isLt⟩)))
    fun j => resolves_queryH ?_).bind ?_
  · rw [bottomPrfInput]
    exact progCache_bottom seed d _
  · rw [halves_eq (fun pair => d.bottom (index, pair)) _ fun _ => rfl]
    exact .pure _

/-- A top key's chain starts are the derivations' answers. -/
theorem chainStarts_top (seed : MasterSeed) (d : Derivations) (key : TopIndex) :
    Resolves (progCache seed d) (Xmss.chainStarts (ofParam d.parameter) (realPrf seed)
        .top (ofTopIndex key) : OracleComp HashSpec (Vector Xmss.Digest V))
      (ofChains (d.topSecret key)) := by
  rw [Xmss.chainStarts_seedPrf]
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
      (Xmss.node queryH (ofParam d.parameter) (realPrf seed) layer 0 j :
        OracleComp HashSpec Xmss.Digest) (ofDigest <$> leaves j)) :
    ∀ (level : Nat), level ≤ LAYER_HEIGHT → ∀ (j : Nat), j < 2 ^ (bits - level) →
      Erases (progCache seed d) (Xmss.node queryH (ofParam d.parameter) (realPrf seed)
          layer level j : OracleComp HashSpec Xmss.Digest)
        (ofDigest <$> EthLib.Cryptography.Merkle.node (Concrete.nodeAt d.parameter layer) leaves
          ⟨level, j⟩)
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
    Erases (progCache seed d) (Xmss.node queryH (ofParam d.parameter) (realPrf seed) .bottom
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
    Erases (progCache seed d) (Xmss.node queryH (ofParam d.parameter) (realPrf seed) .top
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
    Resolves cache (Xmss.node queryH (ofParam d.parameter) (realPrf seed) .bottom level j :
        OracleComp HashSpec Xmss.Digest)
      (ofDigest ((modelSecretKey d result).treeValue ⟨level, by
        have : level ≤ 16 := hlevel; simp only [treeHeight]; omega⟩
        (Concrete.merkleNodeOfNat j))) :=
  (erases_node_bottom seed d level hlevel j hj).resolves h.prog_le
    ((h.tree level hlevel j hj).map _)

theorem realTopNode (h : Prepared seed d result cache) (level : Nat)
    (hlevel : level ≤ LAYER_HEIGHT)
    (j : Nat) (hj : j < 2 ^ (16 - level)) :
    Resolves cache (Xmss.node queryH (ofParam d.parameter) (realPrf seed) .top level j :
        OracleComp HashSpec Xmss.Digest)
      (ofDigest ((modelSecretKey d result).topTreeValue ⟨level, by
        have : level ≤ 16 := hlevel; simp only [treeHeight]; omega⟩
        (Concrete.topNodeOfNat j))) :=
  (erases_node_top seed d level hlevel j hj).resolves h.prog_le
    ((h.topTree level hlevel j hj).map _)

/-- The parameter `P = Th(0^128, A_param, S)` resolves to the programmed one. -/
theorem realParam (h : Prepared seed d result cache) :
    Resolves cache (Xmss.publicParamOf (realPrf seed) :
      OracleComp HashSpec _) (ofParam d.parameter) := by
  rw [Xmss.publicParamOf_seedPrf]
  unfold Xmss.th
  have hparam : cache (paramInput seed) = some d.param := h.prog_le (progCache_param seed d)
  -- The all-zero parameter is the lanes of the zero bit vector.
  have hzero : (⟨0, 0⟩ : Xmss.PublicParam) = ofParam (0 : PublicParameter) := by
    simp only [Xmss.Unforgeability.ofParam, HashSig.ofDigestLanes]
    rfl
  -- The input is `0^128 | A_param | S`, the programmed parameter's.
  have hinput : Hash.Keccak.lanesBytes
      (Xmss.thInput (ofParam (0 : PublicParameter)) Xmss.CallSite.param ((ofSeed seed).toArray))
      = paramInput seed := by
    rw [paramInput_eq]
    simp only [Xmss.thInput_eq_append,
    EthLib.Cryptography.Hash.Keccak.lanesBytes_append, Xmss.Unforgeability.toList_ofParam,
      Xmss.Unforgeability.toList_ofSeed, Xmss.Unforgeability.toList_encode_param]
    rfl
  refine (resolves_queryH (y := d.param) ?_).bind ?_
  · rw [hzero, hinput]
    exact hparam
  · rw [Xmss.Unforgeability.halfOf_zero_ofOutput]
    exact .pure _

/-- EthLib's key generation from `S` resolves to the model's public key, and a key with no tree.

The key's top tree is a build that the cache resolves. -/
theorem realKeygen (h : Prepared seed d result cache) :
    ∃ top : Merkle.Built Xmss.Digest,
      Resolves cache (Xmss.build queryH (ofParam d.parameter) (realPrf seed) .top LAYER_HEIGHT 0 :
        OracleComp HashSpec _) top ∧
      Resolves cache (Bridge.realKeygen seed) (ofPublicKey ⟨result.1.1, d.parameter⟩,
        { schemeSeed := ofSeed seed, publicParam := ofParam d.parameter, top, cache := [] }) := by
  have hroot := h.realTopNode 16 le_rfl 0 (by decide)
  have hnode : Concrete.topNodeOfNat 0 = Concrete.rootNode := rfl
  rw [hnode, h.rootValue] at hroot
  obtain ⟨top, htop, hvalue⟩ := resolves_build _ _ _ _ hroot
  refine ⟨top, htop, ?_⟩
  unfold Bridge.realKeygen Xmss.Internal.keyGenFrom
  refine h.realParam.bind (htop.bind ?_)
  rw [hvalue]
  exact .pure _

end Prepared

end XmssSecurity.Bridge
