module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CacheReplayEval

@[expose] public section

open EthLib.Cryptography

open OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

def pathNode (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  Concrete.merkleNodeOfNat (leafIndex.val / 2 ^ level)

@[simp]
theorem pathNode_zero (leafIndex : LeafIndex) : pathNode leafIndex 0 = leafIndex := by
  apply Fin.ext
  simp only [pathNode, Concrete.merkleNodeOfNat, pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt leafIndex.isLt

theorem div_pow_succ (value level : Nat) :
    value / 2 ^ (level + 1) = (value / 2 ^ level) / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- The node on the path of a leaf and its sibling, in order, are the children of the next node. -/
theorem ordered_pathNode (leafIndex : LeafIndex) (level : MerkleLevel) :
    Merkle.ordered (leafIndex.val / 2 ^ level.val) (pathNode leafIndex level.val)
        (Concrete.authenticationPathNode leafIndex level) =
      (Concrete.childNode (pathNode leafIndex (level.val + 1)) false,
        Concrete.childNode (pathNode leafIndex (level.val + 1)) true) := by
  have hparent : (pathNode leafIndex (level.val + 1)).val = leafIndex.val / 2 ^ level.val / 2 := by
    simp only [pathNode, Concrete.merkleNodeOfNat]
    rw [Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt leafIndex.isLt), div_pow_succ]
  refine (Merkle.ordered_sibling Concrete.merkleNodeOfNat _).trans ?_
  simp [Concrete.childNode, hparent]

theorem recover_signedChainValues (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (encoding : Encoding) :
    XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.chainStep cache secretKey.parameter leafIndex chain)
        encoding (signedChainValues cache secretKey leafIndex encoding) =
      oneTimePublicKey cache secretKey.parameter secretKey.chainStart leafIndex := by
  funext chain
  exact Wots.recover_signChain_eq_publicChain
    (CacheView.chainStep cache secretKey.parameter leafIndex chain)
    (encoding chain) (secretKey.chainStart leafIndex chain)

theorem recoveredEndpoints_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) :
    XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.chainStep cache secretKey.parameter leafIndex chain)
        encoding (signWithEncoding cache secretKey leafIndex randomness encoding).chainValue =
      oneTimePublicKey cache secretKey.parameter secretKey.chainStart leafIndex := by
  exact recover_signedChainValues cache secretKey leafIndex encoding

theorem leafHash_recovered_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) :
    CacheView.leafHash cache secretKey.parameter leafIndex
        (XmssSecurity.recoveredEndpoints
          (fun chain => CacheView.chainStep cache secretKey.parameter leafIndex chain)
          encoding (signWithEncoding cache secretKey leafIndex randomness encoding).chainValue) =
      leafAt cache secretKey.parameter secretKey.chainStart leafIndex := by
  rw [recoveredEndpoints_signWithEncoding]
  rfl

/-- The honest path of a leaf climbs from its leaf to its ancestor on each level. -/
theorem authenticationPath_climbs_to_treeNode (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    (Merkle.climb (CacheView.nodeAt cache secretKey.parameter .bottom) 0 leafIndex.val
        (leafAt cache secretKey.parameter secretKey.chainStart leafIndex)
        ((List.ofFn (signWithEncoding cache secretKey leafIndex randomness encoding).authPath).take
          levels)).run =
      treeNode cache secretKey.parameter secretKey.chainStart levels
        (pathNode leafIndex levels) := by
  induction levels with
  | zero => simp
  | succ level ih =>
      have hlevel : level < treeHeight := Nat.lt_of_succ_le hlevels
      rw [XmssSecurity.Merkle.climb_take_succ_run _ _ _ _ ⟨level, hlevel⟩,
        XmssSecurity.Merkle.pairAt, ih hlevel.le]
      -- The held node and the path's sibling are the two children of the next node.
      have hpair := congrArg
        (Prod.map (treeNode cache secretKey.parameter secretKey.chainStart level)
          (treeNode cache secretKey.parameter secretKey.chainStart level))
        (ordered_pathNode leafIndex ⟨level, hlevel⟩)
      rw [← Merkle.ordered_map] at hpair
      simp only [signWithEncoding, authenticationPath, hpair, Prod.map_fst, Prod.map_snd]
      rw [CacheView.nodeAt_bottom cache secretKey.parameter ⟨level, hlevel⟩, treeNode_succ_eq]
      simp [hlevel, pathNode]

/-- The pair the honest path of a leaf hashes above `level` is the children of its next node. -/
theorem pairAt_authenticationPath (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (randomness : Randomness) (encoding : Encoding)
    (level : MerkleLevel) :
    XmssSecurity.Merkle.pairAt (CacheView.nodeAt cache secretKey.parameter .bottom) leafIndex.val
        (signWithEncoding cache secretKey leafIndex randomness encoding).authPath
        (leafAt cache secretKey.parameter secretKey.chainStart leafIndex) level =
      (treeNode cache secretKey.parameter secretKey.chainStart level.val
          (Concrete.childNode (pathNode leafIndex (level.val + 1)) false),
        treeNode cache secretKey.parameter secretKey.chainStart level.val
          (Concrete.childNode (pathNode leafIndex (level.val + 1)) true)) := by
  rw [XmssSecurity.Merkle.pairAt, authenticationPath_climbs_to_treeNode cache secretKey leafIndex
    randomness encoding level.val level.isLt.le]
  have hpair := congrArg
    (Prod.map (treeNode cache secretKey.parameter secretKey.chainStart level)
      (treeNode cache secretKey.parameter secretKey.chainStart level))
    (ordered_pathNode leafIndex level)
  rw [← Merkle.ordered_map] at hpair
  exact hpair

/-- The honest path of a leaf climbs from its leaf to the root of its bottom tree. -/
theorem authenticationPath_climbs_to_root (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) :
    (Merkle.climb (CacheView.nodeAt cache secretKey.parameter .bottom) 0 leafIndex.val
        (leafAt cache secretKey.parameter secretKey.chainStart leafIndex)
        (List.ofFn (signWithEncoding cache secretKey leafIndex randomness encoding).authPath)).run =
      Concrete.bottomRoot cache secretKey (topKeyOf leafIndex) := by
  have hclimb := authenticationPath_climbs_to_treeNode cache secretKey leafIndex randomness
    encoding treeHeight le_rfl
  rw [List.take_of_length_le (by simp)] at hclimb
  rw [hclimb]
  unfold Concrete.bottomRoot
  congr 1
  apply Fin.ext
  simp only [pathNode, Concrete.bottomRootNode, topKeyOf, Concrete.merkleNodeOfNat]
  exact Nat.mod_eq_of_lt ((Nat.div_le_self leafIndex.val _).trans_lt leafIndex.isLt)

/-! ### The top layer -/

def topPathNodeAt (key : TopIndex) (level : Nat) : TopNode :=
  Concrete.topNodeOfNat (key.val / 2 ^ level)

@[simp]
theorem topPathNodeAt_zero (key : TopIndex) : topPathNodeAt key 0 = key := by
  apply Fin.ext
  simp only [topPathNodeAt, Concrete.topNodeOfNat, pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt key.isLt

/-- The node on the path of a top key and its sibling, in order, are the next node's children. -/
theorem ordered_topPathNodeAt (key : TopIndex) (level : MerkleLevel) :
    Merkle.ordered (key.val / 2 ^ level.val) (topPathNodeAt key level.val)
        (Concrete.topPathNode key level) =
      (Concrete.topChildNode (topPathNodeAt key (level.val + 1)) false,
        Concrete.topChildNode (topPathNodeAt key (level.val + 1)) true) := by
  have hparent : (topPathNodeAt key (level.val + 1)).val = key.val / 2 ^ level.val / 2 := by
    simp only [topPathNodeAt, Concrete.topNodeOfNat]
    rw [Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt key.isLt), div_pow_succ]
  refine (Merkle.ordered_sibling Concrete.topNodeOfNat _).trans ?_
  simp [Concrete.topChildNode, hparent]

/-- The honest top path of a key climbs from its leaf to its ancestor on each level. -/
theorem honestTopPath_climbs_to_topTreeNode (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (key : TopIndex) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    (Merkle.climb (CacheView.nodeAt cache secretKey.parameter .top) 0 key.val
        (topLeafAt cache secretKey.parameter secretKey.topChainStart key)
        ((List.ofFn (Concrete.honestTopPath cache secretKey key)).take levels)).run =
      topTreeNode cache secretKey.parameter secretKey.topChainStart levels
        (topPathNodeAt key levels) := by
  induction levels with
  | zero => simp [topTreeNode_zero_eq]
  | succ level ih =>
      have hlevel : level < treeHeight := Nat.lt_of_succ_le hlevels
      rw [XmssSecurity.Merkle.climb_take_succ_run _ _ _ _ ⟨level, hlevel⟩,
        XmssSecurity.Merkle.pairAt, ih hlevel.le]
      -- The held node and the path's sibling are the two children of the next node.
      have hpair := congrArg
        (Prod.map (topTreeNode cache secretKey.parameter secretKey.topChainStart level)
          (topTreeNode cache secretKey.parameter secretKey.topChainStart level))
        (ordered_topPathNodeAt key ⟨level, hlevel⟩)
      rw [← Merkle.ordered_map] at hpair
      simp only [Concrete.honestTopPath, hpair, Prod.map_fst, Prod.map_snd]
      rw [CacheView.nodeAt_top cache secretKey.parameter ⟨level, hlevel⟩, topTreeNode_succ_eq]
      simp [hlevel, topPathNodeAt]

/-- The pair the honest top path of a key hashes above `level` is the children of its next node. -/
theorem pairAt_honestTopPath (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (key : TopIndex) (level : MerkleLevel) :
    XmssSecurity.Merkle.pairAt (CacheView.nodeAt cache secretKey.parameter .top) key.val
        (Concrete.honestTopPath cache secretKey key)
        (topLeafAt cache secretKey.parameter secretKey.topChainStart key) level =
      (topTreeNode cache secretKey.parameter secretKey.topChainStart level.val
          (Concrete.topChildNode (topPathNodeAt key (level.val + 1)) false),
        topTreeNode cache secretKey.parameter secretKey.topChainStart level.val
          (Concrete.topChildNode (topPathNodeAt key (level.val + 1)) true)) := by
  rw [XmssSecurity.Merkle.pairAt, honestTopPath_climbs_to_topTreeNode cache secretKey key
    level.val level.isLt.le]
  have hpair := congrArg
    (Prod.map (topTreeNode cache secretKey.parameter secretKey.topChainStart level)
      (topTreeNode cache secretKey.parameter secretKey.topChainStart level))
    (ordered_topPathNodeAt key level)
  rw [← Merkle.ordered_map] at hpair
  exact hpair


/-- The honest top path of a key climbs from its leaf to the public root. -/

theorem honestTopPath_climbs_to_root (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (key : TopIndex) :
    (Merkle.climb (CacheView.nodeAt cache secretKey.parameter .top) 0 key.val
        (topLeafAt cache secretKey.parameter secretKey.topChainStart key)
        (List.ofFn (Concrete.honestTopPath cache secretKey key))).run =
      topTreeNode cache secretKey.parameter secretKey.topChainStart treeHeight
        Concrete.rootNode := by
  have hclimb := honestTopPath_climbs_to_topTreeNode cache secretKey key treeHeight le_rfl
  rw [List.take_of_length_le (by simp)] at hclimb
  rw [hclimb]
  congr 1
  apply Fin.ext
  simp only [topPathNodeAt, Concrete.topNodeOfNat, Concrete.rootNode]
  have hkey : key.val < 2 ^ treeHeight := key.isLt
  rw [Nat.div_eq_of_lt hkey]
  rfl

theorem recover_honestTopValues (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (key : TopIndex) (encoding : Encoding) :
    XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.topChainStep cache secretKey.parameter key chain)
        encoding (Concrete.honestTopValues cache secretKey key encoding) =
      topOneTimePublicKey cache secretKey.parameter secretKey.topChainStart key := by
  funext chain
  exact Wots.recover_signChain_eq_publicChain
    (CacheView.topChainStep cache secretKey.parameter key chain)
    (encoding chain) (secretKey.topChainStart key chain)

theorem topPartFromCache_eq (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (key : TopIndex) (randomness : Randomness) (encoding : Encoding)
    (hsigned : secretKey.topSigned key = some (randomness, encoding)) :
    topPartFromCache cache secretKey key =
      ⟨randomness, Concrete.honestTopValues cache secretKey key encoding,
        Concrete.honestTopPath cache secretKey key⟩ := by
  unfold topPartFromCache
  rw [hsigned]

def publicKeyFromCache (cache : QueryCache HashSpec) (secretKey : SecretKey) : PublicKey :=
  ⟨topTreeNode cache secretKey.parameter secretKey.topChainStart treeHeight Concrete.rootNode,
    secretKey.parameter⟩

attribute [irreducible] publicKeyFromCache

theorem publicKey_eq_publicKeyFromCache (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (root : Digest)
    (hroot : root = topTreeNode cache secretKey.parameter secretKey.topChainStart
      treeHeight Concrete.rootNode) :
    PublicKey.mk root secretKey.parameter = publicKeyFromCache cache secretKey := by
  rw [publicKeyFromCache]
  exact congrArg₂ PublicKey.mk hroot rfl

/-- Take the honest top signature of tree `b`, whose digest decodes in the cache.

It verifies on the honest bottom root. -/
theorem verifyTopFromCache_topPart (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (key : TopIndex) (randomness : Randomness) (encoding : Encoding)
    (hsigned : secretKey.topSigned key = some (randomness, encoding))
    (hdecode : TargetSum.decodeDigest
      (CacheView.topEncodingHash cache secretKey.parameter key
        (Concrete.bottomRoot cache secretKey key, randomness)) = some encoding) :
    Concrete.verifyTopFromCache cache (publicKeyFromCache cache secretKey) key
      (Concrete.bottomRoot cache secretKey key) (topPartFromCache cache secretKey key) = true := by
  have hpk : publicKeyFromCache cache secretKey =
      ⟨topTreeNode cache secretKey.parameter secretKey.topChainStart treeHeight Concrete.rootNode,
        secretKey.parameter⟩ := by
    rw [publicKeyFromCache]
  rw [Concrete.verifyTopFromCache_eq_true_iff, hpk,
    topPartFromCache_eq cache secretKey key randomness encoding hsigned]
  refine ⟨encoding, hdecode, ?_⟩
  simp only
  rw [recover_honestTopValues]
  exact honestTopPath_climbs_to_root cache secretKey key

theorem verifyFromCache_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (CacheView.encodingHash cache secretKey.parameter leafIndex (message, randomness)) =
        some encoding)
    (htop : ∃ topRandomness topEncoding,
      secretKey.topSigned (topKeyOf leafIndex) = some (topRandomness, topEncoding) ∧
      TargetSum.decodeDigest
        (CacheView.topEncodingHash cache secretKey.parameter (topKeyOf leafIndex)
          (Concrete.bottomRoot cache secretKey (topKeyOf leafIndex), topRandomness)) =
        some topEncoding) :
    Concrete.verifyFromCache cache (publicKeyFromCache cache secretKey) leafIndex message
      (signWithEncoding cache secretKey leafIndex randomness encoding) = true := by
  obtain ⟨topRandomness, topEncoding, hsigned, htopDecode⟩ := htop
  apply (Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).2
  refine ⟨encoding, ?_, ?_⟩
  · simpa [publicKeyFromCache, signWithEncoding] using hdecode
  · have hparam : (publicKeyFromCache cache secretKey).parameter = secretKey.parameter := by
      simp [publicKeyFromCache]
    rw [hparam, leafHash_recovered_signWithEncoding,
      authenticationPath_climbs_to_root cache secretKey leafIndex randomness encoding]
    exact verifyTopFromCache_topPart cache secretKey (topKeyOf leafIndex) topRandomness topEncoding
      hsigned htopDecode

end XmssSecurity.Concrete.CacheReplay
