module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.CacheReplayEval

@[expose] public section

open EthLib.Cryptography

open OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

def pathNode (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  Concrete.merkleNodeOfNat (leafIndex.val / 2 ^ level)

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

/-- A node of the bottom forest is the shared tree's node, at any index that names it. -/
theorem treeNode_merkleNodeOfNat (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (level j : Nat) :
    treeNode cache parameter secret level (Concrete.merkleNodeOfNat j) =
      (Merkle.node (CacheView.nodeAt cache parameter .bottom)
        (fun j => pure (leafAt cache parameter secret (Concrete.merkleNodeOfNat j))) level
        j).run := by
  rw [treeNode]
  exact congrArg Id.run (EthLib.Cryptography.Merkle.node_mod _ _ lifetime
    (fun j => by rw [Concrete.merkleNodeOfNat_mod]) (CacheView.nodeAt_mod cache parameter .bottom)
    level j).symm

/-- The honest path of a leaf holds the sibling of each of its ancestors. -/
theorem authPath_signWithEncoding (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (randomness : Randomness) (encoding : Encoding) :
    (signWithEncoding cache secretKey leafIndex randomness encoding).authPath =
      fun level : Fin treeHeight =>
      (Merkle.node (CacheView.nodeAt cache secretKey.parameter .bottom)
        (fun j => pure (leafAt cache secretKey.parameter secretKey.chainStart
          (Concrete.merkleNodeOfNat j))) level ((leafIndex.val / 2 ^ level.val) ^^^ 1)).run := by
  funext level
  exact treeNode_merkleNodeOfNat cache secretKey.parameter secretKey.chainStart level _

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
  have hparent : (pathNode leafIndex (level.val + 1)).val = leafIndex.val / 2 ^ (level.val + 1) :=
    Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt leafIndex.isLt)
  have hhonest := XmssSecurity.Merkle.pairAt_honest
    (CacheView.nodeAt cache secretKey.parameter .bottom)
    (fun j => pure (leafAt cache secretKey.parameter secretKey.chainStart
      (Concrete.merkleNodeOfNat j))) leafIndex.val level
  rw [Concrete.merkleNodeOfNat_val] at hhonest
  rw [authPath_signWithEncoding]
  refine hhonest.trans ?_
  simp only [Concrete.childNode, treeNode_merkleNodeOfNat, hparent, Bool.false_eq_true,
    ↓reduceIte, Nat.add_zero]

/-- The honest path of a leaf climbs from its leaf to the root of its bottom tree. -/
theorem authenticationPath_climbs_to_root (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) :
    (Merkle.climb (CacheView.nodeAt cache secretKey.parameter .bottom) 0 leafIndex.val
        (leafAt cache secretKey.parameter secretKey.chainStart leafIndex)
        (List.ofFn (signWithEncoding cache secretKey leafIndex randomness encoding).authPath)).run =
      Concrete.bottomRoot cache secretKey (topKeyOf leafIndex) := by
  have hclimb := XmssSecurity.Merkle.climb_honest
    (CacheView.nodeAt cache secretKey.parameter .bottom)
    (fun j => pure (leafAt cache secretKey.parameter secretKey.chainStart
      (Concrete.merkleNodeOfNat j))) leafIndex.val treeHeight le_rfl
  rw [List.take_of_length_le (by simp), Concrete.merkleNodeOfNat_val] at hclimb
  rw [authPath_signWithEncoding]
  refine hclimb.trans ?_
  rw [Concrete.bottomRoot,
    show Concrete.bottomRootNode (topKeyOf leafIndex) = Concrete.merkleNodeOfNat
      (leafIndex.val / 2 ^ treeHeight) from Fin.ext (Nat.mod_eq_of_lt
        ((Nat.div_le_self _ _).trans_lt leafIndex.isLt)).symm, treeNode_merkleNodeOfNat]

/-! ### The top layer -/

def topPathNodeAt (key : TopIndex) (level : Nat) : TopNode :=
  Concrete.topNodeOfNat (key.val / 2 ^ level)

/-- A node of the top tree is the shared tree's node, at any index that names it. -/
theorem topTreeNode_topNodeOfNat (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) (level j : Nat) :
    topTreeNode cache parameter topSecret level (Concrete.topNodeOfNat j) =
      (Merkle.node (CacheView.nodeAt cache parameter .top)
        (fun j => pure (topLeafAt cache parameter topSecret (Concrete.topNodeOfNat j))) level
        j).run := by
  rw [topTreeNode]
  exact congrArg Id.run (EthLib.Cryptography.Merkle.node_mod _ _ topLifetime
    (fun j => by rw [Concrete.topNodeOfNat_mod]) (CacheView.nodeAt_mod cache parameter .top)
    level j).symm

/-- The honest top path of a key holds the sibling of each of its ancestors. -/
theorem honestTopPath_eq (cache : QueryCache HashSpec) (secretKey : SecretKey) (key : TopIndex) :
    Concrete.honestTopPath cache secretKey key = fun level : Fin treeHeight =>
      (Merkle.node (CacheView.nodeAt cache secretKey.parameter .top)
        (fun j => pure (topLeafAt cache secretKey.parameter secretKey.topChainStart
          (Concrete.topNodeOfNat j))) level ((key.val / 2 ^ level.val) ^^^ 1)).run := by
  funext level
  exact topTreeNode_topNodeOfNat cache secretKey.parameter secretKey.topChainStart level _

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
  have hparent : (topPathNodeAt key (level.val + 1)).val = key.val / 2 ^ (level.val + 1) :=
    Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt key.isLt)
  have hhonest := XmssSecurity.Merkle.pairAt_honest
    (CacheView.nodeAt cache secretKey.parameter .top)
    (fun j => pure (topLeafAt cache secretKey.parameter secretKey.topChainStart
      (Concrete.topNodeOfNat j))) key.val level
  rw [Concrete.topNodeOfNat_val] at hhonest
  rw [honestTopPath_eq]
  refine hhonest.trans ?_
  simp only [Concrete.topChildNode, topTreeNode_topNodeOfNat, hparent, Bool.false_eq_true,
    ↓reduceIte, Nat.add_zero]

/-- The honest top path of a key climbs from its leaf to the public root. -/
theorem honestTopPath_climbs_to_root (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (key : TopIndex) :
    (Merkle.climb (CacheView.nodeAt cache secretKey.parameter .top) 0 key.val
        (topLeafAt cache secretKey.parameter secretKey.topChainStart key)
        (List.ofFn (Concrete.honestTopPath cache secretKey key))).run =
      topTreeNode cache secretKey.parameter secretKey.topChainStart treeHeight
        Concrete.rootNode := by
  have hclimb := XmssSecurity.Merkle.climb_honest (CacheView.nodeAt cache secretKey.parameter .top)
    (fun j => pure (topLeafAt cache secretKey.parameter secretKey.topChainStart
      (Concrete.topNodeOfNat j))) key.val treeHeight le_rfl
  rw [List.take_of_length_le (by simp), Concrete.topNodeOfNat_val,
    Nat.div_eq_of_lt (show key.val < 2 ^ treeHeight from key.isLt)] at hclimb
  rw [honestTopPath_eq]
  refine hclimb.trans ?_
  rw [show Concrete.rootNode = Concrete.topNodeOfNat 0 from rfl, topTreeNode_topNodeOfNat]

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
