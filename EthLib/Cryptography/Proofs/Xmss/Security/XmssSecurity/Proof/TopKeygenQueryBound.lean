module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.HonestKeygenRun
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Translate

/-!
# Key generation queries each top chain, leaf and Merkle address at most once

Only the top tree queries those addresses.

The bottom trees query bottom domains, and the top grinding only top message digests.

The top tree queries each such address at most once.
-/

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

-- The top tree is fully concrete at the tree height, so keep elaboration from unfolding it.
attribute [local irreducible] Concrete.topTreeNode

def TopCovers (levels : Nat) (node : TopNode) (key : TopIndex) : Prop :=
  node.val * 2 ^ levels ≤ key.val ∧ key.val < (node.val + 1) * 2 ^ levels

instance (levels : Nat) (node : TopNode) (key : TopIndex) :
    Decidable (TopCovers levels node key) := by
  unfold TopCovers
  infer_instance

def TopSubtreeValid (levels : Nat) (node : TopNode) : Prop :=
  (node.val + 1) * 2 ^ levels ≤ topLifetime

theorem topCovers_iff (levels : Nat) (node : TopNode) (key : TopIndex) :
    TopCovers levels node key ↔ key.val / 2 ^ levels = node.val := by
  have hpos := Nat.two_pow_pos levels
  rw [TopCovers, Nat.div_eq_iff hpos, Nat.add_mul, one_mul]
  generalize 2 ^ levels = d at *
  omega

/-! ### Top chains and leaves -/

theorem Concrete.topChainWalk_queryBound_zero_of_avoids
    (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (targetDomain : HashDomain)
    (havoid : ∀ offset, offset < steps →
      ∀ hvalid : position + offset < chainLength - 1,
        HashDomain.topChain key chain ⟨position + offset, hvalid⟩ ≠ targetDomain) :
    (Concrete.topChainWalk parameter key chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter targetDomain) 0 := by
  induction steps with
  | zero => simp [Concrete.topChainWalk]
  | succ steps ih =>
      rw [Concrete.topChainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih fun offset hoffset => havoid offset (by omega)) ?_
      intro previous _
      split
      · tweakable_hashes
        exact Concrete.tweakableHash_queryBound_atOtherAddress parameter targetDomain
          (.topChain key chain ⟨position + steps, by assumption⟩)
          (Concrete.digestBytes previous) (havoid steps (by omega) _)
      · simp

set_option maxHeartbeats 800000 in
theorem Concrete.topChainWalk_queryBound_atAddress
    (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (targetDomain : HashDomain) :
    (Concrete.topChainWalk parameter key chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter targetDomain) 1 := by
  induction steps with
  | zero => simp [Concrete.topChainWalk]
  | succ steps ih =>
      rw [Concrete.topChainWalk]
      split
      · rename_i hposition
        let calledDomain : HashDomain :=
          .topChain key chain ⟨position + steps, hposition⟩
        by_cases heq : calledDomain = targetDomain
        · subst targetDomain
          have hprefix :
              (Concrete.topChainWalk parameter key chain position steps value :
                OracleComp HashSpec Digest).IsQueryBoundP
                  (AtHashAddress parameter calledDomain) 0 := by
            apply Concrete.topChainWalk_queryBound_zero_of_avoids
            intro offset hoffset hvalid hsame
            simp only [calledDomain, HashDomain.topChain.injEq, Fin.mk.injEq] at hsame
            omega
          refine OracleComp.isQueryBoundP_bind (m := 1) hprefix ?_
          intro previous _
          tweakable_hashes
          exact Concrete.tweakableHash_queryBound_atAddress parameter calledDomain
            (Concrete.digestBytes previous)
        · refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
          intro previous _
          tweakable_hashes
          exact Concrete.tweakableHash_queryBound_atOtherAddress parameter targetDomain
            calledDomain (Concrete.digestBytes previous) heq
      · refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
        intro previous _
        simp

/-- A top leaf queries the top chain addresses of its own key only, each at most once. -/
theorem Concrete.topLeafAt_queryBound_chainAddress
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key targetKey : TopIndex) (targetChain : ChainIndex) (targetStep : ChainStep) :
    (Concrete.topLeafAt parameter topSecret key : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.topChain targetKey targetChain targetStep))
      (if key = targetKey then 1 else 0) := by
  have hleaf (endpoints : ChainIndex → Digest) :
      (Concrete.topLeafHash parameter key endpoints : OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.topChain targetKey targetChain targetStep)) 0 := by
    tweakable_hashes
    exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
      (.topChain targetKey targetChain targetStep) (.topLeaf key)
      (Concrete.leafPayload endpoints) (by simp)
  rw [Concrete.topLeafAt]
  by_cases hkey : key = targetKey
  · subst targetKey
    rw [ite_eq_left rfl]
    refine OracleComp.isQueryBoundP_bind (m := 0) ?_ fun endpoints _ => hleaf endpoints
    rw [Concrete.topOneTimePublicKey]
    apply Concrete.sequenceFin_queryBound_one _ _ targetChain
    · exact Concrete.topChainWalk_queryBound_atAddress parameter key targetChain 0
        (chainLength - 1) (topSecret key targetChain) _
    · intro chain hchain
      apply Concrete.topChainWalk_queryBound_zero_of_avoids
      intro offset _ hvalid heq
      simp only [HashDomain.topChain.injEq] at heq
      exact hchain heq.2.1
  · rw [ite_eq_right hkey]
    refine OracleComp.isQueryBoundP_bind (m := 0) ?_ fun endpoints _ => hleaf endpoints
    rw [Concrete.topOneTimePublicKey]
    refine Concrete.sequenceFin_queryBound_zero _ _ fun chain => ?_
    apply Concrete.topChainWalk_queryBound_zero_of_avoids
    intro offset _ hvalid heq
    simp only [HashDomain.topChain.injEq] at heq
    exact hkey heq.1

/-- A top leaf queries its own leaf address once and no other top leaf address. -/
theorem Concrete.topLeafAt_queryBound_leafAddress
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key targetKey : TopIndex) :
    (Concrete.topLeafAt parameter topSecret key : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.topLeaf targetKey)) (if key = targetKey then 1 else 0) := by
  have hchains : (Concrete.topOneTimePublicKey parameter topSecret key :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (AtHashAddress parameter (.topLeaf targetKey)) 0 := by
    rw [Concrete.topOneTimePublicKey]
    refine Concrete.sequenceFin_queryBound_zero _ _ fun chain => ?_
    apply Concrete.topChainWalk_queryBound_zero_of_avoids
    intro offset _ hvalid heq
    cases heq
  rw [Concrete.topLeafAt]
  by_cases hkey : key = targetKey
  · subst targetKey
    rw [ite_eq_left rfl]
    tweakable_hashes
    exact OracleComp.isQueryBoundP_bind (n := 0) (m := 1) hchains fun endpoints _ =>
      Concrete.tweakableHash_queryBound_atAddress parameter (.topLeaf key)
        (Concrete.leafPayload endpoints)
  · rw [ite_eq_right hkey]
    tweakable_hashes
    exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hchains fun endpoints _ =>
      Concrete.tweakableHash_queryBound_atOtherAddress parameter (.topLeaf targetKey)
        (.topLeaf key) (Concrete.leafPayload endpoints) (by simpa using hkey)

theorem Concrete.topLeafAt_queryBound_zero_merkleAddress
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key : TopIndex) (targetLevel : MerkleLevel) (targetNode : TopNode) :
    (Concrete.topLeafAt parameter topSecret key : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.topMerkle targetLevel targetNode)) 0 := by
  rw [Concrete.topLeafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0) ?_ ?_
  · rw [Concrete.topOneTimePublicKey]
    refine Concrete.sequenceFin_queryBound_zero _ _ fun chain => ?_
    apply Concrete.topChainWalk_queryBound_zero_of_avoids
    intro offset _ hvalid heq
    cases heq
  · intro endpoints _
    tweakable_hashes
    exact Concrete.tweakableHash_queryBound_atOtherAddress parameter _ (.topLeaf key)
      (Concrete.leafPayload endpoints) (by simp)

/-! ### The top tree -/

/-- The top tree queries a top chain or leaf address of the keys it covers, at most once. -/
theorem Concrete.topTreeNode_queryBound_keyAddress
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (targetKey : TopIndex) (target : HashDomain)
    (hleaf : ∀ key, (Concrete.topLeafAt parameter topSecret key :
      OracleComp HashSpec Digest).IsQueryBoundP (AtHashAddress parameter target)
        (if key = targetKey then 1 else 0))
    (hmerkle : ∀ level node, HashDomain.topMerkle level node ≠ target)
    (levels : Nat) (node : TopNode) (hvalid : TopSubtreeValid levels node) :
    (Concrete.topTreeNode parameter topSecret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP (AtHashAddress parameter target)
        (if TopCovers levels node targetKey then 1 else 0) := by
  rw [Concrete.topTreeNode]
  simp only [topCovers_iff]
  refine node_queryBound_leaf _ _ _ topLifetime targetKey.val (fun j hj => ?_)
    (Concrete.nodeAt_queryBound_zero parameter _ .top fun _ _ _ =>
      Concrete.tweakableHash_queryBound_atOtherAddress parameter _ _ _ (hmerkle _ _))
    levels node.val hvalid
  rw [show Concrete.topNodeOfNat j = ⟨j, hj⟩ from Fin.ext (Nat.mod_eq_of_lt hj)]
  simpa [Fin.ext_iff, eq_comm] using hleaf ⟨j, hj⟩

def TopMerkleInSubtree (targetLevel : MerkleLevel) (targetNode : TopNode)
    (levels : Nat) (node : TopNode) : Prop :=
  targetLevel.val < levels ∧ TopCovers (levels - (targetLevel.val + 1)) node targetNode

instance (targetLevel : MerkleLevel) (targetNode : TopNode) (levels : Nat) (node : TopNode) :
    Decidable (TopMerkleInSubtree targetLevel targetNode levels node) := by
  unfold TopMerkleInSubtree
  infer_instance

theorem Concrete.topTreeNode_queryBound_merkleAddress
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (targetLevel : MerkleLevel) (targetNode : TopNode)
    (levels : Nat) (node : TopNode) (hvalid : TopSubtreeValid levels node) :
    (Concrete.topTreeNode parameter topSecret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.topMerkle targetLevel targetNode))
        (if TopMerkleInSubtree targetLevel targetNode levels node then 1 else 0) := by
  rw [Concrete.topTreeNode]
  have hbound := node_queryBound_node (Concrete.nodeAt parameter .top)
    (fun j => Concrete.topLeafAt parameter topSecret (Concrete.topNodeOfNat j)) _ topLifetime
    (targetLevel.val + 1) targetNode.val
    (by omega) (fun j => Concrete.topLeafAt_queryBound_zero_merkleAddress parameter topSecret _
      targetLevel targetNode) (fun k j left right hj => by
        simpa [Concrete.nodeDomain] using Concrete.nodeAt_queryBound_node parameter .top
          targetLevel targetNode.val targetNode.isLt k j
          (by have := Nat.one_le_two_pow (n := k); simp only [Concrete.layerLeaves]; nlinarith)
          left right) levels node.val hvalid
  have hiff : TopMerkleInSubtree targetLevel targetNode levels node ↔ targetLevel.val + 1 ≤ levels ∧
      targetNode.val / 2 ^ (levels - (targetLevel.val + 1)) = node.val := by
    rw [TopMerkleInSubtree, topCovers_iff, Nat.succ_le_iff]
  simpa only [hiff] using hbound

/-- The top tree queries no top message digest address. -/
theorem Concrete.topTreeNode_queryBound_zero_topEncoding
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key : TopIndex) (levels : Nat) (node : TopNode) :
    (Concrete.topTreeNode parameter topSecret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP (AtHashAddress parameter (.topEncoding key)) 0 := by
  rw [Concrete.topTreeNode]
  refine EthLib.Cryptography.Merkle.node_rec _ (fun x => OracleComp.IsQueryBoundP x _ 0)
    (fun hx hf => OracleComp.isQueryBoundP_bind (m := 0) hx fun b _ => hf b) _ (fun j => ?_)
    (Concrete.nodeAt_queryBound_zero parameter _ .top fun _ _ _ =>
      Concrete.tweakableHash_queryBound_atOtherAddress parameter _ _ _
        (by simp [Concrete.nodeDomain]))
    levels node.val
  rw [Concrete.topLeafAt]
  tweakable_hashes
  refine OracleComp.isQueryBoundP_bind (m := 0) ?_ fun endpoints _ =>
    Concrete.tweakableHash_queryBound_atOtherAddress parameter _ (.topLeaf _)
      (Concrete.leafPayload endpoints) (by simp)
  rw [Concrete.topOneTimePublicKey]
  refine Concrete.sequenceFin_queryBound_zero _ _ fun chain => ?_
  apply Concrete.topChainWalk_queryBound_zero_of_avoids
  intro offset _ hvalid heq
  cases heq

/-! ### Key generation -/

theorem Concrete.topSignFrom_queryBound_zero_of_not_encoding
    (parameter : PublicParameter) (target : HashDomain)
    (htarget : ∀ key, HashDomain.topEncoding key ≠ target)
    (key : TopIndex) (root : Digest) (base : Randomness) (attempts trial : Nat) :
    (Concrete.topSignFrom parameter key root base attempts trial :
      OracleComp HashSpec (Option (Randomness × Encoding))).IsQueryBoundP
        (AtHashAddress parameter target) 0 := by
  induction attempts generalizing trial with
  | zero => simp [Concrete.topSignFrom]
  | succ attempts ih =>
      rw [Concrete.topSignFrom]
      tweakable_hashes
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (Concrete.tweakableHash_queryBound_atOtherAddress parameter target _ _ (htarget key)) ?_
      intro digest _
      split
      · simp
      · exact ih _

/-- Consider a top chain, leaf or Merkle address.

Key generation's honest computation queries it only in its top tree. -/
theorem Concrete.honestKeygen_queryBound_of_topTree
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (target : HashDomain) (htop : target.isTop = true)
    (htarget : ∀ key, HashDomain.topEncoding key ≠ target) (n : Nat)
    (htree : (Concrete.topTreeNode parameter topSecret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest).IsQueryBoundP (AtHashAddress parameter target) n) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP (AtHashAddress parameter target) n := by
  have hbottom : RejectsBottomTree parameter (AtHashAddress parameter target) := by
    intro domain payload hdomain _ hat
    rw [atHashAddress_tweakableHashInput_iff] at hat
    subst hat
    simp [hdomain] at htop
  unfold Concrete.honestKeygen
  refine OracleComp.IsQueryBoundP.mono (n := 0 + (n + 0))
    (OracleComp.isQueryBoundP_bind
      (Concrete.sequenceFin_queryBound_zero _ _ fun key => ?_) fun _ _ =>
      OracleComp.isQueryBoundP_bind htree fun _ _ => OracleComp.isQueryBoundP_pure _ _ _)
    (by omega)
  exact OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.treeNode_queryBound_zero_of_rejectsBottomTree parameter _ hbottom secret _ _)
    fun root _ => OracleComp.isQueryBoundP_bind (m := 0) (by simp) fun base _ =>
      Concrete.topSignFrom_queryBound_zero_of_not_encoding parameter target htarget key root base
        _ 0

theorem topSubtreeValid_rootNode : TopSubtreeValid treeHeight Concrete.rootNode := by
  simp [TopSubtreeValid, Concrete.rootNode, topLifetime]

theorem Concrete.honestKeygen_queryBound_topChainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (key : TopIndex) (chain : ChainIndex) (step : ChainStep) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP (AtHashAddress parameter (.topChain key chain step)) 1 :=
  Concrete.honestKeygen_queryBound_of_topTree parameter secret topSecret topBase _ rfl
    (by simp) 1 ((Concrete.topTreeNode_queryBound_keyAddress parameter topSecret key _
      (fun leafKey => Concrete.topLeafAt_queryBound_chainAddress parameter topSecret leafKey key
        chain step) (by simp) treeHeight Concrete.rootNode topSubtreeValid_rootNode).mono
      (by split <;> omega))

theorem Concrete.honestKeygen_queryBound_topLeafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (key : TopIndex) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP (AtHashAddress parameter (.topLeaf key)) 1 :=
  Concrete.honestKeygen_queryBound_of_topTree parameter secret topSecret topBase _ rfl
    (by simp) 1 ((Concrete.topTreeNode_queryBound_keyAddress parameter topSecret key _
      (fun leafKey => Concrete.topLeafAt_queryBound_leafAddress parameter topSecret leafKey key)
      (by simp) treeHeight Concrete.rootNode topSubtreeValid_rootNode).mono
      (by split <;> omega))

theorem Concrete.honestKeygen_queryBound_topMerkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (level : MerkleLevel) (node : TopNode) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP (AtHashAddress parameter (.topMerkle level node)) 1 :=
  Concrete.honestKeygen_queryBound_of_topTree parameter secret topSecret topBase _ rfl
    (by simp) 1 ((Concrete.topTreeNode_queryBound_merkleAddress parameter topSecret level node
      treeHeight Concrete.rootNode topSubtreeValid_rootNode).mono (by split <;> omega))

end XmssSecurity
