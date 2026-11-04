module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.ConcreteQueryBound
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.StatementLemmas
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Translate

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

def TreeCovers (levels : Nat) (node : MerkleNode) (leafIndex : LeafIndex) : Prop :=
  node.val * 2 ^ levels ≤ leafIndex.val ∧ leafIndex.val < (node.val + 1) * 2 ^ levels

def TreeSubtreeValid (levels : Nat) (node : MerkleNode) : Prop :=
  (node.val + 1) * 2 ^ levels ≤ lifetime

instance (levels : Nat) (node : MerkleNode) (leafIndex : LeafIndex) :
    Decidable (TreeCovers levels node leafIndex) := by
  unfold TreeCovers
  infer_instance

theorem childNode_val_of_subtreeValid_succ (levels : Nat) (node : MerkleNode)
    (right : Bool) (hvalid : TreeSubtreeValid (levels + 1) node) :
    (Concrete.childNode node right).val = 2 * node.val + if right then 1 else 0 := by
  rw [Concrete.childNode, Concrete.merkleNodeOfNat]
  apply Nat.mod_eq_of_lt
  unfold TreeSubtreeValid at hvalid
  rw [pow_succ] at hvalid
  have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
  split <;> nlinarith

theorem childNode_subtreeValid (levels : Nat) (node : MerkleNode)
    (right : Bool) (hvalid : TreeSubtreeValid (levels + 1) node) :
    TreeSubtreeValid levels (Concrete.childNode node right) := by
  unfold TreeSubtreeValid
  rw [childNode_val_of_subtreeValid_succ levels node right hvalid]
  unfold TreeSubtreeValid at hvalid
  rw [pow_succ] at hvalid
  have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
  split <;> nlinarith

theorem treeCovers_iff (levels : Nat) (node : MerkleNode) (leafIndex : LeafIndex) :
    TreeCovers levels node leafIndex ↔ leafIndex.val / 2 ^ levels = node.val := by
  have hpos := Nat.two_pow_pos levels
  rw [TreeCovers, Nat.div_eq_iff hpos, Nat.add_mul, one_mul]
  generalize 2 ^ levels = d at *
  omega

/-! ### Counting along a tree

Node `j` on `level` lies above the leaves `j * 2^level` to `(j + 1) * 2^level - 1`.

It makes the queries of those leaves and of the node hashes between them. -/

/-- A node queries `p` at most once if the only leaf that does lies below it, else never. -/
theorem node_queryBound_leaf (hash : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (leaves : Nat → OracleComp HashSpec Digest) (p : HashInput → Prop) [DecidablePred p]
    (count target : Nat)
    (hleaves : ∀ j < count, (leaves j).IsQueryBoundP p (if target = j then 1 else 0))
    (hhash : ∀ level j left right, (hash level j left right).IsQueryBoundP p 0) :
    ∀ level j, (j + 1) * 2 ^ level ≤ count →
      (EthLib.Cryptography.Merkle.node hash leaves level j).IsQueryBoundP p
        (if target / 2 ^ level = j then 1 else 0)
  | 0, j, hj => by
    simpa [EthLib.Cryptography.Merkle.node_zero] using hleaves j (by simpa using hj)
  | level + 1, j, hj => by
    rw [EthLib.Cryptography.Merkle.node_succ, pow_succ] at *
    refine (OracleComp.isQueryBoundP_bind (node_queryBound_leaf hash leaves p count target hleaves
      hhash level (2 * j) (by nlinarith)) fun _ _ => OracleComp.isQueryBoundP_bind
        (node_queryBound_leaf hash leaves p count target hleaves hhash level (2 * j + 1)
          (by nlinarith)) fun _ _ => hhash _ _ _ _).mono ?_
    rw [← Nat.div_div_eq_div_mul]
    split_ifs <;> omega

/-- A node queries `p` at most once if the only node hash that does is at or below it, else never.

That node hash sits at position `(K, I)`, above the leaves. -/
theorem node_queryBound_node (hash : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (leaves : Nat → OracleComp HashSpec Digest) (p : HashInput → Prop) [DecidablePred p]
    (count K I : Nat) (hK : 0 < K) (hleaves : ∀ j, (leaves j).IsQueryBoundP p 0)
    (hhash : ∀ level j left right, (j + 1) * 2 ^ level ≤ count →
      (hash level j left right).IsQueryBoundP p (if level = K ∧ j = I then 1 else 0)) :
    ∀ level j, (j + 1) * 2 ^ level ≤ count →
      (EthLib.Cryptography.Merkle.node hash leaves level j).IsQueryBoundP p
        (if K ≤ level ∧ I / 2 ^ (level - K) = j then 1 else 0)
  | 0, j, _ => by
    simpa [EthLib.Cryptography.Merkle.node_zero, show ¬K ≤ 0 by omega] using hleaves j
  | level + 1, j, hj => by
    have hpow : 2 ^ (level + 1) = 2 ^ level * 2 := pow_succ 2 level
    rw [EthLib.Cryptography.Merkle.node_succ]
    refine (OracleComp.isQueryBoundP_bind (node_queryBound_node hash leaves p count K I hK hleaves
      hhash level (2 * j) (by rw [hpow] at hj; nlinarith)) fun _ _ => OracleComp.isQueryBoundP_bind
        (node_queryBound_node hash leaves p count K I hK hleaves hhash level (2 * j + 1)
          (by rw [hpow] at hj; nlinarith)) fun _ _ => hhash _ _ _ _ hj).mono ?_
    -- A target below the parent is in one child, and a target at the parent is the parent.
    rcases Nat.lt_or_ge level K with hlt | hge
    · by_cases hKeq : K = level + 1
      · subst hKeq
        simp only [le_refl, Nat.sub_self, pow_zero, Nat.div_one, true_and]
        split_ifs <;> omega
      · split_ifs <;> omega
    · rw [show level + 1 - K = level - K + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul]
      split_ifs <;> omega

/-- A node hash makes no query that `p` accepts, when no hash at a node address does. -/
theorem Concrete.nodeAt_queryBound_zero (parameter : PublicParameter) (p : HashInput → Prop)
    [DecidablePred p] (layer : EthLib.Cryptography.Xmss.Layer)
    (hhash : ∀ level j payload,
      (Concrete.tweakableHash parameter (Concrete.nodeDomain layer level j)
        payload : OracleComp HashSpec Digest).IsQueryBoundP p 0)
    (level j : Nat) (left right : Digest) :
    (Concrete.nodeAt parameter layer level j left right :
      OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  rcases level with _ | level
  · simp [Concrete.nodeAt]
  · by_cases hlevel : level < treeHeight
    · rw [show level = (⟨level, hlevel⟩ : MerkleLevel).val from rfl, Concrete.nodeAt_eq]
      exact hhash _ _ _
    · simp [Concrete.nodeAt, hlevel]

/-- A node hash queries the address of node `I` above `level` at most once, at that node. -/
theorem Concrete.nodeAt_queryBound_node (parameter : PublicParameter)
    (layer : EthLib.Cryptography.Xmss.Layer) (level : MerkleLevel) (I : Nat)
    (hI : I < Concrete.layerLeaves layer) (k j : Nat) (hj : j < Concrete.layerLeaves layer)
    (left right : Digest) :
    (Concrete.nodeAt parameter layer k j left right : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (Concrete.nodeDomain layer level I))
      (if k = level.val + 1 ∧ j = I then 1 else 0) := by
  rcases k with _ | k
  · simp [Concrete.nodeAt]
  · by_cases hk : k < treeHeight
    · rw [show k = (⟨k, hk⟩ : MerkleLevel).val from rfl, Concrete.nodeAt_eq]
      by_cases heq : k = level.val ∧ j = I
      · obtain ⟨hk', rfl⟩ := heq
        obtain rfl : (⟨k, hk⟩ : MerkleLevel) = level := Fin.ext hk'
        simpa using Concrete.tweakableHash_queryBound_atAddress parameter _
          (Concrete.nodePayload left right)
      · have hne : Concrete.nodeDomain layer ⟨k, hk⟩ j ≠ Concrete.nodeDomain layer level I := by
          cases layer <;>
            simp_all [Concrete.nodeDomain, Concrete.merkleNodeOfNat, Concrete.topNodeOfNat,
              Concrete.layerLeaves, Fin.ext_iff, Nat.mod_eq_of_lt]
        simpa [heq] using Concrete.tweakableHash_queryBound_atOtherAddress parameter _ _
          (Concrete.nodePayload left right) hne
    · simp [Concrete.nodeAt, hk]

theorem Concrete.treeNode_queryBound_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLeafIndex : LeafIndex) (levels : Nat) (node : MerkleNode)
    (hvalid : TreeSubtreeValid levels node) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.leaf targetLeafIndex))
        (if TreeCovers levels node targetLeafIndex then 1 else 0) := by
  rw [Concrete.treeNode]
  simp only [treeCovers_iff]
  refine node_queryBound_leaf _ _ _ lifetime targetLeafIndex.val (fun j hj => ?_)
    (Concrete.nodeAt_queryBound_zero parameter _ .bottom fun _ _ _ =>
      Concrete.tweakableHash_queryBound_atOtherAddress parameter _ _ _
        (by simp [Concrete.nodeDomain])) levels node.val hvalid
  rw [show Concrete.merkleNodeOfNat j = ⟨j, hj⟩ from Fin.ext (Nat.mod_eq_of_lt hj)]
  by_cases htarget : targetLeafIndex.val = j
  · obtain rfl : targetLeafIndex = ⟨j, hj⟩ := Fin.ext htarget
    simpa using Concrete.leafAt_queryBound_leafAddress parameter secret _ _
  · simpa [htarget] using Concrete.leafAt_queryBound_zero_at_other_leaf parameter secret ⟨j, hj⟩
      targetLeafIndex fun h => htarget (congrArg Fin.val h).symm

/-! ### Key generation's honest computation by part

The bottom trees query only bottom chain, leaf and Merkle domains.

The top grinding and the top tree query only top domains.

So a predicate that rejects the top domains is bounded by the bottom trees alone. -/

/-- A predicate rejecting every input of the top layer's domains. -/
def RejectsTop (parameter : PublicParameter) (p : HashInput → Prop) : Prop :=
  ∀ domain payload, domain.isTop = true → ¬ p (tweakableHashInput parameter domain payload)

/-- A predicate rejecting every input of the bottom chain, leaf and Merkle domains. -/
def RejectsBottomTree (parameter : PublicParameter) (p : HashInput → Prop) : Prop :=
  ∀ domain payload, domain.isTop = false → (∀ leafIndex, domain ≠ .encoding leafIndex) →
    ¬ p (tweakableHashInput parameter domain payload)

-- The top tree is fully concrete at the tree height, so keep elaboration from unfolding it.
attribute [local irreducible] Concrete.topTreeNode

theorem Concrete.tweakableHash_queryBound_zero_of_not
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (p : HashInput → Prop) [DecidablePred p]
    (hnot : ¬ p (tweakableHashInput parameter domain payload)) :
    (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash, hnot]

section HonestKeygenParts

variable (parameter : PublicParameter) (p : HashInput → Prop) [DecidablePred p]

theorem Concrete.topChainWalk_queryBound_zero_of_rejectsTop (htop : RejectsTop parameter p)
    (key : TopIndex) (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    (Concrete.topChainWalk parameter key chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  induction steps with
  | zero => simp [Concrete.topChainWalk]
  | succ steps ih =>
      rw [Concrete.topChainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro previous _
      split
      · tweakable_hashes
        exact Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p (htop _ _ rfl)
      · simp

theorem Concrete.topTreeNode_queryBound_zero_of_rejectsTop (htop : RejectsTop parameter p)
    (topSecret : TopIndex → ChainIndex → Digest) (levels : Nat) (node : TopNode) :
    (Concrete.topTreeNode parameter topSecret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  rw [Concrete.topTreeNode]
  refine EthLib.Cryptography.Merkle.node_rec _ (fun x => OracleComp.IsQueryBoundP x p 0)
    (fun hx hf => OracleComp.isQueryBoundP_bind (m := 0) hx fun b _ => hf b) _ (fun _ => ?_)
    (Concrete.nodeAt_queryBound_zero parameter p .top fun _ _ _ =>
      Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p (htop _ _ rfl)) levels node.val
  refine OracleComp.isQueryBoundP_bind (m := 0) (Concrete.sequenceFin_queryBound_zero _ p
    fun chain => Concrete.topChainWalk_queryBound_zero_of_rejectsTop parameter p htop _ _ _ _ _) ?_
  intro endpoints _
  tweakable_hashes
  exact Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p (htop _ _ rfl)

theorem Concrete.topSignFrom_queryBound_zero_of_rejectsTop (htop : RejectsTop parameter p)
    (key : TopIndex) (root : Digest) (base : Randomness) (attempts trial : Nat) :
    (Concrete.topSignFrom parameter key root base attempts trial :
      OracleComp HashSpec (Option (Randomness × Encoding))).IsQueryBoundP p 0 := by
  induction attempts generalizing trial with
  | zero => simp [Concrete.topSignFrom]
  | succ attempts ih =>
      rw [Concrete.topSignFrom]
      tweakable_hashes
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p (htop _ _ rfl)) ?_
      intro digest _
      split
      · simp
      · exact ih _

theorem Concrete.chainWalk_queryBound_zero_of_rejectsBottomTree
    (hbottom : RejectsBottomTree parameter p)
    (leafIndex : LeafIndex) (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro previous _
      split
      · tweakable_hashes
        exact Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p
          (hbottom _ _ rfl (by simp))
      · simp

theorem Concrete.treeNode_queryBound_zero_of_rejectsBottomTree
    (hbottom : RejectsBottomTree parameter p)
    (secret : LeafIndex → ChainIndex → Digest) (levels : Nat) (node : MerkleNode) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  rw [Concrete.treeNode]
  refine EthLib.Cryptography.Merkle.node_rec _ (fun x => OracleComp.IsQueryBoundP x p 0)
    (fun hx hf => OracleComp.isQueryBoundP_bind (m := 0) hx fun b _ => hf b) _ (fun _ => ?_)
    (Concrete.nodeAt_queryBound_zero parameter p .bottom fun _ _ _ =>
      Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p
        (hbottom _ _ rfl (by simp [Concrete.nodeDomain])))
    levels node.val
  refine OracleComp.isQueryBoundP_bind (m := 0) (Concrete.sequenceFin_queryBound_zero _ p
    fun chain => Concrete.chainWalk_queryBound_zero_of_rejectsBottomTree parameter p hbottom
      _ _ _ _ _) ?_
  intro endpoints _
  tweakable_hashes
  exact Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p (hbottom _ _ rfl (by simp))

variable (secret : LeafIndex → ChainIndex → Digest) (topSecret : TopIndex → ChainIndex → Digest)
  (topBase : TopIndex → Digest → OracleComp HashSpec Randomness)

/-- Take a predicate that rejects the top domains and that no top base query meets.

For it, key generation's honest computation is bounded by its bottom trees. -/
theorem Concrete.honestKeygen_queryBound_of_bottomTrees (bound : TopIndex → Nat) (n : Nat)
    (htop : RejectsTop parameter p) (hbase : ∀ key root, (topBase key root).IsQueryBoundP p 0)
    (htrees : ∀ key, (Concrete.treeNode parameter secret treeHeight (Concrete.bottomRootNode key) :
      OracleComp HashSpec Digest).IsQueryBoundP p (bound key))
    (hsequence : ∀ computation : TopIndex → OracleComp HashSpec (Option (Randomness × Encoding)),
      (∀ key, (computation key).IsQueryBoundP p (bound key)) →
        (Concrete.sequenceFin computation).IsQueryBoundP p n) :
    (Concrete.honestKeygen parameter secret topSecret topBase :
      OracleComp HashSpec _).IsQueryBoundP p n := by
  unfold Concrete.honestKeygen
  refine OracleComp.IsQueryBoundP.mono (n := n + (0 + 0))
    (OracleComp.isQueryBoundP_bind (hsequence _ fun key => ?_) fun _ _ =>
      OracleComp.isQueryBoundP_bind
        (Concrete.topTreeNode_queryBound_zero_of_rejectsTop parameter p htop topSecret _ _)
        fun _ _ => OracleComp.isQueryBoundP_pure p _ _) (by omega)
  exact OracleComp.IsQueryBoundP.mono (n := bound key + (0 + 0))
    (OracleComp.isQueryBoundP_bind (htrees key) fun root _ =>
      OracleComp.isQueryBoundP_bind (hbase key root) fun base _ =>
        Concrete.topSignFrom_queryBound_zero_of_rejectsTop parameter p htop key root base _ 0)
    (by omega)

/-- Take a query that both layers' trees and grinding reject.

Key generation's honest computation never makes it. -/
theorem Concrete.honestKeygen_queryBound_zero
    (htop : RejectsTop parameter p) (hbottom : RejectsBottomTree parameter p)
    (hbase : ∀ key root, (topBase key root).IsQueryBoundP p 0) :
    (Concrete.honestKeygen parameter secret topSecret topBase :
      OracleComp HashSpec _).IsQueryBoundP p 0 :=
  Concrete.honestKeygen_queryBound_of_bottomTrees parameter p secret topSecret topBase (fun _ => 0) 0
    htop hbase
    (fun _ => Concrete.treeNode_queryBound_zero_of_rejectsBottomTree parameter p hbottom secret _ _)
    fun computation h => Concrete.sequenceFin_queryBound_zero computation p h

/-- Key generation's honest computation queries an address of one bottom tree at most once. -/
theorem Concrete.honestKeygen_queryBound_one (target : TopIndex)
    (htop : RejectsTop parameter p) (hbase : ∀ key root, (topBase key root).IsQueryBoundP p 0)
    (htarget : (Concrete.treeNode parameter secret treeHeight (Concrete.bottomRootNode target) :
      OracleComp HashSpec Digest).IsQueryBoundP p 1)
    (hother : ∀ key, key ≠ target →
      (Concrete.treeNode parameter secret treeHeight (Concrete.bottomRootNode key) :
        OracleComp HashSpec Digest).IsQueryBoundP p 0) :
    (Concrete.honestKeygen parameter secret topSecret topBase :
      OracleComp HashSpec _).IsQueryBoundP p 1 :=
  Concrete.honestKeygen_queryBound_of_bottomTrees parameter p secret topSecret topBase
    (fun key => if key = target then 1 else 0) 1 htop hbase
    (fun key => by split <;> rename_i h <;> [exact h ▸ htarget; exact hother key h])
    fun computation h => Concrete.sequenceFin_queryBound_one computation p target
      (by simpa using h target) fun key hne => by simpa [hne] using h key

end HonestKeygenParts

theorem rejectsTop_atHashAddress (parameter : PublicParameter) (target : HashDomain)
    (htarget : target.isTop = false) : RejectsTop parameter (AtHashAddress parameter target) := by
  intro domain payload hdomain hat
  rw [atHashAddress_tweakableHashInput_iff] at hat
  subst hat
  simp [htarget] at hdomain

theorem treeCovers_bottomRootNode_iff (key : TopIndex) (leafIndex : LeafIndex) :
    TreeCovers treeHeight (Concrete.bottomRootNode key) leafIndex ↔ key = topKeyOf leafIndex := by
  have hleaf := leafIndex.isLt
  simp only [TreeCovers, Concrete.bottomRootNode, topKeyOf, Fin.ext_iff, treeHeight, lifetime] at hleaf ⊢
  omega

theorem treeSubtreeValid_bottomRootNode (key : TopIndex) :
    TreeSubtreeValid treeHeight (Concrete.bottomRootNode key) := by
  have hkey := key.isLt
  simp only [TreeSubtreeValid, Concrete.bottomRootNode, topLifetime, treeHeight, lifetime] at hkey ⊢
  omega

/-- The honest computation of key generation queries each bottom leaf address at most once. -/
theorem Concrete.rootTree_queryBound_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (targetLeafIndex : LeafIndex) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP
        (AtHashAddress parameter (.leaf targetLeafIndex)) 1 := by
  refine Concrete.honestKeygen_queryBound_one parameter _ secret topSecret _ (topKeyOf targetLeafIndex)
    (rejectsTop_atHashAddress parameter _ rfl) (fun _ _ => by simp) ?_ ?_
  · simpa [(treeCovers_bottomRootNode_iff _ _).2 rfl] using
      Concrete.treeNode_queryBound_leafAddress parameter secret targetLeafIndex treeHeight
        (Concrete.bottomRootNode (topKeyOf targetLeafIndex)) (treeSubtreeValid_bottomRootNode _)
  · intro key hne
    simpa [treeCovers_bottomRootNode_iff, hne] using
      Concrete.treeNode_queryBound_leafAddress parameter secret targetLeafIndex treeHeight
        (Concrete.bottomRootNode key) (treeSubtreeValid_bottomRootNode _)

/-- Run key generation's honest computation from an empty cache.

A supported execution contains at most one input at each bottom leaf address. -/
theorem Concrete.CacheReplay.rootTree_cache_unique_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (result : Digest × (TopIndex → Option (Randomness × Encoding))) (cache : QueryCache HashSpec)
    (hmem : (result, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (targetLeafIndex : LeafIndex) (left right : HashInput)
    (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress parameter (.leaf targetLeafIndex) left)
    (hrightP : AtHashAddress parameter (.leaf targetLeafIndex) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right :=
  Concrete.CacheReplay.cache_unique_of_query_bound_one
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _)
    (AtHashAddress parameter (.leaf targetLeafIndex)) ∅ cache result
    (Concrete.rootTree_queryBound_leafAddress parameter secret topSecret topBase targetLeafIndex)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

theorem Concrete.treeNode_queryBound_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (levels : Nat) (node : MerkleNode) (hvalid : TreeSubtreeValid levels node) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep))
        (if TreeCovers levels node targetLeafIndex then 1 else 0) := by
  rw [Concrete.treeNode]
  simp only [treeCovers_iff]
  refine node_queryBound_leaf _ _ _ lifetime targetLeafIndex.val (fun j hj => ?_)
    (Concrete.nodeAt_queryBound_zero parameter _ .bottom fun _ _ _ =>
      Concrete.tweakableHash_queryBound_atOtherAddress parameter _ _ _
        (by simp [Concrete.nodeDomain])) levels node.val hvalid
  rw [show Concrete.merkleNodeOfNat j = ⟨j, hj⟩ from Fin.ext (Nat.mod_eq_of_lt hj)]
  by_cases htarget : targetLeafIndex.val = j
  · obtain rfl : targetLeafIndex = ⟨j, hj⟩ := Fin.ext htarget
    simpa using Concrete.leafAt_queryBound_chainAddress parameter secret _ _ targetChain targetStep
  · simpa [htarget] using Concrete.leafAt_queryBound_zero_chainAddress_at_other_leafIndex parameter
      secret ⟨j, hj⟩ targetLeafIndex targetChain targetStep
      fun h => htarget (congrArg Fin.val h).symm

/-- The honest computation of key generation queries each bottom chain-step address at most once. -/
theorem Concrete.rootTree_queryBound_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP
        (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) 1 := by
  refine Concrete.honestKeygen_queryBound_one parameter _ secret topSecret _ (topKeyOf targetLeafIndex)
    (rejectsTop_atHashAddress parameter _ rfl) (fun _ _ => by simp) ?_ ?_
  · simpa [(treeCovers_bottomRootNode_iff _ _).2 rfl] using
      Concrete.treeNode_queryBound_chainAddress parameter secret targetLeafIndex targetChain
        targetStep treeHeight (Concrete.bottomRootNode (topKeyOf targetLeafIndex))
        (treeSubtreeValid_bottomRootNode _)
  · intro key hne
    simpa [treeCovers_bottomRootNode_iff, hne] using
      Concrete.treeNode_queryBound_chainAddress parameter secret targetLeafIndex targetChain
        targetStep treeHeight (Concrete.bottomRootNode key) (treeSubtreeValid_bottomRootNode _)

/-- Run key generation's honest computation from an empty cache.

A supported execution contains at most one input at each bottom chain-step address. -/
theorem Concrete.CacheReplay.rootTree_cache_unique_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (result : Digest × (TopIndex → Option (Randomness × Encoding))) (cache : QueryCache HashSpec)
    (hmem : (result, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep) left)
    (hrightP : AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right :=
  Concrete.CacheReplay.cache_unique_of_query_bound_one
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _)
    (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) ∅ cache result
    (Concrete.rootTree_queryBound_chainAddress parameter secret topSecret topBase targetLeafIndex
      targetChain targetStep)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright
end XmssSecurity
