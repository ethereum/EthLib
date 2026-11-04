module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.KeygenCache

/-!
# Runs inside key generation's honest computation

Take a lazy random-oracle run of the honest key generation.

It contains a run of every bottom tree and of the top tree.

Each ends in a cache below the final one.

A tree's run contains a run of each of its subtrees.

A chain walk's run contains a run of each of its prefixes.

Every replay of such a run is stable in the final cache and all larger ones.
-/

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

-- The top tree is fully concrete at the tree height, so keep elaboration from unfolding it.
attribute [local irreducible] Concrete.topTreeNode

/-- A run of a computation that ends below `cache`. -/
def RunsBelow {α : Type} (computation : OracleComp HashSpec α) (cache : QueryCache HashSpec) : Prop :=
  ∃ beforeCache afterCache value,
    (value, afterCache) ∈ support ((simulateQ randomOracle computation).run beforeCache) ∧
      afterCache ≤ cache

theorem RunsBelow.mono {α : Type} {computation : OracleComp HashSpec α}
    {cache largerCache : QueryCache HashSpec} (hrun : RunsBelow computation cache)
    (hle : cache ≤ largerCache) : RunsBelow computation largerCache := by
  obtain ⟨beforeCache, afterCache, value, hmem, hafter⟩ := hrun
  exact ⟨beforeCache, afterCache, value, hmem, hafter.trans hle⟩

/-- A computation that ran below `cache` replays the same from `cache` and from any larger cache. -/
theorem RunsBelow.eval_eq {α : Type} {computation : OracleComp HashSpec α}
    {cache : QueryCache HashSpec} (hrun : RunsBelow computation cache)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache) :
    evalWithAnswerFn (answerFn cache) computation =
      evalWithAnswerFn (answerFn largerCache) computation := by
  obtain ⟨beforeCache, afterCache, value, hmem, hafter⟩ := hrun
  rw [eval_answerFn_largerCache_eq_of_mem_support computation beforeCache afterCache cache value
      hmem hafter,
    eval_answerFn_largerCache_eq_of_mem_support computation beforeCache afterCache largerCache value
      hmem (hafter.trans hle)]

/-- A computation that ran below `cache` reruns from any larger cache as a replay of `cache`. -/
theorem RunsBelow.run_eq {α : Type} {computation : OracleComp HashSpec α}
    {cache : QueryCache HashSpec} (hrun : RunsBelow computation cache)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache) :
    (simulateQ randomOracle computation).run largerCache =
      pure (evalWithAnswerFn (answerFn cache) computation, largerCache) := by
  obtain ⟨beforeCache, afterCache, value, hmem, hafter⟩ := hrun
  rw [eval_answerFn_largerCache_eq_of_mem_support computation beforeCache afterCache cache value
    hmem hafter]
  exact randomOracle_rerun_largerCache_eq_pure_of_mem_support computation beforeCache afterCache
    largerCache value hmem (hafter.trans hle)

theorem runsBelow_bind_left {α β : Type} {first : OracleComp HashSpec α}
    {next : α → OracleComp HashSpec β} {initialCache cache : QueryCache HashSpec} {result : β}
    (hmem : (result, cache) ∈ support ((simulateQ randomOracle (first >>= next)).run initialCache)) :
    ∃ value middleCache,
      (value, middleCache) ∈ support ((simulateQ randomOracle first).run initialCache) ∧
      (result, cache) ∈ support ((simulateQ randomOracle (next value)).run middleCache) ∧
      middleCache ≤ cache := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨value, middleCache⟩, hfirst, hnext⟩ := hmem
  exact ⟨value, middleCache, hfirst, hnext, randomOracle_cache_le _ _ _ hnext⟩

theorem runsBelow_sequenceFin {α : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) (target : Fin n)
    (initialCache cache : QueryCache HashSpec) (values : Fin n → α)
    (hmem : (values, cache) ∈ support
      ((simulateQ randomOracle (Concrete.sequenceFin computation)).run initialCache)) :
    RunsBelow (computation target) cache := by
  induction n generalizing initialCache with
  | zero => exact Fin.elim0 target
  | succ n ih =>
      rw [Concrete.sequenceFin] at hmem
      obtain ⟨head, headCache, hhead, hrest, hheadLe⟩ := runsBelow_bind_left hmem
      obtain rfl | ⟨tailTarget, rfl⟩ := target.eq_zero_or_eq_succ
      · exact ⟨initialCache, headCache, head, hhead, hheadLe⟩
      · obtain ⟨tail, tailCache, htail, hfinal, _⟩ := runsBelow_bind_left hrest
        simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hfinal
        rw [← hfinal.2] at htail
        exact ih (fun index => computation index.succ) tailTarget headCache tail htail

section HonestKeygen

variable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
  (topSecret : TopIndex → ChainIndex → Digest)
  (topBase : TopIndex → Digest → OracleComp HashSpec Randomness)
  (initialCache cache : QueryCache HashSpec)
  (result : Digest × (TopIndex → Option (Randomness × Encoding)))

/-- Every bottom tree runs inside key generation's honest computation. -/
theorem honestKeygen_runsBelow_bottomTree
    (hmem : (result, cache) ∈ support ((simulateQ randomOracle
      (Concrete.honestKeygen parameter secret topSecret topBase : OracleComp HashSpec _)).run
        initialCache))
    (key : TopIndex) :
    RunsBelow (Concrete.treeNode parameter secret treeHeight (Concrete.bottomRootNode key) :
      OracleComp HashSpec Digest) cache := by
  unfold Concrete.honestKeygen at hmem
  obtain ⟨topSigned, signedCache, hsigned, _, hsignedLe⟩ := runsBelow_bind_left hmem
  obtain ⟨beforeCache, afterCache, value, hkey, hafterLe⟩ :=
    runsBelow_sequenceFin _ key initialCache signedCache topSigned hsigned
  obtain ⟨root, rootCache, htree, _, hrootLe⟩ := runsBelow_bind_left hkey
  exact ⟨beforeCache, rootCache, root, htree, hrootLe.trans (hafterLe.trans hsignedLe)⟩

/-- The top tree runs inside key generation's honest computation. -/
theorem honestKeygen_runsBelow_topTree
    (hmem : (result, cache) ∈ support ((simulateQ randomOracle
      (Concrete.honestKeygen parameter secret topSecret topBase : OracleComp HashSpec _)).run
        initialCache)) :
    RunsBelow (Concrete.topTreeNode parameter topSecret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest) cache := by
  unfold Concrete.honestKeygen at hmem
  obtain ⟨topSigned, signedCache, _, hrest, _⟩ := runsBelow_bind_left hmem
  obtain ⟨root, rootCache, htree, _, hrootLe⟩ := runsBelow_bind_left hrest
  exact ⟨signedCache, rootCache, root, htree, hrootLe⟩

end HonestKeygen

/-- A subtree of a tree runs inside the tree's run.

Node `i` on `levels` lies below node `i / 2^(height - levels)` on `height`. -/
theorem RunsBelow.node_subtree (hash : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (leaves : Nat → OracleComp HashSpec Digest) (levels i : Nat) (cache : QueryCache HashSpec) :
    ∀ (height : Nat), levels ≤ height →
      RunsBelow (EthLib.Cryptography.Merkle.node hash leaves height (i / 2 ^ (height - levels)))
        cache →
      RunsBelow (EthLib.Cryptography.Merkle.node hash leaves levels i) cache
  | 0, hle, hrun => by
    obtain rfl : levels = 0 := by omega
    simpa using hrun
  | height + 1, hle, hrun => by
    by_cases hsame : levels = height + 1
    · subst levels
      simpa using hrun
    obtain ⟨beforeCache, afterCache, digest, hmem, hafter⟩ := hrun
    rw [EthLib.Cryptography.Merkle.node_succ] at hmem
    obtain ⟨left, leftCache, hleft, hrest, hleftLe⟩ := runsBelow_bind_left hmem
    obtain ⟨right, rightCache, hright, _, hrightLe⟩ := runsBelow_bind_left hrest
    -- The node's ancestor one level lower is the left or the right child, by parity.
    have hdiv : i / 2 ^ (height - levels) = 2 * (i / 2 ^ (height + 1 - levels)) +
        i / 2 ^ (height - levels) % 2 := by
      rw [show height + 1 - levels = height - levels + 1 by omega, pow_succ,
        ← Nat.div_div_eq_div_mul]
      omega
    refine RunsBelow.node_subtree hash leaves levels i cache height (by omega) ?_
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ (height - levels)) with hbit | hbit <;>
      rw [hdiv, hbit]
    · exact ⟨beforeCache, leftCache, left, hleft, hleftLe.trans hafter⟩
    · exact ⟨leftCache, rightCache, right, hright, hrightLe.trans hafter⟩

/-- A prefix of a chain walk runs inside the walk's run. -/
theorem RunsBelow.chainWalk_prefix (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position : Nat) (value : Digest) (cache : QueryCache HashSpec)
    (steps prefixSteps : Nat) (hprefix : prefixSteps ≤ steps)
    (hrun : RunsBelow (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest) cache) :
    RunsBelow (Concrete.chainWalk parameter leafIndex chain position prefixSteps value :
      OracleComp HashSpec Digest) cache := by
  induction steps with
  | zero => obtain rfl : prefixSteps = 0 := by omega
            exact hrun
  | succ steps ih =>
      by_cases hsame : prefixSteps = steps + 1
      · subst hsame
        exact hrun
      obtain ⟨beforeCache, afterCache, digest, hmem, hafter⟩ := hrun
      rw [Concrete.chainWalk] at hmem
      obtain ⟨previous, middleCache, hprevious, _, hmiddleLe⟩ := runsBelow_bind_left hmem
      exact ih (by omega) ⟨beforeCache, middleCache, previous, hprevious, hmiddleLe.trans hafter⟩

/-- A prefix of a top chain walk runs inside the walk's run. -/
theorem RunsBelow.topChainWalk_prefix (parameter : PublicParameter) (key : TopIndex)
    (chain : ChainIndex) (position : Nat) (value : Digest) (cache : QueryCache HashSpec)
    (steps prefixSteps : Nat) (hprefix : prefixSteps ≤ steps)
    (hrun : RunsBelow (Concrete.topChainWalk parameter key chain position steps value :
      OracleComp HashSpec Digest) cache) :
    RunsBelow (Concrete.topChainWalk parameter key chain position prefixSteps value :
      OracleComp HashSpec Digest) cache := by
  induction steps with
  | zero => obtain rfl : prefixSteps = 0 := by omega
            exact hrun
  | succ steps ih =>
      by_cases hsame : prefixSteps = steps + 1
      · subst hsame
        exact hrun
      obtain ⟨beforeCache, afterCache, digest, hmem, hafter⟩ := hrun
      rw [Concrete.topChainWalk] at hmem
      obtain ⟨previous, middleCache, hprevious, _, hmiddleLe⟩ := runsBelow_bind_left hmem
      exact ih (by omega) ⟨beforeCache, middleCache, previous, hprevious, hmiddleLe.trans hafter⟩

section HonestKeygen

variable {parameter : PublicParameter} {secret : LeafIndex → ChainIndex → Digest}
  {topSecret : TopIndex → ChainIndex → Digest}
  {topBase : TopIndex → Digest → OracleComp HashSpec Randomness}
  {initialCache cache : QueryCache HashSpec}
  {result : Digest × (TopIndex → Option (Randomness × Encoding))}

/-- Every bottom subtree below the roots runs inside key generation's honest computation. -/
theorem honestKeygen_runsBelow_treeNode
    (hmem : (result, cache) ∈ support ((simulateQ randomOracle
      (Concrete.honestKeygen parameter secret topSecret topBase : OracleComp HashSpec _)).run
        initialCache))
    (levels : Nat) (node : MerkleNode) (hlevels : levels ≤ treeHeight)
    (hvalid : TreeSubtreeValid levels node) :
    RunsBelow (Concrete.treeNode parameter secret levels node : OracleComp HashSpec Digest) cache := by
  have hkey : node.val / 2 ^ (treeHeight - levels) < topLifetime := by
    unfold TreeSubtreeValid at hvalid
    rw [Nat.div_lt_iff_lt_mul (pow_pos (by omega) _)]
    have hsplit : lifetime = topLifetime * 2 ^ (treeHeight - levels) * 2 ^ levels := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hlevels]
      simp [lifetime, topLifetime, treeHeight]
    have hbound := hvalid.trans_eq hsplit
    have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
    nlinarith
  have htree := honestKeygen_runsBelow_bottomTree parameter secret topSecret topBase initialCache
    cache result hmem ⟨_, hkey⟩
  rw [Concrete.treeNode] at htree ⊢
  exact RunsBelow.node_subtree _ _ levels node.val cache treeHeight hlevels htree

/-- Every top subtree runs inside key generation's honest computation. -/
theorem honestKeygen_runsBelow_topTreeNode
    (hmem : (result, cache) ∈ support ((simulateQ randomOracle
      (Concrete.honestKeygen parameter secret topSecret topBase : OracleComp HashSpec _)).run
        initialCache))
    (levels : Nat) (node : TopNode) (hlevels : levels ≤ treeHeight)
    (hnode : node.val < 2 ^ (treeHeight - levels)) :
    RunsBelow (Concrete.topTreeNode parameter topSecret levels node : OracleComp HashSpec Digest)
      cache := by
  have htree := honestKeygen_runsBelow_topTree parameter secret topSecret topBase initialCache cache
    result hmem
  rw [Concrete.topTreeNode] at htree ⊢
  refine RunsBelow.node_subtree _ _ levels node.val cache treeHeight hlevels ?_
  simpa [Concrete.rootNode, Nat.div_eq_of_lt hnode] using htree

/-- Every bottom chain walk from its start runs inside key generation's honest computation. -/
theorem honestKeygen_runsBelow_chainWalk
    (hmem : (result, cache) ∈ support ((simulateQ randomOracle
      (Concrete.honestKeygen parameter secret topSecret topBase : OracleComp HashSpec _)).run
        initialCache))
    (leafIndex : LeafIndex) (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    RunsBelow (Concrete.chainWalk parameter leafIndex chain 0 steps (secret leafIndex chain) :
      OracleComp HashSpec Digest) cache := by
  obtain ⟨beforeCache, afterCache, leaf, hleaf, hafter⟩ :=
    honestKeygen_runsBelow_treeNode hmem 0 leafIndex (by omega) (by
      have := leafIndex.isLt
      simp only [TreeSubtreeValid, pow_zero, mul_one]
      omega)
  rw [Concrete.treeNode_zero_eq, Concrete.leafAt] at hleaf
  obtain ⟨endpoints, endpointsCache, hendpoints, _, hendpointsLe⟩ := runsBelow_bind_left hleaf
  unfold Concrete.oneTimePublicKey at hendpoints
  exact RunsBelow.chainWalk_prefix parameter leafIndex chain 0 (secret leafIndex chain) cache
    (chainLength - 1) steps hsteps
    ((runsBelow_sequenceFin _ chain beforeCache endpointsCache endpoints hendpoints).mono
      (hendpointsLe.trans hafter))

/-- Every top chain walk from its start runs inside key generation's honest computation. -/
theorem honestKeygen_runsBelow_topChainWalk
    (hmem : (result, cache) ∈ support ((simulateQ randomOracle
      (Concrete.honestKeygen parameter secret topSecret topBase : OracleComp HashSpec _)).run
        initialCache))
    (key : TopIndex) (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    RunsBelow (Concrete.topChainWalk parameter key chain 0 steps (topSecret key chain) :
      OracleComp HashSpec Digest) cache := by
  obtain ⟨beforeCache, afterCache, leaf, hleaf, hafter⟩ :=
    honestKeygen_runsBelow_topTreeNode hmem 0 key (by omega) (by rw [Nat.sub_zero]; exact key.isLt)
  rw [Concrete.topTreeNode_zero_eq, Concrete.topLeafAt] at hleaf
  obtain ⟨endpoints, endpointsCache, hendpoints, _, hendpointsLe⟩ := runsBelow_bind_left hleaf
  unfold Concrete.topOneTimePublicKey at hendpoints
  exact RunsBelow.topChainWalk_prefix parameter key chain 0 (topSecret key chain) cache
    (chainLength - 1) steps hsteps
    ((runsBelow_sequenceFin _ chain beforeCache endpointsCache endpoints hendpoints).mono
      (hendpointsLe.trans hafter))

end HonestKeygen

end XmssSecurity.Concrete.CacheReplay
