module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Graph
public import EthLib.Cryptography.Proofs.Sphincs.Fors
public import EthLib.Cryptography.Proofs.Merkle.Binding

/-!
# Proofs: what an accepted FORS opening contains

Verification recovers a FORS key from the openings, tree by tree.

When that key is the honest key of the instance, each opening is the honest opening of its leaf.

Otherwise verification hashed other children values to the honest value of a node.

That node is a FORS leaf, at another secret, or a FORS node, at another pair of children.

So the node and the other values name a second preimage of the node's honest value.

An explicit search finds them from the openings, and finds nothing in honest openings.

Every statement holds for every hash `f` and every source of secrets, in the identity monad.

When `f` is read from the cache of a run, the second preimage is a cached input at the node's key.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants

/-! ## Second preimages at nodes -/

/-- The value of a node at children values, under a hash `f`.

It is half 0 of the hash of the node's input at those values. -/
def Node.valueAt (f : ByteArray → Vector UInt8 32) (P : PublicParam) (k : Node)
    (vs : List Digest) : Digest :=
  halfOf 0 (f (thInput P k.address (digestsBytes vs ++ k.suffix)))

/-- Children values offered for a node in place of its honest ones. -/
structure NodePreimage where
  /-- The node. -/
  node : Node
  /-- The offered values, in the order of the node's payload. -/
  children : List Digest
  deriving DecidableEq

/-- A valid offer, against the honest children values `honest`.

It has one value per child, differs from the honest values, and gives the honest value. -/
def NodePreimage.Valid (f : ByteArray → Vector UInt8 32) (P : PublicParam)
    (honest : Node → List Digest) (w : NodePreimage) : Prop :=
  w.children.length = (w.node.children P).length ∧ w.children ≠ honest w.node ∧
    w.node.valueAt f P w.children = w.node.valueAt f P (honest w.node)

/-! ## The honest values of FORS -/

variable (f : ByteArray → Vector UInt8 32) (P : PublicParam) (prf : SeedPrf Id)

/-- The honest children values of a FORS node.

A leaf has its secret.

A node on level `level + 1` has its two children on level `level`.

Other nodes have no honest values here. -/
def forsChildren : Node → List Digest
  | .forsLeaf idx kappa l => [(forsSecret P prf idx.val kappa l).run]
  | .forsNode idx kappa level j =>
      [(forsNode (pureHash f) P prf idx.val kappa level.val (2 * j.val)).run,
        (forsNode (pureHash f) P prf idx.val kappa level.val (2 * j.val + 1)).run]
  | _ => []

/-- A FORS leaf's value at a secret is the leaf hash of that secret. -/
theorem valueAt_forsLeaf (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) (s : Digest) :
    (Node.forsLeaf idx kappa l).valueAt f P [s] =
      (forsLeafHash (pureHash f) P idx.val kappa l s).run := by
  simp only [Node.valueAt, Node.address, Node.suffix, digestsBytes_singleton,
    ByteArray.append_empty]
  rfl

/-- A FORS node's value at two children is the node hash of those children. -/
theorem valueAt_forsNode (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (level : Fin (FORS_HEIGHT - 1)) (j : Fin (2 ^ FORS_HEIGHT)) (a b : Digest) :
    (Node.forsNode idx kappa level j).valueAt f P [a, b] =
      (forsNodeHash (pureHash f) P idx.val kappa (level.val + 1) j.val a b).run := by
  simp only [Node.valueAt, Node.address, Node.suffix, digestsBytes_pair, ByteArray.append_empty]
  rfl

/-- A FORS node has two children. -/
theorem length_children_forsNode (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (level : Fin (FORS_HEIGHT - 1)) (j : Fin (2 ^ FORS_HEIGHT)) :
    ((Node.forsNode idx kappa level j).children P).length = 2 := by
  simp only [Node.children]
  split <;> rfl

/-! ## One tree -/

/-- The node of tree `kappa` at which an opening at leaf `l` leaves the honest tree, if any.

The leaf hashed from the revealed secret climbs levels 0 to 8 along the path.

The first level where the climb hashes another pair to the honest node gives a FORS node.

If the climb is honest, a wrong secret with the honest leaf gives the FORS leaf. -/
def findTreePreimage (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) (o : TreeOpening) : Option NodePreimage :=
  match Merkle.findSecondPreimage (forsNodeHash (pureHash f) P idx.val kappa)
      (forsLeaves (pureHash f) P prf idx.val kappa) 0 l.val
      (forsLeafHash (pureHash f) P idx.val kappa l o.secret).run
      (o.path.toList.take (FORS_HEIGHT - 1)) with
  | some w =>
    if h : w.level < FORS_HEIGHT - 1 ∧ w.j < 2 ^ FORS_HEIGHT then
      some ⟨.forsNode idx kappa ⟨w.level, h.1⟩ ⟨w.j, h.2⟩, [w.y.1, w.y.2]⟩
    else none
  | none =>
    if o.secret ≠ (forsSecret P prf idx.val kappa l).run ∧
        (forsLeafHash (pureHash f) P idx.val kappa l o.secret).run =
          (forsLeaves (pureHash f) P prf idx.val kappa l.val).run then
      some ⟨.forsLeaf idx kappa l, [o.secret]⟩
    else none

variable {f P prf}

/-- The leaf of a FORS tree is the leaf hash of its secret. -/
private theorem forsLeaves_run (idx : Nat) (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT)) :
    (forsLeaves (pureHash f) P prf idx kappa l.val).run =
      (forsLeafHash (pureHash f) P idx kappa l (forsSecret P prf idx kappa l).run).run := by
  simp only [forsLeaves, forsIndex_val]
  rfl

/-- A second preimage of the climb is on levels 0 to 8, below index `2^10`. -/
private theorem bounds_of_findSecondPreimage {idx : Nat} {kappa : Fin FORS_TREES}
    {l : Fin (2 ^ FORS_HEIGHT)} {b : Digest} {q : List Digest} (hq : q.length ≤ FORS_HEIGHT - 1)
    {w : Merkle.SecondPreimage Digest}
    (hw : Merkle.findSecondPreimage (forsNodeHash (pureHash f) P idx kappa)
      (forsLeaves (pureHash f) P prf idx kappa) 0 l.val b q = some w) :
    w.level < FORS_HEIGHT - 1 ∧ w.j < 2 ^ FORS_HEIGHT := by
  obtain ⟨-, k, hk, hlevel, hj⟩ := Merkle.findSecondPreimage_valid _ _ q 0 l.val b w hw
  refine ⟨by omega, ?_⟩
  rw [hj]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) l.isLt

/-- Every node the search of one tree returns is a valid offer against the honest FORS values. -/
theorem findTreePreimage_valid {idx : Fin (2 ^ HEIGHT)} {kappa : Fin FORS_TREES}
    {l : Fin (2 ^ FORS_HEIGHT)} {o : TreeOpening} {w : NodePreimage}
    (hw : findTreePreimage f P prf idx kappa l o = some w) :
    w.Valid f P (forsChildren f P prf) := by
  unfold findTreePreimage at hw
  split at hw
  · rename_i w' hw'
    split at hw
    · cases hw
      obtain ⟨⟨hne, heq⟩, -⟩ := Merkle.findSecondPreimage_valid _ _ _ 0 l.val _ w' hw'
      refine ⟨by rw [length_children_forsNode]; rfl, ?_, ?_⟩
      · -- The pair differs from the honest children.
        intro h
        apply hne
        simp only [forsChildren, List.cons.injEq, and_true] at h
        exact Prod.ext h.1 h.2
      · -- The pair hashes to the honest node, the hash of the honest children.
        simp only [forsChildren, valueAt_forsNode]
        rw [heq, Merkle.node_succ_run]
        rfl
    · cases hw
  · split at hw
    · cases hw
      rename_i h
      refine ⟨rfl, ?_, ?_⟩
      · -- The secret differs from the honest one.
        simp only [forsChildren, ne_eq, List.cons.injEq, and_true]
        exact h.1
      · -- The leaf hash of the secret is the honest leaf.
        simp only [forsChildren, valueAt_forsLeaf]
        rw [h.2, forsLeaves_run]
    · cases hw

/-- The honest opening of a leaf leaves the honest tree nowhere. -/
theorem findTreePreimage_honest (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) :
    findTreePreimage f P prf idx kappa l (treeOpen (pureHash f) P prf idx.val kappa l).run =
      none := by
  -- The revealed secret's leaf is the honest leaf.
  have hleaf : (forsLeafHash (pureHash f) P idx.val kappa l
      (treeOpen (pureHash f) P prf idx.val kappa l).run.secret).run =
        (Merkle.node (forsNodeHash (pureHash f) P idx.val kappa)
          (forsLeaves (pureHash f) P prf idx.val kappa) 0 l.val).run := by
    rw [treeOpen_run, Merkle.node_zero, forsLeaves_run]
  -- The first nine path nodes are the leaf's honest siblings below level 9.
  have hpath : (treeOpen (pureHash f) P prf idx.val kappa l).run.path.toList.take
      (FORS_HEIGHT - 1) = (Merkle.siblings (forsNodeHash (pureHash f) P idx.val kappa)
        (forsLeaves (pureHash f) P prf idx.val kappa) 0 l.val (FORS_HEIGHT - 1)).run.toList := by
    rw [treeOpen_run]
    simp only [Merkle.path, FORS_HEIGHT]
    rw [Merkle.siblings_succ_toList_concat, List.take_left' (by simp)]
  unfold findTreePreimage
  rw [hleaf, hpath, Merkle.findSecondPreimage_honest]
  rw [treeOpen_run]
  simp

/-- **Binding of one FORS tree.**

An opening at leaf `l` that recovers the tree's two honest level-9 nodes is the honest opening.

Otherwise the search finds a node where it leaves the honest tree, with a valid offer. -/
theorem treeRecover_binding {idx : Fin (2 ^ HEIGHT)} {kappa : Fin FORS_TREES}
    {l : Fin (2 ^ FORS_HEIGHT)} {o : TreeOpening}
    (h : (treeRecover (pureHash f) P idx.val kappa l o).run =
      ((forsNode (pureHash f) P prf idx.val kappa (FORS_HEIGHT - 1) 0).run,
        (forsNode (pureHash f) P prf idx.val kappa (FORS_HEIGHT - 1) 1).run)) :
    o = (treeOpen (pureHash f) P prf idx.val kappa l).run ∨
      ∃ w, findTreePreimage f P prf idx kappa l o = some w ∧
        w.Valid f P (forsChildren f P prf) := by
  cases hw : findTreePreimage f P prf idx kappa l o with
  | some w => exact .inr ⟨w, rfl, findTreePreimage_valid hw⟩
  | none =>
  refine .inl ?_
  -- Short names for the tree, the leaf hashed from the revealed secret, and the path parts.
  set hash := forsNodeHash (pureHash f) P idx.val kappa
  set leaves := forsLeaves (pureHash f) P prf idx.val kappa
  set leaf := (forsLeafHash (pureHash f) P idx.val kappa l o.secret).run with hleafdef
  set lower := o.path.toList.take (FORS_HEIGHT - 1)
  -- The search stopped nowhere, so the climb found no second preimage.
  have hsearch : Merkle.findSecondPreimage hash leaves 0 l.val leaf lower = none := by
    cases hs : Merkle.findSecondPreimage hash leaves 0 l.val leaf lower with
    | none => rfl
    | some w =>
      have hb := bounds_of_findSecondPreimage (by simp [lower]) hs
      unfold findTreePreimage at hw
      rw [hs] at hw
      simp only [hb, and_self, ↓reduceDIte, reduceCtorEq] at hw
  -- The recovered pair is the climb's node and the last path node, in the order of bit 9.
  have hpair := h
  simp only [treeRecover, Id.run_bind, Id.run_pure, Nat.shiftRight_eq_div_pow] at hpair
  -- The honest pair is the level-9 node above `l` and its sibling, in the same order.
  have hl : l.val / 2 ^ (FORS_HEIGHT - 1) / 2 = 0 := by
    have := l.isLt
    simp only [FORS_HEIGHT] at *
    omega
  have honest := Merkle.ordered_sibling (fun i => (Merkle.node hash leaves (FORS_HEIGHT - 1) i).run)
    (l.val / 2 ^ (FORS_HEIGHT - 1))
  rw [hl, Nat.mul_zero, Nat.zero_add] at honest
  change _ = ((Merkle.node hash leaves (FORS_HEIGHT - 1) 0).run,
    (Merkle.node hash leaves (FORS_HEIGHT - 1) 1).run) at hpair
  rw [← honest, Merkle.ordered_inj] at hpair
  obtain ⟨hreach, hlast⟩ := hpair
  -- The climb reaches the honest level-9 node with no second preimage, so it is honest.
  rcases Merkle.climb_binding_node hash leaves (FORS_HEIGHT - 1) 0 l.val leaf lower
      (by simp [lower]) (by rw [Nat.zero_add]; exact hreach) with ⟨hleaf, hlower⟩ | hsome
  · -- The revealed secret is the honest one, or the search would have found the leaf.
    have hsecret : o.secret = (forsSecret P prf idx.val kappa l).run := by
      by_contra hne
      unfold findTreePreimage at hw
      rw [← hleafdef, hsearch] at hw
      dsimp only at hw
      split at hw
      · cases hw
      · rename_i hc
        exact hc ⟨hne, by rw [hleaf]; rfl⟩
    -- The path is the honest siblings below level 9, then the other level-9 node.
    have hpath : o.path.toList = (Merkle.path hash leaves FORS_HEIGHT l.val).run.toList := by
      have hsplit := Merkle.siblings_succ_toList_concat hash leaves (FORS_HEIGHT - 1) 0 l.val
      rw [Nat.zero_add] at hsplit
      have hsplit' : o.path.toList = lower ++ [o.path[FORS_HEIGHT - 1]] := by
        conv_lhs => rw [← List.take_length (l := o.path.toList)]
        rw [Vector.length_toList]
        change List.take (FORS_HEIGHT - 1 + 1) _ = _
        rw [List.take_add_one]
        simp [lower]
      rw [hsplit', hlower, hlast]
      exact hsplit.symm
    rw [treeOpen_run]
    cases o
    simp only at hsecret hpath
    rw [hsecret, Vector.toList_inj.1 hpath]
  · simp [hsearch] at hsome

/-! ## Every tree -/

variable (f P prf) in
/-- The node at which FORS openings leave the honest trees of instance `idx`, if any.

The trees are searched in order, tree 0 first, each at the leaf the digest picked for it. -/
def findForsPreimage (idx : Fin (2 ^ HEIGHT))
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) : Option NodePreimage :=
  (List.finRange FORS_TREES).findSome? fun kappa =>
    findTreePreimage f P prf idx kappa leaves[kappa] openings[kappa]

/-- Every node the search returns is a valid offer against the honest FORS values. -/
theorem findForsPreimage_valid {idx : Fin (2 ^ HEIGHT)}
    {leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES}
    {openings : Vector TreeOpening FORS_TREES} {w : NodePreimage}
    (hw : findForsPreimage f P prf idx leaves openings = some w) :
    w.Valid f P (forsChildren f P prf) := by
  rw [findForsPreimage] at hw
  obtain ⟨kappa, -, hkappa⟩ := List.exists_of_findSome?_eq_some hw
  exact findTreePreimage_valid hkappa

/-- Honest openings leave no honest tree. -/
theorem findForsPreimage_honest (idx : Fin (2 ^ HEIGHT))
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    findForsPreimage f P prf idx leaves (forsSign (pureHash f) P prf idx.val leaves).run =
      none := by
  rw [findForsPreimage, List.findSome?_eq_none_iff]
  intro kappa _
  rw [forsSign, HashSig.ofFnInOrder_run]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact findTreePreimage_honest idx kappa _

/-- **Binding of FORS.**

Openings that recover the honest FORS key of instance `idx` are its honest openings.

Each is at the leaf the digest picked for its tree.

Otherwise the search finds a node where they leave an honest tree, with a valid offer. -/
theorem forsRecover_binding {idx : Fin (2 ^ HEIGHT)}
    {leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES}
    {openings : Vector TreeOpening FORS_TREES}
    (h : (forsRecover (pureHash f) P idx.val leaves openings).run =
      (forsKey (pureHash f) P prf idx.val).run) :
    openings = (forsSign (pureHash f) P prf idx.val leaves).run ∨
      ∃ w, findForsPreimage f P prf idx leaves openings = some w ∧
        w.Valid f P (forsChildren f P prf) := by
  cases hw : findForsPreimage f P prf idx leaves openings with
  | some w => exact .inr ⟨w, rfl, findForsPreimage_valid hw⟩
  | none =>
  refine .inl (Vector.ext fun i hi => ?_)
  rw [findForsPreimage, List.findSome?_eq_none_iff] at hw
  -- Tree `i` recovers its honest pair, and its search found nothing.
  have htree := congrArg (fun key : ForsKey => key[i]) h
  simp only [forsRecover, forsKey, HashSig.ofFnInOrder_run, Vector.getElem_ofFn, Id.run_bind,
    Id.run_pure] at htree
  simp only [forsSign, HashSig.ofFnInOrder_run, Vector.getElem_ofFn]
  rcases treeRecover_binding (prf := prf) (idx := idx) (kappa := ⟨i, hi⟩) htree with
    ho | ⟨w, hsome, -⟩
  · exact ho
  · rw [hw ⟨i, hi⟩ (List.mem_finRange _)] at hsome
    cases hsome

end EthLib.Cryptography.Sphincs.Unforgeability
