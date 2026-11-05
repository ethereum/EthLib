module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.LabTree

/-!
# Proofs: FORS in the eager game

A FORS leaf hashes a secret, and the secrets of leaves `2p` and `2p + 1` are one derivation.

The lab leaf touches both halves of that derivation and reads the leaf.

It never reads a secret, so a later game can defer the secrets of the leaves no signature opens.

- The honest leaves, nodes and key of a FORS instance have the law of the lab ones.
- An opening reads the secret it reveals and touches the other half of its derivation.
  The honest opening and the lab opening have one law.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open OracleSpec OracleComp

/-! ## Leaves -/

/-- The cell of node `j` on `level` of tree `kappa` of a FORS instance.

Level 0 holds the leaves, and levels 1 to 9 the nodes. -/
def forsCell (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES) : Nat → Nat → Cell
  | 0, j => .inr (.forsLeaf idx kappa (Fin.ofNat _ j))
  | level + 1, j => .inr (.forsNode idx kappa
      ⟨level % (FORS_HEIGHT - 1), Nat.mod_lt _ (by decide)⟩ (Fin.ofNat _ j))

/-- The lab leaf `j` of a tree: touch both halves of its secret's derivation, read the leaf. -/
noncomputable def labForsLeaf (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (j : Nat) : OracleComp LabWorld Digest := do
  touchDerivation (secretCell P idx kappa (forsIndex j)).1
  readNode (.forsLeaf idx kappa (forsIndex j))

/-- A FORS leaf, from its secret held in its cell, is one draw of the leaf's label. -/
theorem forsLeafHash_labTriple (P : PublicParam) (idx : Fin (2 ^ HEIGHT))
    (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT)) (secret : Digest) :
    LabTriple P (fun st => st.2 (.inl (secretCell P idx kappa l)) = some secret)
      (forsLeafHash labH P idx.val kappa l secret) (readNode (.forsLeaf idx kappa l))
      fun y st => st.2 (.inr (.forsLeaf idx kappa l)) = some y := by
  have e : forsLeafHash labH P idx.val kappa l secret =
      th labH P (Node.forsLeaf idx kappa l).address
        (digestsBytes [secret] ++ (Node.forsLeaf idx kappa l).suffix) := by
    simp only [forsLeafHash, Node.address, Node.suffix, digestsBytes_singleton,
      ByteArray.append_empty]
  rw [e]
  exact (th_labTriple P _ [secret]).mono (fun _ h => .cons h .nil) fun _ _ h => h

/-- **FORS leaves.**

The honest leaf `j` of a tree and its lab leaf have one law of output and state.

The leaf's cell then holds the result. -/
theorem forsLeaves_labTriple (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (j : Nat) :
    LabTriple P (fun _ => True) (forsLeaves labH P labPrf idx.val kappa j)
      (labForsLeaf P idx kappa j) fun y st => True ∧ st.2 (forsCell idx kappa 0 j) = some y := by
  have hlab : simulateQ (graph P).eagerImpl (labForsLeaf P idx kappa j) =
      simulateQ (graph P).eagerImpl (do
        let _ ← labPrf P (addrForsPrf idx.val kappa ⟨(forsIndex j).val / 2,
          by have := (forsIndex j).isLt; simp only [FORS_HEIGHT] at *; omega⟩) .empty
        readNode (.forsLeaf idx kappa (forsIndex j))) := by
    simp only [labForsLeaf, secretCell, simulateQ_bind,
      simulateQ_eagerImpl_touchDerivation P (isDerivationAddress_addrForsPrf _ _ _), bind_map_left]
  refine QueryImpl.EqDistTriple.of_simulateQ_eq_right ?_ hlab.symm
  simp only [forsLeaves, forsSecret, bind_assoc, pure_bind]
  refine (derivation_labTriple P (isDerivationAddress_addrForsPrf _ _ _)).bind fun out => ?_
  exact (forsLeafHash_labTriple P idx kappa (forsIndex j) _).mono (fun _ h => h _)
    fun _ _ h => ⟨trivial, h⟩

/-! ## Nodes -/

/-- The lab node of a tree: the lab leaves, and a read of each parent's cell. -/
noncomputable def labForsNode (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (level j : Nat) : OracleComp LabWorld Digest :=
  Merkle.node (fun level j _ _ => readCell (some (forsCell idx kappa level j)))
    (labForsLeaf P idx kappa) level j

/-- A position of a FORS tree: a level up to 9, and an index on that level. -/
def ForsPos (level j : Nat) : Prop :=
  level < FORS_HEIGHT ∧ j < 2 ^ (FORS_HEIGHT - level)

/-- The children of a position of a FORS tree are positions. -/
theorem ForsPos.children {level j : Nat} (h : ForsPos (level + 1) j) :
    ForsPos level (2 * j) ∧ ForsPos level (2 * j + 1) := by
  obtain ⟨hl, hj⟩ := h
  have e : 2 ^ (FORS_HEIGHT - level) = 2 * 2 ^ (FORS_HEIGHT - (level + 1)) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- A parent step of a FORS tree, at a position above level 0, from children held in cells. -/
theorem forsNodeHash_labTriple (P : PublicParam) (idx : Fin (2 ^ HEIGHT))
    (kappa : Fin FORS_TREES) (level j : Nat) (left right : Digest) (h : ForsPos (level + 1) j) :
    LabTriple P (fun st => True ∧ st.2 (forsCell idx kappa level (2 * j)) = some left ∧
        st.2 (forsCell idx kappa level (2 * j + 1)) = some right)
      (forsNodeHash labH P idx.val kappa (level + 1) j left right)
      (readCell (some (forsCell idx kappa (level + 1) j)))
      fun y st => True ∧ st.2 (forsCell idx kappa (level + 1) j) = some y := by
  have hl : level < FORS_HEIGHT - 1 := by
    have := h.1
    simp only [FORS_HEIGHT] at *
    omega
  have hj : j < 2 ^ FORS_HEIGHT :=
    lt_of_lt_of_le h.2 (Nat.pow_le_pow_right (by decide) (by omega))
  have e : forsNodeHash labH P idx.val kappa (level + 1) j left right =
      th labH P (Node.forsNode idx kappa ⟨level, hl⟩ ⟨j, hj⟩).address
        (digestsBytes [left, right] ++ (Node.forsNode idx kappa ⟨level, hl⟩ ⟨j, hj⟩).suffix) := by
    simp only [forsNodeHash, Node.address, Node.suffix, digestsBytes_pair,
      ByteArray.append_empty]
  have hc : forsCell idx kappa (level + 1) j =
      .inr (.forsNode idx kappa ⟨level, hl⟩ ⟨j, hj⟩) := by
    simp only [forsCell, Nat.mod_eq_of_lt hl, Fin.ofNat, Nat.mod_eq_of_lt hj]
  rw [e, hc]
  refine (th_labTriple P _ [left, right]).mono (fun st ⟨_, hL, hR⟩ => ?_) fun _ _ h => ⟨trivial, h⟩
  rcases level with _ | l
  · exact .cons hL (.cons hR .nil)
  · have hl' : (⟨l % (FORS_HEIGHT - 1), Nat.mod_lt _ (by decide)⟩ : Fin (FORS_HEIGHT - 1)) =
        ⟨l, by omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    simp only [forsCell] at hL hR
    rw [hl'] at hL hR
    simp only [Node.children, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact .cons hL (.cons hR .nil)

/-- **FORS nodes.**

The honest node at a position of a FORS tree and its lab node have one law of output and state.

The node's cell then holds the result. -/
theorem forsNode_labTriple (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (level j : Nat) (h : ForsPos level j) :
    LabTriple P (fun _ => True) (forsNode labH P labPrf idx.val kappa level j)
      (labForsNode P idx kappa level j)
      fun y st => True ∧ st.2 (forsCell idx kappa level j) = some y :=
  node_eqDistTriple (so := (graph P).eagerImpl) (fun _ => True) ForsPos
    (fun level j y (st : LabState) => st.2 (forsCell idx kappa level j) = some y)
    (fun _ _ h => h.children)
    (fun _ _ _ _ _ (hle : (_ : LabState) ≤ _) h => hle.2 h)
    (fun j _ => forsLeaves_labTriple P idx kappa j)
    (forsNodeHash_labTriple P idx kappa) level j h

/-! ## Keys -/

/-- The lab FORS key of an instance: the lab level-9 nodes of every tree, tree 0 first. -/
noncomputable def labForsKey (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) :
    OracleComp LabWorld ForsKey :=
  Xmss.ofFnInOrder FORS_TREES fun kappa => do
    let left ← labForsNode P idx kappa (FORS_HEIGHT - 1) 0
    let right ← labForsNode P idx kappa (FORS_HEIGHT - 1) 1
    return (left, right)

/-- **FORS keys.**

The honest FORS key of an instance and its lab key have one law of output and state.

The cells of the two level-9 nodes of each tree then hold that tree's entry of the key. -/
theorem forsKey_labTriple (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) :
    LabTriple P (fun _ => True) (forsKey labH P labPrf idx.val) (labForsKey P idx)
      fun key st => True ∧ ∀ kappa : Fin FORS_TREES,
        st.2 (forsCell idx kappa (FORS_HEIGHT - 1) 0) = some key[kappa].1 ∧
          st.2 (forsCell idx kappa (FORS_HEIGHT - 1) 1) = some key[kappa].2 := by
  refine ofFnInOrder_eqDistTriple (fun _ => True)
    (fun kappa (t : Digest × Digest) (st : LabState) =>
      st.2 (forsCell idx kappa (FORS_HEIGHT - 1) 0) = some t.1 ∧
        st.2 (forsCell idx kappa (FORS_HEIGHT - 1) 1) = some t.2)
    (fun _ _ _ _ hle h => ⟨hle.2 h.1, hle.2 h.2⟩) fun kappa => ?_
  have h0 : ForsPos (FORS_HEIGHT - 1) 0 := ⟨by decide, by decide⟩
  have h1 : ForsPos (FORS_HEIGHT - 1) 1 := ⟨by decide, by decide⟩
  refine (forsNode_labTriple P idx kappa (FORS_HEIGHT - 1) 0 h0).bind fun left => ?_
  refine ((forsNode_labTriple P idx kappa (FORS_HEIGHT - 1) 1 h1).frame
    (F := fun st => st.2 (forsCell idx kappa (FORS_HEIGHT - 1) 0) = some left)
    fun _ _ hle h => hle.2 h).bind fun right => ?_
  exact QueryImpl.EqDistTriple.pure _ fun _ ⟨⟨_, hr⟩, hl⟩ => ⟨trivial, hl, hr⟩

/-! ## Openings -/

/-- The lab secret of leaf `l`: read its half of the derivation, touch the other, half 0 first. -/
noncomputable def labForsSecret (P : PublicParam) (idx : Fin (2 ^ HEIGHT))
    (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT)) : OracleComp LabWorld Digest :=
  if l.val % 2 = 0 then do
    let secret ← readCell (some (.inl ((secretCell P idx kappa l).1, 0)))
    touchCell (some (.inl ((secretCell P idx kappa l).1, 1)))
    return secret
  else do
    touchCell (some (.inl ((secretCell P idx kappa l).1, 0)))
    readCell (some (.inl ((secretCell P idx kappa l).1, 1)))

/-- In the eager game, the lab secret of a leaf is its honest secret. -/
theorem simulateQ_eagerImpl_labForsSecret (P : PublicParam) (idx : Fin (2 ^ HEIGHT))
    (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT)) :
    simulateQ (graph P).eagerImpl (labForsSecret P idx kappa l) =
      simulateQ (graph P).eagerImpl (forsSecret P labPrf idx.val kappa l) := by
  rw [forsSecret, labPrf_eq P (isDerivationAddress_addrForsPrf _ _ _)]
  rcases Nat.mod_two_eq_zero_or_one l.val with hl | hl
  · have e : (⟨l.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := Fin.ext hl
    rw [labForsSecret, ite_eq_left hl]
    simp only [simulateQ_bind, simulateQ_pure, (graph P).simulateQ_eagerImpl_touchCell,
      bind_assoc, pure_bind, bind_map_left]
    refine bind_congr fun u => bind_congr fun v => ?_
    rw [e]
    exact congrArg pure (halfOf_zero_hashHalves_symm u v).symm
  · have e : (⟨l.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 1 := Fin.ext hl
    rw [labForsSecret, ite_eq_right (by omega)]
    simp only [simulateQ_bind, simulateQ_pure, (graph P).simulateQ_eagerImpl_touchCell,
      bind_assoc, pure_bind, bind_map_left]
    refine bind_congr fun u => (bind_pure _).symm.trans (bind_congr fun v => ?_)
    rw [e]
    exact congrArg pure (halfOf_one_hashHalves_symm u v).symm

/-- The lab path of leaf `l` of a tree: the lab nodes of its siblings, from the leaf up. -/
noncomputable def labForsPath (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (l : Nat) : OracleComp LabWorld (Vector Digest FORS_HEIGHT) :=
  Merkle.path (fun level j _ _ => readCell (some (forsCell idx kappa level j)))
    (labForsLeaf P idx kappa) FORS_HEIGHT l

/-- **FORS paths.**

The honest path of a leaf of a FORS tree and its lab path have one law of output and state.

The cell of each sibling then holds its value. -/
theorem forsPath_labTriple (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) :
    LabTriple P (fun _ => True)
      (Merkle.path (forsNodeHash labH P idx.val kappa) (forsLeaves labH P labPrf idx.val kappa)
        FORS_HEIGHT l)
      (labForsPath P idx kappa l)
      fun v st => True ∧ ∀ i : Fin FORS_HEIGHT,
        st.2 (forsCell idx kappa (0 + i) (l.val / 2 ^ i.val ^^^ 1)) = some v[i] :=
  siblings_eqDistTriple (so := (graph P).eagerImpl) (fun _ => True) ForsPos
    (fun level j y (st : LabState) => st.2 (forsCell idx kappa level j) = some y)
    (fun _ _ h => h.children)
    (fun _ _ _ _ _ (hle : (_ : LabState) ≤ _) h => hle.2 h)
    (fun j _ => forsLeaves_labTriple P idx kappa j)
    (forsNodeHash_labTriple P idx kappa) FORS_HEIGHT 0 l fun i hi => by
      refine ⟨by omega, Nat.xor_lt_two_pow ?_ (Nat.one_lt_two_pow (by omega))⟩
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      convert l.isLt using 2
      omega

/-- The lab opening of tree `kappa` at leaf `l`: the lab secret, then the lab path. -/
noncomputable def labTreeOpen (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) : OracleComp LabWorld TreeOpening := do
  let secret ← labForsSecret P idx kappa l
  let path ← labForsPath P idx kappa l
  return { secret, path }

/-- **FORS openings.**

The honest opening of a tree at a leaf and its lab opening have one law of output and state. -/
theorem treeOpen_labTriple (P : PublicParam) (idx : Fin (2 ^ HEIGHT)) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) :
    LabTriple P (fun _ => True) (treeOpen labH P labPrf idx.val kappa l)
      (labTreeOpen P idx kappa l) fun _ _ => True := by
  have hlab : simulateQ (graph P).eagerImpl (labTreeOpen P idx kappa l) =
      simulateQ (graph P).eagerImpl (do
        let secret ← forsSecret P labPrf idx.val kappa l
        let path ← labForsPath P idx kappa l
        return ({ secret, path } : TreeOpening)) := by
    simp only [labTreeOpen, simulateQ_bind, simulateQ_eagerImpl_labForsSecret]
  refine QueryImpl.EqDistTriple.of_simulateQ_eq_right ?_ hlab.symm
  simp only [treeOpen, forsSecret, bind_assoc, pure_bind]
  refine (derivation_labTriple P (isDerivationAddress_addrForsPrf _ _ _)).bind fun out => ?_
  refine ((forsPath_labTriple P idx kappa l).mono (fun _ _ => trivial) fun _ _ h => h).bind
    fun path => ?_
  exact QueryImpl.EqDistTriple.pure _ fun _ _ => trivial

/-- **FORS signatures.**

The honest openings of every tree and the lab openings have one law of output and state. -/
theorem forsSign_labTriple (P : PublicParam) (idx : Fin (2 ^ HEIGHT))
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    LabTriple P (fun _ => True) (forsSign labH P labPrf idx.val leaves)
      (Xmss.ofFnInOrder FORS_TREES fun kappa => labTreeOpen P idx kappa leaves[kappa])
      fun _ _ => True :=
  (ofFnInOrder_eqDistTriple (fun _ => True) (fun _ _ _ => True) (fun _ _ _ _ _ h => h)
    fun kappa => (treeOpen_labTriple P idx kappa leaves[kappa]).mono (fun _ h => h)
      fun _ _ _ => ⟨trivial, trivial⟩).mono (fun _ h => h) fun _ _ _ => trivial

end EthLib.Cryptography.Sphincs.Unforgeability
