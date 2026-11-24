module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Tree
public import EthLib.Cryptography.Proofs.HashSig
public import EthLib.Cryptography.Proofs.Sphincs.Sign
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Recovery

/-!
# Proofs: EthLib's FORS is the model's

EthLib recovers a FORS public key from openings with the same calls as the model, in order.

So under every answer function, EthLib's FORS public key and openings are the model's.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open SphincsSecurity.Concrete (tweakableHash sequenceFin)
open EthLib.Cryptography.HashSig (ofFnInOrder_eq_sequenceFin ofFnInOrder_eq_sequenceFin_cast)

/-- A model opening as EthLib's. -/
def ofOpening (o : SphincsSecurity.TreeOpening) : TreeOpening :=
  { secret := ofDigest o.secret, path := ofPath o.path }

/-- The model's leaves of the FORS trees as EthLib's. -/
def ofLeaves (leaves : SphincsSecurity.FTree → SphincsSecurity.FLeaf) :
    Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES :=
  Vector.ofFn fun κ => ⟨(leaves ⟨κ.val, κ.isLt⟩).val, (leaves ⟨κ.val, κ.isLt⟩).isLt⟩

/-- The model's openings of the FORS trees as EthLib's. -/
def ofOpenings (opening : SphincsSecurity.FTree → SphincsSecurity.TreeOpening) :
    Vector TreeOpening FORS_TREES :=
  Vector.ofFn fun κ => ofOpening (opening ⟨κ.val, κ.isLt⟩)

/-! ## Recovering the key, call for call

Each tree climbs from its leaf to its root, and `T_k` hashes the 24 roots.

So the recovery with the query is the model's, value for value. -/

section Query

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSig.HashSpec m]

/-- A FORS leaf from its secret derivation is the model's node at height 0. -/
theorem forsLeaves_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) (j : Nat)
    (hj : j < 2 ^ FORS_HEIGHT) :
    forsLeaves (queryH (m := m)) (ofParam P) (secretsOf S P) index.val (treeOf κ) j
      = ofDigest <$> SphincsSecurity.Seeded.forsNode (m := m) P index κ S 0 j := by
  let leaf : SphincsSecurity.FLeaf := ⟨j, hj⟩
  -- The model reduces the leaf index modulo `2^10`, which keeps it.
  have hl : (⟨j % 2 ^ SphincsSecurity.forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :
      SphincsSecurity.FLeaf) = leaf :=
    Fin.ext (Nat.mod_eq_of_lt hj)
  rw [forsLeaves, SphincsSecurity.Seeded.forsNode_zero, SphincsSecurity.Seeded.forsLeaf, hl,
    show j = leaf.val from rfl, forsSecret_queryH S P index κ leaf, bind_map_left, map_bind]
  exact bind_congr fun secret => forsLeafHash_queryH P index κ leaf secret

/-- A leaf divided by `2^(level + 1)` is below `2^(10 - (level + 1))`. -/
theorem div_two_pow_lt (leaf : SphincsSecurity.FLeaf) (level : Nat) (h : level < FORS_HEIGHT) :
    leaf.val / 2 ^ (level + 1) < 2 ^ (FORS_HEIGHT - (level + 1)) := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
    show FORS_HEIGHT - (level + 1) + (level + 1) = FORS_HEIGHT by omega]
  exact leaf.isLt

/-- The climb of a FORS tree over its `a` levels is the model's fold, value for value. -/
theorem forsFold_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (κ : SphincsSecurity.FTree) (leaf : SphincsSecurity.FLeaf)
    (path : Fin SphincsSecurity.forsHeight → SphincsSecurity.Digest) (v : SphincsSecurity.Digest) :
    ofDigest <$> SphincsSecurity.Concrete.forsFold (m := m) P index κ leaf path
        SphincsSecurity.forsHeight v
      = Merkle.climb (forsNodeHash (queryH (m := m)) (ofParam P) index.val (treeOf κ))
          ⟨0, leaf.val⟩ (ofDigest v) (List.ofFn fun i => ofDigest (path i)) := by
  -- Inside the tree, the path extension reads the path.
  have hpath : (List.ofFn fun i : Fin SphincsSecurity.forsHeight =>
      SphincsSecurity.Concrete.extendPath path i.val).map ofDigest =
        List.ofFn fun i => ofDigest (path i) := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext fun i => by
      simp only [Function.comp_apply, SphincsSecurity.Concrete.extendPath, dite_eq_left i.isLt])
  rw [SphincsSecurity.Concrete.forsFold, ← hpath]
  refine (Merkle.climb_map_ancestors (SphincsSecurity.Concrete.forsHash (m := m) P index κ) _
    ofDigest _ _ _ ?_).symm
  -- The climb hashes at the leaf's ancestors on levels `1` to `a`, inside the tree.
  intro k hk1 hk2 left right
  obtain ⟨level, rfl⟩ : ∃ level, k = level + 1 := ⟨k - 1, by omega⟩
  simp only [List.length_ofFn] at hk2
  have hlevel : level < SphincsSecurity.forsHeight := by omega
  rw [Merkle.Position.ancestor_mk_zero, SphincsSecurity.Concrete.forsHash,
    dite_eq_left hlevel]
  exact forsNodeHash_queryH_mod P index κ ⟨level, hlevel⟩ _ (div_two_pow_lt leaf level hlevel)
    left right

/-- The root that an opening leads to is the model's. -/
theorem treeRecover_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (κ : SphincsSecurity.FTree) (leaf : SphincsSecurity.FLeaf) (o : SphincsSecurity.TreeOpening) :
    treeRecover (queryH (m := m)) (ofParam P) index.val (treeOf κ) leaf (ofOpening o)
      = ofDigest <$> SphincsSecurity.Concrete.treeRecover (m := m) P index κ leaf o := by
  have hclimb := forsFold_queryH (m := m) P index κ leaf o.path
  simp only [treeRecover, SphincsSecurity.Concrete.treeRecover, ofOpening]
  rw [forsLeafHash_queryH, bind_map_left, map_bind]
  refine bind_congr fun value => ?_
  -- The climb takes all 10 heights, from the leaf to the root.
  simp only [ofPath, Vector.toList_ofFn]
  rw [hclimb value]
  rfl

/-- The model's FORS roots as EthLib's vector of roots. -/
def ofRoots (roots : SphincsSecurity.ForsKey) : Vector Digest FORS_TREES :=
  Vector.ofFn fun κ => ofDigest (roots ⟨κ.val, κ.isLt⟩)

/-- The FORS public key that the openings lead to is the model's. -/
theorem forsRecover_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (leaves : SphincsSecurity.FTree → SphincsSecurity.FLeaf)
    (opening : SphincsSecurity.FTree → SphincsSecurity.TreeOpening) :
    forsRecover (queryH (m := m)) (ofParam P) index.val (ofLeaves leaves) (ofOpenings opening)
      = ofDigest <$> (SphincsSecurity.Concrete.forsRecover (m := m) P index leaves opening >>=
          SphincsSecurity.Concrete.forsPublicKey P index) := by
  have h : FORS_TREES = SphincsSecurity.forsTrees := rfl
  have htrees : (fun kappa : Fin FORS_TREES => treeRecover (queryH (m := m)) (ofParam P) index.val
      kappa (ofLeaves leaves)[kappa] (ofOpenings opening)[kappa])
      = fun kappa => ofDigest <$> SphincsSecurity.Concrete.treeRecover (m := m) P index
          (Fin.cast h kappa) (leaves (Fin.cast h kappa)) (opening (Fin.cast h kappa)) :=
    funext fun kappa => by
      simp only [ofLeaves, ofOpenings, Fin.getElem_fin, Vector.getElem_ofFn]
      exact treeRecover_queryH P index (Fin.cast h kappa) _ _
  rw [forsRecover, htrees, ofFnInOrder_eq_sequenceFin_cast h (fun κ =>
    SphincsSecurity.Concrete.treeRecover (m := m) P index κ (leaves κ) (opening κ)) ofDigest,
    bind_map_left, SphincsSecurity.Concrete.forsRecover, map_bind]
  exact bind_congr fun roots => forsPkFromRoots_queryH P index roots

end Query

/-! ## Key and openings under fixed answers

Key generation and signing compute each node from scratch in EthLib, and so does the model.

Under a fixed answer function a repeated call gets the same answer. -/

section Answers

open OracleComp SphincsSecurity.Completeness

variable (f : QueryImpl HashSig.HashSpec Id)

/-- Under fixed answers, a vector computed in order is the vector of the values. -/
theorem eval_ofFnInOrder {α : Type} (n : Nat) (c : Fin n → OracleComp HashSig.HashSpec α) :
    evalWithAnswerFn f (ofFnInOrder n c) = Vector.ofFn fun i => evalWithAnswerFn f (c i) := by
  rw [HashSig.ofFnInOrder_map_monad (m := OracleComp HashSig.HashSpec) (n := Id)
    (fun {β} (x : OracleComp HashSig.HashSpec β) => (evalWithAnswerFn f x : Id β))
    (fun b => evalWithAnswerFn_pure f b) (fun x g => evalWithAnswerFn_bind f x g)]
  exact HashSig.ofFnInOrder_run _ _

/-- Under fixed answers, a FORS node at height `level <= 10` is the model's. -/
theorem forsNode_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) :
    ∀ (level j : Nat), level ≤ FORS_HEIGHT → j < 2 ^ (FORS_HEIGHT - level) →
      evalWithAnswerFn f (forsNode (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
          (secretsOf S P) index.val (treeOf κ) level j)
        = ofDigest (forsNodeValue f P index κ S level j)
  | 0, j, _, hj => by
    rw [forsNode, Merkle.node_zero, forsLeaves_queryH S P index κ j hj, evalWithAnswerFn_map]
    rfl
  | level + 1, j, hlevel, hj => by
    have hpow : 2 ^ (FORS_HEIGHT - level) = 2 * 2 ^ (FORS_HEIGHT - (level + 1)) := by
      rw [show FORS_HEIGHT - level = FORS_HEIGHT - (level + 1) + 1 by omega, pow_succ]
      ring
    have hl := forsNode_answers S P index κ level (2 * j) (by omega) (by omega)
    have hr := forsNode_answers S P index κ level (2 * j + 1) (by omega) (by omega)
    have hlt : level < SphincsSecurity.forsHeight := by
      change _ < 10; simp only [FORS_HEIGHT] at hlevel; omega
    simp only [forsNode] at hl hr ⊢
    rw [Merkle.node_succ, evalWithAnswerFn_bind, hl, evalWithAnswerFn_bind, hr,
      forsNodeValue_succ f P index κ S level j hlt]
    erw [forsNodeHash_queryH_mod (m := OracleComp HashSig.HashSpec) P index κ ⟨level, hlt⟩ j hj,
      evalWithAnswerFn_map, eval_tweakableHash]

/-- Under fixed answers, the root of a FORS tree is the model's. -/
theorem forsRoot_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) :
    evalWithAnswerFn f (forsRoot (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (secretsOf S P) index.val (treeOf κ))
      = ofDigest (rootValue f P index S κ) :=
  forsNode_answers f S P index κ FORS_HEIGHT 0 le_rfl (Nat.two_pow_pos _)

/-- Under fixed answers, the FORS public key is the model's. -/
theorem forsKey_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) :
    evalWithAnswerFn f (forsKey (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (secretsOf S P) index.val)
      = ofDigest (evalWithAnswerFn f
          (SphincsSecurity.Seeded.forsKey P index S : OracleComp HashSig.HashSpec _)) := by
  have hroots : evalWithAnswerFn f (ofFnInOrder FORS_TREES fun kappa =>
      forsRoot (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P) (secretsOf S P) index.val
        kappa)
      = ofRoots fun κ => rootValue f P index S κ := by
    rw [eval_ofFnInOrder]
    exact Vector.ext fun i hi => by
      simp only [Vector.getElem_ofFn, ofRoots]
      exact forsRoot_answers f S P index ⟨i, hi⟩
  rw [forsKey_eq, forsKey, evalWithAnswerFn_bind, hroots, ofRoots, forsPkFromRoots_queryH,
    evalWithAnswerFn_map]

/-- Under fixed answers, the siblings above a FORS leaf are the model's nodes, height by height. -/
theorem forsSiblings_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) (e : Nat)
    (he : e < 2 ^ FORS_HEIGHT) :
    ∀ (n level : Nat), level + n ≤ FORS_HEIGHT →
      evalWithAnswerFn f (Merkle.siblings
          (forsNodeHash (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P) index.val
            (treeOf κ))
          (forsLeaves queryH (ofParam P) (secretsOf S P) index.val (treeOf κ))
          ((⟨0, e⟩ : Merkle.Position).ancestor level) n)
        = Vector.ofFn fun i : Fin n =>
            ofDigest (forsNodeValue f P index κ S (level + i.val)
              (Nat.xor (e / 2 ^ (level + i.val)) 1))
  | 0, level, _ => Vector.ext fun _ hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, level, hn => by
    -- The node at height `level` has index below `2^(10 - level)`, and so has its sibling.
    have hlt : e / 2 ^ level < 2 ^ (FORS_HEIGHT - level) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      exact he.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hsib : (e / 2 ^ level) ^^^ 1 < 2 ^ (FORS_HEIGHT - level) :=
      Nat.xor_lt_two_pow hlt (Nat.one_lt_two_pow (by omega))
    have hnode := forsNode_answers f S P index κ level ((e / 2 ^ level) ^^^ 1) (by omega) hsib
    simp only [forsNode] at hnode
    rw [Merkle.siblings, Merkle.Position.parent_ancestor, Merkle.Position.ancestor_mk_zero e level,
      Merkle.Position.sibling_mk]
    rw [evalWithAnswerFn_bind, hnode, evalWithAnswerFn_bind,
      forsSiblings_answers S P index κ e he n (level + 1) (by omega), evalWithAnswerFn_pure]
    apply Vector.ext
    intro i hi
    cases i with
    | zero => simp
    | succ i => simp [Nat.add_right_comm, Nat.add_assoc]

/-- Under fixed answers, the opening of a FORS tree, its path computed alone, is the model's. -/
theorem treeOpen_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) (leaf : SphincsSecurity.FLeaf) :
    evalWithAnswerFn f (Recompute.treeOpen (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (secretsOf S P) index.val (treeOf κ) leaf)
      = ofOpening (evalWithAnswerFn f
          (SphincsSecurity.Seeded.treeOpen P index κ leaf S : OracleComp HashSig.HashSpec _)) := by
  have h := forsSiblings_answers f S P index κ (Fin.val (n := 2 ^ FORS_HEIGHT) leaf) leaf.isLt
    FORS_HEIGHT 0 (by simp)
  simp only [Merkle.Position.ancestor_zero, Nat.zero_add] at h
  -- EthLib reads the leaf as one of `2^FORS_HEIGHT`, the model as one of `2^forsHeight`.
  have hs : forsSecret (secretsOf (m := OracleComp HashSig.HashSpec) S P) index.val (treeOf κ)
      (Fin.val (n := 2 ^ FORS_HEIGHT) leaf)
      = ofDigest <$> SphincsSecurity.Seeded.forsSecret P index κ leaf S :=
    forsSecret_queryH S P index κ leaf
  rw [eval_treeOpen]
  simp only [Recompute.treeOpen, evalWithAnswerFn_bind, Merkle.path]
  rw [hs, evalWithAnswerFn_map, h, evalWithAnswerFn_pure]
  rfl

/-- Under fixed answers, the FORS openings, their paths computed alone, are the model's. -/
theorem forsSign_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (leaves : SphincsSecurity.FTree → SphincsSecurity.FLeaf) :
    evalWithAnswerFn f (Recompute.forsSign (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (secretsOf S P) index.val (ofLeaves leaves))
      = ofOpenings (evalWithAnswerFn f
          (SphincsSecurity.Seeded.forsOpen P index leaves S : OracleComp HashSig.HashSpec _)) := by
  rw [Recompute.forsSign, eval_ofFnInOrder]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, ofLeaves, ofOpenings,
    SphincsSecurity.Seeded.forsOpen, eval_sequenceFin]
  exact treeOpen_answers f S P index ⟨i, hi⟩ (leaves ⟨i, hi⟩)

end Answers

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
