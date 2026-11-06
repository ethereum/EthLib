module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Tree
public import EthLib.Cryptography.Proofs.HashSig
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Recovery

/-!
# Proofs: EthLib's FORS is the model's

EthLib recovers a FORS key from openings with the same calls as the model, in the same order.

So the recovery with the query is the model's, value for value.

Key generation and signing make more calls than the model: each leaf derives its pair of secrets.

Under a fixed answer function a repeated call gets the same answer.

So under every answer function, EthLib's FORS key and openings are the model's.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open SphincsSecurity.Concrete (tweakableHash sequenceFin)

/-- A model opening as EthLib's. -/
def ofOpening (o : SphincsSecurity.TreeOpening) : TreeOpening :=
  { secret := ofDigest o.secret, path := ofPath o.path }

/-- A model pair of level-9 nodes as EthLib's. -/
def ofTops (t : SphincsSecurity.Digest × SphincsSecurity.Digest) : Digest × Digest :=
  (ofDigest t.1, ofDigest t.2)

/-- A model FORS key as EthLib's. -/
def ofForsKey (k : SphincsSecurity.ForsKey) : ForsKey :=
  Vector.ofFn fun κ => ofTops (k ⟨κ.val, κ.isLt⟩)

/-- The model's leaves of the FORS trees as EthLib's. -/
def ofLeaves (leaves : SphincsSecurity.FTree → SphincsSecurity.FLeaf) :
    Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES :=
  Vector.ofFn fun κ => ⟨(leaves ⟨κ.val, κ.isLt⟩).val, (leaves ⟨κ.val, κ.isLt⟩).isLt⟩

/-- The model's openings of the FORS trees as EthLib's. -/
def ofOpenings (opening : SphincsSecurity.FTree → SphincsSecurity.TreeOpening) :
    Vector TreeOpening FORS_TREES :=
  Vector.ofFn fun κ => ofOpening (opening ⟨κ.val, κ.isLt⟩)

/-! ## Recovering the key, call for call -/

section Query

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSig.HashSpec m]

/-- The secret of a FORS leaf is the model's. -/
theorem forsSecret_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) (leaf : SphincsSecurity.FLeaf) :
    forsSecret (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S)) index.val (treeOf κ) leaf
      = ofDigest <$> SphincsSecurity.Seeded.forsSecret (m := m) P index κ leaf S := by
  have hprf : seedPrf (queryH (m := m)) (ofSeed S) (ofParam P)
      (addrForsPrf index.val (treeOf κ) ⟨leaf.val / 2, (SphincsSecurity.leafPair leaf).isLt⟩) .empty
      = (ofOutput <$> SphincsSecurity.deriveOutput (m := m) P
          (.fors index κ (SphincsSecurity.leafPair leaf)) S :
            m EthLib.Cryptography.Sphincs.HashOutput) :=
    forsPrf_queryH S P index κ (SphincsSecurity.leafPair leaf)
  simp only [forsSecret, SphincsSecurity.Seeded.forsSecret]
  rw [hprf, map_bind]
  refine (bind_map_left _ _ _).trans (bind_congr fun out => ?_)
  rw [map_pure, halfOf_mod_two_ofOutput]

/-- A FORS leaf from its seed derivation is the model's node at level 0. -/
theorem forsLeaves_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) (j : Nat) :
    forsLeaves (queryH (m := m)) (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S)) index.val
        (treeOf κ) j
      = ofDigest <$> SphincsSecurity.Seeded.forsNode (m := m) P index κ S 0 j := by
  let leaf : SphincsSecurity.FLeaf :=
    ⟨j % 2 ^ SphincsSecurity.forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  have hl : forsIndex j = leaf := rfl
  rw [forsLeaves, SphincsSecurity.Seeded.forsNode, hl, forsSecret_queryH S P index κ leaf,
    bind_map_left, map_bind]
  exact bind_congr fun secret => forsLeafHash_queryH P index κ _ secret

/-- The climb of a FORS tree from a level is the model's fold, continued from that level. -/
theorem forsClimb_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (κ : SphincsSecurity.FTree) (leaf : SphincsSecurity.FLeaf)
    (path : Fin SphincsSecurity.forsHeight → SphincsSecurity.Digest) (v : SphincsSecurity.Digest) :
    ∀ (n level : Nat), level + n ≤ FORS_HEIGHT →
      ofDigest <$> SphincsSecurity.Concrete.forsFold (m := m) P index κ leaf path (level + n) v
        = SphincsSecurity.Concrete.forsFold (m := m) P index κ leaf path level v >>= fun c =>
            Merkle.climb (forsNodeHash (queryH (m := m)) (ofParam P) index.val (treeOf κ)) level
              (leaf.val / 2 ^ level) (ofDigest c)
              (((List.ofFn fun i => ofDigest (path i)).drop level).take n)
  | 0, level, _ => by simp [Merkle.climb]
  | n + 1, level, hn => by
    rw [show level + (n + 1) = level + 1 + n by omega,
      forsClimb_queryH P index κ leaf path v n (level + 1) (by omega)]
    have hlevel : level < SphincsSecurity.forsHeight := by
      change _ < 10
      simp only [FORS_HEIGHT] at hn
      omega
    rw [List.drop_eq_getElem_cons (i := level) (by simp only [List.length_ofFn]; exact hlevel),
      List.take_succ_cons]
    simp only [SphincsSecurity.Concrete.forsFold, dite_eq_left hlevel, bind_assoc,
      List.getElem_ofFn]
    refine bind_congr fun c => ?_
    have hdiv : leaf.val / 2 ^ level / 2 = leaf.val / 2 ^ (level + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    have hnode := forsNodeHash_queryH (m := m) P index κ ⟨level, hlevel⟩
      ⟨leaf.val / 2 ^ (level + 1), Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt⟩
    rw [Merkle.climb, hdiv, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (leaf.val / 2 ^ level) with h | h
    · simp only [h, Merkle.ordered, ↓reduceIte, Nat.zero_ne_one, decide_false,
        Bool.false_eq_true]
      rw [hnode, bind_map_left]
    · simp only [h, Merkle.ordered, ↓reduceIte, Nat.one_ne_zero, decide_true]
      rw [hnode, bind_map_left]

/-- The two level-9 nodes that an opening leads to are the model's. -/
theorem treeRecover_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (κ : SphincsSecurity.FTree) (leaf : SphincsSecurity.FLeaf) (o : SphincsSecurity.TreeOpening) :
    treeRecover (queryH (m := m)) (ofParam P) index.val (treeOf κ) leaf (ofOpening o)
      = ofTops <$> SphincsSecurity.Concrete.treeRecover (m := m) P index κ leaf o := by
  have hclimb := forsClimb_queryH (m := m) P index κ leaf o.path
  simp only [treeRecover, SphincsSecurity.Concrete.treeRecover, ofOpening]
  rw [forsLeafHash_queryH, bind_map_left, map_bind]
  refine bind_congr fun value => ?_
  have h9 := hclimb value (SphincsSecurity.forsHeight - 1) 0 (by decide)
  simp only [Nat.zero_add, SphincsSecurity.Concrete.forsFold, pure_bind, pow_zero, Nat.div_one,
    List.drop_zero] at h9
  simp only [ofPath, Vector.toList_ofFn,
    show FORS_HEIGHT - 1 = SphincsSecurity.forsHeight - 1 from rfl]
  erw [← h9]
  rw [bind_map_left, map_bind]
  refine bind_congr fun node => ?_
  rw [map_pure]
  refine congrArg pure ?_
  erw [Vector.getElem_ofFn]
  simp only [Merkle.ordered, SphincsSecurity.Concrete.orderTops, ofTops, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (leaf.val / 2 ^ (SphincsSecurity.forsHeight - 1)) with h | h
  · simp only [h, ↓reduceIte, Nat.zero_ne_one, decide_false, Bool.false_eq_true]
    rfl
  · simp only [h, ↓reduceIte, Nat.one_ne_zero, decide_true]
    rfl

/-- The FORS key that the openings lead to is the model's. -/
theorem forsRecover_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (leaves : SphincsSecurity.FTree → SphincsSecurity.FLeaf)
    (opening : SphincsSecurity.FTree → SphincsSecurity.TreeOpening) :
    forsRecover (queryH (m := m)) (ofParam P) index.val (ofLeaves leaves) (ofOpenings opening)
      = ofForsKey <$> SphincsSecurity.Concrete.forsRecover (m := m) P index leaves opening := by
  have h : FORS_TREES = SphincsSecurity.forsTrees := rfl
  have htrees : (fun kappa : Fin FORS_TREES => treeRecover (queryH (m := m)) (ofParam P) index.val
      kappa (ofLeaves leaves)[kappa] (ofOpenings opening)[kappa])
      = fun kappa => ofTops <$> SphincsSecurity.Concrete.treeRecover (m := m) P index
          (Fin.cast h kappa) (leaves (Fin.cast h kappa)) (opening (Fin.cast h kappa)) :=
    funext fun kappa => by
      simp only [ofLeaves, ofOpenings, Fin.getElem_fin, Vector.getElem_ofFn]
      exact treeRecover_queryH P index (Fin.cast h kappa) _ _
  rw [forsRecover, htrees, ofFnInOrder_eq_sequenceFin_cast h (fun κ =>
    SphincsSecurity.Concrete.treeRecover (m := m) P index κ (leaves κ) (opening κ)) ofTops]
  rfl

end Query

/-! ## Key and openings under fixed answers -/

section Answers

open OracleComp SphincsSecurity.Completeness

variable (f : QueryImpl HashSig.HashSpec Id)

/-- A FORS node hash reads only the low 10 bits of the node index. -/
theorem forsNodeHash_mod {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
    (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (level j : Nat) (left right : Digest) :
    forsNodeHash H pp idx kappa level j left right
      = forsNodeHash H pp idx kappa level (j % 2 ^ FORS_HEIGHT) left right := by
  simp only [forsNodeHash, forsIndex, Nat.mod_mod]

/-- Under fixed answers, a FORS node up to level 10 is the model's. -/
theorem forsNode_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) :
    ∀ (level j : Nat), level ≤ FORS_HEIGHT →
      evalWithAnswerFn f (forsNode (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
          (seedPrf queryH (ofSeed S)) index.val (treeOf κ) level j)
        = ofDigest (forsNodeValue f P index κ S level j)
  | 0, j, _ => by
    rw [forsNode, Merkle.node, forsLeaves_queryH, evalWithAnswerFn_map]
    rfl
  | level + 1, j, hlevel => by
    have hl := forsNode_answers S P index κ level (2 * j) (by omega)
    have hr := forsNode_answers S P index κ level (2 * j + 1) (by omega)
    have hlt : level < SphincsSecurity.forsHeight := by
      change _ < 10; simp only [FORS_HEIGHT] at hlevel; omega
    simp only [forsNode] at hl hr ⊢
    rw [Merkle.node, evalWithAnswerFn_bind, hl, evalWithAnswerFn_bind, hr, forsNodeHash_mod,
      forsNodeValue_succ f P index κ S level j hlt]
    have hnode := forsNodeHash_queryH (m := OracleComp HashSig.HashSpec) P index κ ⟨level, hlt⟩
      ⟨j % 2 ^ 10, Nat.mod_lt _ (by decide)⟩ (forsNodeValue f P index κ S level (2 * j))
      (forsNodeValue f P index κ S level (2 * j + 1))
    erw [hnode, evalWithAnswerFn_map, eval_tweakableHash]
    rfl

/-- Under fixed answers, a FORS key is the model's. -/
theorem forsKey_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) :
    evalWithAnswerFn f (forsKey (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) index.val)
      = ofForsKey (evalWithAnswerFn f
          (SphincsSecurity.Seeded.forsKey P index S : OracleComp HashSig.HashSpec _)) := by
  rw [forsKey_eq, forsKey,
    HashSig.ofFnInOrder_map_monad (m := OracleComp HashSig.HashSpec) (n := Id)
    (fun {β} (x : OracleComp HashSig.HashSpec β) => (evalWithAnswerFn f x : Id β))
    (fun b => evalWithAnswerFn_pure f b) (fun x g => evalWithAnswerFn_bind f x g)]
  refine (HashSig.ofFnInOrder_run _ _).trans (Vector.ext fun i hi => ?_)
  simp only [Vector.getElem_ofFn, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Id.run]
  have hk : (⟨i, hi⟩ : Fin FORS_TREES) = treeOf ⟨i, hi⟩ := rfl
  rw [hk, forsNode_answers f S P index _ _ _ (by decide),
    forsNode_answers f S P index _ _ _ (by decide)]
  simp only [ofForsKey, Vector.getElem_ofFn, ofTops, topsValue]
  rfl
/-- Under fixed answers, the siblings above a FORS leaf are the model's nodes, level by level. -/
theorem forsSiblings_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) (e : Nat) :
    ∀ (n level : Nat), level + n ≤ FORS_HEIGHT →
      evalWithAnswerFn f (Merkle.siblings
          (forsNodeHash (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P) index.val
            (treeOf κ))
          (forsLeaves queryH (ofParam P) (seedPrf queryH (ofSeed S)) index.val (treeOf κ))
          level (e / 2 ^ level) n)
        = Vector.ofFn fun i : Fin n =>
            ofDigest (forsNodeValue f P index κ S (level + i.val)
              (Nat.xor (e / 2 ^ (level + i.val)) 1))
  | 0, level, _ => Vector.ext fun _ hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, level, hn => by
    have hdiv : e / 2 ^ level / 2 = e / 2 ^ (level + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    have hnode := forsNode_answers f S P index κ level ((e / 2 ^ level) ^^^ 1) (by omega)
    simp only [forsNode] at hnode
    rw [Merkle.siblings, evalWithAnswerFn_bind, hnode, evalWithAnswerFn_bind, hdiv,
      forsSiblings_answers S P index κ e n (level + 1) (by omega), evalWithAnswerFn_pure]
    apply Vector.ext
    intro i hi
    cases i with
    | zero => simp
    | succ i => simp [Nat.add_right_comm, Nat.add_assoc]

/-- Under fixed answers, the opening of a FORS tree is the model's. -/
theorem treeOpen_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) (leaf : SphincsSecurity.FLeaf) :
    evalWithAnswerFn f (treeOpen (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) index.val (treeOf κ) leaf)
      = ofOpening (evalWithAnswerFn f
          (SphincsSecurity.Seeded.treeOpen P index κ leaf S : OracleComp HashSig.HashSpec _)) := by
  have h := forsSiblings_answers f S P index κ (Fin.val (n := 2 ^ FORS_HEIGHT) leaf) FORS_HEIGHT 0
    (by simp)
  simp only [pow_zero, Nat.div_one, Nat.zero_add] at h
  rw [eval_treeOpen]
  simp only [EthLib.Cryptography.Sphincs.treeOpen, evalWithAnswerFn_bind, forsSecret_queryH,
    evalWithAnswerFn_map, Merkle.path]
  rw [h, evalWithAnswerFn_pure]
  rfl

/-- Under fixed answers, the FORS openings are the model's. -/
theorem forsSign_answers (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (leaves : SphincsSecurity.FTree → SphincsSecurity.FLeaf) :
    evalWithAnswerFn f (forsSign (queryH (m := OracleComp HashSig.HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) index.val (ofLeaves leaves))
      = ofOpenings (evalWithAnswerFn f
          (SphincsSecurity.Seeded.forsOpen P index leaves S : OracleComp HashSig.HashSpec _)) := by
  rw [forsSign, HashSig.ofFnInOrder_map_monad (m := OracleComp HashSig.HashSpec) (n := Id)
    (fun {β} (x : OracleComp HashSig.HashSpec β) => (evalWithAnswerFn f x : Id β))
    (fun b => evalWithAnswerFn_pure f b) (fun x g => evalWithAnswerFn_bind f x g)]
  refine (HashSig.ofFnInOrder_run _ _).trans (Vector.ext fun i hi => ?_)
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, Id.run, ofLeaves, ofOpenings,
    SphincsSecurity.Seeded.forsOpen, eval_sequenceFin]
  exact treeOpen_answers f S P index ⟨i, hi⟩ (leaves ⟨i, hi⟩)

end Answers

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
