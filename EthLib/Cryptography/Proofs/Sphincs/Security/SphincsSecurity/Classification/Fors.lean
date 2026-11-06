module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.Chain

/-!
# Extraction from a FORS opening

Take an opening that recovers the canonical FORS key.

Then every tree opens at its canonical secret and path, or a verifier query hits a canonical value.

The hit is at a leaf or at a node, from an input other than the canonical one.

No collision resistance or other assumption on the hash function is used.

A FORS tree has no hashed root, and the key is the two nodes at level `a - 1` of every tree.

The opening reaches one of them by a fold over `a - 1` levels, and its last path node is the other.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SphincsSecurity.Security

variable [Params]
open Concrete

namespace Fors

/--
The hash domain of a FORS node, from its height and position.

Outside the hashed heights it is a fixed domain that no algorithm uses.
-/
def forsDomain (index : Index) (κ : FTree) (height position : Nat) : HashDomain :=
  if hheight : 0 < height ∧ height ≤ forsHeight then
    .forsNode index κ ⟨height - 1, by omega⟩
      ⟨position % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  else .forsNode index κ topLevel 0

/-- A FORS path, extended by zero above its last level. -/
def extendPath (path : Fin forsHeight → Digest) (level : Nat) : Digest :=
  if hlevel : level < forsHeight then path ⟨level, hlevel⟩ else 0

theorem merkleFold_forsFold (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (path : Fin forsHeight → Digest) (levels : Nat) (hlevels : levels ≤ forsHeight)
    (value : Digest) :
    merkleFold parameter (forsDomain index κ) leaf.val (extendPath path) levels value =
      (forsFold parameter index κ leaf path levels value : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      have hl : levels < forsHeight := by omega
      rw [merkleFold, forsFold, ih (by omega)]
      apply bind_congr
      intro current
      rw [dite_eq_left hl]
      have hdom : forsDomain index κ (levels + 1) (leaf.val / 2 ^ (levels + 1)) =
          .forsNode index κ ⟨levels, hl⟩ ⟨leaf.val / 2 ^ (levels + 1),
            Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt⟩ := by
        rw [forsDomain, dite_eq_left ⟨by omega, by omega⟩]
        congr 1
        exact Fin.ext (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt))
      rw [hdom, extendPath, dite_eq_left hl]
      cases leaf.val.testBit levels <;> rfl

section Tree

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (κ : FTree)
  (seed : MasterSeed)

/-- The canonical path of a leaf. -/
def canonicalPath (leaf : FLeaf) (level : Fin forsHeight) : Digest :=
  Completeness.forsNodeValue f parameter index κ seed level.val
      (Nat.xor (leaf.val / 2 ^ level.val) 1)

/-- The leaf that a secret hashes to. -/
def leafValue (leaf : FLeaf) (secret : Digest) : Digest :=
  evalWithAnswerFn f (forsLeafHash parameter index κ leaf secret : OracleComp HashSpec Digest)

/-- The node at level `a - 1` that an opening reaches on the side of its leaf. -/
def topValue (leaf : FLeaf) (secret : Digest) (path : Fin forsHeight → Digest) : Digest :=
  evalWithAnswerFn f (forsFold parameter index κ leaf path (forsHeight - 1)
    (leafValue f parameter index κ leaf secret) : OracleComp HashSpec Digest)

/-- The last path node, which is the other node at level `a - 1`. -/
def topSibling (path : Fin forsHeight → Digest) : Digest := path topLevel

theorem leafValue_canonical (leaf : FLeaf) :
    leafValue f parameter index κ leaf
        (Completeness.forsSecretValue f parameter index κ seed leaf) =
      Completeness.forsNodeValue f parameter index κ seed 0 leaf.val := by
  rw [Completeness.forsNodeValue_zero, leafValue, forsLeafHash, Completeness.eval_tweakableHash]
  rfl

theorem canonical_top (leaf : FLeaf) :
    topValue f parameter index κ leaf (Completeness.forsSecretValue f parameter index κ seed leaf)
      (canonicalPath f parameter index κ seed leaf) =
        Completeness.forsNodeValue f parameter index κ seed (forsHeight - 1)
            (leaf.val / 2 ^ (forsHeight - 1)) := by
  rw [topValue, leafValue_canonical]
  exact Completeness.eval_forsFold_path f parameter index κ seed leaf _ _ (Nat.sub_le _ _)
    (fun _ _ _ => rfl)

/-- A secret other than the canonical one whose leaf hash is the canonical leaf. -/
def LeafMatch (leaf : FLeaf) (secret : Digest) : Prop :=
  secret ≠ Completeness.forsSecretValue f parameter index κ seed leaf ∧
  leafValue f parameter index κ leaf secret =
    leafValue f parameter index κ leaf (Completeness.forsSecretValue f parameter index κ seed leaf)

/-- A node query of the opening hits the canonical value at the same tree position. -/
def NodeMatch (leaf : FLeaf) (secret : Digest) (path : Fin forsHeight → Digest)
    (level : Nat) : Prop :=
  MerkleMatch f parameter (forsDomain index κ) leaf.val leaf.val (extendPath path)
    (extendPath (canonicalPath f parameter index κ seed leaf))
    (leafValue f parameter index κ leaf secret)
    (leafValue f parameter index κ leaf
      (Completeness.forsSecretValue f parameter index κ seed leaf)) level

/--
Take a tree whose two top nodes, in node order, are the canonical ones.

Then its opening is canonical, or it has a leaf match, or a node match below level `a - 1`.

The last path node is not hashed, since it is one of the two top nodes.
-/
theorem tree_classification (leaf : FLeaf) (secret : Digest) (path : Fin forsHeight → Digest)
    (htops : orderTops (leaf.val.testBit (forsHeight - 1))
        (topValue f parameter index κ leaf secret path)
      (topSibling path) = Completeness.topsValue f parameter index seed κ) :
    (secret = Completeness.forsSecretValue f parameter index κ seed leaf ∧
      path = canonicalPath f parameter index κ seed leaf) ∨
    LeafMatch f parameter index κ seed leaf secret ∨
    ∃ level, level < forsHeight - 1 ∧
      NodeMatch f parameter index κ seed leaf secret path level := by
  have ha := Params.forsHeight_ge
  have hhalf : leaf.val / 2 ^ (forsHeight - 1) < 2 := by
    have hl := leaf.isLt
    have : 2 ^ forsHeight = 2 * 2 ^ (forsHeight - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    exact Nat.div_lt_of_lt_mul (by omega)
  obtain ⟨htop, hsibling⟩ := (Completeness.orderTops_eq_iff
    (Completeness.forsNodeValue f parameter index κ seed (forsHeight - 1)) leaf.val (forsHeight - 1)
      hhalf _ _).mp htops
  have hfold : merkleValue f parameter (forsDomain index κ) leaf.val (extendPath path)
      (leafValue f parameter index κ leaf secret) (forsHeight - 1) =
    merkleValue f parameter (forsDomain index κ) leaf.val
      (extendPath (canonicalPath f parameter index κ seed leaf))
      (leafValue f parameter index κ leaf
        (Completeness.forsSecretValue f parameter index κ seed leaf))
      (forsHeight - 1) := by
    simp only [merkleValue, merkleFold_forsFold _ _ _ _ _ _ (Nat.sub_le _ _)]
    exact htop.trans (canonical_top f parameter index κ seed leaf).symm
  rcases merkleFold_same_index f parameter _ leaf.val _ _ _ _ (forsHeight - 1) hfold with
    ⟨hleaf, hpath⟩ | hmatch
  · by_cases hsecret : secret = Completeness.forsSecretValue f parameter index κ seed leaf
    · refine Or.inl ⟨hsecret, ?_⟩
      funext level
      by_cases hlevel : level.val < forsHeight - 1
      · have hp := hpath level.val hlevel
        simpa only [extendPath, dite_eq_left level.isLt] using hp
      · have hlast : level = topLevel := by
          apply Fin.ext
          have := level.isLt
          simp only [topLevel]
          omega
        rw [hlast]
        exact hsibling
    · exact Or.inr (Or.inl ⟨hsecret, hleaf⟩)
  · exact Or.inr (Or.inr hmatch)

end Tree

section Key

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (seed : MasterSeed)

/-- The `2k` top nodes that an opening reaches, in node order. -/
def tops (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) : ForsKey :=
  fun κ => orderTops ((leaves κ).val.testBit (forsHeight - 1))
    (topValue f parameter index κ (leaves κ) (opening κ).secret (opening κ).path)
    (topSibling (opening κ).path)

/-- Every selected secret and path is canonical. -/
def Opening (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) : Prop :=
  ∀ κ, (opening κ).secret = Completeness.forsSecretValue f parameter index κ seed (leaves κ) ∧
    (opening κ).path = canonicalPath f parameter index κ seed (leaves κ)

/-- A leaf match, or a node match below level `a - 1`, in some tree. -/
def Exception (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) : Prop :=
  (∃ κ, LeafMatch f parameter index κ seed (leaves κ) (opening κ).secret) ∨
  (∃ κ level, level < forsHeight - 1 ∧
    NodeMatch f parameter index κ seed (leaves κ) (opening κ).secret (opening κ).path level)

theorem eval_forsRecover (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) :
    evalWithAnswerFn f (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey) =
      tops f parameter index leaves opening := by
  simp only [forsRecover, treeRecover, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    Completeness.eval_sequenceFin]
  rfl

/-- An opening that recovers the canonical FORS key is canonical, or it has a leaf or node match. -/
theorem recover_classification (leaves : FTree → FLeaf) (opening : FTree → TreeOpening)
    (hrecover : evalWithAnswerFn f
        (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey) =
      evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec ForsKey)) :
    Opening f parameter index seed leaves opening ∨
      Exception f parameter index seed leaves opening := by
  classical
  have htops : tops f parameter index leaves opening =
      fun κ => Completeness.topsValue f parameter index seed κ := by
    rw [← eval_forsRecover, hrecover, Completeness.forsKey_eq]
  by_cases hopening : Opening f parameter index seed leaves opening
  · exact Or.inl hopening
  · unfold Opening at hopening
    push Not at hopening
    obtain ⟨κ, hκ⟩ := hopening
    rcases tree_classification f parameter index κ seed (leaves κ) (opening κ).secret
        (opening κ).path (congrFun htops κ) with hopen | hleaf | ⟨level, hlevel, hnode⟩
    · exact False.elim (hκ hopen.1 hopen.2)
    · exact Or.inr (Or.inl ⟨κ, hleaf⟩)
    · exact Or.inr (Or.inr ⟨κ, level, hlevel, hnode⟩)

/-- Recovery hashes every selected secret. -/
theorem leafInput_mem (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) (κ : FTree) :
    tweakableHashInput parameter (.forsLeaf index κ (leaves κ)) (bytesLE 16 (opening κ).secret) ∈
      queriedInputs f
        (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey) := by
  rw [forsRecover]
  apply queriedInputs_sequenceFin_component f _ κ
  rw [treeRecover]
  apply queriedInputs_mono_bind_left
  simp only [forsLeafHash, queriedInputs_tweakableHash, List.mem_singleton]

theorem nodeInput_mem (leaves : FTree → FLeaf) (opening : FTree → TreeOpening)
    (κ : FTree) (level : Nat) (hlevel : level < forsHeight - 1) :
    merkleInput f parameter (forsDomain index κ) (leaves κ).val (extendPath (opening κ).path)
      (leafValue f parameter index κ (leaves κ) (opening κ).secret) level ∈
        queriedInputs f
          (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey) := by
  rw [forsRecover]
  apply queriedInputs_sequenceFin_component f _ κ
  rw [treeRecover]
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_left
  rw [← merkleFold_forsFold _ _ _ _ _ _ (Nat.sub_le _ _)]
  exact merkleInput_mem f parameter _ _ _ _ _ _ hlevel

/-- An exception gives a queried input and another canonical input with equal truncated hashes. -/
theorem Exception.queried_output_match (leaves : FTree → FLeaf) (opening : FTree → TreeOpening)
    (hexception : Exception f parameter index seed leaves opening) :
    ∃ input canonicalInput : HashInput,
      input ∈ queriedInputs f
        (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey) ∧
      input ≠ canonicalInput ∧ truncateHash (f input) = truncateHash (f canonicalInput) := by
  rcases hexception with ⟨κ, hne, heq⟩ | ⟨κ, level, hlevel, hnode⟩
  · refine ⟨tweakableHashInput parameter (.forsLeaf index κ (leaves κ))
      (bytesLE 16 (opening κ).secret),
      tweakableHashInput parameter (.forsLeaf index κ (leaves κ))
        (bytesLE 16 (Completeness.forsSecretValue f parameter index κ seed (leaves κ))),
      leafInput_mem f parameter index leaves opening κ, ?_, ?_⟩
    · intro hinput
      exact hne (bytesLE_injective (List.append_cancel_left hinput))
    · simpa only [leafValue, forsLeafHash, Completeness.eval_tweakableHash] using heq
  · refine ⟨_, _, nodeInput_mem f parameter index leaves opening κ level hlevel, hnode.2.1, ?_⟩
    exact hnode.2.2.trans (merkleValue_succ f parameter _ _ _ _ level)

end Key

end Fors
end SphincsSecurity.Security
