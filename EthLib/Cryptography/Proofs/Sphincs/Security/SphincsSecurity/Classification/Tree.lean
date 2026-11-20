module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Pruning
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Landing
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Bytes
import EthLib.Base.Proofs.List

/-!
# Extraction from a Merkle path

Two Merkle folds that reach the same root are compared at the first level where they differ.

They agree, or one crosses into the sibling of the other, or a queried input hits a node value.

The crossing case matters above a kept subtree, since the sibling can be a surrogate value.
-/

@[expose] public section

-- The byte-length lemmas must see the digest width as `8 * 16` to match.
set_option backward.isDefEq.respectTransparency false

open OracleComp OracleSpec

namespace SphincsSecurity.Security

variable [Params]
open Concrete
open EthLib.Cryptography

/-- The inputs that a computation queries when a fixed function answers every query. -/
def queriedInputs {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) :
    List HashInput :=
  ((simulateQ f.withLogging oa).run).2.map Sigma.fst

omit [Params] in
@[simp] theorem queriedInputs_pure {α : Type} (f : QueryImpl HashSpec Id) (x : α) :
    queriedInputs f (pure x) = [] := rfl

omit [Params] in
@[simp] theorem queriedInputs_query_bind {α : Type} (f : QueryImpl HashSpec Id)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    queriedInputs f (liftM (HashSpec.query input) >>= next) =
      input :: queriedInputs f (next (f input)) := by
  simp [queriedInputs, QueryImpl.withLogging_apply, WriterT.run_bind, WriterT.run_tell]
  rfl

omit [Params] in
theorem queriedInputs_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    queriedInputs f (oa >>= next) =
      queriedInputs f oa ++ queriedInputs f (next (evalWithAnswerFn f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind input rest ih =>
      rw [bind_assoc, queriedInputs_query_bind, queriedInputs_query_bind, ih,
        evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, List.cons_append]

@[simp] theorem queriedInputs_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    queriedInputs f (tweakableHash parameter domain payload : OracleComp HashSpec Digest) =
      [tweakableHashInput parameter domain payload] := by
  change queriedInputs f (liftM (HashSpec.query (tweakableHashInput parameter domain payload)) >>=
    fun answer => pure (truncateHash answer)) = _
  rw [queriedInputs_query_bind, queriedInputs_pure]

omit [Params] in
theorem nodePayload_injective {left right left' right' : Digest}
    (h : nodePayload left right = nodePayload left' right') : left = left' ∧ right = right' := by
  obtain ⟨hl, hr⟩ := List.append_inj h (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hl, bytesLE_injective hr⟩

theorem rootsPayload_injective {roots roots' : ForsKey}
    (h : rootsPayload roots = rootsPayload roots') : roots = roots' :=
  List.ofFn_injective (EthLib.Base.flatMap_inj_of_length (by decide) (bytesLE_length 16)
    (fun _ _ hroot => bytesLE_injective hroot) h)

def orderedPayload (bit : Bool) (current sibling : Digest) : HashInput :=
  if bit then nodePayload sibling current else nodePayload current sibling

/-- The node that a climb reaches from a leaf, under the answers `f`. -/
def merkleValue (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest)
    (value : Digest) (levels : Nat) : Digest :=
  evalWithAnswerFn f (Merkle.climb (merkleHash parameter domain) ⟨0, index⟩ value
    (List.ofFn fun level : Fin levels => path level.val))

/-- The oracle input of the climb step from level `level`, taken by the generic Merkle step.

The step hashes the node held on that level and its sibling, in order, into their parent. -/
def merkleInput (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest)
    (value : Digest) (level : Nat) : HashInput :=
  let position : Merkle.Position := (⟨0, index⟩ : Merkle.Position).ancestor level
  let children :=
    Merkle.ordered position (merkleValue f parameter domain index path value level) (path level)
  tweakableHashInput parameter (domain position.parent.level position.parent.index)
    (nodePayload children.1 children.2)

/-- The climb step from level `level` hashes at the parent index, in the order of the child bit.

The proofs that compare the climbs of two leaves read these two parts. -/
theorem merkleInput_eq (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest)
    (value : Digest) (level : Nat) :
    merkleInput f parameter domain index path value level =
      tweakableHashInput parameter (domain (level + 1) (index / 2 ^ (level + 1)))
        (orderedPayload (index.testBit level)
          (merkleValue f parameter domain index path value level) (path level)) := by
  simp only [merkleInput, Merkle.Position.parent_ancestor_mk_zero, Merkle.ordered,
    Merkle.Position.isLeft_ancestor]
  cases index.testBit level <;> rfl

@[simp] theorem merkleValue_zero (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest) (value : Digest) :
    merkleValue f parameter domain index path value 0 = value := rfl

theorem merkleValue_succ (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest)
    (value : Digest) (level : Nat) :
    merkleValue f parameter domain index path value (level + 1) =
      truncateHash (f (merkleInput f parameter domain index path value level)) := by
  simp only [merkleValue, Merkle.climb_ofFn_succ_ordered, evalWithAnswerFn_bind, merkleHash,
    Completeness.eval_tweakableHash]
  rfl

theorem merkleInput_mem (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path : Nat → Digest) (value : Digest)
    (levels level : Nat) (hlevel : level < levels) :
    merkleInput f parameter domain index path value level ∈
      queriedInputs f (Merkle.climb (merkleHash parameter domain) ⟨0, index⟩ value
        (List.ofFn fun level : Fin levels => path level.val)) := by
  induction levels with
  | zero => omega
  | succ levels ih =>
      rw [Merkle.climb_ofFn_succ_ordered, queriedInputs_bind, List.mem_append]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlevel with hlt | rfl
      · exact Or.inl (ih hlt)
      · -- The last step queries the input of the last level.
        refine Or.inr ?_
        simp [merkleHash, merkleInput, merkleValue]

/-- A different input at the same node position hits the reference value at that position. -/
def MerkleMatch (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index reference : Nat) (path referencePath : Nat → Digest)
    (value referenceValue : Digest) (level : Nat) : Prop :=
  index / 2 ^ (level + 1) = reference / 2 ^ (level + 1) ∧
  merkleInput f parameter domain index path value level ≠
    merkleInput f parameter domain reference referencePath referenceValue level ∧
  truncateHash (f (merkleInput f parameter domain index path value level)) =
    merkleValue f parameter domain reference referencePath referenceValue (level + 1)

/-- At a level where two paths separate, the candidate reaches the reference sibling. -/
def MerkleCrossing (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index reference : Nat) (path referencePath : Nat → Digest)
    (value : Digest) (level : Nat) : Prop :=
  index / 2 ^ (level + 1) = reference / 2 ^ (level + 1) ∧
  index.testBit level ≠ reference.testBit level ∧
  merkleValue f parameter domain index path value level = referencePath level

/--
Two folds that reach the same value at the same position agree, cross, or have a node match.

No assumption on the hash function is used.
-/
theorem merkleValue_classification (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index reference : Nat) (path referencePath : Nat → Digest)
    (value referenceValue : Digest) :
    ∀ levels,
      index / 2 ^ levels = reference / 2 ^ levels →
      merkleValue f parameter domain index path value levels =
        merkleValue f parameter domain reference referencePath referenceValue levels →
      (index = reference ∧ value = referenceValue ∧
        ∀ level, level < levels → path level = referencePath level) ∨
      (∃ level, level < levels ∧
        MerkleCrossing f parameter domain index reference path referencePath value level) ∨
      (∃ level, level < levels ∧
        MerkleMatch f parameter domain index reference path referencePath value
            referenceValue level) := by
  intro levels
  induction levels with
  | zero =>
      intro hparent hfold
      exact Or.inl ⟨by simpa using hparent, hfold, fun _ h => by omega⟩
  | succ levels ih =>
      intro hparent hfold
      -- The two climbs step into the same parent from level `levels`.
      have hparents : ((⟨0, index⟩ : Merkle.Position).ancestor levels).parent =
          ((⟨0, reference⟩ : Merkle.Position).ancestor levels).parent := by
        rw [Merkle.Position.parent_ancestor_mk_zero, Merkle.Position.parent_ancestor_mk_zero,
          hparent]
      by_cases hinput : merkleInput f parameter domain index path value levels =
          merkleInput f parameter domain reference referencePath referenceValue levels
      · have hchildren : Merkle.ordered ((⟨0, index⟩ : Merkle.Position).ancestor levels)
              (merkleValue f parameter domain index path value levels) (path levels) =
            Merkle.ordered ((⟨0, reference⟩ : Merkle.Position).ancestor levels)
              (merkleValue f parameter domain reference referencePath referenceValue levels)
              (referencePath levels) := by
          simp only [merkleInput] at hinput
          rw [hparents] at hinput
          obtain ⟨hleft, hright⟩ := nodePayload_injective (List.append_cancel_left hinput)
          exact Prod.ext hleft hright
        have hside := Merkle.Position.isLeft_ancestor (⟨0, index⟩ : Merkle.Position) levels
        have hside' := Merkle.Position.isLeft_ancestor (⟨0, reference⟩ : Merkle.Position) levels
        by_cases hbit : index.testBit levels = reference.testBit levels
        · -- On the same side of the same parent, both climbs hold the same node.
          have hposition := Merkle.Position.eq_of_parent_eq_of_isLeft_eq hparents
            (by rw [hside, hside']; exact congrArg (!·) hbit)
          rw [hposition, Merkle.ordered_inj] at hchildren
          obtain ⟨hvalue, hpath⟩ := hchildren
          have hquotient : index / 2 ^ levels = reference / 2 ^ levels := by
            simpa [Merkle.Position.ancestor_mk_zero] using
              congrArg Merkle.Position.index hposition
          rcases ih hquotient hvalue with
            ⟨hindex, hstart, hpaths⟩ | ⟨level, hlevel, hcross⟩ | ⟨level, hlevel, hmatch⟩
          · refine Or.inl ⟨hindex, hstart, fun level hlevel => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlevel with hlt | rfl
            · exact hpaths level hlt
            · exact hpath
          · exact Or.inr (Or.inl ⟨level, Nat.lt_succ_of_lt hlevel, hcross⟩)
          · exact Or.inr (Or.inr ⟨level, Nat.lt_succ_of_lt hlevel, hmatch⟩)
        · -- On opposite sides, each climb holds the sibling of the other.
          refine Or.inr (Or.inl ⟨levels, Nat.lt_succ_self _, hparent, hbit,
            (Merkle.ordered_cross ?_ hchildren).1⟩)
          rw [hside, hside']
          simpa using hbit
      · refine Or.inr (Or.inr ⟨levels, Nat.lt_succ_self _, hparent, hinput, ?_⟩)
        rwa [← merkleValue_succ]

theorem merkleValue_same_index (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (domain : Nat → Nat → HashDomain) (index : Nat) (path referencePath : Nat → Digest)
    (value referenceValue : Digest) (levels : Nat)
    (hfold : merkleValue f parameter domain index path value levels =
      merkleValue f parameter domain index referencePath referenceValue levels) :
    (value = referenceValue ∧ ∀ level, level < levels → path level = referencePath level) ∨
    ∃ level, level < levels ∧
      MerkleMatch f parameter domain index index path referencePath value referenceValue level := by
  rcases merkleValue_classification f parameter domain index index path referencePath value
      referenceValue levels rfl hfold with hgood | ⟨level, _, _, hbit, _⟩ | hmatch
  · exact Or.inl hgood.2
  · exact False.elim (hbit rfl)
  · exact Or.inr hmatch

omit [Params] in
theorem quotient_eq_above {index reference lower upper : Nat} (hlevels : lower ≤ upper)
    (hquotient : index / 2 ^ lower = reference / 2 ^ lower) :
    index / 2 ^ upper = reference / 2 ^ upper := by
  have hsplit : upper = lower + (upper - lower) := (Nat.add_sub_of_le hlevels).symm
  rw [hsplit, Nat.pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hquotient]

/-- The honest authentication path of a leaf, extended by zero above the layer height. -/
def canonicalTreePath (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex)
    (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then
    evalWithAnswerFn f (Seeded.treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) ⟨level, hlevel⟩
  else 0

theorem canonicalTreePath_surrogate (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex) (level : Nat)
    (hlow : keptHeight lay ≤ level) (hhigh : level < layerHeight lay) :
    canonicalTreePath f parameter lay tree seed leaf level =
      evalWithAnswerFn f (Seeded.surrogate parameter seed level : OracleComp HashSpec Digest) := by
  rw [canonicalTreePath, dite_eq_left hhigh, Completeness.eval_treePath,
    ite_eq_right (Nat.not_lt.mpr hlow)]

theorem canonicalTreePath_root (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex)
    (hkept : Kept parameter lay leaf) :
    merkleValue f parameter (fun level index => .node lay tree level index) leaf.val
      (canonicalTreePath f parameter lay tree seed leaf)
      (Completeness.node f parameter lay tree seed 0 leaf.val) (layerHeight lay) =
        evalWithAnswerFn f
          (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest) := by
  rw [merkleValue]
  apply Completeness.eval_treeFold_pruned_path f parameter lay tree seed leaf hkept
  intro level hlevel
  exact dite_eq_left hlevel

/--
A queried node input gives the surrogate value of a level at or above the kept height.

Unlike a node match, the target has no honest preimage, since the key derives it from the seed.
-/
def SurrogatePreimage (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex)
    (path : Nat → Digest) (value : Digest) (level : Nat) : Prop :=
  keptHeight lay ≤ level ∧ 0 < level ∧
  truncateHash (f (merkleInput f parameter (fun height index => .node lay tree height index)
    leaf.val path value (level - 1))) =
      evalWithAnswerFn f (Seeded.surrogate parameter seed level : OracleComp HashSpec Digest)

/--
For a kept leaf, a fold that reaches the honest root is canonical or has a node match.

A node match is a different queried input that gives a canonical node value.
-/
theorem inside_subtree_treeFold_witness (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed)
    (leaf : LeafIndex) (path : Nat → Digest) (value : Digest) (hkept : Kept parameter lay leaf)
    (hfold : evalWithAnswerFn f (treeFold parameter lay tree leaf path (layerHeight lay) value :
      OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest)) :
    (value = Completeness.node f parameter lay tree seed 0 leaf.val ∧
      ∀ level, level < layerHeight lay →
        path level = canonicalTreePath f parameter lay tree seed leaf level) ∨
    ∃ level, level < layerHeight lay ∧
      MerkleMatch f parameter (fun height index => .node lay tree height index)
        leaf.val leaf.val path (canonicalTreePath f parameter lay tree seed leaf)
        value (Completeness.node f parameter lay tree seed 0 leaf.val) level := by
  apply merkleValue_same_index
  rw [canonicalTreePath_root f parameter lay tree seed leaf hkept,
    merkleValue]
  exact hfold

end SphincsSecurity.Security
