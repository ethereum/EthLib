module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.Accepted

/-!
# Classifying a recovered FORS key tree by tree

A recovered canonical FORS key can have a node match at a hashed level, a first-order hit.

Otherwise every tree has the canonical path, and a secret that is canonical or a leaf match.

The classification of one FORS tree gives this, with the canonical path kept in the leaf branch.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SphincsSecurity.Security.Fors

variable [Params]
open Concrete

section Refined

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (κ : FTree)
  (seed : MasterSeed)

/-- One tree whose two top nodes are canonical, with the path kept.

The path is canonical and the secret is canonical or a leaf match.

Otherwise a node query hits a canonical value. -/
theorem tree_refined (leaf : FLeaf) (secret : Digest) (path : Fin forsHeight → Digest)
    (htops : orderTops (leaf.val.testBit (forsHeight - 1))
        (topValue f parameter index κ leaf secret path)
      (topSibling path) = Completeness.topsValue f parameter index seed κ) :
    (path = canonicalPath f parameter index κ seed leaf ∧
      (secret = Completeness.forsSecretValue f parameter index κ seed leaf ∨
        LeafMatch f parameter index κ seed leaf secret)) ∨
    ∃ level, level < forsHeight - 1 ∧ NodeMatch f parameter index κ seed leaf secret path
        level := by
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
  · refine Or.inl ⟨?_, ?_⟩
    · funext level
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
    · by_cases hsecret : secret = Completeness.forsSecretValue f parameter index κ seed leaf
      · exact Or.inl hsecret
      · exact Or.inr ⟨hsecret, hleaf⟩
  · exact Or.inr hmatch

end Refined

section Key

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (seed : MasterSeed)

/-- The exception of a recovered key that is a first-order hit: a node match at a hashed level.

A leaf match stays in the refined classification, since it touches a hidden secret. -/
def NodeException (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) : Prop :=
  ∃ κ level, level < forsHeight - 1 ∧
    NodeMatch f parameter index κ seed (leaves κ) (opening κ).secret (opening κ).path level

/-- A recovered canonical FORS key has a node exception.

Otherwise every tree has the canonical path, and a secret that is canonical or a leaf match. -/
theorem recovered_classification (leaves : FTree → FLeaf) (opening : FTree → TreeOpening)
    (hrecover : evalWithAnswerFn f (forsRecover parameter index leaves opening : OracleComp HashSpec
        ForsKey) =
      evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec ForsKey)) :
    NodeException f parameter index seed leaves opening ∨
    ∀ κ, (opening κ).path = canonicalPath f parameter index κ seed (leaves κ) ∧
      ((opening κ).secret = Completeness.forsSecretValue f parameter index κ seed (leaves κ) ∨
        LeafMatch f parameter index κ seed (leaves κ) (opening κ).secret) := by
  classical
  have htops : tops f parameter index leaves opening = fun κ =>
      Completeness.topsValue f parameter index seed κ := by
    rw [← eval_forsRecover, hrecover, Completeness.forsKey_eq]
  by_cases hN : NodeException f parameter index seed leaves opening
  · exact Or.inl hN
  refine Or.inr fun κ => ?_
  rcases tree_refined f parameter index κ seed (leaves κ) (opening κ).secret (opening κ).path
    (congrFun htops κ) with h | ⟨level, hlevel, hnode⟩
  · exact h
  · exact absurd ⟨κ, level, hlevel, hnode⟩ hN

end Key

end SphincsSecurity.Security.Fors


namespace SphincsSecurity.Security.SignatureWitness

variable [Params]
open Concrete

attribute [local irreducible] messageDigest forsRecover otsLeaf treeFold
  Seeded.forsKey Seeded.treeRoot Seeded.treePath chainWalk encode


/-- A recovered opening whose FORS part is the canonical opening is a canonical opening. -/
theorem RecoveredOpening.canonical {f : QueryImpl HashSpec Id} {pk : PublicKey} {seed : MasterSeed}
    {message : Message} {signature : Signature} {counter : Layer → Counter}
    (h : RecoveredOpening f pk seed message signature counter)
    (hopening : Fors.Opening f pk.parameter (index f pk message signature) seed
      (digestLeaves (verificationDigest f pk message signature)) signature.fors) :
    CanonicalOpening f pk seed message signature counter
      (chosenWord f pk.parameter seed (index f pk message signature)) :=
  ⟨h.1, h.2.1, hopening⟩

/-- The FORS part of a recovered opening has a node exception.

Otherwise every tree has the canonical path, and a secret that is canonical or a leaf match. -/
theorem RecoveredOpening.fors_classification {f : QueryImpl HashSpec Id} {pk : PublicKey}
    {seed : MasterSeed} {message : Message} {signature : Signature} {counter : Layer → Counter}
    (h : RecoveredOpening f pk seed message signature counter) :
    Fors.NodeException f pk.parameter (index f pk message signature) seed
        (digestLeaves (verificationDigest f pk message signature)) signature.fors ∨
    ∀ κ, (signature.fors κ).path = Fors.canonicalPath f pk.parameter
        (index f pk message signature) κ seed
        (digestLeaves (verificationDigest f pk message signature) κ) ∧
      ((signature.fors κ).secret = Completeness.forsSecretValue f pk.parameter
          (index f pk message signature) κ seed
          (digestLeaves (verificationDigest f pk message signature) κ) ∨
        Fors.LeafMatch f pk.parameter (index f pk message signature) κ seed
          (digestLeaves (verificationDigest f pk message signature) κ) (signature.fors κ).secret) :=
  Fors.recovered_classification f pk.parameter (index f pk message signature) seed
    (digestLeaves (verificationDigest f pk message signature)) signature.fors h.2.2

end SphincsSecurity.Security.SignatureWitness
