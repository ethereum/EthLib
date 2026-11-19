module

public import EthLib.Cryptography.Aggregation.Interface

/-!
# Correctness of signature aggregation

An honest aggregate is built along a tree.

Each node holds raw signatures, each with its claim, and child trees.

A node aggregates its children first, then its raw signatures with the children's aggregates.

Correctness says that such an aggregate verifies for the claims the tree covers.

It assumes that every raw signature of the tree is valid for its claim.

Validity is a parameter, because the interface does not fix the underlying signature scheme.

This file states correctness; the instance for a concrete scheme proves it.
-/

@[expose] public section

namespace EthLib.Cryptography.Aggregation

/-- A tree that builds an aggregate honestly: a node of raw signatures over child trees. -/
inductive HonestTree (S : Scheme) : Type where
  | node (raw : List (S.Claim × S.Signature)) (children : List (HonestTree S))

namespace HonestTree

variable {S : Scheme}

/-- The claims a tree covers: its raw claims, then each child's, in order.

A claim that appears twice is kept at its first place only. -/
def claims [DecidableEq S.PublicKey] [DecidableEq S.Message] : HonestTree S → List S.Claim
  | node raw children =>
      (raw.map Prod.fst ++ (children.attach.map fun ⟨c, _⟩ => c.claims).flatten).eraseDups
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem ‹_ ∈ children›
  simp only [node.sizeOf_spec]
  omega

/-- Every raw signature of a tree with its claim: the node's own first, then each child's. -/
def rawSignatures : HonestTree S → List (S.Claim × S.Signature)
  | node raw children => raw ++ (children.attach.map fun ⟨c, _⟩ => c.rawSignatures).flatten
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem ‹_ ∈ children›
  simp only [node.sizeOf_spec]
  omega

/-- The aggregate of a tree, built from the leaves up.

Each child is built first and paired with the claims it covers.

The node then aggregates its raw signatures with those pairs.

The build fails if any aggregation on the way fails. -/
def build [DecidableEq S.PublicKey] [DecidableEq S.Message] :
    HonestTree S → Option S.Aggregate
  | node raw children => do
      let inner ← children.attach.mapM fun ⟨c, _⟩ => do
        let α ← c.build
        pure (c.claims, α)
      S.aggregate S.setup raw inner
termination_by t => sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem ‹_ ∈ children›
  simp only [node.sizeOf_spec]
  omega

end HonestTree

/-- Correctness of an aggregation scheme.

Take an honest tree whose raw signatures are all valid for their claims.

If the tree builds an aggregate, that aggregate verifies for the claims the tree covers. -/
def Correct (S : Scheme) [DecidableEq S.PublicKey] [DecidableEq S.Message]
    (signatureValid : S.Params → S.Claim → S.Signature → Prop) : Prop :=
  ∀ (t : HonestTree S) (α : S.Aggregate),
    (∀ c σ, (c, σ) ∈ t.rawSignatures → signatureValid S.setup c σ) →
    t.build = some α → S.verify S.setup t.claims α = true

end EthLib.Cryptography.Aggregation
