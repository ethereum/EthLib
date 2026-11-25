module

public import EthLib.Cryptography.Aggregation.Interface

/-!
# Correctness of signature aggregation

The source is Definition 8 of [Hofheinz et al.](https://eprint.iacr.org/2026/723).
-/

@[expose] public section

namespace EthLib.Cryptography.Aggregation

/-- Signing correctness: an honest signature verifies for its claim, in every context. -/
def SigningCorrect (S : Scheme) : Prop :=
  ∀ (input : S.KeyGenInput) (ctx : S.SignContext) (m : S.Message),
    -- Generate the key pair from any input.
    let (pk, sk) := S.gen S.setup input
    -- Sign the message in the context, then check the signature against its claim.
    S.verifySignature S.setup (pk, ctx, m) (S.sign S.setup sk ctx m) = true

/-- Aggregation correctness: valid inputs give an aggregate that verifies for their union.

Correctness of nested aggregates follows by induction on the nesting. -/
def AggregationCorrect (S : Scheme) : Prop :=
  ∀ (raw : List (S.Claim × S.Signature)) (inner : List (List S.Claim × S.Aggregate))
    (claims : List S.Claim),
    -- Every signature verifies for its claim.
    (∀ c σ, (c, σ) ∈ raw → S.verifySignature S.setup c σ = true) →
    -- Every earlier aggregate verifies for its claims:
    -- - whoever built it does not matter;
    -- - so an aggregator may take aggregates from untrusted peers.
    (∀ cs β, (cs, β) ∈ inner → S.verify S.setup cs β = true) →
    -- The list to verify holds each claim once, for example:
    -- - signatures on claims 1 and 2, and an earlier aggregate over 2 and 3;
    -- - claim 2 is covered twice, yet the list is 1, 2, 3;
    -- - so verification cannot ask how often a claim was aggregated.
    claims.Nodup →
    -- The list holds exactly the claims of the inputs, in any order:
    -- - 1, 2, 3 and 3, 1, 2 must both verify;
    -- - so verification cannot depend on the order of the claims.
    (∀ c, c ∈ claims ↔ c ∈ raw.map Prod.fst ∨ ∃ cs ∈ inner.map Prod.fst, c ∈ cs) →
    -- The union fits in one aggregate, as in Remark 1 of the paper.
    claims.length ≤ S.capacity →
    -- Aggregation always returns an aggregate, and that aggregate verifies for the union.
    S.verify S.setup claims (S.aggregate S.setup raw inner) = true

/-- Correctness of an aggregation scheme: signing and aggregation are both correct. -/
def Correct (S : Scheme) : Prop :=
  SigningCorrect S ∧ AggregationCorrect S

end EthLib.Cryptography.Aggregation
