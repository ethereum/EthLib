module

public import EthLib.Cryptography.Aggregation.Interface

/-!
# Correctness of signature aggregation

The source is Definition 8 of [Hofheinz, Reichle and Wagner](https://eprint.iacr.org/2026/723).
-/

@[expose] public section

namespace EthLib.Cryptography.Aggregation

/-- Correctness of one aggregation step: valid inputs give a result that verifies for their union.

Validity of a raw signature is a parameter, because the interface does not fix the signature scheme.

Correctness of nested aggregates follows by induction on the nesting. -/
def Correct (S : Scheme) (signatureValid : S.Params → S.Claim → S.Signature → Prop) : Prop :=
  ∀ (raw : List (S.Claim × S.Signature)) (inner : List (List S.Claim × S.Aggregate))
    (α : S.Aggregate) (claims : List S.Claim),
    -- Every raw signature is valid for its claim under the underlying signature scheme.
    (∀ c σ, (c, σ) ∈ raw → signatureValid S.setup c σ) →
    -- Every earlier aggregate verifies for its claims:
    -- - whoever built it does not matter;
    -- - so an aggregator may take aggregates from untrusted peers.
    (∀ cs β, (cs, β) ∈ inner → S.verify S.setup cs β = true) →
    -- The step succeeds:
    -- - a step may fail, for instance beyond the scheme's capacity;
    -- - a failed step has nothing to verify.
    S.aggregate S.setup raw inner = some α →
    -- The list to verify holds each claim once, for example:
    -- - raw claims 1 and 2, and an earlier aggregate over 2 and 3;
    -- - claim 2 is covered twice, yet the list is 1, 2, 3;
    -- - so verification cannot ask how often a claim was aggregated.
    claims.Nodup →
    -- The list holds exactly the claims of the inputs, in any order:
    -- - 1, 2, 3 and 3, 1, 2 must both verify;
    -- - so verification cannot depend on the order of the claims.
    (∀ c, c ∈ claims ↔ c ∈ raw.map Prod.fst ∨ ∃ cs ∈ inner.map Prod.fst, c ∈ cs) →
    -- The result verifies for that union.
    S.verify S.setup claims α = true

end EthLib.Cryptography.Aggregation
