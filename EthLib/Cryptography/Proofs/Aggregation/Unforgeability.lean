module

public import EthLib.Cryptography.Aggregation.Interface
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Unforgeability of signature aggregation

The game is inspired by Definition 9 of [Hofheinz et al.](https://eprint.iacr.org/2026/723).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace EthLib.Cryptography.Aggregation

/-- The interface of the signing oracle.

A query is a context and a message.

The answer is a signature, or nothing when the oracle refuses the query. -/
abbrev SigningSpec (S : Scheme) :=
  S.SignContext × S.Message →ₒ Option S.Signature

/-- An adversary of the unforgeability game.

It reads the parameters and the honest public key.

It may draw random coins and ask the signing oracle.

It outputs a list of claims with an aggregate. -/
structure Adversary (S : Scheme) where
  /-- The adversary's computation. -/
  run : S.Params → S.PublicKey →
    OracleComp (unifSpec + SigningSpec S) (List S.Claim × S.Aggregate)

/-- The signing oracle of a secret key.

Its state is the list of queries it answered, each a context and a message. -/
def signingOracle (S : Scheme) [DecidableEq S.SignContext] (sk : S.SecretKey) :
    QueryImpl (SigningSpec S) (StateT (List (S.SignContext × S.Message)) ProbComp) :=
  fun (ctx, m) => do
    let answered ← get
    -- A stateful key signs at most once in each context.
    --
    -- So the oracle refuses a query whose context it already signed in, and records nothing.
    if S.stateful && answered.any (·.1 == ctx) then
      return none
    else
      -- Otherwise it signs, and records the query as answered.
      set (answered ++ [(ctx, m)])
      return some (S.sign S.setup sk ctx m)

/-- The unforgeability game, in the chosen-key model.

One key is honest, and the adversary chooses every other key.

It departs from the paper in two ways:
- the forgery is a list of claims, because signers may sign different messages and contexts;
- the parameters are fixed once for the scheme, where the paper draws them at random. -/
noncomputable def unforgeabilityGame (S : Scheme) [DecidableEq S.PublicKey]
    [DecidableEq S.SignContext] [DecidableEq S.Message] [SampleableType S.KeyGenInput]
    (A : Adversary S) : ProbComp Bool := do
  -- Step 1: draw the input of key generation uniformly, such as a uniform seed.
  let input ← $ᵗ S.KeyGenInput
  -- Step 2: generate the honest key pair.
  let (pk, sk) := S.gen S.setup input
  -- Step 3: run the adversary on the parameters and the honest public key:
  -- - its random coins pass through unchanged;
  -- - its signing queries go to the honest signer, which starts with no answered query.
  let ((claims, α), answered) ←
    (simulateQ (QueryImpl.ofLift unifSpec
        (StateT (List (S.SignContext × S.Message)) ProbComp) + signingOracle S sk)
      (A.run S.setup pk)).run []
  -- A claim is fresh when the oracle never signed its message in its context:
  -- - a signature on the same message in another epoch does not make it stale;
  -- - a query the oracle refused does not make it stale either.
  let fresh (ctx : S.SignContext) (m : S.Message) : Bool := !answered.contains (ctx, m)
  -- Step 4: the adversary wins when two conditions hold:
  -- - the aggregate verifies for its claims;
  -- - one claim pairs the honest public key with a fresh context and message.
  return S.verify S.setup claims α && claims.any fun (key, ctx, m) => key == pk && fresh ctx m

/-- The advantage of an adversary: the probability that it wins the unforgeability game. -/
noncomputable def unforgeabilityAdvantage (S : Scheme) [DecidableEq S.PublicKey]
    [DecidableEq S.SignContext] [DecidableEq S.Message] [SampleableType S.KeyGenInput]
    (A : Adversary S) : ℝ≥0∞ :=
  Pr{let won ← unforgeabilityGame S A}[won = true]

end EthLib.Cryptography.Aggregation
