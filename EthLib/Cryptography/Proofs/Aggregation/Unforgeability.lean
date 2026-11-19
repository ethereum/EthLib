module

public import EthLib.Cryptography.Aggregation.Interface
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Unforgeability of signature aggregation

The game is Definition 9 of [Hofheinz, Reichle and Wagner](https://eprint.iacr.org/2026/723).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace EthLib.Cryptography.Aggregation

/-- The interface of the signing oracle.

A query is a context and a message.

The answer is a signature, or nothing when the signer cannot sign. -/
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

/-- The signing oracle of a secret key, which logs every query with its answer. -/
def signingOracle (S : Scheme) (sk : S.SecretKey) :
    QueryImpl (SigningSpec S) (WriterT (QueryLog (SigningSpec S)) ProbComp) :=
  QueryImpl.withLogging fun query => pure (S.sign S.setup sk query.1 query.2)

/-- The unforgeability game, in the chosen-key model.

One key is honest, and the adversary chooses every other key.

It departs from the paper in three ways:
- the forgery is a list of claims, because signers may sign different messages;
- the contexts of the signing queries must be admissible, since a stateful signer needs it;
- the parameters are fixed once for the scheme, where the paper draws them at random.

Admissibility is a parameter, because it depends on the underlying signature scheme. -/
noncomputable def unforgeabilityGame (S : Scheme) [DecidableEq S.PublicKey]
    [DecidableEq S.Message] (keyInput : ProbComp S.KeyGenInput)
    (admissible : List S.SignContext → Bool) (A : Adversary S) : ProbComp Bool := do
  -- Step 1: draw an input for key generation, such as a uniform seed.
  let input ← keyInput
  -- Step 2: generate the honest key pair.
  match S.gen S.setup input with
  -- Key generation rejected the input, so the adversary loses.
  | none => return false
  | some (pk, sk) =>
      -- Step 3: run the adversary on the parameters and the honest public key:
      -- - its random coins pass through unchanged;
      -- - its signing queries go to the honest signer, which logs each query with its answer.
      let ((claims, α), log) ←
        (simulateQ (QueryImpl.ofLift unifSpec (WriterT (QueryLog (SigningSpec S)) ProbComp) +
          signingOracle S sk) (A.run S.setup pk)).run
      -- A message is fresh when no signing query asked for it, in any context.
      let fresh (m : S.Message) : Bool := !(log.any fun entry => entry.1.2 == m)
      -- Step 4: the adversary wins when three conditions hold:
      -- - the contexts of its queries, in order, are admissible:
      --   a stateful scheme rejects two queries in one context, since a reused one-time key leaks;
      -- - the aggregate verifies for its claims;
      -- - one claim pairs the honest public key with a fresh message.
      return admissible (log.map fun entry => entry.1.1) && S.verify S.setup claims α &&
        claims.any fun c => c.1 == pk && fresh c.2

/-- The advantage of an adversary: the probability that it wins the unforgeability game. -/
noncomputable def unforgeabilityAdvantage (S : Scheme) [DecidableEq S.PublicKey]
    [DecidableEq S.Message] (keyInput : ProbComp S.KeyGenInput)
    (admissible : List S.SignContext → Bool) (A : Adversary S) : ℝ≥0∞ :=
  Pr{let won ← unforgeabilityGame S keyInput admissible A}[won = true]

end EthLib.Cryptography.Aggregation
