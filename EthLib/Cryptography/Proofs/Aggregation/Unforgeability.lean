module

public import EthLib.Cryptography.Aggregation.Interface
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Unforgeability of signature aggregation

The game is in the chosen-key model: one key is honest, and the adversary chooses every other key.

The game draws an input for key generation and generates the honest key pair.

The adversary sees the parameters and the honest public key.

It may ask a signing oracle for signatures under the honest secret key.

The oracle answers a context and a message with the scheme's signature, and the game logs it.

The adversary then outputs a list of claims and an aggregate.

It wins when three conditions hold:

- the contexts of its signing queries are admissible;
- the aggregate verifies for its claims;
- one of its claims pairs the honest public key with a message it never asked to be signed.

Admissibility is a parameter of the game, because it depends on the underlying signature scheme.

A stateful scheme forbids two signatures in one context, since a reused one-time key leaks secrets.

A stateless scheme admits every list of contexts.

This file states the game and its advantage; the instance for a concrete scheme bounds it.
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

/-- The unforgeability game.

It draws an input for key generation and generates the honest key pair.

If key generation fails, the adversary loses.

It runs the adversary with the signing oracle of the honest secret key, and logs every query.

The adversary wins when the contexts of its queries are admissible and its aggregate verifies.

One of its claims must also pair the honest public key with a message it never queried. -/
noncomputable def unforgeabilityGame (S : Scheme) [DecidableEq S.PublicKey]
    [DecidableEq S.Message] (keyInput : ProbComp S.KeyGenInput)
    (admissible : List S.SignContext → Bool) (A : Adversary S) : ProbComp Bool := do
  let input ← keyInput
  match S.gen S.setup input with
  | none => return false
  | some (pk, sk) =>
      let ((claims, α), log) ←
        (simulateQ (QueryImpl.ofLift unifSpec (WriterT (QueryLog (SigningSpec S)) ProbComp) +
          signingOracle S sk) (A.run S.setup pk)).run
      let fresh (m : S.Message) : Bool := !(log.any fun entry => entry.1.2 == m)
      return admissible (log.map fun entry => entry.1.1) && S.verify S.setup claims α &&
        claims.any fun c => c.1 == pk && fresh c.2

/-- The advantage of an adversary: the probability that it wins the unforgeability game. -/
noncomputable def unforgeabilityAdvantage (S : Scheme) [DecidableEq S.PublicKey]
    [DecidableEq S.Message] (keyInput : ProbComp S.KeyGenInput)
    (admissible : List S.SignContext → Bool) (A : Adversary S) : ℝ≥0∞ :=
  Pr{let won ← unforgeabilityGame S keyInput admissible A}[won = true]

end EthLib.Cryptography.Aggregation
