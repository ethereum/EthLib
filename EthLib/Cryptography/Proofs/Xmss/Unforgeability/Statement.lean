import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Algorithms
import EthLib.Cryptography.Proofs.Xmss.Security.LeanXmss.Statement

/-!
# Proofs: the security game of leanXMSS, for EthLib's algorithms

Strong unforgeability under chosen-message attacks, in the random oracle model.

Source: the leanXMSS specification draft, section "Security".

```text
    S_0 uniform 32 bytes,   (sk, pk) = Gen(S_0)
    adversary(pk): queries H, requests Sig(sk, idx, m), never the same idx twice
    returns (m*, sigma*)
    wins  iff  Ver(pk, m*, sigma*) = 1  and  no request for m* returned sigma*

    every hash call is answered by one random oracle
```

The algorithms are EthLib's own: `keyGenWith`, `signWith` and `verifyWith`.

Their `H` is a query to the oracle (`queryH`).

The budget `q` counts every hash call of the experiment, repeated inputs included.

That is key generation, signing, the adversary's queries and the final verification.

A hash call is one call of `H`, whatever its input's length.

The signer re-derives `S` and `P` from `S_0` on each request, as `signWith` does.

Those calls count too.

The oracle's cost model is the one of the security proof (`LeanXmss.Security.countedOracle`).
-/

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss

/-- `H` in the game: a query to the random oracle. -/
abbrev H : ByteArray → OracleComp LeanXmss.HashSpec (Vector UInt8 32) := queryH

/-- A signing request: a leaf index and a message. -/
structure SignRequest where
  leafIndex : LeafIndex
  message : Message
  deriving DecidableEq

/-- A claimed forgery: a message and a signature, which carries its leaf index. -/
structure Forgery where
  message : Message
  signature : Signature
  deriving DecidableEq

/-- The signing oracle answers a request with a signature, or nothing when signing fails. -/
abbrev SigningSpec := SignRequest →ₒ Option Signature

/-- An adaptive adversary.

From the public key, it samples coins, queries `H`, requests signatures, and returns a forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (LeanXmss.OracleWorld + SigningSpec) Forgery

/-- No leaf index was requested twice. -/
def Valid (log : QueryLog SigningSpec) : Prop :=
  (log.map fun entry => entry.1.leafIndex).Nodup

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (List.Nodup _))

/-- Some request for the forgery's message was answered with the forgery's signature.

Any other signature of a signed message is a strong forgery. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1.message = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs (Decidable (∃ entry ∈ log, _ ∧ _))

/-- `Sig(sk, idx, m)` on each request, recorded with its answer. -/
def signingOracle (sk : SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp LeanXmss.OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Except.toOption <$> signWith H sk request.leafIndex request.message)

/-- A uniform seed `S_0`: the bytes of a uniform 256-bit vector, which `ofSeed` maps one to one. -/
noncomputable def sampleSeed : ProbComp Seed :=
  ofSeed <$> LeanXmss.sampleMasterSeed

/-- The game: key generation, the adversary with its oracles, then the check of its forgery. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp LeanXmss.OracleWorld Bool := do
  let seed ← liftM sampleSeed
  let (sk, pk) ← liftM (keyGenWith H seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift LeanXmss.OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp LeanXmss.OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return decide (Valid log ∧ ¬Contains log forgery) && verified

/-- The game against one lazily sampled random oracle, from an empty cache.

It counts every hash call. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ LeanXmss.Security.countedOracle (gameCore adversary)).run.run' ∅

/-- The probability that the adversary forges. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← experiment adversary}[result.1 = true]

/-- Every run of the experiment makes at most `q` hash calls. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- An adversary with a budget of `q >= 1` hash calls forges with probability `<= q / 2^bits`. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end EthLib.Cryptography.Xmss.Unforgeability
