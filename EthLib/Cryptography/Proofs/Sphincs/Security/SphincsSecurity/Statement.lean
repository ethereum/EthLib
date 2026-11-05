module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# The security statement

This file states strong unforgeability under chosen-message attack (SUF-CMA).

The hash is a random oracle.

The game samples a uniform 32-byte seed `S0` and generates the key from it.

Key generation first hashes `S0` into the scheme seed `S = H(leanSPHINCS || S0)`.

The signer is deterministic: it derives each randomizer from `S` and the message.

So a repeated request returns the same signature.

Every hash call counts toward the query bound, repeated calls included.

The calls of key generation, signing and verification count too.

The file ends with the forgery advantage and the target of `bits` bits of classical security.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

variable [Params]

/-- A forgery: a message and a signature. -/
structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

/-- The signing oracle: a message, answered by a signature or by `none` if the signer fails. -/
abbrev SigningSpec := Message →ₒ Option Signature

namespace SigningTranscript

/-- The transcript holds at most `N` signing requests, the signature limit of the parameters. -/
def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

/-- The transcript holds a request for the message of the forgery, answered with its signature.

A new signature of a signed message is thus still a forgery: this is strong unforgeability. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

end SigningTranscript

namespace Security

/-- An adversary: a computation from the public key to a forgery.

It can sample uniform randomness and query the hash (the random oracle) and the signing oracle. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

/-- The counted random oracle: a lazily sampled cache of uniform 32-byte answers.

Each hash query costs one, repeated queries included.

Uniform sampling costs nothing. -/
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- The signing oracle: the deterministic signer with the secret key.

It logs every request and its answer. -/
noncomputable def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Seeded.sign sk request : OracleComp HashSpec (Option Signature))

/-- The game: sample a seed `S0`, generate the key, run the adversary and verify its forgery.

The adversary wins when its forgery verifies and it made at most `N` signing requests.

The win also needs that no signing answer was the forgery. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygen seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM
    (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The game under the counted random oracle, from an empty cache.

It returns whether the adversary won and the number of hash queries of the whole run.

That number includes the queries of key generation, signing and verification. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

/-- The probability that the adversary wins. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← experiment adversary}[result.1 = true]

/-- Every run of the experiment makes at most `q` hash queries. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- The scheme has `bits` bits of classical security.

Let `q >= 1`.

An adversary whose runs make at most `q` hash queries wins with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end Security

/-- The security target: the scheme with parameters `P` has `bits` bits of classical security. -/
abbrev SecurityBits (P : Params) (bits : Nat) : Prop := @Security.HasClassicalSecurityBits P bits

end SphincsSecurity
