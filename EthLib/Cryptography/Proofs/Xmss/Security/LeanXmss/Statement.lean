module

public import EthLib.Cryptography.Proofs.Xmss.Security.LeanXmss.Scheme
public import VCVio.OracleComp.QueryTracking.WriterCost
public import EthLib.Cryptography.Proofs.Xmss.Security.Statement.LeanXmss

/-!
# leanXMSS security statement

Strong unforgeability under chosen-message attacks (SUF-CMA) in the classical random-oracle model,
with a 127-bit target, for the scheme of `Scheme.lean`. The adversary picks each request's leaf index
and may not reuse one: the scheme is stateful.
-/

open OracleComp OracleSpec ENNReal

namespace LeanXmss

@[expose] public section

namespace Security

/-- A probabilistic adaptive adversary with private randomness and access to hashing and signing. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

/-- Record each signing request and its answer. -/
def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Seeded.sign sk request.leafIndex request.message : OracleComp HashSpec _)

/-- Sample the master seed, then run all parties with one shared hash oracle. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
      signingOracle sk) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- Forward private sampling for free; answer hash queries consistently and count every call,
including cache hits. -/
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- Run the game from an empty random-oracle cache, recording success and the total number of hash
calls. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

/-- The probability of a successful forgery. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← experiment adversary}[result.1 = true]

/-- Every execution uses at most `q` hash calls, including key generation, signing and verification. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- Every adversary with query budget `q ≥ 1` wins with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end Security

/-- The security claim. -/
abbrev LeanXmssSecurityStatement : Prop := Security.HasClassicalSecurityBits 127

end

end LeanXmss
