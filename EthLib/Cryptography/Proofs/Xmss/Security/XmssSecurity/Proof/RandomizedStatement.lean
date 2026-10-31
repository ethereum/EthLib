import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Statement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

namespace Concrete

abbrev digestBytes (value : Digest) : HashInput := bytesLE 16 value

abbrev messageBytes (message : Message) : HashInput := bytesLE 32 message

abbrev randomnessBytes (randomness : Randomness) : HashInput := bytesLE 16 randomness

end Concrete

/-- The random-oracle semantics.

Hash queries are answered lazily and consistently by uniform sampling, and cached.

Uniform-sampling queries are forwarded unchanged. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

/-- The interface of a synchronized signature scheme in the random-oracle experiment. -/
structure Scheme (Key : Type) where
  keygen : OracleComp OracleWorld (PublicKey × Key)
  sign : Key → LeafIndex → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → LeafIndex → Message → Signature → OracleComp OracleWorld Bool

/-- A classical adaptive adversary.

After receiving the public key, it may query the shared random oracle and request signatures.

Finally it returns a claimed forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

/-- The signing oracle used in the game.

It records every request and response while forwarding the request to the scheme's signer. -/
def signingOracle {Key : Type} (scheme : Scheme Key) (sk : Key) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request.leafIndex request.message

/-- Forward the shared random oracle and uniform sampling to the adversary unchanged.

The logged signing oracle runs alongside them. -/
def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)

noncomputable def Seeded.gameRest {Key : Type} (randomizedScheme : Scheme Key) (adversary : Adversary)
    (pk : PublicKey) (sk : Key) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle randomizedScheme sk) (adversary.main pk)).run
  let verified ← randomizedScheme.verify pk forgery.leafIndex forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- Key generation, followed by the adversary and final verification. -/
noncomputable def gameCore {Key : Type} (scheme : Scheme Key) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  Seeded.gameRest scheme adversary pk sk

/-- Success probability from an empty random-oracle cache. -/
noncomputable def forgeAdvantage {Key : Type} (scheme : Scheme Key) (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let x ← (simulateQ romImpl (gameCore scheme adversary)).run' ∅}[x = true]

/-- Count one per hash call, including cache hits, and zero per uniform sample. -/
noncomputable def countedRomImpl :=
  romImpl.withAddCost (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- Every execution of the consistent random oracle uses at most `q` hash calls.

The count includes key generation, adversarial hashing, signing, and final verification. -/
def HasHashQueryBound {Key : Type} (scheme : Scheme Key) (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ countedRomImpl (gameCore scheme adversary)).run.run' ∅),
    result.2 ≤ q

/-- The security bound for an intermediate scheme. -/
def HasClassicalSecurityBits {Key : Type} (scheme : Scheme Key) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound scheme adversary q →
    forgeAdvantage scheme adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- Every execution after key generation uses at most `q` hash calls.

This holds from any cache key generation can leave.

The calls are the adversary's, the signer's and the final verification's.

Model key generation does more work than the real scheme's and is not charged. -/
def HasAfterKeygenHashQueryBound {Key : Type} (scheme : Scheme Key) (adversary : Adversary) (q : Nat) :
    Prop :=
  ∀ keyResult ∈ support ((simulateQ romImpl scheme.keygen).run ∅),
    ∀ result ∈ support ((simulateQ countedRomImpl
      (Seeded.gameRest scheme adversary keyResult.1.1 keyResult.1.2)).run.run' keyResult.2),
      result.2 ≤ q

/-- Room for the verification's constant and other lower-order terms.

This room is set against the key-generation calls of the real scheme. -/
def lowerOrderSlack : Nat := 2 ^ 20

/-- Two units per hash call after key generation, plus the slack. -/
def HasAfterKeygenSecurity {Key : Type} (scheme : Scheme Key) : Prop :=
  ∀ q, q < 2 ^ 127 → ∀ adversary, HasAfterKeygenHashQueryBound scheme adversary q →
    forgeAdvantage scheme adversary ≤ ((2 * q + lowerOrderSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)

end XmssSecurity
