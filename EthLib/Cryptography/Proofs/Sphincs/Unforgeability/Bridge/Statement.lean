module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Bytes
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Base.Prelude
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Proofs: the security game of leanSPHINCS with every hash call counted

Strong unforgeability under chosen-message attacks, for one key, in the random oracle model.

The algorithms are EthLib's own key generation, signing and verification.

Their hash is a query to the random oracle, which is sampled lazily from an empty cache.

The adversary requests signatures of messages of its choice.

It wins with a pair that verifies and that no request returned, after at most `2^30` requests.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec OracleWorld)

/-- `H` in the game: a query to the random oracle. -/
abbrev H : ByteArray → OracleComp HashSpec (Vector UInt8 32) := queryH

/-- A claimed forgery: a message and a signature. -/
structure Forgery where
  message : Message
  signature : Signature
  deriving DecidableEq

/-- The signing oracle answers a message with a signature, or nothing when signing fails.

The signer is stateless and deterministic, so a request is the message alone. -/
abbrev SigningSpec := Message →ₒ Option Signature

/-- An adaptive adversary.

From the public key, it samples coins, queries `H`, requests signatures, and returns a forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

/-- The adversary made at most `2^30` signing requests. -/
def Valid (log : QueryLog SigningSpec) : Prop :=
  log.length ≤ SIGNATURE_LIMIT

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Some request for the forgery's message was answered with the forgery's signature.

Any other signature of a signed message is a strong forgery. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs (Decidable (∃ entry ∈ log, _ ∧ _))

/-- `Sign(sk, m)` on each request, recorded with its answer. -/
def signingOracle (sk : SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun message =>
    liftM (Except.toOption <$> signWith H sk message)

/-- A uniform `SK.seed`: the bytes of a uniform 256-bit vector, which are uniform bytes. -/
noncomputable def sampleSeed : ProbComp Seed :=
  ofSeed <$> SphincsSecurity.sampleMasterSeed

/-- The game: key generation, the adversary with its oracles, then the check of its forgery. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleSeed
  let (sk, pk) ← liftM (keyGenWith H seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return decide (Valid log ∧ ¬Contains log forgery) && verified

/-- The oracles of the game.

Coins pass through for free.

`H` is a random oracle, sampled lazily, and each call costs 1, a repeated input included. -/
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec
    (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    -- Uniform samples are free.
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- The game against one random oracle, from an empty cache.

It counts every hash call. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

/-- The probability that the adversary forges. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← experiment adversary}[result.1 = true]

/-- Every run of the experiment makes at most `q` hash calls.

The budget `q` counts every hash call of the experiment, repeated inputs included.

That is key generation, signing, the adversary's queries and the final verification.

On each request the signer derives `PK.seed` and `SK.prf` again, and rebuilds the top tree.

Those calls count too. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- An adversary with a budget of `q >= 1` hash calls forges with probability `<= q / 2^bits`.

The budget counts every hash call of the experiment, the signer's included. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-! ## The adversary's own hash calls

A second budget counts only the adversary's own hash calls.

The calls of key generation, signing and verification then enter as a fixed additive constant. -/

/-- A query of the adversary that is a hash call, neither a coin nor a signing request. -/
def IsAdversaryHashCall : (OracleWorld + SigningSpec).Domain → Prop
  | .inl input => input.isRight = true
  | .inr _ => False

instance : DecidablePred IsAdversaryHashCall
  | .inl input => inferInstanceAs (Decidable (input.isRight = true))
  | .inr _ => inferInstanceAs (Decidable False)

/-- The game, which also returns the adversary's hash calls and its number of signing requests.

The adversary runs with a counter of its hash calls; the rest is the game above. -/
noncomputable def adversaryGameCore (adversary : Adversary) :
    OracleComp OracleWorld (Bool × Nat × Nat) := do
  let seed ← liftM sampleSeed
  let (sk, pk) ← liftM (keyGenWith H seed)
  let (((forgery, calls), log) : (Forgery × Nat) × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
      (SphincsSecurity.QueryCap.counted IsAdversaryHashCall (adversary.main pk))).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return (decide (Valid log ∧ ¬Contains log forgery) && verified, calls, log.length)

/-- The game against one random oracle, from an empty cache, sampled lazily as above.

It returns the verdict, the adversary's hash calls and its number of signing requests. -/
noncomputable def adversaryExperiment (adversary : Adversary) : ProbComp (Bool × Nat × Nat) :=
  (simulateQ (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec
    (StateT (QueryCache HashSpec) ProbComp))) (adversaryGameCore adversary)).run' ∅

/-- In every run, the adversary makes at most `q` hash calls and `r` signing requests.

The calls of key generation, signing and verification do not count.

`r` is not capped: a run past `2^30` requests loses, but its signer calls still count. -/
def HasAdversaryQueryBound (adversary : Adversary) (q r : Nat) : Prop :=
  ∀ result ∈ support (adversaryExperiment adversary), result.2.1 ≤ q ∧ result.2.2 ≤ r

/-- The hash calls of key generation: `2 + (258 * 2^10 - 1)`. -/
def keyGenCalls : Nat := 264193

/-- A bound on the hash calls of one request: 470595 and three counter searches of `2^32`. -/
def signCalls : Nat := 470595 + 3 * MAX_COUNTER_TRIALS

/-- A bound on the hash calls of one verification: the digest, FORS and the three layers. -/
def verifyCalls : Nat := 491

/-- A bound on the scheme's calls in a run: key generation, `r` requests and one verification.

At the model's cap of 1,182,000,000 requests it is about `2^63.7`. -/
def schemeCalls (r : Nat) : Nat := keyGenCalls + r * signCalls + verifyCalls

/-- With `q` own hash calls and `r` requests, the forging probability is `<= (q + C) / 2^bits`.

`C` bounds the scheme's calls for `r` requests.

So the bound is never below `C / 2^bits`, about `2^-63.3` at 127 bits and 1,182,000,000 requests. -/
def HasAdversarySecurityBits (bits : Nat) : Prop :=
  ∀ q r adversary, HasAdversaryQueryBound adversary q r →
    forgeAdvantage adversary ≤ ((q + schemeCalls r : Nat) : ℝ≥0∞) / ((2 ^ bits : Nat) : ℝ≥0∞)

/-! ## The signer's long counter searches, charged apart -/

/-- The bound on a counter search that the third budget charges to every request: `2^22`. -/
def searchCap : Nat := 2 ^ 22

/-- A bound on the scheme's calls when every request but the last searches below `T`.

Key generation, `470595 + 3 T` per request, `3 * 2^32` for the last request, and verification. -/
def cappedCalls (T r : Nat) : Nat :=
  keyGenCalls + r * (470595 + 3 * T) + 3 * MAX_COUNTER_TRIALS + verifyCalls

/-- With `q` own hash calls and `r` requests, the forging probability is `<= (q + C + 1) / 2^bits`.

`C` charges each request its searches up to `2^22` counters, and one request all `2^32`.

The `1` covers the chance that some search runs past `2^22` counters.

At 127 bits and `2^30` requests, the bound is never below about `2^-73.4`. -/
def HasCappedSecurityBits (bits : Nat) : Prop :=
  ∀ q r adversary, HasAdversaryQueryBound adversary q r →
    forgeAdvantage adversary ≤
      ((q + cappedCalls searchCap r + 1 : Nat) : ℝ≥0∞) / ((2 ^ bits : Nat) : ℝ≥0∞)

/-! ## Signing inside the game -/

/-- The game up to its verdict: the forgery, the log of signing requests and the verification.

The game above is the verdict on this run. -/
noncomputable def gameRun (adversary : Adversary) :
    OracleComp OracleWorld (Forgery × QueryLog SigningSpec × Bool) := do
  let seed ← liftM sampleSeed
  let (sk, pk) ← liftM (keyGenWith H seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return (forgery, log, verified)

/-- The probability that some signing request of the game gets no signature.

The game runs against one random oracle, from an empty cache, as above but with no cost. -/
noncomputable def signingFailure (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← (simulateQ (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec
    (StateT (QueryCache HashSpec) ProbComp))) (gameRun adversary)).run' ∅}[
    ∃ entry ∈ result.2.1, entry.2 = none]

/-- The cap on signing requests is within the model's cap of 1,182,000,000. -/
theorem signatureLimit_le : SIGNATURE_LIMIT ≤ SphincsSecurity.signatureLimit := by
  decide

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
