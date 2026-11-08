module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Bytes
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Proofs: the security game of leanSPHINCS with every hash call counted

Strong unforgeability under chosen-message attacks, for one key, in the random oracle model.

The algorithms are EthLib's own key generation, signing and verification.

Their hash is a query to the random oracle, which is sampled lazily from an empty cache.

The adversary requests signatures of messages of its choice.

It wins with a pair that verifies and that no request returned, after at most `2^30` requests.

The budget `q` counts every hash call of the experiment, repeated inputs included.

That is key generation, signing, the adversary's queries and the final verification.

On each request the signer derives `PK.seed` and `SK.prf` again, and rebuilds the top tree.

Those calls count too.

Uniform samples are free.
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
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- The game against one random oracle, from an empty cache.

It counts every hash call. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

/-- The probability that the adversary forges. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← experiment adversary}[result.1 = true]

/-- Every run of the experiment makes at most `q` hash calls. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- An adversary with a budget of `q >= 1` hash calls forges with probability `<= q / 2^bits`.

The budget counts every hash call of the experiment, the signer's included. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- The cap on signing requests is within the model's cap of 1,182,000,000. -/
theorem signatureLimit_le : SIGNATURE_LIMIT ≤ SphincsSecurity.signatureLimit := by
  decide

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
