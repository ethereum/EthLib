module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Translate
public import EthLib.Cryptography.Proofs.Xmss.Reference
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Proofs: the security game of leanXMSS, for EthLib's algorithms

Strong unforgeability under chosen-message attacks, in the random oracle model.

Source: the leanXMSS specification draft, section "Security".

```text
    S_0 uniform 32 bytes,   (pk, sk) = Gen(S_0)
    adversary(pk): queries H, requests Sig(sk, idx, m), never the same idx twice
    returns (m*, sigma*)
    wins  iff  Ver(pk, m*, sigma*) = 1  and  no request for m* returned sigma*

    every hash call is answered by one random oracle
```

The algorithms are EthLib's own: `keyGenWith`, `signWith` and `verifyWith`.

Their `H` is a query to the oracle (`queryH`).

The signer keeps its key across requests, as a real signer does.

Each request signs with the key the request before it returned.

The budget `q` counts the hash calls of the same game with the note's stateless signer.

That signer re-derives `S` and `P` from `S_0`, and rebuilds every tree, on each request.

It returns the same signatures, and a theorem proves that the two games win equally often.

The budget counts key generation, signing, the adversary's queries and the final verification.

It counts repeated inputs too, and a hash call is one call of `H`, whatever its input's length.

The oracle is lazily sampled, from an empty cache, and counts every call (`countedOracle`).
-/
@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss

/-- `H` in the game: a query to the random oracle. -/
abbrev H : Array UInt64 → OracleComp XmssSecurity.HashSpec Lanes4 := queryH

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
  main : PublicKey → OracleComp (XmssSecurity.OracleWorld + SigningSpec) Forgery

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

/-- `Sig(sk, idx, m)` on each request, recorded with its answer.

Each request signs with the key the request before it returned, and the oracle keeps the new key. -/
def signingOracle : QueryImpl SigningSpec
    (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp XmssSecurity.OracleWorld))) :=
  fun request => StateT.mk fun sk => WriterT.mk
    ((fun result => ((result.1.toOption, result.2), [⟨request, result.1.toOption⟩])) <$>
      liftM (signWith H sk request.leafIndex request.message))

/-- A uniform seed `S_0`: the lanes of a uniform 256-bit vector, which `ofSeed` maps one to one. -/
noncomputable def sampleSeed : ProbComp Seed :=
  ofSeed <$> XmssSecurity.sampleMasterSeed

/-- The game: key generation, the adversary with its oracles, then the check of its forgery. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp XmssSecurity.OracleWorld Bool := do
  let seed ← liftM sampleSeed
  let (pk, sk) ← liftM (keyGenWith H seed)
  let (((forgery, _), log) : (Forgery × SecretKey) × QueryLog SigningSpec) ←
    ((simulateQ (QueryImpl.ofLift XmssSecurity.OracleWorld
      (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp XmssSecurity.OracleWorld))) +
        signingOracle) (adversary.main pk)).run sk).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return decide (Valid log ∧ ¬Contains log forgery) && verified

/-- The oracles of the game.

Coins pass through for free.

`H` is a random oracle, sampled lazily, and each call costs 1, a repeated input included. -/
noncomputable def countedOracle :=
  (unifFwdImpl XmssSecurity.HashSpec + (randomOracle : QueryImpl XmssSecurity.HashSpec
    (StateT (QueryCache XmssSecurity.HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- The game against one random oracle, from an empty cache.

It counts every hash call. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

/-- The probability that the adversary forges. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← experiment adversary}[result.1 = true]

/-! ## The game with the stateless signer

The budget of the theorem counts the calls of this game. -/

/-- `Sig(S_0, idx, m)` of the stateless signer on each request, recorded with its answer. -/
def statelessSigningOracle (seed : Seed) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp XmssSecurity.OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Except.toOption <$> statelessSignWith H seed request.leafIndex request.message)

/-- The game with the stateless signer: the secret key is the seed itself. -/
noncomputable def statelessGameCore (adversary : Adversary) :
    OracleComp XmssSecurity.OracleWorld Bool := do
  let seed ← liftM sampleSeed
  let (sk, pk) ← liftM (statelessKeyGenWith H seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift XmssSecurity.OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp XmssSecurity.OracleWorld)) +
        statelessSigningOracle sk) (adversary.main pk)).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return decide (Valid log ∧ ¬Contains log forgery) && verified

/-- The game with the stateless signer against one random oracle, from an empty cache.

It counts every hash call. -/
noncomputable def statelessExperiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (statelessGameCore adversary)).run.run' ∅

/-- The probability that the adversary forges against the stateless signer. -/
noncomputable def statelessForgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← statelessExperiment adversary}[result.1 = true]

/-! ## The statement -/

/-- Every run of the game with the stateless signer makes at most `q` hash calls. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (statelessExperiment adversary), result.2 ≤ q

/-- An adversary with a budget of `q >= 1` hash calls forges with probability `<= q / 2^bits`.

The budget counts every hash call of the game with the stateless signer, the signer's included. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end EthLib.Cryptography.Xmss.Unforgeability
