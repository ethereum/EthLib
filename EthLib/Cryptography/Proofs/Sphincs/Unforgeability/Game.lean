module

public import EthLib.Cryptography.Sphincs
public import EthLib.Cryptography.Proofs.HashSig.Bytes
public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount

/-!
# Proofs: the security game of leanSPHINCS

Strong unforgeability under chosen-message attacks, for one key, in the random-oracle model.

1. `SK.seed` is 32 uniform bytes, and `(sk, pk) = Gen(SK.seed)`.
2. The adversary gets `pk`, queries `H`, and requests `Sign(sk, m)` for messages of its choice.
3. It returns a pair `(m*, sigma*)`.
4. It wins when `Ver(pk, m*, sigma*) = 1` and no request for `m*` returned `sigma*`.

One random oracle answers every hash call.

The algorithms are EthLib's own: `keyGenWith`, `signWith` and `verifyWith`.

Their `H` is a query to the random oracle that leanXMSS's game also uses.

The oracle is lazily sampled, from an empty cache.

A failed signing request is answered with nothing, and nothing never verifies.

The game, the advantage and the budget are VCVio's, for this scheme.

# The budget

An adversary's budget is two numbers, counted on every path of its own program.

- `qH`: its hash queries.
- `qS`: its signing requests.

The calls of key generation, of the signer and of the final verification are not charged.

No signing limit is built into the game.

A bound in `qS` then says how the security falls with the number of signatures.

The signer does not count its signatures, so the limit of `2^30` is the caller's to keep.

# Scope

The game has one key pair.

The message digest hashes `R`, `PK.seed`, `PK.root` and `M`, as FIPS 205 §9.2, Algorithm 19, does.

Every addressed hash starts with the 16-byte `PK.seed`, as in FIPS 205.

Security for many keys is not claimed.

The adversary returns a signature as a structure, not as bytes.

Decoding and encoding are inverse on strings of the right length, so the two views agree.

The win event is leanXMSS's.

The budget is not: leanXMSS's game counts every hash call of the experiment in one number.

Its signer also takes a leaf index, which no two requests may share.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open OracleSpec OracleComp ENNReal MeasureTheory

/-- `H` in the game: a query to the random oracle. -/
abbrev H : ByteArray → OracleComp HashSig.OracleWorld (Vector UInt8 32) :=
  HashSig.queryH

/-- A uniform 32-byte `SK.seed`. -/
noncomputable def sampleSeed : ProbComp Seed :=
  letI := SampleableType.ofFintype Seed
  $ᵗ Seed

/-- leanSPHINCS as a signature scheme over the random oracle.

- Key generation samples `SK.seed`, then runs `keyGenWith`.
- Signing runs `signWith`, and answers nothing when it fails.
- Verification runs `verifyWith`, and rejects nothing. -/
noncomputable def scheme :
    SignatureAlg (OracleComp HashSig.OracleWorld) Message PublicKey SecretKey
      (Option Signature) where
  keygen := do
    let seed ← liftM sampleSeed
    let (sk, pk) ← keyGenWith H seed
    return (pk, sk)
  sign _ sk msg := Except.toOption <$> signWith H sk msg
  verify pk msg
    | none => pure false
    | some sig => verifyWith H pk msg sig

/-- An adversary: from the public key, it queries `H`, requests signatures and returns a pair. -/
abbrev Adversary := SignatureAlg.StrongUnforgeableAdversary scheme

/-- The probability that the adversary returns a valid pair that no request returned. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  SignatureAlg.strongUnforgeableAdvantage (ProbCompRuntime.rom HashSig.HashSpec) adversary

/-! ## What the game checks -/

/-- A pair without a signature never verifies. -/
@[simp] theorem scheme_verify_none (pk : PublicKey) (msg : Message) :
    scheme.verify pk msg none = pure false :=
  rfl

/-- A pair with a signature verifies as `verifyWith` says. -/
@[simp] theorem scheme_verify_some (pk : PublicKey) (msg : Message) (sig : Signature) :
    scheme.verify pk msg (some sig) = verifyWith H pk msg sig :=
  rfl

/-! ## Replaying an answer never wins

The argument holds for every signature scheme, so it is made once, for all of them. -/

section Replay

variable {ι : Type} {spec : OracleSpec ι} {M PK SK S : Type}

/-- The adversary that requests a signature of `msg` and returns the answer as its pair. -/
def replayOf (sigAlg : SignatureAlg (OracleComp spec) M PK SK S) (msg : M) :
    SignatureAlg.StrongUnforgeableAdversary sigAlg where
  main _ := do
    let answer ← (spec + (M →ₒ S)).query (.inr msg)
    return (msg, answer)

/-- With the replaying adversary, the game computes as usual, then returns false.

The signing oracle logs the pair it returns, so the freshness check rejects it. -/
theorem strongUnforgeableExperiment_replayOf (sigAlg : SignatureAlg (OracleComp spec) M PK SK S)
    (msg : M) :
    SignatureAlg.strongUnforgeableExperiment (replayOf sigAlg msg)
      = (do
        let keys ← sigAlg.keygen
        let answer ← sigAlg.sign keys.1 keys.2 msg
        (fun _ => false) <$> sigAlg.verify keys.1 msg answer) := by
  simp only [SignatureAlg.strongUnforgeableExperiment, SignatureAlg.runWithSigningOracle, replayOf,
    SignatureAlg.signingOracle]
  simp [QueryImpl.withLogging_apply]
  rfl

/-- The replaying adversary wins with probability 0, in every runtime. -/
theorem strongUnforgeableAdvantage_replayOf
    (sigAlg : SignatureAlg (OracleComp spec) M PK SK S)
    (runtime : ProbCompRuntime (OracleComp spec)) (msg : M) :
    SignatureAlg.strongUnforgeableAdvantage runtime (replayOf sigAlg msg) = 0 := by
  rw [SignatureAlg.strongUnforgeableAdvantage, strongUnforgeableExperiment_replayOf]
  -- The game returns a constant, false, after the honest computation.
  simp only [← map_bind]
  rw [ProbCompRuntime.evalDist_map _ _ measurable_const, Measure.map_apply measurable_const
    (measurableSet_singleton true)]
  simp

end Replay

/-- The adversary that requests a signature of `msg` and returns the answer as its pair. -/
noncomputable abbrev replay (msg : Message) : Adversary :=
  replayOf scheme msg

/-- The replaying adversary makes no hash query and one signing request. -/
theorem replay_romQueryBound (msg : Message) : (replay msg).RomQueryBound 0 1 := by
  intro pk
  refine ⟨(isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 ?_),
    (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)⟩
  simp [SignatureAlg.IsHashQuery]

/-- The replaying adversary wins with probability 0. -/
theorem forgeAdvantage_replay (msg : Message) : forgeAdvantage (replay msg) = 0 :=
  strongUnforgeableAdvantage_replayOf scheme _ msg

end EthLib.Cryptography.Sphincs.Unforgeability
