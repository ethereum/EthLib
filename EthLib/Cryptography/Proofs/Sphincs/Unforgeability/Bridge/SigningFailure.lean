module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.SearchGame

/-!
# Proofs: signing inside the game rarely fails, in the random-oracle model

Take an adversary with at most `q` hash calls of its own and `r` signing requests in every run.

Some request of its game gets no signature with probability at most `(q + C) (1 - p)^(2^32)`.

`C` bounds the scheme's calls, and `p` is the chance that one counter gives a codeword.

So the probability is at most `(q + C) exp(-2^18)`.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic
open scoped OracleComp.Lower
open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open HashSig (HashSpec OracleWorld)

/-- The game up to its result: keys, the adversary with its log, then the verification. -/
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

The game runs against one random oracle, from an empty cache. -/
noncomputable def signingFailure (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← (simulateQ HashSpec.romImpl (gameRun adversary)).run' ∅}[
    ∃ entry ∈ result.2.1, entry.2 = none]

/-- The run is key generation, then the adversary's run with its oracles, then the verification. -/
theorem gameRun_eq_keys_run (adversary : Adversary) :
    gameRun adversary = (do
      let keys : SecretKey × PublicKey ← (do
        let seed ← liftM sampleSeed
        liftM (keyGenWith H seed) : OracleComp OracleWorld (SecretKey × PublicKey))
      let run : Forgery × QueryLog SigningSpec ←
        (simulateQ (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
            QueryImpl.withLogging (fun msg => liftM (signerOf keys.1 msg) :
              QueryImpl SigningSpec (OracleComp OracleWorld))) (adversary.main keys.2)).run
      let verified ← liftM (verifierOf keys.2 run.1)
      pure (run.1, run.2, verified)) := by
  unfold gameRun signingOracle signerOf verifierOf
  rw [bind_assoc]

/-- The game is the verdict on its run. -/
theorem gameCore_eq_map_gameRun (adversary : Adversary) :
    gameCore adversary = (fun run => verdictOf run.1 run.2.1 run.2.2) <$> gameRun adversary := by
  rw [gameRun_eq_keys_run, gameCore_eq_keys_run]
  simp only [map_bind, map_pure]

/-- Take any keys, then the adversary's run with its oracles, then the verification.

A run in which some request gets no signature ends with a failed search.

All `2^32` counters of that search miss the code in the final cache. -/
theorem failedSearch_of_mem_support_keys_run
    (keys : OracleComp OracleWorld (SecretKey × PublicKey)) (adversary : Adversary)
    (z : (Forgery × QueryLog SigningSpec × Bool) × HashSpec.QueryCache)
    (hz : z ∈ support ((simulateQ HashSpec.romImpl (do
      let keyPair : SecretKey × PublicKey ← keys
      let run : Forgery × QueryLog SigningSpec ←
        (simulateQ (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
            QueryImpl.withLogging (fun msg => liftM (signerOf keyPair.1 msg) :
              QueryImpl SigningSpec (OracleComp OracleWorld))) (adversary.main keyPair.2)).run
      let verified ← liftM (verifierOf keyPair.2 run.1)
      pure (run.1, run.2, verified) : OracleComp OracleWorld _)).run ∅))
    (h : ∃ entry ∈ z.1.2.1, entry.2 = none) :
    HashSig.FailedSearch searchPoint SearchMiss MAX_COUNTER_TRIALS z.2 := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨v, hv, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨x, hx, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨entry, hmem, hnone⟩ := h
  -- No signature is a long search for every bound, `2^32` included.
  have hlong : ¬∀ e ∈ v.1.2, SearchesBelow MAX_COUNTER_TRIALS e.2 := fun hall => by
    have hbelow := hall entry hmem
    rw [hnone] at hbelow
    exact hbelow
  -- The verification only adds entries to the cache, so the search stays failed.
  exact (failedSearch_of_mem_support_run MAX_COUNTER_TRIALS le_rfl w.1.1 _ w.2 v hv hlong).mono
    _ _ _ (HashSig.le_snd_of_mem_support_run_romImpl (z := x) _ hx)

/-- A run of the game in which some request gets no signature ends with a failed search.

All `2^32` counters of that search miss the code in the final cache. -/
theorem failedSearch_of_mem_support_gameRun (adversary : Adversary)
    (z : (Forgery × QueryLog SigningSpec × Bool) × HashSpec.QueryCache)
    (hz : z ∈ support ((simulateQ HashSpec.romImpl (gameRun adversary)).run ∅))
    (h : ∃ entry ∈ z.1.2.1, entry.2 = none) :
    HashSig.FailedSearch searchPoint SearchMiss MAX_COUNTER_TRIALS z.2 := by
  -- The step holds for any keys: on the game's own keys, the kernel replay runs key generation.
  rw [gameRun_eq_keys_run] at hz
  exact failedSearch_of_mem_support_keys_run _ adversary z hz h

/-- **Some request of the game gets no signature with probability `<= (q + C) (1 - p)^(2^32)`.**

Take an adversary with at most `q` hash calls of its own and `r` signing requests in every run.

`C` bounds the scheme's calls for `r` requests.

`p` is the chance that one counter gives a codeword, about `2^-13.84`. -/
theorem signingFailure_le (adversary : Adversary) (q r : Nat)
    (h : HasAdversaryQueryBound adversary q r) :
    signingFailure adversary ≤
      ((q + schemeCalls r : Nat) : ℝ≥0∞) *
        (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ MAX_COUNTER_TRIALS := by
  have hT₁ : 1 ≤ MAX_COUNTER_TRIALS := by unfold MAX_COUNTER_TRIALS; norm_num
  calc signingFailure adversary
      = wp ((simulateQ HashSpec.romImpl (gameRun adversary)).run ∅)
          (fun z => propInd (∃ entry ∈ z.1.2.1, entry.2 = none)) := by
        rw [signingFailure, prEvent_eq_wp_propInd, StateT.run'_eq, wp_map]
        rfl
    -- A run with a request that got no signature ends with a failed search in its cache.
    _ ≤ wp ((simulateQ HashSpec.romImpl (gameRun adversary)).run ∅)
          (fun z => propInd
            (HashSig.FailedSearch searchPoint SearchMiss MAX_COUNTER_TRIALS z.2)) :=
        ExpectationWP.Lower.wp_mono_of_support _ fun z hz =>
          propInd_mono (failedSearch_of_mem_support_gameRun adversary z hz)
    -- The game is a map of the run, so it ends with the same cache.
    _ = wp ((simulateQ HashSpec.romImpl (gameCore adversary)).run ∅)
          (fun z => propInd
            (HashSig.FailedSearch searchPoint SearchMiss MAX_COUNTER_TRIALS z.2)) := by
        rw [gameCore_eq_map_gameRun, simulateQ_map, StateT.run_map, wp_map]
        rfl
    -- The game makes at most `q + C` hash calls.
    _ ≤ _ := wp_failedSearch_gameCore_le MAX_COUNTER_TRIALS hT₁ le_rfl adversary q r h

/-- Some request of the game gets no signature with probability at most `(q + C) exp(-2^18)`.

Take an adversary with at most `q` hash calls of its own and `r` signing requests in every run.

`C` bounds the scheme's calls for `r` requests. -/
theorem signingFailure_le_exp (adversary : Adversary) (q r : Nat)
    (h : HasAdversaryQueryBound adversary q r) :
    signingFailure adversary ≤
      ((q + schemeCalls r : Nat) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(2 ^ 18))) := by
  refine (signingFailure_le adversary q r h).trans ?_
  gcongr
  exact searchMiss_pow_le_exp

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
