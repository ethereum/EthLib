module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialMoment
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.WatchedCost

/-!
# Fresh message trials before the signer registers a digest

The leanXMSS draft in "Security" charges every public hash from key generation through verification.

The "WOTS+C" signing algorithm uses the first codeword in the trial window.

A fresh word at a message key with no registered digest gives one trial for the second moment.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch.Trials

open Constants HashSig OracleComp OracleSpec CachedCodeword PostSigning
open scoped ENNReal

/-- A cold message input at a key without a registered digest. -/
@[expose] noncomputable def eligible (pp : PublicParam) :
    WatchQueries.Domain → (WatchState × Nat) → Bool
  | .inl (.inr b), st =>
    (st.1.cache b).isNone && (messageKey pp b).any (fun k => (st.1.target k).isNone)
  | _, _ => false

/-- A message trial succeeds when the low digest of its actual full reply is a codeword. -/
@[expose] def validReply : (t : WatchQueries.Domain) → WatchQueries.Range t → Bool
  | .inl (.inr _), w => (digits w).isSome
  | _, _ => false

/-- Add success and trial counts to the registration watch and the original physical hash meter. -/
noncomputable abbrev handler (pp : PublicParam) (q : ℕ) :=
  BernoulliMoment.observe (randomOracle.Targets.counted (record pp) (messageKey pp) low)
    q (eligible pp) validReply

/-- A fresh eligible step at either layer accepts with the native codeword fraction. -/
theorem counts (pp : PublicParam) (q : ℕ) :
    BernoulliMoment.CountsTrials (handler pp q) (fun s => s.2.1) (fun s => s.2.2)
      TrialMoment.rate q := by
  apply BernoulliMoment.counts_observe
  rintro ((i | b) | notice) s active
  · contradiction
  · obtain ⟨cold, _⟩ := Bool.and_eq_true_iff.mp active
    rw [Option.isNone_iff_eq_none] at cold
    have hit (w : HashOutput) : (digits w).isSome = true ↔ w ∈ accepted := (mem_accepted w).symm
    simpa only [randomOracle.Targets.counted, QueryImpl.extendState_apply,
      randomOracle.Targets.public_run, randomOracle.run_eq, cold, bind_pure_comp, map_bind,
      bind_map_left, map_pure, validReply, prEvent_norm, hit] using TrialMoment.fresh_rate
  · contradiction

/-- Generate the real master seed and public key and retain the cache and hash count. -/
@[expose] noncomputable def initialKey :
    ProbComp (Seed × PublicKey × HashSpec.QueryCache × Nat) := do
  let z ← (simulateQ randomOracle.Targets.publicMeter
    (liftM XmssSecurity.sampleMasterSeed : OracleComp World _)).run (∅, 0)
  let H := hashOf (QueryImpl.id' World)
  let raw := ofSeed z.1
  let keyed ← (simulateQ randomOracle.Targets.publicMeter
    (schemeSeed H raw >>= fun x => publicKeyOf H (seedPrf H x))).run z.2
  return (raw, keyed)

/-- Continue the native client and verifier from the key generator's actual parameter and cache. -/
@[expose] noncomputable def game (A : Adversary) (q : Nat) :
    ProbComp (Outcome × (WatchState × Nat) × Nat × Nat) := do
  let (raw, pk, cache, paid) ← initialKey
  let H := hashOf (QueryImpl.id' World)
  (simulateQ (handler pk.publicParam q)
    (afterKey (QueryImpl.id' World) (schemeSeed H raw) (seedPrf H) A pk)).run
    ((⟨cache, fun _ => none, 0, false⟩, paid), 0, 0)

/-- Removing the trial counts keeps the original outcome, registration state and physical cost. -/
theorem erase_game (A : Adversary) (q : Nat) :
    Prod.map id Prod.fst <$> game A q = countedGame A := by
  simp only [game, initialKey, countedGame, countedSource, map_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro seed
  apply bind_congr
  intro keyed
  exact extendState_run_proj_eq _ _ _ _ _

/-- Price the fresh, unregistered trials on the genuine seeded adversary and signing run.

Both expectations retain the outcome, cache, registered digests and number of physical hash calls.
-/
theorem expected_game_product (A : Adversary) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    let m := game A q
    (∑' z, Pr{let u ← m}[u = z] * ENNReal.ofReal
      ((z.2.2.2 / TrialMoment.rate) * z.2.2.1 +
        (1 - TrialMoment.rate) * (z.2.2.2 / TrialMoment.rate) ^ 2)) ≤
      ENNReal.ofReal ((2 - TrialMoment.rate) * q + 2 ^ 76) *
        ∑' z, Pr{let u ← m}[u = z] * (z.2.2.1 : ℝ≥0∞) := by
  let (t : unifSpec.Domain) : Finite (unifSpec.Range t) :=
    OracleSpec.UniformAnswerMeasure.finite_range t
  dsimp only [game]
  rw [tsum_prEvent_bind_mul, tsum_prEvent_bind_mul]
  let w := ENNReal.ofReal ((2 - TrialMoment.rate) * q + 2 ^ 76)
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun z => ?_
  rcases z with ⟨raw, pk, cache, paid⟩
  dsimp only
  rw [mul_left_comm]
  gcongr
  exact TrialMoment.expected_product_of_counts _ _ _ q hq (counts pk.publicParam q)
    _ ((⟨cache, fun _ => none, 0, false⟩, paid), 0, 0) rfl rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch.Trials
