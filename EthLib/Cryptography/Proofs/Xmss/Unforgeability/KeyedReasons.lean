module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.IdealFailure
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.KeyedSigner

/-!
# Proofs: a signer that keeps its key and tells why signing failed

This is the game of the signer that replies with its whole result, its error included.

Its signer keeps its key across requests, as the theorem's game does.

The game with the stateless signer wins as often, and fails a request as often.

So its bounds hold here: the forgery bound plus that of a failure, and the bound of a failure.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open XmssSecurity (OracleWorld HashSpec romImpl)
open DeterministicSigning (Resolves resolves_of_run cache_le_of_run)

/-- `H` in the game, on the hash oracle alone. -/
local notation "Hh" => (queryH : Array UInt64 → OracleComp HashSpec Lanes4)

/-! ## The game -/

/-- `Sig(sk, idx, m)` on each request, its error included, with the key the last request returned.

The log records whether it succeeded, as the winning rule needs. -/
def reasonSigningOracle : QueryImpl ReasonSigningSpec
    (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) :=
  fun request => StateT.mk fun sk => WriterT.mk
    ((fun result => ((result.1, result.2), [⟨request, result.1.toOption⟩])) <$>
      liftM (signWith H sk request.leafIndex request.message))

/-- The game up to its result: keys, the adversary with its log, then the verification. -/
noncomputable def reasonRun (adversary : ReasonAdversary) :
    OracleComp OracleWorld (Forgery × QueryLog SigningSpec × Bool) := do
  let seed ← liftM sampleSeed
  let (pk, sk) ← liftM (keyGenWith H seed)
  let (((forgery, _), log) : (Forgery × SecretKey) × QueryLog SigningSpec) ←
    ((simulateQ (QueryImpl.ofLift OracleWorld
      (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) +
        reasonSigningOracle) (adversary.main pk)).run sk).run
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return (forgery, log, verified)

/-- The game against the counted random oracle of the theorem, from an empty cache. -/
noncomputable def reasonExperiment (adversary : ReasonAdversary) :
    ProbComp ((Forgery × QueryLog SigningSpec × Bool) × Nat) :=
  (simulateQ countedOracle (reasonRun adversary)).run.run' ∅

/-- The probability that the adversary forges, under the winning rule of the theorem. -/
noncomputable def reasonForgeAdvantage (adversary : ReasonAdversary) : ℝ≥0∞ :=
  Pr{let result ← reasonExperiment adversary}[
    (Valid result.1.2.1 ∧ ¬Contains result.1.2.1 result.1.1) ∧ result.1.2.2 = true]

/-- The probability that some signing request of the game fails. -/
noncomputable def signingFailure (adversary : ReasonAdversary) : ℝ≥0∞ :=
  Pr{let result ← reasonExperiment adversary}[∃ entry ∈ result.1.2.1, entry.2 = none]

/-! ## The game wins as the stateless one -/

/-- The game's oracles: coins and hashes pass through, and a request signs with the kept key. -/
abbrev keyedReasonOracles : QueryImpl (OracleWorld + ReasonSigningSpec)
    (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) :=
  QueryImpl.ofLift OracleWorld
    (StateT SecretKey (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) +
      reasonSigningOracle

/-- The oracles of the game with the stateless signer. -/
abbrev statelessReasonOracles (seed : Seed) : QueryImpl (OracleWorld + ReasonSigningSpec)
    (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
    statelessReasonSigningOracle seed

section Oracles

variable {seed : Seed} {sk : SecretKey} {cache : QueryCache HashSpec}

/-- A coin or hash query of the game passes through, and leaves the key as it is. -/
theorem run_keyedReasonOracles_inl (t : OracleWorld.Domain) (sk : SecretKey) :
    ((keyedReasonOracles (.inl t)).run sk).run =
      (fun u => ((u, sk), [])) <$> (liftM (OracleWorld.query t) : OracleComp OracleWorld _) := by
  simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
  rfl

/-- A coin or hash query of the stateless game passes through. -/
theorem run_statelessReasonOracles_inl (seed : Seed) (t : OracleWorld.Domain) :
    (statelessReasonOracles seed (.inl t)).run =
      (fun u => (u, [])) <$> (liftM (OracleWorld.query t) : OracleComp OracleWorld _) := by
  simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
  rfl

/-- A request of the game signs with the kept key, and replies with the whole result. -/
theorem run_keyedReasonOracles_inr (request : SignRequest) (sk : SecretKey) :
    ((keyedReasonOracles (.inr request)).run sk).run =
      (fun r => ((r.1, r.2), ([⟨request, r.1.toOption⟩] : QueryLog SigningSpec))) <$>
        (liftM (signWith H sk request.leafIndex request.message) : OracleComp OracleWorld _) :=
  rfl

/-- A request of the stateless game signs from the seed, and replies alike. -/
theorem run_statelessReasonOracles_inr (seed : Seed) (request : SignRequest) :
    (statelessReasonOracles seed (.inr request)).run =
      (fun r => (r, ([⟨request, r.toOption⟩] : QueryLog SigningSpec))) <$>
        (liftM (statelessSignWith H seed request.leafIndex request.message) :
          OracleComp OracleWorld _) :=
  rfl

/-- Each query answers alike in the two games, once the key is forgotten. -/
theorem keyedReasonOracles_step (h : KeyInv seed sk cache)
    (q : (OracleWorld + ReasonSigningSpec).Domain) :
    dropState <$> (simulateQ romImpl ((keyedReasonOracles q).run sk).run).run cache =ᵈ
      (simulateQ romImpl (statelessReasonOracles seed q).run).run cache := by
  rcases q with t | request
  · rw [run_keyedReasonOracles_inl, run_statelessReasonOracles_inl, simulateQ_map, simulateQ_map,
      StateT.run_map, StateT.run_map, Functor.map_map]
    exact EvalDistEq.rfl
  · rw [run_keyedReasonOracles_inr, run_statelessReasonOracles_inr]
    rw [simulateQ_map, simulateQ_map, StateT.run_map, StateT.run_map, Functor.map_map]
    have he := (evalDistEq_signWith h request.leafIndex request.message).map
      (Prod.map (fun r : Except XmssError Signature =>
        (r, ([⟨request, r.toOption⟩] : QueryLog SigningSpec))) id)
    rw [Functor.map_map] at he
    exact he

/-- Each query of the game returns a key that the cache after it knows. -/
theorem keyedReasonOracles_inv (h : KeyInv seed sk cache)
    (q : (OracleWorld + ReasonSigningSpec).Domain) :
    ∀ x ∈ support ((simulateQ romImpl ((keyedReasonOracles q).run sk).run).run cache),
      KeyInv seed x.1.1.2 x.2 := by
  intro x hx
  rcases q with t | request
  · rw [run_keyedReasonOracles_inl, simulateQ_map, StateT.run_map, support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [simulateQ_spec_query] at hy
    exact h.mono (XmssSecurity.romImpl_query_cache_le _ _ _ hy)
  · rw [run_keyedReasonOracles_inr] at hx
    rw [simulateQ_map, StateT.run_map, support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact keyInv_of_mem_support_signWith h hy

end Oracles

/-- The game's result, once the adversary returned its forgery with the log. -/
noncomputable def checkReason (pk : PublicKey) (y : Forgery × QueryLog SigningSpec) :
    OracleComp OracleWorld (Forgery × QueryLog SigningSpec × Bool) := do
  let verified ← liftM (verifyWith H pk y.1.message y.1.signature)
  return (y.1, y.2, verified)

/-- The game's result, its seed drawn, with the keys of key generation. -/
noncomputable def keyedReasonRun (adversary : ReasonAdversary) (seed : Seed) :
    OracleComp OracleWorld (Forgery × QueryLog SigningSpec × Bool) :=
  (liftM (keyGenWith Hh seed) : OracleComp OracleWorld _) >>= fun p =>
    ((simulateQ keyedReasonOracles (adversary.main p.1)).run p.2).run >>= fun x =>
      checkReason p.1 (x.1.1, x.2)

/-- The result of the game with the stateless signer, its seed drawn. -/
noncomputable def statelessReasonRunOf (adversary : ReasonAdversary) (seed : Seed) :
    OracleComp OracleWorld (Forgery × QueryLog SigningSpec × Bool) :=
  (liftM (keyGenWith Hh seed) : OracleComp OracleWorld _) >>= fun p =>
    (simulateQ (statelessReasonOracles seed) (adversary.main p.1)).run >>= checkReason p.1

/-- The game draws a seed, then runs from that seed. -/
theorem reasonRun_eq_bind (adversary : ReasonAdversary) :
    reasonRun adversary = liftM sampleSeed >>= keyedReasonRun adversary :=
  rfl

/-- The stateless game draws a seed, then runs from that seed. -/
theorem statelessReasonRun_eq_bind (adversary : ReasonAdversary) :
    statelessReasonRun adversary = liftM sampleSeed >>= statelessReasonRunOf adversary := by
  unfold statelessReasonRun statelessReasonRunOf
  refine bind_congr fun seed => ?_
  rw [statelessKeyGenWith_eq, XmssSecurity.Bridge.liftM_hash_map, bind_map_left]
  rfl

/-- **The game's result has the distribution of the stateless signer's game.** -/
theorem evalDistEq_reasonRun (adversary : ReasonAdversary) :
    (simulateQ romImpl (reasonRun adversary)).run' ∅ =ᵈ
      (simulateQ romImpl (statelessReasonRun adversary)).run' ∅ := by
  rw [reasonRun_eq_bind, statelessReasonRun_eq_bind, XmssSecurity.Seeded.run'_lift_sample_bind,
    XmssSecurity.Seeded.run'_lift_sample_bind]
  refine EvalDistEq.bind_right _ fun seed => ?_
  unfold keyedReasonRun statelessReasonRunOf
  rw [run'_romImpl_bind, run'_romImpl_bind]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun b hb => ?_
  exact evalDistEq_run_bind seed keyedReasonOracles (statelessReasonOracles seed)
    (fun q _ _ hs => keyedReasonOracles_step hs q) (fun q _ _ hs => keyedReasonOracles_inv hs q)
    (adversary.main b.1.1) b.1.2 b.2 (keyInv_of_mem_support_keyGenWith hb) _ _ fun _ => rfl

/-- The game forges as often as the stateless signer's game. -/
theorem reasonForgeAdvantage_eq_stateless (adversary : ReasonAdversary) :
    reasonForgeAdvantage adversary = statelessReasonForgeAdvantage adversary := by
  unfold reasonForgeAdvantage statelessReasonForgeAdvantage reasonExperiment
    statelessReasonExperiment
  let P := fun x : Forgery × QueryLog SigningSpec × Bool =>
    (Valid x.2.1 ∧ ¬Contains x.2.1 x.1) ∧ x.2.2 = true
  exact (prEvent_countedOracle (reasonRun adversary) P).trans
    (((evalDistEq_reasonRun adversary).prEvent_eq P).trans
      (prEvent_countedOracle (statelessReasonRun adversary) P).symm)

/-- Some request fails as often as in the stateless signer's game. -/
theorem signingFailure_eq_stateless (adversary : ReasonAdversary) :
    signingFailure adversary = statelessSigningFailure adversary := by
  unfold signingFailure statelessSigningFailure reasonExperiment statelessReasonExperiment
  let P := fun x : Forgery × QueryLog SigningSpec × Bool => ∃ entry ∈ x.2.1, entry.2 = none
  exact (prEvent_countedOracle (reasonRun adversary) P).trans
    (((evalDistEq_reasonRun adversary).prEvent_eq P).trans
      (prEvent_countedOracle (statelessReasonRun adversary) P).symm)

/-! ## The bounds -/

/-- **The signer's reasons cost at most the probability of a failure.**

The adversary forges at most as often as its reduction, plus the probability of a failure.

The reduction plays the theorem's game. -/
theorem reasonForgeAdvantage_le (adversary : ReasonAdversary) :
    reasonForgeAdvantage adversary
      ≤ forgeAdvantage (hideReasons adversary) + signingFailure adversary := by
  rw [reasonForgeAdvantage_eq_stateless, signingFailure_eq_stateless,
    forgeAdvantage_eq_statelessForgeAdvantage]
  exact statelessReasonForgeAdvantage_le adversary

/-- **leanXMSS with a signer that reveals its reasons.**

Take an adversary whose reduction to the theorem's game has a budget of `q >= 1` hash calls.

It forges with probability at most `q / 2^127`, plus the probability that a request fails. -/
theorem reasonForgeAdvantage_le_add (q : Nat) (hq : 1 ≤ q) (adversary : ReasonAdversary)
    (hbound : HasHashQueryBound (hideReasons adversary) q) :
    reasonForgeAdvantage adversary
      ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞) + signingFailure adversary :=
  (reasonForgeAdvantage_le adversary).trans
    (add_le_add_left (unforgeable q hq _ hbound) _)

/-- **The failure of some signing request.**

The adversary makes at most `qH` hash queries and `r` signing requests.

Let `Q` be the bound on the calls of the game with the stateless signer, for `qH` and `r`.

Some request fails with probability at most `2 Q / 2^256 + r (Q / 2^95 + 2 exp(-4000))`. -/
theorem signingFailure_le (adversary : ReasonAdversary) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    signingFailure adversary ≤
      2 * (gameQueries qH r : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
        r * ((gameQueries qH r : ℝ≥0∞) / 2 ^ 95 + 2 * ENNReal.ofReal (Real.exp (-4000))) := by
  rw [signingFailure_eq_stateless]
  exact statelessSigningFailure_le adversary hh hr

/-- **leanXMSS with a signer that reveals its reasons, with its failure term bounded.**

Take an adversary whose reduction to the theorem's game has a budget of `q >= 1` hash calls.

The adversary itself makes at most `qH` hash queries and `r` signing requests.

Let `Q` be the budget of the game's hash calls, with the stateless signer, for the same adversary.

The bound says nothing from about `2^31` requests, since its last term is quadratic in `r`.

It forges with probability at most `q / 2^127 + 2 Q / 2^256 + r (Q / 2^95 + 2 exp(-4000))`. -/
theorem reasonForgeAdvantage_le_bounded (q : ℕ) (hq : 1 ≤ q) (adversary : ReasonAdversary)
    (hbound : HasHashQueryBound (hideReasons adversary) q) {qH r : ℕ}
    (hh : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryHash qH)
    (hr : ∀ pk, IsQueryBoundP (adversary.main pk) IsAdversaryRequest r) :
    reasonForgeAdvantage adversary ≤
      q / ((2 ^ 127 : ℕ) : ℝ≥0∞) + (2 * (gameQueries qH r : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
        r * ((gameQueries qH r : ℝ≥0∞) / 2 ^ 95 + 2 * ENNReal.ofReal (Real.exp (-4000)))) :=
  (reasonForgeAdvantage_le_add q hq adversary hbound).trans
    (add_le_add_right (signingFailure_le adversary hh hr) _)

end EthLib.Cryptography.Xmss.Unforgeability
