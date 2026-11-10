module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnly
public import EthLib.Cryptography.Proofs.IndependentOverlay

/-!
# Proofs: the key-only game with new forward answers asked of one oracle

Run the key-only forger on a fixed key, with independent answers to `Π`.

Ask each new forward answer of one outside oracle with no input, and log the query.

The run then ends with the forgery, the result of the check, the cache, the flag and the log.

With the key drawn uniformly, it wins with the chance of the game with independent answers.

The forking lemma can rewind this run at the query that answered the forgery's conversion.

The run asks the outside oracle at most once more than the forger asks `Π` or its inverse.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

This is their algorithm `A` of Figure 8, in the proof of their Theorem 2, before its aborts.

Its answers to new forward queries are their values `β_1, …, β_Q`, asked one at a time.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

/-- The end of a run of a key-only forger with new forward answers asked outside. -/
structure KeyOnlyTrace (F A M : Type) where
  /-- The message and the claimed signature `(t, s)`. -/
  forgery : M × F × F
  /-- Whether the check of the forgery passed. -/
  verified : Bool
  /-- The pairs of `Π` answered, the most recent first. -/
  cache : PermCache A
  /-- Whether a new answer repeated a cached value in the direction of its query. -/
  bad : Bool
  /-- The new forward queries, the first one first. -/
  forward : List A

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A key-only forger on the key `X`, then the check of its forgery, which may ask for `Π`. -/
def keyOnlyRunQ (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M) (X : G) :
    PermComp A ((M × F × F) × Bool) := do
  let z ← adversary.main X
  let b ← verifyQ scheme X z.1 z.2.1 z.2.2
  pure (z, b)

/-- The run asks for `Π` or its inverse at most once more than the forger. -/
theorem isQueryBoundP_keyOnlyRunQ (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) (X : G) {q : ℕ}
    (hq : IsQueryBoundP (adversary.main X) (·.isRight = true) q) :
    IsQueryBoundP (keyOnlyRunQ scheme adversary X) (·.isRight = true) (q + 1) := by
  have h := isQueryBoundP_bind hq fun z _ =>
    isQueryBoundP_bind (isQueryBoundP_verifyQ scheme X z.1 z.2.1 z.2.2) fun b _ =>
      isQueryBoundP_pure (fun t : (unifSpec + PermSpec A).Domain => t.isRight = true)
        ((z, b) : (M × F × F) × Bool) 0
  simpa [keyOnlyRunQ] using h

variable [FinEnum A]

/-- The run on the key `X`, with new forward answers asked outside, from the empty state. -/
def keyOnlyOverlay (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M) (X : G) :
    OracleComp (OverlaySpec A) (KeyOnlyTrace F A M) :=
  (fun r => ⟨r.1.1, r.1.2, r.2.1.1, r.2.1.2, r.2.2⟩) <$>
    (simulateQ overlayImpl (keyOnlyRunQ scheme adversary X)).run (([], false), [])

/-- The run logs at most `q + 1` new forward queries, when the forger asks `Π` at most `q` times. -/
theorem length_forward_le (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M)
    (X : G) {q : ℕ} (hq : IsQueryBoundP (adversary.main X) (·.isRight = true) q)
    {tr : KeyOnlyTrace F A M} (htr : tr ∈ support (keyOnlyOverlay scheme adversary X)) :
    tr.forward.length ≤ q + 1 := by
  simp only [keyOnlyOverlay, support_map, Set.mem_image] at htr
  obtain ⟨r, hr, rfl⟩ := htr
  simpa using length_log_le_of_mem_support_simulateQ_overlayImpl
    (isQueryBoundP_keyOnlyRunQ scheme adversary X hq) _ r hr

variable [SampleableType F]

omit [FinEnum A] in
/-- The key-only game draws the key, then runs the forger and the check on it. -/
theorem keyOnlyExperimentQ_eq (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M) :
    keyOnlyExperimentQ scheme adversary =
      (do
        let x ← (liftM ($ᵗ F : ProbComp F) : PermComp A F)
        Prod.snd <$> keyOnlyRunQ scheme adversary (x • scheme.g)) := by
  simp [keyOnlyExperimentQ, keyOnlyRunQ]

variable [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)]

/-- **The key-only game with independent answers, with new forward answers asked outside.**

Draw the key uniformly, and run the forger on it with the outside oracle uniform.

The check passes with no flag raised as often as the forger wins with independent answers. -/
theorem keyOnlyIndepAdvantage_eq_overlay (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) :
    keyOnlyIndepAdvantage scheme adversary =
      Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OverlaySpec A)
         let tr ← keyOnlyOverlay scheme adversary (x • scheme.g)}[
        tr.verified = true ∧ tr.bad = false] := by
  have hL : keyOnlyIndepExperiment scheme adversary =
      (fun z => z.1 && !z.2) <$> (do
        let x ← ($ᵗ F : ProbComp F)
        (fun r : ((M × F × F) × Bool) × IndepState A => (r.1.2, r.2.2)) <$>
          (simulateQ indepPermImpl (keyOnlyRunQ scheme adversary (x • scheme.g))).run
            ([], false)) := by
    rw [keyOnlyIndepExperiment, keyOnlyExperimentQ_eq, simulateQ_bind, StateT.run_bind,
      simulateQ_indepPermImpl_liftM_run]
    simp
  have hR : EvalDistEq
      (do
        let x ← liftComp ($ᵗ F : ProbComp F) (OverlaySpec A)
        (fun tr : KeyOnlyTrace F A M => (tr.verified, tr.bad)) <$>
          keyOnlyOverlay scheme adversary (x • scheme.g))
      (do
        let x ← ($ᵗ F : ProbComp F)
        (fun r : ((M × F × F) × Bool) × IndepState A => (r.1.2, r.2.2)) <$>
          (simulateQ indepPermImpl (keyOnlyRunQ scheme adversary (x • scheme.g))).run
            ([], false)) := by
    refine (evalDistEq_liftComp_uniform _).bind fun x => ?_
    have h := (simulateQ_overlayImpl_run_evalDistEq
      (keyOnlyRunQ scheme adversary (x • scheme.g)) ([], false) []).map (fun r => (r.1.2, r.2.2))
    simpa [keyOnlyOverlay, Functor.map_map] using h
  rw [keyOnlyIndepAdvantage, hL, prEvent_map, ← hR.prEvent_eq]
  congr 1
  simp [map_bind, Functor.map_map, Bool.and_eq_true]

end EthLib.Cryptography.Secp256k1.Security
