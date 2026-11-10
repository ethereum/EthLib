module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnly
public import EthLib.Cryptography.Proofs.IndependentOutside

/-!
# Proofs: the key-only game with new forward answers asked of one oracle

Run the key-only forger on a fixed key, with independent answers to `Π`.

Ask each new forward answer of one outside oracle with no input, and log it with its query.

The run then ends with the forgery, the result of the check, the cache, the flag and the log.

With the key drawn uniformly, it wins with the chance of the game with independent answers.

The run logs at most one more pair than the forger asks for `Π` or its inverse.

When the outside oracle answered the conversion of a forgery, a replay fork can rewind there.

A later proof can split forgeries from forward and inverse pairs on this run.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The run is their Game G1 of Figure 7, in the proof of their Theorem 2.

It takes the forward change of their Game G2, lines 01 and 19: the values `β_1, …, β_Q`.

Here each is asked of the outside oracle when needed.

Their Game G2 also changes the inverse answers, in lines 26 to 28, which this run leaves out.

Their `Q` counts the query of the conversion, which their forger asks first.

Here the check may ask it, hence one more pair.
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
  /-- The new forward queries with their answers, the first one first. -/
  forward : List (A × A)

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

variable [FinEnum A]

/-- The run on the key `X`, with new forward answers asked outside, from the empty state. -/
def keyOnlyOutsideRun (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M) (X : G) :
    OracleComp (OutsideSpec A) (KeyOnlyTrace F A M) :=
  (fun r => ⟨r.1.1, r.1.2, r.2.1.1, r.2.1.2, r.2.2⟩) <$>
    (simulateQ outsideImpl (keyOnlyRunQ scheme adversary X)).run (([], false), [])

/-- The run logs at most `q + 1` pairs.

The forger must ask for `Π` or its inverse at most `q` times. -/
theorem length_forward_le_of_mem_support_keyOnlyOutsideRun (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M)
    (X : G) {q : ℕ} (hq : IsQueryBoundP (adversary.main X) (·.isRight = true) q)
    {tr : KeyOnlyTrace F A M} (htr : tr ∈ support (keyOnlyOutsideRun scheme adversary X)) :
    tr.forward.length ≤ q + 1 := by
  simp only [keyOnlyOutsideRun, support_map, Set.mem_image] at htr
  obtain ⟨r, hr, rfl⟩ := htr
  simpa using length_log_le_of_mem_support_simulateQ_outsideImpl
    (isQueryBoundP_keyOnlyRunQ scheme adversary X hq) _ r hr

variable [SampleableType F]

variable [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)]

/-- **The key-only game with independent answers, with new forward answers asked outside.**

Draw the key uniformly, and run the forger on it with the outside oracle uniform.

The check passes with no flag raised as often as the forger wins with independent answers. -/
theorem keyOnlyIndepAdvantage_eq_outside (scheme : Scheme F G A M)
    (adversary : KeyOnlyAdversary F G A M) :
    keyOnlyIndepAdvantage scheme adversary =
      Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
         let tr ← keyOnlyOutsideRun scheme adversary (x • scheme.g)}[
        tr.verified = true ∧ tr.bad = false] := by
  have hL : keyOnlyIndepExperiment scheme adversary =
      (fun z => z.1 && !z.2) <$> (do
        let x ← ($ᵗ F : ProbComp F)
        (fun r : ((M × F × F) × Bool) × IndepState A => (r.1.2, r.2.2)) <$>
          (simulateQ indepPermImpl (keyOnlyRunQ scheme adversary (x • scheme.g))).run
            ([], false)) := by
    rw [keyOnlyIndepExperiment, keyOnlyExperimentQ, simulateQ_bind, StateT.run_bind,
      simulateQ_passthrough_add_liftM_run]
    simp
  have hR : EvalDistEq
      (do
        let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
        (fun tr : KeyOnlyTrace F A M => (tr.verified, tr.bad)) <$>
          keyOnlyOutsideRun scheme adversary (x • scheme.g))
      (do
        let x ← ($ᵗ F : ProbComp F)
        (fun r : ((M × F × F) × Bool) × IndepState A => (r.1.2, r.2.2)) <$>
          (simulateQ indepPermImpl (keyOnlyRunQ scheme adversary (x • scheme.g))).run
            ([], false)) := by
    refine (evalDistEq_liftComp_uniform _).bind fun x => ?_
    have h := (simulateQ_outsideImpl_run_evalDistEq
      (keyOnlyRunQ scheme adversary (x • scheme.g)) ([], false) []).map (fun r => (r.1.2, r.2.2))
    simpa [keyOnlyOutsideRun, Functor.map_map] using h
  rw [keyOnlyIndepAdvantage, hL, prEvent_map, ← hR.prEvent_eq]
  congr 1
  simp [map_bind, Functor.map_map, Bool.and_eq_true]

end EthLib.Cryptography.Secp256k1.Security
