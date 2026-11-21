module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchLedger
public import VCVio.OracleComp.SimSemantics.StateT.Compensated

/-!
# Paying for adaptive pre-search probes on the deferred graph

Only a new physical word in a still-live signing key changes its price.

The actual shared graph supplies the uniform word used in that expected change.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger

open Constants HashSig OracleComp OracleSpec TwoLayerGraph CanonicalGraph.PairedQueries
  randomOracle.Partners
open RealClient.GraphPrefix RealClient.GraphPrefix.TrialGraphWatch
open scoped ENNReal Classical

noncomputable def total (keys : Finset Key) (f : Key → Entry → ℝ≥0∞) (h : History) :=
  ∑ k ∈ keys, f k (entry h.2 k h.1)

noncomputable abbrev av {α : Type} (p : ProbComp α) (f : α → ℝ≥0∞) :=
  ∑' x, Pr{let y ← p}[y = x] * f x

private theorem av_update {Note : Type} (pp : PublicParam) (cut : Note → Option Key)
    (t : (Spec Note).Domain) (st : D) (h : History) (f : History → ℝ≥0∞) :
    av ((handler pp cut t).run (st, h)) (fun z => f z.2.2) =
      av ((backend pp t).run st) (fun z => f (update pp cut t z.1 h)) := by
  rw [handler, QueryImpl.extendState_apply, bind_pure_comp, av, tsum_prEvent_map_mul]

private theorem fresh_avg {Note : Type} (pp : PublicParam) (cut : Note → Option Key)
    (a : HashInput) (real : MessageAt pp a) (st : D) (h : History) (sound : Sound pp (st, h))
    (cold : h.1.1 a = none) (f : History → ℝ≥0∞) :
    av ((handler pp cut (.inl (.inl (.inr a)))).run (st, h)) (fun z => f z.2.2) =
      freshMean (fun w => f (recordWordAt a w h)) := by
  obtain ⟨l, e, msg, r, enc⟩ := real
  have has : MessageAt pp a := ⟨l, e, msg, r, enc⟩
  have ⟨lo, hi⟩ := sound.rows a has
  simp only [cold, Option.map_none] at lo hi
  have law := trial_fresh pp a (enc ▸ isTrial_message pp l e msg r) st lo hi
  rw [av_update]
  simp only [backend]
  calc
    _ = av ((fun w => (w, recordWord PairedHashWord.halves a w st)) <$> ($ᵗ HashOutput)) _ := by
      exact tsum_congr fun z => congrArg (· * _) (law.prEvent_eq (· = z)).symm
    _ = _ := by
      rw [av, tsum_prEvent_map_mul]
      simp only [update, has, cold, and_self, ite_true]
      rfl

private theorem total_begin (keys : Finset Key) (f : Key → Entry → ℝ≥0∞)
    (h : History) (k : Key) : total keys f (h.1, begin h.2 k h.1) = total keys f h := by
  simp only [total, entry_begin]

private theorem unchanged_avg {Note : Type} (pp : PublicParam) (cut : Note → Option Key)
    (t : (Spec Note).Domain) (st : D) (h : History) (keys : Finset Key) (f : Key → Entry → ℝ≥0∞)
    (unchanged : ∀ w, total keys f (update pp cut t w h) = total keys f h) :
    av ((handler pp cut t).run (st, h)) (fun z => total keys f z.2.2) = total keys f h := by
  rw [av_update]
  exact tsum_prEvent_mul_of_const_on_support _ (fun _ _ => unchanged _)

/-- At every actual operation the expected increase in partnered selections is paid by the reserve.
-/
theorem step_price {Note : Type} (pp : PublicParam) (cut : Note → Option Key)
    (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32) (keys : Finset Key)
    (t : (Spec Note).Domain) (s : D × History) (sound : Sound pp s) :
    let value := total keys (searchMass pp c fuel)
    let reserve := total keys (searchReserve pp c fuel)
    av ((handler pp cut t).run s) (fun z => value z.2.2) + reserve s.2 ≤
      value s.2 + av ((handler pp cut t).run s) (fun z => reserve z.2.2) := by
  rcases s with ⟨st, h⟩
  intro value reserve
  have keep (t : (Spec Note).Domain)
      (eqn : ∀ f : Key → Entry → ℝ≥0∞, ∀ w, total keys f (update pp cut t w h) = total keys f h) :
      av ((handler pp cut t).run (st, h)) (fun z => value z.2.2) + reserve h ≤
        value h + av ((handler pp cut t).run (st, h)) (fun z => reserve z.2.2) := by
    dsimp only [value, reserve]
    rw [unchanged_avg pp cut t st h keys _ (eqn _), unchanged_avg pp cut t st h keys _ (eqn _)]
  rcases t with ((coin | a) | op) | note
  · exact keep (.inl (.inl (.inl coin))) fun _ _ => rfl
  · by_cases fresh : MessageAt pp a ∧ h.1.1 a = none
    · rw [fresh_avg pp cut a fresh.1 st h sound fresh.2,
        fresh_avg pp cut a fresh.1 st h sound fresh.2]
      exact snapshot_probe pp c fuel within keys h.2 h.1.1 h.1.2 sound.live a fresh.2
    · exact keep (.inl (.inl (.inr a))) fun _ _ => by simp only [update, fresh, ite_false]
  · exact keep (.inl (.inr op)) fun _ _ => rfl
  · apply keep (.inr note)
    intro f w
    cases key : cut note with
    | none => simp only [update, key]
    | some k => exact (show _ by simp only [update, key, total_begin])

private theorem reserve_finite (pp : PublicParam) (c fuel : Nat) (keys : Finset Key) (h : History) :
    total keys (searchReserve pp c fuel) h ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro k hk
  unfold searchReserve
  apply ENNReal.mul_ne_top (by norm_num)
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.sum_ne_top.mpr fun _ _ =>
      prEvent_ne_top _)

/-- The deferred graph pays all pre-search selection risks through one shared pair of expectations.

The computation can adapt to sampled words and may return early at the physical cutoff.
-/
theorem run_price {Note α : Type} (pp : PublicParam) (cut : Note → Option Key)
    (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32) (keys : Finset Key)
    (p : OracleComp (Spec Note) α) (s : D × History) (sound : Sound pp s) :
    let value := total keys (searchMass pp c fuel)
    let reserve := total keys (searchReserve pp c fuel)
    let run := (simulateQ (handler pp cut) p).run s
    (∑' z, Pr{let y ← run}[y = z] * value z.2.2) + reserve s.2 ≤
      value s.2 + ∑' z, Pr{let y ← run}[y = z] * reserve z.2.2 :=
  QueryImpl.run_compensated (handler pp cut) (Sound pp) (sound_step pp cut)
    (fun st => total keys (searchMass pp c fuel) st.2) (fun st =>
      total keys (searchReserve pp c fuel) st.2)
    (fun st _ => reserve_finite pp c fuel keys st.2)
      (step_price pp cut c fuel within keys) p s sound

/-- Two physical counts pay the total selection mass from the genuine empty shared state. -/
theorem empty_price {Note α : Type} (pp : PublicParam) (cut : Note → Option Key)
    (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32) (keys : Finset Key) (p : OracleComp (Spec Note) α) :
    let rate : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
    let ε : ℝ≥0∞ := 1 / 2 ^ 128
    let run := (simulateQ (handler pp cut) p).run (((∅, ∅), []), ((∅, ∅), fun _ => none))
    let n := total keys (fun k h => inputCount pp k h)
    let v := total keys (fun k h => validCount pp k h)
    rate * (∑' z, Pr{let y ← run}[y = z] * total keys (searchMass pp c fuel) z.2.2) ≤
      ε * (∑' z, Pr{let y ← run}[y = z] * (v z.2.2 * (rate * n z.2.2 + (1-rate) * v z.2.2))) := by
  intro rate ε run n v
  let initial : D × History := (((∅, ∅), []), ((∅, ∅), fun _ => none))
  have price := run_price pp cut c fuel within keys p initial (sound_empty pp)
  have emptyMass : total keys (searchMass pp c fuel) initial.2 = 0 := by
    simp [initial, total, searchMass, activeMessages, entry, partneredSelections]
  have emptyReserve : total keys (searchReserve pp c fuel) initial.2 = 0 := by
    simp [initial, total, searchReserve, validInputs, entry]
  dsimp only at price
  rw [emptyReserve, emptyMass, add_zero, zero_add] at price
  refine (mul_le_mul_right price rate).trans ?_
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply tsum_le_tsum
  intro z
  change rate * (Pr{let u ← run}[u = z] * total keys (searchReserve pp c fuel) z.2.2) ≤
    ε * (Pr{let u ← run}[u = z] * (v z.2.2 * (rate * n z.2.2 + (1-rate) * v z.2.2)))
  by_cases reached : z ∈ support run
  · have sound := simulateQ_run_preservesInv _ _ (sound_step pp cut) p initial
      (sound_empty pp) z reached
    have final (k : Key) : Covered (entry z.2.2.2 k z.2.2.1) := by
      cases saved : z.2.2.2 k with
      | none => simpa [entry, saved] using sound.live
      | some old => simpa [entry, saved] using sound.saved k old saved
    rw [mul_left_comm rate, mul_left_comm ε]
    apply mul_le_mul_right
    exact reserve_le_product pp c fuel within keys _ (fun k _ => final k)
  · simp only [prEvent_eq_zero_of_not_mem_support run reached, zero_mul, mul_zero, le_refl]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger
