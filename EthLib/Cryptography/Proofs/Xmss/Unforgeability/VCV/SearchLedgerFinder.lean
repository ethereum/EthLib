module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchLedger
public import VCVio.OracleComp.SimSemantics.StateT.RestrictedProjection

/-!
# Run the native finder on the watched graph's physical message words

The first-search estimate uses the cache at the end of the finder.

Both cold and warm runs reproduce the native finder's complete reply and this full-word table.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger

open Constants HashSig OracleComp OracleSpec CachedCodeword TwoLayerGraph
  CanonicalGraph.PairedQueries
open RealClient.GraphPrefix RealClient.GraphPrefix.TrialGraphWatch
open scoped ENNReal Classical

/-- The genuine full-word public port of the watched graph. -/
def publicWords {Note : Type} : QueryImpl HashSpec (OracleComp (Spec Note)) :=
  fun b => liftM ((Spec Note).query (.inl (.inl (.inr b))))

/-- Each byte hash makes exactly one full-word request to that port. -/
def messageHash {Note : Type} (bytes : ByteArray) : OracleComp (Spec Note) (Vector UInt8 32) :=
  simulateQ publicWords (CachedCodeword.hash bytes)

private theorem native_role (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (r : Randomizer)
    (c fuel : Nat) : (Internal.findCodeword CachedCodeword.hash pp l e m r c fuel).AllQueriesSatisfy
      (MessageAt pp) := by
  rw [findCodeword_eq_scan, ← bind_pure_comp]
  apply allQueriesSatisfy_bind _ (fun _ => allQueriesSatisfy_pure _ _)
  generalize (List.range' c fuel).map (trialRandomizer r) = trials
  induction trials with
  | nil => exact allQueriesSatisfy_pure _ _
  | cons v vs ih =>
    rw [AcceptedScan.scanWithAnswer, allQueriesSatisfy_query_bind_iff]
    exact ⟨⟨l, e, m, v, rfl⟩, fun w =>
      by split <;> first | exact ih | exact allQueriesSatisfy_pure _ _⟩

private theorem query_word {Note : Type} (pp : PublicParam) (cut : Note → Option Key)
    (a : HashInput) (real : MessageAt pp a) (s : D × History) (sound : Sound pp s) :
    (Prod.map id (fun z : D × History => z.2.1.1) <$>
      (((handler pp cut) ∘ₛ publicWords) a).run s) =ᵈ (HashSpec.randomOracle a).run s.2.1.1 := by
  obtain ⟨st, h⟩ := s
  obtain ⟨l, e, m, r, enc⟩ := real
  have trial : IsTrial a := enc ▸ isTrial_message pp l e m r
  have mem : MessageAt pp a := ⟨l, e, m, r, enc⟩
  obtain ⟨low, high⟩ := sound.rows a mem
  simp only [QueryImpl.compose, publicWords, simulateQ_spec_query, handler,
      QueryImpl.extendState_apply,
    bind_pure_comp, Functor.map_map, backend]
  cases hw : h.1.1 a with
  | none =>
    simp only [hw, Option.map_none] at low high
    apply EvalDistEq.of_forall_prEvent_eq
    intro event
    simp only [update, mem, hw, and_self, ite_true, recordWordAt, Prod.map, id_eq,
      randomOracle.run_eq, bind_pure_comp, prEvent_norm]
    rw [← (trial_fresh pp a trial st low high).prEvent_eq]
    simp only [prEvent_norm, SampleableType.prEvent_uniformSample]
  | some w =>
    simp only [hw, Option.map_some] at low high
    rw [trial_warm pp a trial st w low high, map_pure]
    simp [update, hw]

/-- Restrict adaptive public queries to message addresses at the current parameter.

The answers and final physical cache then match the ordinary full-word random oracle.
-/
theorem message_program {Note α : Type} (pp : PublicParam) (cut : Note → Option Key)
    (p : OracleComp HashSpec α) (domain : p.AllQueriesSatisfy (MessageAt pp))
    (s : D × History) (sound : Sound pp s) :
    (Prod.map id (fun st : D × History => st.2.1.1) <$>
      (simulateQ (handler pp cut) (simulateQ publicWords p)).run s) =ᵈ
      (simulateQ HashSpec.randomOracle p).run s.2.1.1 := by
  rw [← QueryImpl.simulateQ_compose]
  apply domain.evalDist_map_run _ _ _ (Sound pp) _ (query_word pp cut) s sound
  intro t _ st hs z hz
  exact sound_step pp cut (.inl (.inl (.inr t))) st hs z (by simpa only [QueryImpl.compose,
      publicWords, simulateQ_spec_query] using hz)

/-- The shared graph finder returns the same optional codeword and full-word message cache. -/
theorem finder_words {Note : Type} (pp : PublicParam) (cut : Note →
    Option Key) (l : Layer) (e : UInt32)
    (m : ByteArray) (r : Randomizer) (c fuel : Nat) (s : D × History) (sound : Sound pp s) :
    (Prod.map id (fun st : D × History => st.2.1.1) <$>
      (simulateQ (handler pp cut) (Internal.findCodeword messageHash pp l e m r c fuel)).run s) =ᵈ
      (simulateQ HashSpec.randomOracle
        (Internal.findCodeword CachedCodeword.hash pp l e m r c fuel)).run s.2.1.1 := by
  have law := message_program pp cut _ (native_role pp l e m r c fuel) s sound
  rwa [findCodeword_map_monad (simulateQ publicWords) (fun a => simulateQ_pure _ a)
    (fun a f => simulateQ_bind _ a f)] at law

/-- Price the native graph search at a newly sampled low private word.

The event checks for a partner in the actual final ledger, including the last query.
-/
theorem fresh_finder_booked {Note : Type} (pp : PublicParam) (cut : Note → Option Key)
    (l : Layer) (e : UInt32) (m : ByteArray) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (s : D × History) (sound : Sound pp s) :
    let run := do
      let low ← $ᵗ BitVec digestBits
      (simulateQ (handler pp cut) (Internal.findCodeword messageHash pp l e m
        (ofBV 16 low) c fuel)).run s
    let event := fun z => ∃ rho digits, z.1 = some (rho, digits) ∧
      EarlierDigest.Partner pp z.2.2.1.1 (trialInput pp l e m rho)
    (CODE_SIZE / 2 ^ 128 : ℝ≥0∞) * Pr{let z ← run}[event z] ≤
      (2 ^ 128)⁻¹ * (searchMass pp c fuel (l,e) s.2.1 + validCount pp (l,e) s.2.1) := by
  intro run event
  have exactEvent : Pr{let z ← run}[event z] = freshStopped pp l e m c fuel s.2.1.1 := by
    rw [freshStopped, prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
    apply tsum_congr
    intro low
    apply congrArg (fun v => _ * v)
    let r := ofBV 16 low
    have eq := (finder_words pp cut l e m r c fuel s sound).prEvent_eq
      (fun z => ∃ rho d, z.1 = some (rho,d) ∧
        EarlierDigest.Partner pp z.2 (trialInput pp l e m rho))
    simp only [prEvent_norm] at eq
    refine eq.trans ?_
    simp only [selected, simulateQ_map, StateT.run_map, prEvent_norm]
    apply prEvent_congr
    rintro ⟨_ | ⟨rho, d⟩, state⟩ <;> simp
  rw [exactEvent]
  exact fresh_stopped_le pp l e m c fuel within s.2.1.1 s.2.1.2 sound.live

/-- A physical refusal inside the finder cannot claim the completed first-search event. -/
theorem fresh_capped_finder_booked {Note : Type} (pp : PublicParam) (cut : Note → Option Key)
    (l : Layer) (e : UInt32) (m : ByteArray) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (left : Nat) (s : D × History) (sound : Sound pp s) :
    let search (low : BitVec digestBits) :=
      Internal.findCodeword (messageHash (Note := Note)) pp l e m (ofBV 16 low) c fuel
    let run := do
      let low ← $ᵗ BitVec digestBits
      (simulateQ (handler pp cut) (WeightedCap.capCompOpt fee left (search low))).run s
    let partnered := fun z => ∃ rho digits, z.1 = some (rho, digits) ∧
      EarlierDigest.Partner pp z.2.2.1.1 (trialInput pp l e m rho)
    (CODE_SIZE / 2 ^ 128 : ℝ≥0∞) * Pr{let z ← run}[z.1.elim False (fun ans =>
      partnered (ans, z.2))] ≤
      (2 ^ 128)⁻¹ * (searchMass pp c fuel (l,e) s.2.1 + validCount pp (l,e) s.2.1) := by
  intro search run partnered
  refine (mul_le_mul_right ?_ _).trans (fresh_finder_booked pp cut l e m c fuel within s sound)
  exact prEvent_bind_mono_of_forall_le _ _ _ _ _ fun low =>
    WeightedCap.prEvent_run_capCompOpt_some_le (handler pp cut) fee partnered (search low) left s

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger
