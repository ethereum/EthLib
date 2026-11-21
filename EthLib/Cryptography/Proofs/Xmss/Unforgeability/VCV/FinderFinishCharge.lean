module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinishLocal

/-!
# Gains and first-key charges at a finder boundary

Physical steps never erase a booked snapshot.

At a first search, the full price is saved even when the cap interrupts the search.
-/

@[expose] public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open HashSig Constants OracleComp OracleSpec EarlierDigest EarlierDigest.Ledger TrialGraphWatch
open scoped ENNReal Classical

noncomputable abbrev validRate : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
noncomputable abbrev epsilon : ℝ≥0∞ := (2 ^ 128)⁻¹

def Hit {pp : PublicParam} (xs : List (Finish pp)) : Prop := ∃ m ∈ xs, FirstHit m

noncomputable def gain {pp : PublicParam} (s : State pp) : ℝ≥0∞ := if Hit s.2 then validRate else 0

noncomputable def reserve {pp : PublicParam} (s : State pp) : ℝ≥0∞ :=
    epsilon * savedPrice pp (ledger s.1).2.2

theorem finite_reserve {pp : PublicParam} (s : State pp) : reserve s ≠ ⊤ := by
  refine ENNReal.mul_ne_top (by norm_num [epsilon]) (ENNReal.sum_ne_top.mpr ?_)
  intro k _
  cases h : (ledger s.1).2.2 k with
  | none => simp
  | some e =>
    simp only [Option.elim_some, keyPrice, ne_eq, ENNReal.add_eq_top, not_or]
    refine ⟨ENNReal.mul_ne_top (ENNReal.div_ne_top (by simp) (by norm_num)) ?_,
      ENNReal.natCast_ne_top _⟩
    exact ENNReal.sum_ne_top.mpr fun _ _ => prEvent_ne_top _

private theorem savedIncreases (pp : PublicParam) (amount : ℝ≥0∞) :
    (handler pp cut).PreservesInv (fun s => amount ≤ savedPrice pp s.2.2) := by
  rintro t s bound ⟨a,next⟩ issued
  obtain ⟨_,observed⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp issued
  change next.2 = update pp cut t a s.2 at observed
  rw [observed]
  rcases t with (coin | b) | note
  · cases coin <;> first | exact bound | simp only [update]; split <;> exact bound
  · exact bound
  · simpa only [cut, update, savedPrice_begin] using bound.trans
      (le_self_add : savedPrice pp s.2.2 ≤ savedPrice pp s.2.2 +
        (if s.2.2 note.key = none then keyPrice pp note.key s.2.1 else 0))

theorem guarded_sound {pp : PublicParam} {q left : Nat} {α : Type} (p : OracleComp Queries α)
    (s : ChronicleState) (sound : Sound pp (ledger s)) {z}
      (run : z ∈ support (guarded pp q left p s)) :
    Sound pp (ledger z.2) := by
  apply simulateQ_run_preservesInv (handler pp cut) _ (sound_step pp cut)
    (WeightedCap.capCompOpt fee left p)
    (ledger s) sound (z.1.1,ledger z.2)
  rw [← project_guard pp q left p s, support_map]
  exact ⟨z,run,rfl⟩

theorem guarded_price_mono {pp : PublicParam} {q left : Nat} {α : Type} (p : OracleComp Queries α)
    (s : ChronicleState) {z} (run : z ∈ support (guarded pp q left p s)) :
    savedPrice pp (ledger s).2.2 ≤ savedPrice pp (ledger z.2).2.2 := by
  apply simulateQ_run_preservesInv (handler pp cut) _ (savedIncreases pp _)
    (WeightedCap.capCompOpt fee left p)
    (ledger s) le_rfl (z.1.1,ledger z.2)
  rw [← project_guard pp q left p s, support_map]
  exact ⟨z,run,rfl⟩

private theorem av_mono {α : Type} (p : ProbComp α) (f g : α → ℝ≥0∞)
    (le : ∀ z ∈ support p, f z ≤ g z) : av p f ≤ av p g := by
  apply tsum_le_tsum
  intro z
  by_cases run : z ∈ support p
  · exact mul_le_mul_right (le z run) _
  · simp [prEvent_eq_zero_of_not_mem_support p run]

private theorem av_event {α : Type} (p : ProbComp α) (E : α → Prop) :
    av p (fun z => if E z then validRate else 0) = validRate * Pr{let z ← p}[E z] := by
  rw [prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun z => by by_cases h : E z <;> simp [h, mul_comm]

private def marksAfter {pp : PublicParam} (c : Call pp) (s : State pp)
    (z : (Option (Answer × ResidualCache pp) × Nat) × ChronicleState) : List (Finish pp) :=
  match z.1.1 with | none => s.2 | some a => ⟨c,s.1,a,z.2⟩ :: s.2

private theorem search_step (pp : PublicParam) (q left : Nat) (c : Call pp) (s : State pp)
    (sound : Sound pp (ledger s.1)) :
    let p := guarded pp q left (expandCall pp (.inr c)) s.1
    av p (fun z => gain (z.2, marksAfter c s z)) + reserve s ≤
      gain s + av p (fun z => reserve (pp := pp) (z.2,marksAfter c s z)) := by
  intro p
  let k := (c.layer,c.epoch)
  let first := (ledger s.1).2.2 k = none
  let price := if first then keyPrice pp k (ledger s.1).2.1 else 0
  let E := fun z : (Option (Answer × ResidualCache pp) × Nat) × ChronicleState =>
    ∃ a, z.1.1 = some a ∧ FirstHit ⟨c,s.1,a,z.2⟩
  have booked : av p (fun z => reserve (pp := pp) (z.2,marksAfter c s z)) =
    reserve s + epsilon * price := by
    apply tsum_prEvent_mul_of_const_on_support
    intro z ran
    simp only [reserve, search_saved pp q left c s.1 ran, savedPrice_begin, mul_add]
    rfl
  have increment : av p (fun z => gain (z.2,marksAfter c s z)) ≤ gain s +
    validRate * Pr{let z ← p}[E z] := by
    rw [← av_event p E]
    apply tsum_prEvent_mul_le_add_of_le
    intro z
    by_cases old : Hit s.2
    · have bound : gain (pp := pp) (z.2, marksAfter c s z) ≤ validRate := by
        simp [gain]; split <;> simp
      rw [show gain s = validRate from ite_eq_left old]
      exact le_add_right bound
    · cases ans : z.1.1 with
      | none => simp [gain, marksAfter, ans, old]
      | some a =>
        have casesHit : Hit (⟨c,s.1,a,z.2⟩ :: s.2) ↔ FirstHit ⟨c,s.1,a,z.2⟩ ∨ Hit s.2 := by
          simp [Hit]
        have selected : E z ↔ FirstHit ⟨c,s.1,a,z.2⟩ := by
          constructor
          · rintro ⟨b, hb, hit⟩
            cases Option.some.inj (ans.symm.trans hb)
            exact hit
          · exact fun hit => ⟨a,ans,hit⟩
        simp [gain, marksAfter, ans, casesHit, old, selected]
  have paid : validRate * Pr{let z ← p}[E z] ≤ epsilon * price := by
    by_cases seen : first
    · by_cases cold : c.privateIn.2 ⟨.inl (pp,addrRnd c.layer c.epoch,c.msg),
          (randomizer_residual pp c.layer c.epoch c.msg).1⟩ = none
      · simp only [price, seen, ite_true]
        apply (mul_le_mul_right (prEvent_mono p _ _ ?_) _).trans
          (search_price pp q left c s.1 sound cold)
        rintro z ⟨a,found,_,_,rho,x,selected,other⟩
        exact ⟨a,rho,x,found,selected,other⟩
      · have zero := prEvent_eq_zero_of_forall_mem_support p E (fun _ _ ⟨_,_,h⟩ => cold h.2.1)
        simp [zero]
    · have zero := prEvent_eq_zero_of_forall_mem_support p E (fun _ _ ⟨_,_,h⟩ => seen h.1)
      simp [zero]
  rw [booked]
  calc
    _ ≤ (gain s + epsilon * price) + reserve s := add_le_add_left
      (increment.trans (add_le_add_right paid _)) _
    _ = _ := by ac_rfl

/-- Each native operation pays its gain using only the price newly saved at this operation. -/
theorem operation (pp : PublicParam) (q left : Nat) (t : (Ops pp).Domain) (s : State pp)
    (sound : Sound pp (ledger s.1)) :
    let run := (((observeCall pp q t).run).run left).run s
    av run (fun z => gain z.2) + reserve s ≤ gain s + av run (fun z => reserve z.2) := by
  rcases t with t | c
  · let p := guarded pp q left (expandCall pp (.inl t)) s.1
    have unchanged : av p (fun z => gain (pp := pp) (z.2,s.2)) = gain s :=
      tsum_prEvent_mul_of_const_on_support p fun _ _ => rfl
    have mono := av_mono p (fun _ => reserve s) (fun z => reserve (pp := pp) (z.2,s.2))
      (fun z issued => mul_le_mul_right (guarded_price_mono _ _ issued) _)
    rw [show av p (fun _ => reserve s) = reserve s from tsum_prEvent_mul_of_const_on_support p
      (fun _ _ => rfl)] at mono
    have both := add_le_add_right mono (gain s)
    conv at both => lhs; rw [← unchanged]
    simpa only [observeCall, OptionT.run_mk, StateT.run_mk, bind_pure_comp, av,
      tsum_prEvent_map_mul, p, guarded]
      using both
  · let p := guarded pp q left (expandCall pp (.inr c)) s.1
    have exactRun : (((observeCall pp q (.inr c)).run).run left).run s =
        (fun z : (Option ((Ops pp).Range (.inr c)) × Nat) × ChronicleState =>
          (z.1,z.2,marksAfter c s z)) <$> p := by
      simp only [observeCall, OptionT.run_mk, StateT.run_mk, bind_pure_comp, p, guarded]
      apply congrArg (fun f => f <$> _)
      funext z
      rcases z with ⟨⟨_ | a,n⟩,st⟩ <;> rfl
    dsimp only
    rw [exactRun]
    simpa only [av, tsum_prEvent_map_mul,p] using search_step pp q left c s sound

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
