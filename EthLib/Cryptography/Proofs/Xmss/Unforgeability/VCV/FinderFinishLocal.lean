module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderBookCharge
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinish

/-!
# The physical guard books a first attempt before it may refuse a search

The residual sampler uses the physical port for its private coins.

Every later finder operation uses this same port and leaves the saved entries intact.
-/

@[expose] public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open HashSig Constants OracleComp OracleSpec EarlierDigest EarlierDigest.Ledger TrialGraphWatch
open scoped ENNReal Classical

def ledger (s : ChronicleState) : D × History := (s.1.1.1.1.1.1,s.1.1.2)

/-- First-time physical word insertion and first-key bookings come from the same graph path. -/
theorem project_ledger {α : Type} (pp : PublicParam) (q : Nat) (p : OracleComp Queries α)
    (s : ChronicleState) :
    Prod.map id ledger <$> (simulateQ (chronicle pp q) p).run s =
      (simulateQ (handler pp cut) p).run (ledger s) := by
  have w := Ledger.project_watch pp cut register (fun r b => (target pp r b).isSome) q
    (fun word => (CachedCodeword.digits word).isSome) p s.1.1
  change Prod.map id (fun s : WatchedState => (s.1.1.1.1,s.2)) <$>
    (simulateQ (watched pp cut register (fun r b => (target pp r b).isSome) q) p).run s.1.1 = _ at w
  rw [← joint_ledger pp q p s.1.1 s.1.2, ← chronicle_joint pp q p s.1 s.2] at w
  rw [show Prod.map (id : α → α) ledger = (fun z => (z.1, ledger z.2)) from funext fun ⟨_,_⟩ => rfl]
  simpa only [ledger, Functor.map_map, Function.comp_def, Prod.map, id_eq] using w

noncomputable def guarded {α : Type} (pp : PublicParam) (q left : Nat)
    (p : OracleComp Queries α) (s : ChronicleState) :=
  (((simulateQ (WeightedCap.guard fee (chronicle pp q)) p).run).run left).run s

theorem project_guard {α : Type} (pp : PublicParam) (q left : Nat)
    (p : OracleComp Queries α) (s : ChronicleState) :
    (fun z => (z.1.1, ledger z.2)) <$> guarded pp q left p s =
      (simulateQ (handler pp cut) (WeightedCap.capCompOpt fee left p)).run (ledger s) := by
  rw [← project_ledger pp q _ s, ← WeightedCap.run_guard]
  simp [guarded, StateT.run_map, Functor.map_map, ledger]

private theorem update_raw (pp : PublicParam) (t : MixedWorld.Domain)
    (a : MixedWorld.Range t) (h : History) :
    (update pp cut (.inl t) a h).2 = h.2 := by
  rcases t with (t | b) | k
  · rfl
  · simp [update,recordWordAt]; split <;> rfl
  · rfl

private theorem cap_raw {α : Type} (pp : PublicParam) (p : OracleComp MixedWorld α)
    (left : Nat) (s : D × History) {z}
    (ran : z ∈ support ((simulateQ (handler pp cut)
      (WeightedCap.capCompOpt fee left (simulateQ raw p))).run s)) : z.2.2.2 = s.2.2 := by
  induction p using OracleComp.inductionOn generalizing left s with
  | pure a =>
    simp only [simulateQ_pure, WeightedCap.capCompOpt_pure, StateT.run_pure,
      mem_support_pure_iff] at ran
    cases ran
    rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, raw, WeightedCap.capCompOpt_query_bind] at ran
    split_ifs at ran
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at ran
      obtain ⟨y, issued, next⟩ := ran
      rw [ih y.1 _ _ next]
      obtain ⟨_, updated⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp issued
      exact (congrArg Prod.snd updated).trans (update_raw ..)
    · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at ran
      cases ran
      rfl

/-- Even a search interrupted by the cap retains the snapshot at its free incoming notice. -/
theorem search_saved (pp : PublicParam) (q left : Nat) (c : Call pp) (s : ChronicleState) {z}
    (ran : z ∈ support (guarded pp q left (expandCall pp (.inr c)) s)) :
    (ledger z.2).2.2 = begin (ledger s).2.2 (c.layer,c.epoch) (ledger s).2.1 := by
  let books := ledger s
  have path : (z.1.1,ledger z.2) ∈ support ((simulateQ (handler pp cut)
        (WeightedCap.capCompOpt fee left (expandCall pp (.inr c)))).run books) := by
    rw [← project_guard pp q left _ s, support_map]
    exact ⟨z,ran,rfl⟩
  change (_, ledger z.2) ∈ support ((simulateQ (handler pp cut) (WeightedCap.capCompOpt fee left
    ((find pp c.layer c.epoch c.msg).run c.privateIn))).run books) at path
  simp only [find, StateT.run_bind, emit, StateT.run_mk, bind_map_left, carry,
    WeightedCap.capCompOpt_query_bind] at path
  simp [fee, simulateQ_bind, StateT.run_bind, handler, QueryImpl.extendState_apply, backend,
    update, cut, FinderNotice.key] at path
  exact cap_raw pp _ left _ path

/-- The guarded run pays for a partnered first return at this cold private key. -/
theorem search_price (pp : PublicParam) (q left : Nat) (c : Call pp) (s : ChronicleState)
    (sound : Sound pp (ledger s))
    (cold : c.privateIn.2 ⟨.inl (pp, addrRnd c.layer c.epoch,c.msg),
      (randomizer_residual pp c.layer c.epoch c.msg).1⟩ = none) :
    let p := guarded pp q left (expandCall pp (.inr c)) s
    (CODE_SIZE / 2 ^ 128 : ℝ≥0∞) * Pr{let z ← p}[∃ a rho x, z.1.1 = some a ∧ a.1 = some (rho,x) ∧
      Partner pp (ledger z.2).2.1.1 (CachedCodeword.trialInput pp c.layer c.epoch c.msg rho)] ≤
      (2 ^ 128)⁻¹ * keyPrice pp (c.layer,c.epoch) (ledger s).2.1 := by
  intro p
  have cost := cold_capped_find_price pp c.layer c.epoch c.msg c.privateIn
    (ledger s) sound left cold
  dsimp only at cost
  rw [← project_guard pp q left ((find pp c.layer c.epoch c.msg).run c.privateIn) s,
    prEvent_map] at cost
  refine (mul_le_mul_right (prEvent_mono p _ _ ?_) _).trans cost
  rintro z ⟨a,rho,x,found,selected,other⟩
  change z.1.1.elim False _
  rw [found]
  exact ⟨rho,x,selected,other⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
