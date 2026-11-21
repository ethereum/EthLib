module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinishCharge
public import VCVio.OracleComp.SimSemantics.OptionT.Answer

/-!
# Accumulate first-search charges across adaptive continuation and refusal

The caller may branch on any genuine finder result or stop early.

The guard keeps each completed finder mark and each booked key on its actual path.
-/

@[expose] public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open HashSig Constants OracleComp OracleSpec EarlierDigest EarlierDigest.Ledger TrialGraphWatch
open scoped ENNReal Classical

private noncomputable def replies (pp : PublicParam) (q : Nat) :
    QueryImpl (OptionalAnswer.Spec (Ops pp)) (StateT Nat (StateT (State pp) ProbComp)) :=
  fun t => (observeCall pp q t).run

private theorem good_step {pp : PublicParam} (q : Nat) :
    (replies pp q).flattenStateT.PreservesInv (fun s => Sound pp (ledger s.2.1)) := by
  rintro t ⟨left,s⟩ sound z ran
  simp only [QueryImpl.flattenStateT, StateT.run_mk, replies, observeCall, OptionT.run_mk,
    bind_pure_comp, Functor.map_map, support_map] at ran
  obtain ⟨v, reached, rfl⟩ := ran
  exact guarded_sound (expandCall pp t) s.1 sound reached

theorem all_searches {pp : PublicParam} (q : Nat) {α : Type} (p : OracleComp (Ops pp) α)
    (left : Nat) (s : State pp) (sound : Sound pp (ledger s.1)) :
    let run := (((simulateQ (observeCall pp q) p).run).run left).run s
    av run (fun z => gain z.2) + reserve s ≤ gain s + av run (fun z => reserve z.2) := by
  let base := replies pp q
  have one (t : (Ops pp).Domain) (st : Nat × State pp) (hs : Sound pp (ledger st.2.1)) :
      av ((base.flattenStateT t).run st) (fun z => gain z.2.2) + reserve st.2 ≤
        gain st.2 + av ((base.flattenStateT t).run st) (fun z => reserve z.2.2) := by
    simpa only [av, base, QueryImpl.flattenStateT, replies, StateT.run_mk, tsum_prEvent_map_mul]
      using operation pp q st.1 t st.2 hs
  have total := QueryImpl.run_compensated base.flattenStateT _ (good_step q) (fun z => gain z.2)
    (fun z => reserve z.2) (fun z _ => finite_reserve z.2) one (OptionalAnswer.program p)
      (left,s) sound
  dsimp only at total
  rw [simulateQ_flattenStateT_run] at total
  have view : simulateQ base (OptionalAnswer.program p) = (simulateQ (observeCall pp q) p).run :=
    OptionalAnswer.simulate_program _ _
  rw [view] at total
  simpa only [av, bind_pure_comp, tsum_prEvent_map_mul] using total

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
