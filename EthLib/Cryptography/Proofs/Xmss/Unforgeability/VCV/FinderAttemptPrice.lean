module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchLedgerFinder
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeSigner
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistry
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RandomizerFreshness

/-!
# Price a partner at the end of the signing algorithm's own first search

The attempt records the message table before the private randomizer lookup.

Its low half supplies the finder base, and its high half still runs on the updated private table.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig Constants OracleComp OracleSpec TwoLayerGraph EarlierDigest EarlierDigest.Ledger
open CanonicalGraph.PairedQueries TrialGraphWatch
open ChainGraph (Word)
open scoped ENNReal Classical

private theorem coin_query (pp : PublicParam) (n : unifSpec.Domain) (s : D × History) :
    ((Ledger.handler pp cut) (.inl (.inl (.inl n)))).run s =
      (fun w => (w,s)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  obtain ⟨⟨st, pending⟩, history⟩ := s
  simp only [Ledger.handler, QueryImpl.extendState_apply, Ledger.backend, Ledger.update, expand,
    RandomOraclePairedValue.readHalves, simulateQ_spec_query, liftPublic, simulateQ_HasQuery_query,
    bind_pure_comp]
  rw [(graph pp).deferredImpl_run_inl (.inl (.inl n)) (st,pending),
    (graph pp).relabelImpl_run_unif n st, Functor.map_map, Functor.map_map]

private theorem coins {α : Type} (pp : PublicParam) (p : ProbComp α) (s : D × History) :
    (simulateQ (Ledger.handler pp cut) (simulateQ raw (liftM p : OracleComp MixedWorld α))).run s =
      (fun w => (w,s)) <$> p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [liftM_bind, simulateQ_bind, StateT.run_bind, map_bind]
    have forward : simulateQ raw (liftM (liftM (unifSpec.query t) : ProbComp _) :
      OracleComp MixedWorld _) =
        liftM (Queries.query (.inl (.inl (.inl t)))) := rfl
    rw [forward, simulateQ_spec_query, coin_query, bind_map_left]
    exact bind_congr ih

private theorem raw_search (pp : PublicParam) (l : Layer) (e : UInt32)
    (m : ByteArray) (r : Randomizer) :
    simulateQ raw (Internal.findCodeword mixedHash pp l e m r 0 MAX_RANDOMIZER_TRIALS) =
      Internal.findCodeword messageHash pp l e m r 0 MAX_RANDOMIZER_TRIALS := by
  rw [findCodeword_map_monad (simulateQ raw) (fun a => simulateQ_pure _ a)
    (fun a f => simulateQ_bind _ a f)]
  congr 1

private theorem find_base (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (r : ResidualCache pp) :
    (mixedFind pp l e m).run r = ((mixedBase pp l e m).run r >>= fun z =>
      (fun a => (a,z.2)) <$> Internal.findCodeword mixedHash pp l e m z.1 0
        MAX_RANDOMIZER_TRIALS) := by
  have projected : (mixedBase pp l e m).run r =
      (fun z => (halfOf 0 z.1,z.2)) <$> (mixedRandomizer pp l e m).run r := by
    simp only [mixedBase, mixedRandomizer, StateT.run_mk, StateT.run_map, Functor.map_map]
  simp [mixedFind, projected, StateT.run_bind, StateT.run_monadLift, bind_map_left]

private theorem notice_run (pp : PublicParam) (l : Layer) (e : UInt32)
    (m : ByteArray) (s : D × History) :
    ((Ledger.handler pp cut) (.inr (.attempt l e m))).run s =
      pure ((),s.1,s.2.1,begin s.2.2 (l,e) s.2.1) := by
  simp [Ledger.handler, Ledger.backend, Ledger.update, QueryImpl.extendState_apply,
    cut, FinderNotice.key]

/-- After the first notice and a cold low lookup, the public search starts at a uniform base.

The residual high lookup still executes, whether warm or cold.

The projection keeps the complete public graph and the first-attempt ledger. -/
theorem cold_find_run (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (r : ResidualCache pp) (s : D × History)
    (cold : r.2 ⟨.inl (pp, addrRnd l e, m), (randomizer_residual pp l e m).1⟩ = none) :
    (fun z => (z.1.1,z.2)) <$> (simulateQ (Ledger.handler pp cut) ((find pp l e m).run r)).run s =ᵈ
      (do
        let w ← $ᵗ Word
        (simulateQ (Ledger.handler pp cut) (Internal.findCodeword messageHash pp l e m
          (ofBV 16 w) 0 MAX_RANDOMIZER_TRIALS)).run (s.1,s.2.1,begin s.2.2 (l,e) s.2.1)) := by
  simp only [find, StateT.run_bind, emit, StateT.run_mk, bind_map_left, carry, simulateQ_bind,
    simulateQ_spec_query, find_base, mixedBase_miss pp l e m r cold,
    bind_assoc, simulateQ_map, StateT.run_map, coins, map_bind, Functor.map_map]
  rw [notice_run pp l e m s, pure_bind]
  apply EvalDistEq.bind_right
  intro low
  rw [raw_search pp l e m (ofBV 16 low)]
  simp only [Prod.mk.eta, id_map']
  exact OracleComp.EvalDistEq.bind_const (spec := unifSpec) _ _

/-- The first completed native signing search can spend its key's booking.

This includes the real private lookup and the physical cap on the whole call.

A refusal or an exhausted finder makes the event false. -/
theorem cold_capped_find_price (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (r : ResidualCache pp) (s : D × History) (sound : Sound pp s) (left : Nat)
    (cold : r.2 ⟨.inl (pp, addrRnd l e, m), (randomizer_residual pp l e m).1⟩ = none) :
    let run := (simulateQ (Ledger.handler pp cut)
      (WeightedCap.capCompOpt fee left ((find pp l e m).run r))).run s
    let partnered := fun z => ∃ rho digits, z.1.1 = some (rho,digits) ∧
      EarlierDigest.Partner pp z.2.2.1.1 (CachedCodeword.trialInput pp l e m rho)
    (CODE_SIZE / 2 ^ 128 : ℝ≥0∞) * Pr{let z ← run}[z.1.elim False (fun out =>
      partnered (out,z.2))] ≤
      (2 ^ 128)⁻¹ * (searchMass pp 0 MAX_RANDOMIZER_TRIALS (l,e) s.2.1 + validCount pp
        (l,e) s.2.1) := by
  intro run partnered
  let booked : D × History := (s.1,s.2.1,begin s.2.2 (l,e) s.2.1)
  have saved : Sound pp booked := sound_step pp cut (.inr (.attempt l e m)) s sound ((),booked)
    (by rw [notice_run pp l e m s]; simp [booked])
  have cap := WeightedCap.prEvent_run_capCompOpt_some_le (Ledger.handler pp cut) fee partnered
    ((find pp l e m).run r) left s
  refine (mul_le_mul_right cap _).trans ?_
  let event (z : Option (Randomizer × Vector (Fin CHAIN_LENGTH) V) × D × History) : Prop :=
    ∃ rho digits, z.1 = some (rho,digits) ∧
    EarlierDigest.Partner pp z.2.2.1.1 (CachedCodeword.trialInput pp l e m rho)
  have eq := (cold_find_run pp l e m r s cold).prEvent_eq event
  simp only [prEvent_norm] at eq
  exact eq ▸ fresh_finder_booked pp cut l e m 0 MAX_RANDOMIZER_TRIALS (by decide) booked saved

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
