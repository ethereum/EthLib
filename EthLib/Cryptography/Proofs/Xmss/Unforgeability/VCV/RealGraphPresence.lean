module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphFootprint
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerPaid
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphFootprint

/-!
# The two rows of a physical query remain present together

Both graph rows are ready at the same byte input or both are absent from the graph.

Only a full public request can change the ordinary cache.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Footprint

open OracleComp OracleSpec HashSig SecretEncoding.Residual RandomOraclePairedValue
open CanonicalGraph.PairedQueries TwoLayerGraph
open ChainGraph (Word)
open scoped Classical OracleSpec.PrimitiveQuery

private noncomputable abbrev rowDecidable : DecidableEq Row :=
  fun a b => Classical.propDecidable (a = b)
attribute [local instance 2000] rowDecidable

private theorem ordinary_present (pp : PublicParam) (b : HashInput) (s : State Row)
    (old : PairedPresence s) (lo hi : Word × State Row)
    (low : lo ∈ support (((graph pp).relabelImpl (.inl (.inr (.inl b)))).run s))
    (high : hi ∈ support (((graph pp).relabelImpl (.inl (.inr (.inr b)))).run lo.2)) :
    PairedPresence hi.2 := by
  let g := graph pp
  let q := PairedHashWord.halves.symm (lo.1, hi.1)
  have hlo : (lo.1, lo.2, ([] : List Cell)) ∈ support
      ((g.deferredImpl (.inl (.inl (.inr (.inl b))))).run (s, [])) := by
    rw [g.deferredImpl_run_inl, support_map]
    exact ⟨lo, low, rfl⟩
  have hhi : (hi.1, hi.2, ([] : List Cell)) ∈ support
      ((g.deferredImpl (.inl (.inl (.inr (.inr b))))).run (lo.2, [])) := by
    rw [g.deferredImpl_run_inl, support_map]
    exact ⟨hi, high, rfl⟩
  have both : (q, hi.2, ([] : List Cell)) ∈ support
      (((callerImpl g PairedHashWord.halves) (.inr b)).run (s, [])) := by
    simp only [callerImpl, QueryImpl.compose, RandomOraclePairedValue.readHalves, simulateQ_bind,
      simulateQ_pure, simulateQ_spec_query, liftPublic, simulateQ_HasQuery_query, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨_, hlo, _, hhi, rfl⟩
  exact caller_preserves_presence g PairedHashWord.halves (ready_pair pp) (.inr b) (s,
      []) old _ both

open Classical in
private theorem uniform_frame {K : Type} (G : CanonicalGraph PairedHashWord.HalfSpec StartKey K
    (BitVec digestBits))
    (pp : PublicParam) (n : Nat) (l : ResidualCache pp) (s : State K) {w}
    (hw : w ∈ support ((simulateQ G.relabelImpl ((inner pp (.inl (.inl n))).run l)).run s)) :
    w.2 = s := by
  simp [inner, QueryImpl.compose, Derivations.expand, SecretEncoding.reindexQueries, handler,
    G.relabelImpl_run_unif, Functor.map_map] at hw
  obtain ⟨_, _, rfl⟩ := hw
  rfl

open Classical in
private theorem step_present (pp : PublicParam) :
    (step (graph pp) pp).PreservesInv (fun st => PairedPresence st.2) := by
  intro t initial old z hit
  rcases initial with ⟨l, s⟩
  simp only [step, StateT.run_mk, support_map] at hit
  obtain ⟨w, hw, rfl⟩ := hit
  rcases t with ((n | (b | tick)) | key)
  · change PairedPresence w.2
    rw [uniform_frame (graph pp) pp n l s hw]
    exact old
  · rw [public_split] at hw
    simp only [simulateQ_bind, simulateQ_pure, simulateQ_spec_query, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hw
    obtain ⟨lo, hlo, hi, hhi, rfl⟩ := hw
    exact ordinary_present pp b s old lo hi hlo hhi
  · simp [inner, QueryImpl.compose, Derivations.expand, SecretEncoding.reindexQueries, handler,
      draw_frame (graph pp), Functor.map_map] at hw
    obtain ⟨_, _, _, rfl⟩ := hw
    exact old
  · rw [private_split] at hw
    simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
      mem_support_bind_iff, mem_support_pure_iff] at hw
    obtain ⟨lo, hlo, hi, hhi, rfl⟩ := hw
    have a := private_frame (graph pp) pp _ l s hlo
    have b := private_frame (graph pp) pp _ lo.1.2 lo.2 hhi
    change PairedPresence hi.2
    simpa only [PairedPresence, a, b] using old

open Classical in
private theorem preserve_from_empty {K α : Type}
    (G : CanonicalGraph PairedHashWord.HalfSpec StartKey K (BitVec digestBits))
    (pp : PublicParam) (body : OracleComp Source α) (l : ResidualCache pp)
    (P : State K → Prop) (inv : (step G pp).PreservesInv fun s => P s.2)
    (base : P (∅, ∅)) (a : α) (extra : ResidualCache pp) (t : State K)
    (next : List (StartKey ⊕ K)) (run : ((a, extra), t, next) ∈ support (coldRun G pp body l)) :
    P t := by
  unfold coldRun at run
  rw [deferred_lift, support_map] at run
  obtain ⟨⟨_, last⟩, supported, same⟩ := run
  cases same
  rw [source_eq, run_step, support_map] at supported
  obtain ⟨⟨_, _, _⟩, actual, same⟩ := supported
  cases same
  exact OracleComp.simulateQ_run_preservesInv _ _ inv body (l, ∅, ∅) base _ actual

/-- All adaptive source programs preserve paired presence from empty graph tables.

This includes operational cutoffs at any point and an arbitrary warm residual cache.
-/
theorem deferred_present {α : Type} (pp : PublicParam) (body : OracleComp Source α)
    (l : ResidualCache pp) (t : State Row) (next : List Cell)
    (a : α) (extra : ResidualCache pp)
    (run : ((a, extra), t, next) ∈ support (coldRun (graph pp) pp body l)) :
    PairedPresence t :=
  preserve_from_empty _ pp body l PairedPresence (step_present pp)
    (by simp [PairedPresence]) a extra t next run

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Footprint
