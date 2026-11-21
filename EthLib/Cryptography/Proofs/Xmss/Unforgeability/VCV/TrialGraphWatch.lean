module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialRows
public import VCVio.OracleComp.QueryTracking.CountingOracle.ObserveTrials

/-!
# Adaptive message-trial counts in one normalized graph

A notice updates the registration state without reading a hash.

Each physical trial checks the incoming registration state and the two ordinary rows.

The run records fresh registered words, fresh unregistered trials and valid unregistered words.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch

open HashSig OracleSpec OracleComp TwoLayerGraph CanonicalGraph.PairedQueries
open ChainGraph (Word Public)
open scoped ENNReal Classical OracleSpec.PrimitiveQuery

abbrev D := DeferredState HashInput Word Start Row
abbrev Raw := Mixed HashInput HashOutput Start Row Word
abbrev Spec (Note : Type) := Raw + (Note →ₒ Unit)

/-- A message trial in the current parameter, regardless of its message length. -/
@[expose] def MessageAt (pp : PublicParam) (b : HashInput) : Prop :=
  ∃ (l : Layer) (e : UInt32) (m : ByteArray) (r : Randomizer),
    (thInput pp (addrMsg l e) (m ++ packBytes r)).data.toList = b

/-- An eligible missed input is recognized before drawing either physical half. -/
@[expose] noncomputable def cold (pp : PublicParam) (b : HashInput) (s : D) : Bool :=
  decide (MessageAt pp b) && (s.1.1 (.inl b)).isNone && (s.1.1 (.inr b)).isNone

/-- Keep the original graph operation, or perform a registration notice at no graph cost. -/
@[expose] noncomputable def base {Note R : Type} (pp : PublicParam) (notice : Note → R → R) :
    QueryImpl (Spec Note) (StateT (D × R) ProbComp)
  | .inl t => StateT.mk fun s => (fun z => (z.1, z.2, s.2)) <$>
      (simulateQ (graph pp).deferredImpl (expand PairedHashWord.halves t)).run s.1
  | .inr n => StateT.mk fun s => pure ((), s.1, notice n s.2)

/-- Register a paid post-sign trial only at an ordinary fresh word that was already watched. -/
@[expose] noncomputable def withPost {Note R : Type} (pp : PublicParam)
    (notice : Note → R → R) (registered : R → HashInput → Bool) :=
  (base pp notice).extendState (fun t s _ _ (spent : Nat) => match t with
    | .inl (.inl (.inr b)) => if cold pp b s.1 && registered s.2 b then spent + 1 else spent
    | _ => spent)

/-- Count pre-sign trials on a fresh message word exactly when it has no registered target. -/
@[expose] noncomputable def pre {Note R : Type} (pp : PublicParam)
    (registered : R → HashInput → Bool) :
    (Spec Note).Domain → ((D × R) × Nat) → Bool
  | .inl (.inl (.inr b)), s => cold pp b s.1.1 && !(registered s.1.2 b)
  | _, _ => false

/-- Only a full public reply can be tested for a valid digest. -/
@[expose] def valid {Note : Type} (test : HashOutput → Bool) : (t : (Spec Note).Domain) →
    (Spec Note).Range t → Bool
  | .inl (.inl (.inr _)), w => test w
  | _, _ => false

/-- The checked counters retain the graph, registration state and actual paid post-sign count. -/
@[expose] noncomputable def observe {Note R : Type} (pp : PublicParam) (notice : Note → R → R)
    (registered : R → HashInput → Bool) (q : Nat) (test : HashOutput → Bool) :=
  BernoulliMoment.observe (withPost pp notice registered) q (pre pp registered) (valid test)

/--
Before a fresh physical response, eligibility may depend on the full incoming registration table.

Arbitrary adaptive clients and guard refusals then satisfy the reusable stopping-time moment law.
-/
theorem counts {Note R : Type} (pp : PublicParam) (notice : Note → R → R)
    (registered : R → HashInput → Bool) (q : Nat) (test : HashOutput → Bool) (p : ℝ)
    (rate : Pr{let w ← $ᵗ HashOutput}[test w] = ENNReal.ofReal p) :
    BernoulliMoment.CountsTrials (observe pp notice registered q test) (fun s => s.2.1) (fun s =>
      s.2.2) p q := by
  apply BernoulliMoment.counts_observe
  rintro (((u | b) | internal) | n) ⟨⟨st, reg⟩, spent⟩ active
  · simp [pre] at active
  · have h : MessageAt pp b ∧ st.1.1 (.inl b) = none ∧ st.1.1 (.inr b) = none := by
      simpa [pre, cold, and_assoc] using (Bool.and_eq_true_iff.mp active).1
    obtain ⟨⟨l, e, m, r, represented⟩, low, high⟩ := h
    have trial : IsTrial b := represented ▸ isTrial_message pp l e m r
    simp only [withPost, QueryImpl.extendState_apply, base, StateT.run_mk, bind_pure_comp,
      prEvent_norm, valid, Functor.map_map]
    exact (trial_rate pp b trial st low high (fun w => test w)).trans rate
  · simp [pre] at active
  · simp [pre] at active

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch
