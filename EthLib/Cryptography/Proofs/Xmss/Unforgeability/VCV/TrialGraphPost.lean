module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialGraphRisk
public import EthLib.Cryptography.Proofs.Xmss.CodewordSearch
public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedHit

/-!
# Matches after a signing target is registered

The target table is read before drawing a fresh message word.

A matching low digest costs one chance in the 128-bit space.

The counter and the graph hazard refer to the same observed run.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch

open Constants HashSig OracleSpec OracleComp TwoLayerGraph
open scoped ENNReal

/-- A registered target can fire on a new full physical word at its message address. -/
@[expose] noncomputable def activePost {Note R : Type} (pp : PublicParam)
    (target : R → HashInput → Option Digest) : (Spec Note).Domain → Observed R → Bool
  | .inl (.inl (.inr b)), s => cold pp b s.1.1.1 && (target s.1.1.2 b).isSome
  | _, _ => false

/-- The candidate digest is the first 16 bytes of the actual public answer. -/
@[expose] def matchesPost {Note R : Type} (target : R → HashInput → Option Digest) :
    (t : (Spec Note).Domain) → Observed R → (Spec Note).Range t → Bool
  | .inl (.inl (.inr b)), s, w => target s.1.1.2 b == some (halfOf 0 (ofOutput w))
  | _, _, _ => false

/-- The registered-hit flag uses only the prior target and the response returned to the caller. -/
@[expose] noncomputable def trackPost {Note R : Type} (pp : PublicParam) (notice : Note → R → R)
    (target : R → HashInput → Option Digest) (q : Nat) (test : HashOutput → Bool) :=
  (observe pp notice (fun r b => (target r b).isSome) q test).extendState
    (MarkedHit.update (activePost pp target) (matchesPost target))

private theorem paid_post {Note R : Type} (pp : PublicParam) (notice : Note → R → R)
    (target : R → HashInput → Option Digest) (q : Nat) (test : HashOutput → Bool)
    (t : (Spec Note).Domain) (s : Observed R) {z}
    (hz : z ∈ support (((observe pp notice (fun r b => (target r b).isSome) q test) t).run s)) :
    z.2.1.2 = s.1.2 + (if activePost pp target t s then 1 else 0) := by
  obtain ⟨post, _⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).1 hz
  have count := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).1 post).2
  rcases t with ((u | b) | op) | n <;> simp [activePost] at count ⊢
  · exact count
  · split at count <;> simp_all
  · exact count
  · exact count

private theorem post_rate {Note R : Type} (pp : PublicParam) (notice : Note → R → R)
    (target : R → HashInput → Option Digest) (q : Nat) (test : HashOutput → Bool)
    (t : (Spec Note).Domain) (s : Observed R) (active : activePost pp target t s = true) :
    Pr{let z ← ((observe pp notice (fun r b => (target r b).isSome) q test) t).run s}[
      matchesPost target t s z.1] ≤ (1 : ℝ≥0∞) / 2 ^ 128 := by
  rcases t with ((u | b) | op) | n
  · simp [activePost] at active
  · obtain ⟨fresh, registered⟩ := Bool.and_eq_true_iff.mp active
    obtain ⟨⟨l, e, msg, rho, address⟩, low, high⟩ :
        MessageAt pp b ∧ s.1.1.1.1.1 (.inl b) = none ∧ s.1.1.1.1.1 (.inr b) = none := by
      simpa [cold, and_assoc] using fresh
    cases ht : target s.1.1.2 b with
    | none => simp [ht] at registered
    | some d =>
      simp only [observe, withPost, BernoulliMoment.observe, QueryImpl.extendState_apply, base,
        StateT.run_mk, bind_pure_comp, prEvent_norm, matchesPost, ht, beq_iff_eq, Option.some.injEq]
      rw [trial_rate pp b (address ▸ isTrial_message pp l e msg rho) s.1.1.1 low high
        (fun w => d = halfOf 0 (ofOutput w)), prEvent_halfOf_ofOutput (fun h => d = h)]
      simp
  · simp [activePost] at active
  · simp [activePost] at active

/-- Only the expected number of registered fresh inputs is charged, including on refused runs. -/
theorem post_price {Note R α : Type} (pp : PublicParam) (notice : Note → R → R)
    (target : R → HashInput → Option Digest) (q : Nat) (test : HashOutput → Bool)
    (body : OracleComp (Spec Note) α) (s : Observed R) :
    Pr{let z ← (simulateQ (trackPost pp notice target q test) body).run (s, false)}[z.2.2 = true] ≤
      mean ((simulateQ (observe pp notice (fun r b => (target r b).isSome) q test) body).run s)
        (fun z => z.2.1.2) / 2 ^ 128 := by
  have price := MarkedHit.prEvent_le_expected
    (observe pp notice (fun r b => (target r b).isSome) q test) (fun s => s.1.2)
    (activePost pp target) (matchesPost target) (1 / 2 ^ 128)
    (fun t u _ hz => paid_post pp notice target q test t u hz)
    (post_rate pp notice target q test) body s
  simpa [trackPost, mean, div_eq_mul_inv] using price

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch
