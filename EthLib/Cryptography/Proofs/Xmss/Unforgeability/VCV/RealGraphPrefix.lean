module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SeedReduction

/-!
# The two paid calls before the public parameter is known

The leanXMSS draft, section "The scheme", derives the public parameter before building the top tree.

The operational cap charges the master read and the parameter word before the first tree call.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open OracleComp OracleSpec Constants
open XmssSecurity (HashOutput)
open scoped Classical ENNReal

/-- The only private label touched before the top-tree build. -/
@[expose] def parameterLabel : PrfInput :=
  (Vector.replicate PUBLIC_PARAM_LEN 0, addrParam, ByteArray.empty)

/-- Key generation selects the first 16 bytes of the returned word. -/
@[expose] def parameterOfWord (w : HashOutput) : PublicParam := halfOf 0 (ofOutput w)

abbrev sourcePass := Backend.withDerivationsLift PrfInput HashOutput ∘ₛ ordinary
abbrev sourceTick : OracleComp Source Unit := liftM (Source.query (.inl (.inr (.inr ()))))
abbrev sourcePrf (p : PublicParam) (a : Address) (suffix : ByteArray) : OracleComp Source
    (Vector UInt8 32) :=
  ofOutput <$> Source.query (.inr (p, a, suffix))

/-- Resume production key generation at the top-tree root and pass the actual key to the client. -/
@[expose] def continuation (A : Adversary) (pp : PublicParam) : OracleComp Source Outcome := do
  let root ← node (hashOf sourcePass) pp sourcePrf .top LAYER_HEIGHT 0
  let pk : PublicKey := ⟨root, pp⟩
  let (candidate, log) ← (simulateQ (signerOf sourcePass sourceTick (fun _ =>
      sourcePrf)) (A.main pk)).run
  let valid ← verifyWith (hashOf sourcePass) pk candidate.message candidate.signature
  return ⟨pk, candidate, log, valid⟩

/-- Split the actual source at its first two physical queries. -/
theorem paid_prefix (A : Adversary) : paidSource A = (do
    let _ ← sourceTick
    let word ← (liftM (Source.query (.inr parameterLabel)) : OracleComp Source HashOutput)
    continuation A (parameterOfWord word)) := by
  let finish (pp : PublicParam) := do
    let root ← node (hashOf sourcePass) pp sourcePrf .top LAYER_HEIGHT 0
    pure (⟨root, pp⟩ : PublicKey)
  have read : publicParamOf sourcePrf = parameterOfWord <$>
      (liftM (Source.query (.inr parameterLabel)) : OracleComp Source HashOutput) := by
    simp only [publicParamOf, sourcePrf, bind_pure_comp]
    rfl
  have key : publicKeyOf (hashOf sourcePass) sourcePrf =
      ((liftM (Source.query (.inr parameterLabel)) : OracleComp Source HashOutput) >>=
        fun word => finish (parameterOfWord word)) := by
    unfold publicKeyOf
    rw [read, bind_map_left]
  change (sourceTick >>= fun _ => publicKeyOf (hashOf sourcePass) sourcePrf >>= _) = _
  rw [key]
  simp only [bind_assoc]
  apply bind_congr
  intro u
  apply bind_congr
  intro w
  simp only [finish, bind_assoc, pure_bind]
  rfl

attribute [local irreducible] continuation

/-- A budget of two plus an arbitrary remainder runs the corresponding capped continuation. -/
theorem cap_prefix (A : Adversary) (left : Nat) :
    WeightedCap.capCompOpt paidFee (left + 2) (paidSource A) = (do
      let _ ← sourceTick
      let word ← (liftM (Source.query (.inr parameterLabel)) : OracleComp Source HashOutput)
      WeightedCap.capCompOpt paidFee left (continuation A (parameterOfWord word))) := by
  rw [paid_prefix, WeightedCap.capCompOpt_query_bind]
  simp only [paidFee, ambientFee, Nat.le_add_left, ite_true]
  apply bind_congr
  intro u
  rw [WeightedCap.capCompOpt_query_bind]
  simp [paidFee]

/-- One paid call reaches the tick and stops before requesting the parameter. -/
theorem cap_one (A : Adversary) :
    WeightedCap.capCompOpt paidFee 1 (paidSource A) = (sourceTick >>= fun _ => pure none) := by
  rw [paid_prefix, WeightedCap.capCompOpt_query_bind]
  simp only [paidFee, ambientFee, Nat.le_refl, ite_true, Nat.sub_self]
  apply bind_congr
  intro u
  rw [WeightedCap.capCompOpt_query_bind]
  rfl

/-- Any applicable budget of at most one call gives zero keyed forge advantage. -/
theorem forge_zero_of_le_one (A : Adversary) (q : Nat) (small : q ≤ 1)
    (bounded : HasHashQueryBound A q) : forgeAdvantage A = 0 := by
  have one : HasHashQueryBound A 1 := fun z hz => (bounded z hz).trans small
  have h := forge_le_paid A 1 (by decide) one
  rw [cap_one, simulateQ_bind, StateT.run_bind] at h
  simp [simulateQ_pure, StateT.run_pure, accepted, prEvent_norm] at h
  exact h

/-- Exactly the tick and the complete parameter word are warm when the graph starts. -/
@[expose] noncomputable def afterWord (w : HashOutput) :
    SecretEncoding.SplitCache Backend PrfInput HashOutput :=
  ((∅ : Backend.QueryCache).cacheQuery (.inr ()) (),
    (∅ : (PrfInput →ₒ HashOutput).QueryCache).cacheQuery parameterLabel w)

open scoped OracleSpec.PrimitiveQuery in
/-- Both prefix queries pay once, then each realized branch starts with its own two cached entries.
-/
theorem cold_probability_le (A : Adversary) (left : Nat)
    (P : Option Outcome × SecretEncoding.SplitCache Backend PrfInput HashOutput → Prop)
    (bound : ℝ≥0∞) (each : ∀ w : HashOutput,
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl Backend PrfInput HashOutput)
        (WeightedCap.capCompOpt paidFee left (continuation A (parameterOfWord w)))).run
          (afterWord w)}[P z] ≤ bound) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl Backend PrfInput HashOutput)
      (WeightedCap.capCompOpt paidFee (left + 2) (paidSource A))).run (∅, ∅)}[P z] ≤ bound := by
  rw [cap_prefix]
  simp only [sourceTick, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  apply prEvent_bind_le_of_forall_le_of_support
  intro first reached
  rw [SecretEncoding.idealImpl_run_pub_none (by rfl), support_map] at reached
  obtain ⟨u, _, rfl⟩ := reached
  cases u
  apply prEvent_bind_le_of_forall_le_of_support
  intro second reached
  rw [SecretEncoding.idealImpl_run_derive_none (by rfl), support_map] at reached
  obtain ⟨w, _, rfl⟩ := reached
  exact each w

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
