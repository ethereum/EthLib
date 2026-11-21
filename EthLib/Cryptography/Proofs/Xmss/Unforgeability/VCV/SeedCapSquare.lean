module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.OriginalCap
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed.Unit

/-!
# The current capped master source evaluated through a paid private table

Fixing the scheme word leaves every corresponding paid tick in place.

Both sides stop before the same first unaffordable query.

The complete raw observation and the retained full cache survive presampling.

Source: leanXMSS draft, sections "The scheme" and "Security".
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient

open OracleComp OracleSpec
open XmssSecurity (HashSpec HashOutput)
open scoped Classical

/-- The ordinary hash and tick both represent physical calls. -/
@[expose] def ambientFee : Ambient.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- Every private PRF derivation represents one physical call, like an ordinary hash. -/
@[expose] def paidFee : Source.Domain → Nat
  | .inl t => ambientFee t
  | .inr _ => 1

private def payIndex : SeedSpec.Domain → Ambient.Domain
  | .inl (.inl n) => .inl n
  | .inl (.inr k) => .inr (.inl k)
  | .inr _ => .inr (.inr ())

private def payAnswer (word : HashOutput) (t : SeedSpec.Domain) : Ambient.Range (payIndex t) →
    SeedSpec.Range t :=
  match t with | .inl (.inl _) => id | .inl (.inr _) => id | .inr _ => fun _ => word

private def rawIndex (word : HashOutput) : Source.Domain → Ambient.Domain
  | .inl t => t
  | .inr k => .inr (paidEncoding.enc word k)

private theorem rawRange (word : HashOutput) (t : Source.Domain) :
    Ambient.Range (rawIndex word t) = Source.Range t := by cases t <;> rfl

/-- Both seed interpreters commute with the same original budget, including a stopped execution. -/
theorem capped_square (word : HashOutput) (A : Adversary) (q : Nat) :
    simulateQ (payMaster word) (WeightedCap.capCompOpt masterFee q (masterSource A)) =
      simulateQ (paidEncoding.deriveImpl word) (WeightedCap.capCompOpt paidFee q
        (paidSource A)) := by
  have pay : (fun t => payAnswer word t
      <$> (liftM (Ambient.query (payIndex t)) : OracleComp Ambient _)) =
      payMaster word := by
    funext t
    rcases t with (n | k) | u <;> rfl
  have raw : (fun t => (cast (rawRange word t))
      <$> (liftM (Ambient.query (rawIndex word t)) : OracleComp Ambient _)) =
      paidEncoding.deriveImpl word := by
    funext t
    rcases t with (n | k) | x <;> rfl
  have left := WeightedCap.simulateQ_capCompOpt_single_query masterFee ambientFee payIndex
    (payAnswer word) (fun t => by rcases t with (n | k) | u <;> rfl) (masterSource A) q
  have right := WeightedCap.simulateQ_capCompOpt_single_query paidFee ambientFee (rawIndex word)
    (fun t => cast (rawRange word t)) (fun t => by cases t <;> rfl) (paidSource A) q
  rw [pay] at left
  rw [raw] at right
  rw [left, right, paid_square]

private theorem master_head (A : Adversary) :
    ∃ k : HashOutput → OracleComp SeedSpec Outcome,
      masterSource A = liftM (SeedSpec.query (.inr ())) >>= k := by
  simp only [masterSource, sourceOf, bind_map_left]
  exact ⟨_, rfl⟩

/-- For q > 0, the first private query samples a word.

Each later tick and the final cache readback use that same word.
-/
theorem capped_presample (A : Adversary) (q : Nat) (positive : 0 < q) :
    (simulateQ (SecretEncoding.idealImpl HashSpec Unit HashOutput)
        (WeightedCap.capCompOpt masterFee q (masterSource A))).run (∅, ∅) =ᵈ
      (do
        let word ← ($ᵗ HashOutput : ProbComp HashOutput)
        let z ← (simulateQ (paidEncoding.realImpl word) (WeightedCap.capCompOpt paidFee q
          (paidSource A))).run ∅
        pure (z.1, SecretEncoding.paidUnitReadback HashSpec word z.2)) := by
  obtain ⟨k, first⟩ := master_head A
  have head : WeightedCap.capCompOpt masterFee q (masterSource A) =
      liftM (SeedSpec.query (.inr ())) >>= fun w =>
        WeightedCap.capCompOpt masterFee (q - 1) (k w) := by
    rw [first, WeightedCap.capCompOpt_query_bind]
    split_ifs with paid
    · rfl
    · exact False.elim (paid positive)
  have cold := SecretEncoding.idealImpl_run_presample_first_derive HashSpec ()
    (fun w => WeightedCap.capCompOpt masterFee (q - 1) (k w)) (∅, ∅) (by rfl)
  erw [← head] at cold
  rw [cold]
  apply EvalDistEq.bind_right
  intro word
  have same : SecretEncoding.paidInlineUnitDerivations HashSpec word = payMaster word := by
    funext t
    rcases t with (n | k) | u <;> rfl
  have init : SecretEncoding.paidUnitReadback HashSpec word (∅ : Backend.QueryCache) =
      (∅, SecretEncoding.unitCache word) := by
    rw [← QueryCache.addEquiv_empty (spec₁ := HashSpec) (spec₂ := Tick),
      SecretEncoding.paidUnitReadback_addEquiv]
  have warm := (SecretEncoding.map_run_simulateQ_paidInlineUnitDerivations HashSpec word
    (WeightedCap.capCompOpt masterFee q (masterSource A)) ∅).symm
  rw [same, capped_square, ← QueryImpl.simulateQ_compose] at warm
  have project : Prod.map (id : Option Outcome →
      _) (SecretEncoding.paidUnitReadback HashSpec word) =
      (fun z : Option Outcome × Backend.QueryCache =>
        (z.1, SecretEncoding.paidUnitReadback HashSpec word z.2)) := by
    funext ⟨o, cache⟩
    rfl
  erw [project] at warm
  simpa only [SecretEncoding.empty_cacheQuery_unit, init, bind_pure_comp,
      SecretEncoding.realImpl] using warm

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
