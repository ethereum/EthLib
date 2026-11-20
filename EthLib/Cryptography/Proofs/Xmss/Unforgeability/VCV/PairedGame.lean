module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.ConcreteStatement
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PairedHashWord
import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial.Cost

/-!
# The security game with two cache rows per hash input

The leanXMSS specification draft, section "Security", measures the game in calls to the hash oracle.
The keyed signer determines the chance of a forgery.
The stateless signer determines the query budget.
Both games charge a repeated input again.

The paired oracle stores the two halves of a hash reply in separate rows.
Recording the charge before the two reads gives the caller its original cost.
-/

public section

open OracleComp OracleSpec

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.PairedGame

open PairedHashWord

/-- A public hash query costs one call and a private draw costs zero. -/
abbrev physicalCharge : XmssSecurity.OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- Record each charge on the original caller before expanding its hash queries. -/
@[expose] noncomputable def meter {α : Type} (p : OracleComp XmssSecurity.OracleWorld α) :
    OracleComp XmssSecurity.OracleWorld (α × Nat) :=
  (simulateQ ((QueryImpl.id' XmssSecurity.OracleWorld).withAddCost physicalCharge) p).runAdd

private theorem run_meter {α : Type} (p : OracleComp XmssSecurity.OracleWorld α) :
    simulateQ XmssSecurity.HashSpec.romImpl (meter p) = (simulateQ countedOracle p).run := by
  rw [meter, QueryImpl.simulateQ_withAddCost_runAdd_fusion]
  change (Prod.map id Multiplicative.toAdd <$> (simulateQ countedOracle p).run) = _
  exact id_map _

/-- Preserve the caller's reply and charge together with both forms of the final cache. -/
theorem counted_run_joint {α : Type} (p : OracleComp XmssSecurity.OracleWorld α)
    (initial : XmssSecurity.HashSpec.QueryCache) :
    (fun z : (α × Nat) × XmssSecurity.HashSpec.QueryCache => (z.1, z.2, splitCache z.2)) <$>
      ((simulateQ countedOracle p).run.run initial) =ᵈ
    (fun z : (α × Nat) × HalfSpec.QueryCache => (z.1, joinCache z.2, z.2)) <$>
      (simulateQ HalfSpec.romImpl (simulateQ readHalves (meter p))).run (splitCache initial) := by
  rw [← run_meter]
  exact run_joint _ _

/-- Discarding two cache representations keeps the caller's result. -/
private theorem result_of_joint {α σ τ : Type} (p : ProbComp (α × σ)) (r : ProbComp (α × τ))
    (f : σ → τ) (g : τ → σ)
    (h : (fun z : α × σ => (z.1, z.2, f z.2)) <$> p =ᵈ
      (fun z : α × τ => (z.1, g z.2, z.2)) <$> r) :
    Prod.fst <$> p =ᵈ Prod.fst <$> r := by
  have k := h.map (fun z : α × σ × τ => z.1)
  simpa only [Functor.map_map, Function.comp_def] using k

private theorem counted_run'_paired {α : Type} (p : OracleComp XmssSecurity.OracleWorld α)
    (initial : XmssSecurity.HashSpec.QueryCache) :
    (simulateQ countedOracle p).run.run' initial =ᵈ
      (simulateQ HalfSpec.romImpl (simulateQ readHalves (meter p))).run' (splitCache initial) := by
  rw [StateT.run'_eq, StateT.run'_eq]
  exact result_of_joint (α := α × Nat) _ _ splitCache joinCache (counted_run_joint p initial)

/-- Run the original game against two cache rows per hash and retain its physical charge. -/
@[expose] noncomputable def pairedExperiment (p : OracleComp XmssSecurity.OracleWorld Bool) :
    ProbComp (Bool × Nat) :=
  (simulateQ HalfSpec.romImpl (simulateQ readHalves (meter p))).run' (splitCache ∅)

/-- The stateless game has the same joint distribution of winning bit and charge. -/
theorem statelessExperiment_paired (adversary : Adversary) :
    statelessExperiment adversary =ᵈ pairedExperiment (statelessGameCore adversary) :=
  counted_run'_paired (statelessGameCore adversary) ∅

/-- Each budget on the stateless game transfers in both directions. -/
theorem hashQueryBound_iff_paired (adversary : Adversary) (q : Nat) :
    HasHashQueryBound adversary q ↔
      ∀ z ∈ support (pairedExperiment (statelessGameCore adversary)), z.2 ≤ q := by
  unfold HasHashQueryBound
  rw [support_eq_of_evalDistEq (statelessExperiment_paired adversary)]

/-- A forgery against the keyed signer has the same probability in both games. -/
theorem forgeAdvantage_eq_paired (adversary : Adversary) :
    forgeAdvantage adversary =
      Pr{let result ← pairedExperiment (gameCore adversary)}[result.1 = true] :=
  (counted_run'_paired (gameCore adversary) ∅).prEvent_eq _

/-- The stated number of security bits is equivalent to the same bound in the paired game. -/
theorem securityBits_iff_paired (bits : Nat) :
    HasClassicalSecurityBits bits ↔
      ∀ q, 1 ≤ q → ∀ adversary,
        (∀ z ∈ support (pairedExperiment (statelessGameCore adversary)), z.2 ≤ q) →
          Pr{let z ← pairedExperiment (gameCore adversary)}[z.1 = true] ≤
            q / ((2 ^ bits : Nat) : ENNReal) := by
  constructor
  · intro h q hq adversary bound
    exact (forgeAdvantage_eq_paired adversary).symm.trans_le
      (h q hq adversary ((hashQueryBound_iff_paired adversary q).2 bound))
  · intro h q hq adversary bound
    exact (forgeAdvantage_eq_paired adversary).trans_le
      (h q hq adversary ((hashQueryBound_iff_paired adversary q).1 bound))

end EthLib.Cryptography.Xmss.Unforgeability.VCV.PairedGame
