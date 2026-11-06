module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.PreparedRun
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.Memo
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.CoverPotential.OneCoinGame

/-!
# The start value of the one-coin potential

At the start of the run, a new pair has a one-coin excess forecast.

That forecast is the start value of the future-pair term of the one-coin FORS potential.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
    HiddenReveal SphincsSecurity.Base.Domination

set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable


section TotalO

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable
    highsSampleable
  remainingSampleable

/-- The one-coin excess forecast of a new pair at the start of the run. -/
noncomputable def startExcessO (wbar b0 : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar
      (excess b0) signatureLimit I 0) k []

theorem hValueO_start (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (s : State)
    (k : ℕ) :
    hValueO parameter data wbar b0 s [] [] 0 signatureLimit k = startExcessO wbar b0 k := rfl

/-- At the start no digest block is cached, so the empty list of touched messages is valid. -/
theorem start_minv (parameter : PublicParameter) (data : PublicData)
    (initial : HiddenOutside.Cache HashInput HashOutput)
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (known : Knowledge Coordinate) : MInv parameter data (DebtState.start initial known) [] :=
  ⟨List.nodup_nil, fun m ρ h => absurd (hclean (m, ρ) firstCall) h⟩

/-- At the start of the run, the potential is at most a sum of three terms.

The terms charge the future pairs, the failing indices and the cap of the landed pairs. -/
theorem potO_start_le (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞)
    (Fail : Finset (Fin (2 ^ subtreeHeight))) (tg : Targeting HashInput HashOutput Coordinate)
    (initial : HiddenOutside.Cache HashInput HashOutput) (Lmax : ℕ) (s : State) (k : ℕ) :
    potO parameter data wbar b0 Fail tg initial Lmax s [] [] [] 0 k ≤
      (k * (startExcessO wbar b0 k + failMass Fail) + signatureLimit * failMass Fail) +
          lam Lmax 0 k := by
  unfold potO
  refine add_le_add ?_ (le_of_eq rfl)
  split_ifs
  · exact bot_le
  · unfold coreO
    simp only [List.map_nil, List.sum_nil, zero_add, List.length_nil, Nat.sub_zero]
    rw [hValueO_start]

end TotalO

end SphincsSecurity.Security.ForsPotential
