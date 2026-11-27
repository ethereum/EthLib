module

public import ProofCoverageTest.Rules

/-!
# Property theorems of the fixtures, each with the pairs it touches
-/

@[expose] public section

namespace ProofCoverageTest

open EthLib.Base

/-- No fork variable, so every fork of the rule. -/
theorem eligible_iff (n : Nat) : eligible n = true ↔ n = 0 := by
  simp [eligible]

/-- From Altair, below Dencun: Altair, Bellatrix and Shapella. -/
theorem sync_bounded {fork : Fork} (altair : .altair ≤ fork) (_before : fork < .dencun)
    (n : Nat) : sync fork altair n = n := rfl

/-- With the bound written the other way, from Altair on. -/
theorem sync_eq {fork : Fork} (altair : fork ≥ .altair) (n : Nat) : sync fork altair n = n :=
  rfl

/-- A constructor in place of the fork: Glamsterdam only. -/
theorem payload_glamsterdam : payload .glamsterdam (Nat.le_refl _) = 0 := rfl

/-- A bound at Phase 0, at which the rule holds. -/
theorem early_eq {fork : Fork} (before : fork < .altair) : early fork before = 0 := rfl

/-- Another hypothesis on the fork, so it touches nothing. -/
theorem sync_odd {fork : Fork} (altair : .altair ≤ fork) (_h : fork ≠ .bellatrix) :
    sync fork altair 0 = 0 := rfl

/-- A private theorem touches nothing. -/
private theorem payload_private : payload .hegota (by decide) = 0 := rfl

end ProofCoverageTest
