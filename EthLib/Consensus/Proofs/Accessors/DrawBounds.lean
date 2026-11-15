module

public import EthLib.Consensus.Proofs.Accessors.Draw

/-! Bounds for the checked comparison of a balance-weighted draw. -/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork}

/-- The largest effective balance that the draw of a fork compares against.

From Electra it is the cap of a compounding validator. -/
def drawCap (preset : Preset) (fork : Base.Fork) : Nat :=
  if .pectra ≤ fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  else preset.MAX_EFFECTIVE_BALANCE.toNat

/-- The products of the draw fit in 64 bits.

The draw compares the cap times a random value with a balance times the largest such value.

The value takes two bytes from Electra, and one before. -/
def DrawFits (preset : Preset) (fork : Base.Fork) : Prop :=
  if .pectra ≤ fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat * (2 ^ 16 - 1) < 2 ^ 64
  else preset.MAX_EFFECTIVE_BALANCE.toNat * (2 ^ 8 - 1) < 2 ^ 64

/-- A draw of a balance at most the cap succeeds, and accepts a balance at the cap. -/
theorem drawAccepts_ok_of_le (fits : DrawFits preset fork) (random : Bytes32) (i : Nat)
    {e : Gwei} (capped : e.toNat ≤ drawCap preset fork) :
    ∃ accepted, drawAccepts preset fork random i e = .ok accepted ∧
      (e.toNat = drawCap preset fork → accepted = true) := by
  unfold DrawFits at fits
  unfold drawCap at capped
  by_cases electra : .pectra ≤ fork
  · rw [ite_eq_left electra] at fits capped
    refine ⟨_, drawAccepts_eq_of_pectra preset fork electra random i e fits capped, ?_⟩
    intro atCap
    rw [atCap, drawCap, ite_eq_left electra]
    have small : i % 16 * 2 + 1 < 32 := by have := Nat.mod_lt i (by decide : 0 < 16); omega
    have low := (random[i % 16 * 2]'(by omega)).toNat_lt
    have high := random[i % 16 * 2 + 1].toNat_lt
    exact decide_eq_true (Nat.mul_le_mul_left _ (by omega))
  · rw [ite_eq_right electra] at fits capped
    refine ⟨_, drawAccepts_eq_of_before_pectra preset fork electra random i e fits capped, ?_⟩
    intro atCap
    rw [atCap, drawCap, ite_eq_right electra]
    have byte := (random[i % 32]'(Nat.mod_lt i (by decide))).toNat_lt
    exact decide_eq_true (Nat.mul_le_mul_left _ (by omega))

end EthLib.Consensus
