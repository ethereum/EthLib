module

public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Accessors
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range

/-!
# Proofs: acceptance of one balance-weighted draw

The accepted values form an inclusive interval starting at zero.

These are counts and deterministic comparisons, not probability or independence claims.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

/-- Count the accepted values of a `b`-bit draw, including zero even at zero balance. -/
theorem card_draw_values (b M e : Nat) (positive : 0 < M) (balance : e ≤ M) :
    ((Finset.range (2 ^ b)).filter (fun v => M * v ≤ e * (2 ^ b - 1))).card =
      e * (2 ^ b - 1) / M + 1 := by
  have bound : e * (2 ^ b - 1) / M ≤ 2 ^ b - 1 :=
    Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ balance)
  have nonempty : 0 < 2 ^ b := Nat.pow_pos (by decide)
  -- Division describes the inclusive endpoint, so the range has one more element.
  have interval : (Finset.range (2 ^ b)).filter (fun v => M * v ≤ e * (2 ^ b - 1)) =
      Finset.range (e * (2 ^ b - 1) / M + 1) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    have comparison : M * v ≤ e * (2 ^ b - 1) ↔ v ≤ e * (2 ^ b - 1) / M := by
      rw [Nat.le_div_iff_mul_le positive, Nat.mul_comm v M]
    rw [comparison]
    omega
  rw [interval, Finset.card_range]

/-- Before Electra, each draw reads one byte. -/
theorem card_draw_values_eight (M e : Nat) (positive : 0 < M) (balance : e ≤ M) :
    ((Finset.range (2 ^ 8)).filter (fun v => M * v ≤ e * (2 ^ 8 - 1))).card =
      e * (2 ^ 8 - 1) / M + 1 :=
  card_draw_values 8 M e positive balance

/-- From Electra, each draw reads two bytes. -/
theorem card_draw_values_sixteen (M e : Nat) (positive : 0 < M) (balance : e ≤ M) :
    ((Finset.range (2 ^ 16)).filter (fun v => M * v ≤ e * (2 ^ 16 - 1))).card =
      e * (2 ^ 16 - 1) / M + 1 :=
  card_draw_values 16 M e positive balance

/-- Zero balance accepts exactly one value, not zero values. -/
theorem card_draw_values_zero (b M : Nat) (positive : 0 < M) :
    ((Finset.range (2 ^ b)).filter (fun v => M * v ≤ 0 * (2 ^ b - 1))).card = 1 := by
  simpa using card_draw_values b M 0 positive (Nat.zero_le M)

/-- Full balance accepts every value. -/
theorem card_draw_values_full (b M : Nat) (positive : 0 < M) :
    ((Finset.range (2 ^ b)).filter (fun v => M * v ≤ M * (2 ^ b - 1))).card = 2 ^ b := by
  rw [card_draw_values b M M positive (Nat.le_refl M), Nat.mul_div_cancel_left _ positive]
  have : 0 < 2 ^ b := Nat.pow_pos (by decide)
  omega

private theorem checked_draw_comparison (M e v scale : UInt64)
    (leftFits : M.toNat * v.toNat < 2 ^ 64)
    (rightFits : e.toNat * scale.toNat < 2 ^ 64) :
    liftArith (do return decide ((← mulChecked M v) ≤ (← mulChecked e scale))) =
      .ok (decide (M.toNat * v.toNat ≤ e.toNat * scale.toNat)) := by
  simp [mulChecked_of_lt leftFits, mulChecked_of_lt rightFits, liftArith,
    bind, Except.bind, pure, Except.pure, Except.mapError,
    UInt64.le_iff_toNat_le, UInt64.toNat_mul, Nat.mod_eq_of_lt leftFits,
    Nat.mod_eq_of_lt rightFits]

/-- Before Electra, successful checked products compare the selected byte as a natural number. -/
theorem drawAccepts_eq_of_before_pectra (preset : Preset) (fork : Base.Fork)
    (before : ¬ .pectra ≤ fork) (random : Bytes32) (i : Nat) (e : Gwei)
    (leftFits : preset.MAX_EFFECTIVE_BALANCE.toNat *
      (random[i % 32]'(Nat.mod_lt i (by decide))).toNat < 2 ^ 64)
    (rightFits : e.toNat * (2 ^ 8 - 1) < 2 ^ 64) :
    drawAccepts preset fork random i e = .ok (decide
      (preset.MAX_EFFECTIVE_BALANCE.toNat *
        (random[i % 32]'(Nat.mod_lt i (by decide))).toNat ≤ e.toNat * (2 ^ 8 - 1))) := by
  simp only [drawAccepts, before, ↓reduceIte]
  have scaleNat : (2 ^ 8 - 1 : UInt64).toNat = 2 ^ 8 - 1 := by decide
  have rightFits' : e.toNat * (2 ^ 8 - 1 : UInt64).toNat < 2 ^ 64 := by rwa [scaleNat]
  simpa only [UInt8.toNat_toUInt64, scaleNat] using
    checked_draw_comparison preset.MAX_EFFECTIVE_BALANCE e
      (random[i % 32]'(Nat.mod_lt i (by decide))).toUInt64 (2 ^ 8 - 1) leftFits rightFits'

/-- From Electra, the two selected bytes form a little-endian natural number.

Both checked products must fit in 64 bits. -/
theorem drawAccepts_eq_of_pectra (preset : Preset) (fork : Base.Fork)
    (electra : .pectra ≤ fork) (random : Bytes32) (i : Nat) (e : Gwei) :
    let offset := i % 16 * 2
    have small : offset + 1 < 32 := by have := Nat.mod_lt i (by decide : 0 < 16); omega
    let value := (random[offset]'(by omega)).toNat + 256 * random[offset + 1].toNat
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat * value < 2 ^ 64 →
    e.toNat * (2 ^ 16 - 1) < 2 ^ 64 →
    drawAccepts preset fork random i e = .ok (decide
      (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat * value ≤ e.toNat * (2 ^ 16 - 1))) := by
  dsimp only
  intro leftFits rightFits
  have small : i % 16 * 2 + 1 < 32 := by have := Nat.mod_lt i (by decide : 0 < 16); omega
  -- Widening the bytes before arithmetic makes the little-endian sum exact.
  have valueNat : ((random[i % 16 * 2]'(by omega)).toUInt64 +
      256 * random[i % 16 * 2 + 1].toUInt64).toNat =
      random[i % 16 * 2].toNat + 256 * random[i % 16 * 2 + 1].toNat := by
    have low := (random[i % 16 * 2]'(by omega)).toNat_lt
    have high := random[i % 16 * 2 + 1].toNat_lt
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64]
    change (_ + (256 * _) % 2 ^ 64) % 2 ^ 64 = _
    omega
  simp only [drawAccepts, electra, ↓reduceIte]
  have leftFits' : preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat *
      ((random[i % 16 * 2]'(by omega)).toUInt64 +
        256 * random[i % 16 * 2 + 1].toUInt64).toNat < 2 ^ 64 := by
    rwa [valueNat]
  have scaleNat : (2 ^ 16 - 1 : UInt64).toNat = 2 ^ 16 - 1 := by decide
  have rightFits' : e.toNat * (2 ^ 16 - 1 : UInt64).toNat < 2 ^ 64 := by rwa [scaleNat]
  simpa only [valueNat, scaleNat] using
    checked_draw_comparison _ e _ (2 ^ 16 - 1) leftFits' rightFits'

end EthLib.Consensus
