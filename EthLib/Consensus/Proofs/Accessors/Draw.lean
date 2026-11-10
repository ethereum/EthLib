module

public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Accessors
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod

/-!
# Proofs: acceptance of one balance-weighted draw

It counts the values one draw accepts, as a function of the balance.

From Electra it also counts the pairs of bytes, read little-endian, that a draw accepts.

It also shows that the checked draw makes the same comparison on natural numbers.

This holds when the balance is at most the largest, and the largest times the scale fits in 64 bits.

It states counts, not probabilities.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

/-- When the balance `e` is at most `M`, a `b`-bit draw accepts the values up to an endpoint.

The endpoint is `e * (2^b - 1) / M`, so the value zero is always accepted. -/
theorem filter_draw_values (b M e : Nat) (positive : 0 < M) (balance : e ≤ M) :
    (Finset.range (2 ^ b)).filter (fun v => M * v ≤ e * (2 ^ b - 1)) =
      Finset.range (e * (2 ^ b - 1) / M + 1) := by
  have bound : e * (2 ^ b - 1) / M ≤ 2 ^ b - 1 :=
    Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ balance)
  have nonempty : 0 < 2 ^ b := Nat.pow_pos (by decide)
  ext v
  simp only [Finset.mem_filter, Finset.mem_range]
  have comparison : M * v ≤ e * (2 ^ b - 1) ↔ v ≤ e * (2 ^ b - 1) / M := by
    rw [Nat.le_div_iff_mul_le positive, Nat.mul_comm v M]
  rw [comparison]
  omega

/-- A `b`-bit draw accepts `e * (2^b - 1) / M + 1` values when the balance `e` is at most `M`. -/
theorem card_draw_values (b M e : Nat) (positive : 0 < M) (balance : e ≤ M) :
    ((Finset.range (2 ^ b)).filter (fun v => M * v ≤ e * (2 ^ b - 1))).card =
      e * (2 ^ b - 1) / M + 1 := by
  rw [filter_draw_values b M e positive balance, Finset.card_range]

/-- Zero balance accepts exactly one value. -/
theorem card_draw_values_zero (b M : Nat) (positive : 0 < M) :
    ((Finset.range (2 ^ b)).filter (fun v => M * v ≤ 0)).card = 1 := by
  simpa using card_draw_values b M 0 positive (Nat.zero_le M)

/-- A balance equal to the largest accepts all `2^b` values. -/
theorem card_draw_values_full (b M : Nat) (positive : 0 < M) :
    ((Finset.range (2 ^ b)).filter (fun v => M * v ≤ M * (2 ^ b - 1))).card = 2 ^ b := by
  rw [card_draw_values b M M positive (Nat.le_refl M), Nat.mul_div_cancel_left _ positive]
  have : 0 < 2 ^ b := Nat.pow_pos (by decide)
  omega

/-- Pairs of digits below `k`, read as `low + k * high`, match the values below `k * k`. -/
private theorem card_filter_digit_pairs (k : Nat) (P : Nat → Prop) [DecidablePred P] :
    ((Finset.range k ×ˢ Finset.range k).filter (fun p => P (p.1 + k * p.2))).card =
      ((Finset.range (k * k)).filter P).card := by
  apply Finset.card_nbij' (fun p => p.1 + k * p.2) (fun v => (v % k, v / k))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    refine ⟨?_, hp.2⟩
    have step : k * (p.2 + 1) = k * p.2 + k := Nat.mul_succ k p.2
    have : k * (p.2 + 1) ≤ k * k := Nat.mul_le_mul_left _ hp.1.2
    omega
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hv ⊢
    have positive : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hv)
    rw [Nat.mod_add_div]
    exact ⟨⟨Nat.mod_lt _ positive, Nat.div_lt_of_lt_mul hv.1⟩, hv.2⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    have positive : 0 < k := by omega
    ext
    · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1.1]
    · simp [Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt hp.1.1]
  · intro v _
    exact Nat.mod_add_div v k

/-- A draw from Electra accepts `e * (2^16 - 1) / M + 1` pairs of bytes.

The first byte of a pair is the low one, so the pair reads as the first plus 256 times the second.

The balance `e` must be at most `M`, and `M` must be positive. -/
theorem card_draw_byte_pairs (M e : Nat) (positive : 0 < M) (balance : e ≤ M) :
    ((Finset.range 256 ×ˢ Finset.range 256).filter
      (fun p => M * (p.1 + 256 * p.2) ≤ e * (2 ^ 16 - 1))).card =
      e * (2 ^ 16 - 1) / M + 1 := by
  have size : (256 : Nat) * 256 = 2 ^ 16 := by decide
  rw [card_filter_digit_pairs 256 (fun v => M * v ≤ e * (2 ^ 16 - 1)), size]
  exact card_draw_values 16 M e positive balance

private theorem checked_draw_comparison (M e v scale : UInt64)
    (leftFits : M.toNat * v.toNat < 2 ^ 64)
    (rightFits : e.toNat * scale.toNat < 2 ^ 64) :
    liftArith (do return decide ((← mulChecked M v) ≤ (← mulChecked e scale))) =
      .ok (decide (M.toNat * v.toNat ≤ e.toNat * scale.toNat)) := by
  simp [mulChecked_of_lt leftFits, mulChecked_of_lt rightFits, liftArith,
    bind, Except.bind, pure, Except.pure, Except.mapError,
    UInt64.le_iff_toNat_le, UInt64.toNat_mul]
  -- Both products are below the modulus, so reducing them changes nothing.
  omega

/-- The two products of a draw fit in 64 bits when the balance is at most the largest one.

It needs the largest balance times the scale `2^b - 1` to fit, and a value below `2^b`. -/
private theorem draw_products_fit (b M e v : Nat) (balance : e ≤ M) (value : v < 2 ^ b)
    (fits : M * (2 ^ b - 1) < 2 ^ 64) : M * v < 2 ^ 64 ∧ e * (2 ^ b - 1) < 2 ^ 64 :=
  ⟨Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) fits,
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ balance) fits⟩

/-- Before Electra, the draw compares the selected byte as a natural number.

The largest effective balance times `2^8 - 1` must fit in 64 bits.

The balance must be at most the largest effective balance. -/
theorem drawAccepts_eq_of_before_pectra (preset : Preset) (fork : Base.Fork)
    (before : ¬ .pectra ≤ fork) (random : Bytes32) (i : Nat) (e : Gwei)
    (fits : preset.MAX_EFFECTIVE_BALANCE.toNat * (2 ^ 8 - 1) < 2 ^ 64)
    (balance : e.toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat) :
    drawAccepts preset fork random i e = .ok (decide
      (preset.MAX_EFFECTIVE_BALANCE.toNat *
        (random[i % 32]'(Nat.mod_lt i (by decide))).toNat ≤ e.toNat * (2 ^ 8 - 1))) := by
  simp only [drawAccepts, before, ↓reduceIte]
  have byte := (random[i % 32]'(Nat.mod_lt i (by decide))).toNat_lt
  obtain ⟨leftFits, rightFits⟩ := draw_products_fit 8 _ _ _ balance byte fits
  have scaleNat : (2 ^ 8 - 1 : UInt64).toNat = 2 ^ 8 - 1 := by decide
  have rightFits' : e.toNat * (2 ^ 8 - 1 : UInt64).toNat < 2 ^ 64 := by rwa [scaleNat]
  simpa only [UInt8.toNat_toUInt64, scaleNat] using
    checked_draw_comparison preset.MAX_EFFECTIVE_BALANCE e
      (random[i % 32]'(Nat.mod_lt i (by decide))).toUInt64 (2 ^ 8 - 1) leftFits rightFits'

/-- From Electra, the draw compares the two selected bytes as a little-endian natural number.

The bytes start at `2 * (i mod 16)`.

The largest effective balance times `2^16 - 1` must fit in 64 bits.

The balance must be at most the largest effective balance. -/
theorem drawAccepts_eq_of_pectra (preset : Preset) (fork : Base.Fork)
    (electra : .pectra ≤ fork) (random : Bytes32) (i : Nat) (e : Gwei)
    (fits : preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat * (2 ^ 16 - 1) < 2 ^ 64)
    (balance : e.toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) :
    drawAccepts preset fork random i e = .ok (decide
      (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat *
        ((random[i % 16 * 2]'(by have := Nat.mod_lt i (by decide : 0 < 16); omega)).toNat +
          256 * (random[i % 16 * 2 + 1]'(by
            have := Nat.mod_lt i (by decide : 0 < 16); omega)).toNat) ≤
        e.toNat * (2 ^ 16 - 1))) := by
  have small : i % 16 * 2 + 1 < 32 := by have := Nat.mod_lt i (by decide : 0 < 16); omega
  have low := (random[i % 16 * 2]'(by omega)).toNat_lt
  have high := random[i % 16 * 2 + 1].toNat_lt
  -- Widening the bytes before arithmetic makes the little-endian sum exact.
  have valueNat : ((random[i % 16 * 2]'(by omega)).toUInt64 +
      256 * random[i % 16 * 2 + 1].toUInt64).toNat =
      random[i % 16 * 2].toNat + 256 * random[i % 16 * 2 + 1].toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64]
    change (_ + (256 * _) % 2 ^ 64) % 2 ^ 64 = _
    omega
  obtain ⟨leftFits, rightFits⟩ := draw_products_fit 16 _ _
    (random[i % 16 * 2].toNat + 256 * random[i % 16 * 2 + 1].toNat) balance (by omega) fits
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
