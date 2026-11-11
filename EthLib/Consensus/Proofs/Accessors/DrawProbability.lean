module

public import EthLib.Consensus.Proofs.Accessors.Draw
public import EthLib.Cryptography.Proofs.EvalDistEq

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Proofs: acceptance probability of one balance-weighted draw

The digest supplied to `drawAccepts` is sampled uniformly from the 32-byte values.

Selecting distinct byte positions preserves the uniform distribution on those bytes.

The acceptance counts then give the exact probability of a successful checked draw.

The balance must be at most the positive largest balance, whose product with the scale must fit.

This model samples one digest; it makes no claim about SHA-256 or a sequence of proposer draws.
-/

@[expose] public section

namespace EthLib.Consensus

open Base OracleComp OracleSpec ENNReal

/-- Distinct positions of a uniform digest give a uniform tuple of bytes. -/
theorem evalDist_uniform_bytes32_select {n : Nat} (positions : Fin n → Fin 32)
    (distinct : Function.Injective positions) :
    ((fun random : Bytes32 => fun j => random[(positions j).val]) <$> ($ᵗ Bytes32)) =ᵈ
      ($ᵗ (Fin n → UInt8)) := by
  calc
    _ =ᵈ ((fun bytes : Fin 32 → UInt8 => bytes ∘ positions) <$>
        (arrayVectorEquivFin UInt8 32 <$> ($ᵗ Bytes32))) := by
      simp only [Functor.map_map]
      exact EvalDistEq.rfl
    _ =ᵈ ((fun bytes : Fin 32 → UInt8 => bytes ∘ positions) <$>
        ($ᵗ (Fin 32 → UInt8))) :=
      (SampleableType.map_uniformSample_evalDistEq_of_bijective
        (arrayVectorEquivFin UInt8 32).bijective).map _
    _ =ᵈ ($ᵗ (Fin n → UInt8)) :=
      evalDistEq_uniformSample_map_comp_injective distinct

private theorem evalDist_uniform_bytes32_byte (j : Fin 32) :
    ((fun random : Bytes32 => random[j.val]) <$> ($ᵗ Bytes32)) =ᵈ ($ᵗ UInt8) := by
  have selected := evalDist_uniform_bytes32_select (fun _ : Fin 1 => j)
    (fun _ _ _ => Subsingleton.elim _ _)
  calc
    _ =ᵈ ((Equiv.funUnique (Fin 1) UInt8) <$>
        ((fun random : Bytes32 => fun _ : Fin 1 => random[j.val]) <$> ($ᵗ Bytes32))) := by
      simp only [Functor.map_map]
      exact EvalDistEq.rfl
    _ =ᵈ ((Equiv.funUnique (Fin 1) UInt8) <$> ($ᵗ (Fin 1 → UInt8))) := selected.map _
    _ =ᵈ ($ᵗ UInt8) :=
      SampleableType.map_uniformSample_evalDistEq_of_bijective
        (Equiv.funUnique (Fin 1) UInt8).bijective

private theorem evalDist_uniform_bytes32_pair (j k : Fin 32) (different : j ≠ k) :
    ((fun random : Bytes32 => (random[j.val], random[k.val])) <$> ($ᵗ Bytes32)) =ᵈ
      ($ᵗ (UInt8 × UInt8)) := by
  let positions : Fin 2 → Fin 32 := ![j, k]
  have distinct : Function.Injective positions := by
    intro a b same
    fin_cases a <;> fin_cases b <;> simp_all [positions]
  have selected := evalDist_uniform_bytes32_select positions distinct
  calc
    _ =ᵈ (finTwoArrowEquiv UInt8 <$>
        ((fun random : Bytes32 => fun a => random[(positions a).val]) <$> ($ᵗ Bytes32))) := by
      simp only [Functor.map_map]
      exact EvalDistEq.rfl
    _ =ᵈ (finTwoArrowEquiv UInt8 <$> ($ᵗ (Fin 2 → UInt8))) := selected.map _
    _ =ᵈ ($ᵗ (UInt8 × UInt8)) :=
      SampleableType.map_uniformSample_evalDistEq_of_bijective (finTwoArrowEquiv UInt8).bijective

private theorem card_filter_bytes (P : Nat → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun byte : UInt8 => P byte.toNat)).card =
      ((Finset.range (2 ^ 8)).filter P).card := by
  apply Finset.card_nbij UInt8.toNat
  · intro byte accepted
    simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range] using And.intro byte.toNat_lt (Finset.mem_filter.mp accepted).2
  · intro a _ b _ same
    exact UInt8.toNat_inj.mp same
  · intro value accepted
    obtain ⟨small, accepted⟩ := Finset.mem_filter.mp accepted
    have valueNat : (UInt8.ofNat value).toNat = value :=
      UInt8.toNat_ofNat_of_lt' (by simpa using Finset.mem_range.mp small)
    exact ⟨UInt8.ofNat value, by simpa [valueNat] using accepted, valueNat⟩

private theorem card_filter_byte_pairs (P : Nat × Nat → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun pair : UInt8 × UInt8 => P (pair.1.toNat, pair.2.toNat))).card =
      ((Finset.range 256 ×ˢ Finset.range 256).filter P).card := by
  apply Finset.card_nbij (fun pair : UInt8 × UInt8 => (pair.1.toNat, pair.2.toNat))
  · simp only [Set.MapsTo, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_range]
    intro pair accepted
    exact ⟨⟨pair.1.toNat_lt, pair.2.toNat_lt⟩, accepted⟩
  · intro a _ b _ same
    exact Prod.ext (UInt8.toNat_inj.mp (congrArg Prod.fst same))
      (UInt8.toNat_inj.mp (congrArg Prod.snd same))
  · simp only [Set.SurjOn, Set.subset_def, Set.mem_image, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Finset.mem_range]
    intro pair accepted
    obtain ⟨⟨low, high⟩, accepted⟩ := accepted
    have lowNat : (UInt8.ofNat pair.1).toNat = pair.1 := UInt8.toNat_ofNat_of_lt' low
    have highNat : (UInt8.ofNat pair.2).toNat = pair.2 := UInt8.toNat_ofNat_of_lt' high
    exact ⟨(UInt8.ofNat pair.1, UInt8.ofNat pair.2),
      by simpa only [lowNat, highNat] using accepted,
      by simp [lowNat, highNat]⟩

/-- Before Electra, a uniform digest gives the accepted fraction of the 256 byte values.

The largest balance is positive, the balance is at most it, and both products fit in 64 bits. -/
theorem prEvent_drawAccepts_uniform_of_before_pectra (preset : Preset) (fork : Base.Fork)
    (before : ¬ .pectra ≤ fork) (i : Nat) (e : Gwei)
    (positive : 0 < preset.MAX_EFFECTIVE_BALANCE.toNat)
    (balance : e.toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat)
    (fits : preset.MAX_EFFECTIVE_BALANCE.toNat * (2 ^ 8 - 1) < 2 ^ 64) :
    Pr{let random ← $ᵗ Bytes32}[drawAccepts preset fork random i e = .ok true] =
      ((e.toNat * (2 ^ 8 - 1) / preset.MAX_EFFECTIVE_BALANCE.toNat + 1 : Nat) : ℝ≥0∞) /
        2 ^ 8 := by
  have same : (fun random : Bytes32 => drawAccepts preset fork random i e = .ok true) =
      (fun random => preset.MAX_EFFECTIVE_BALANCE.toNat *
        (random[i % 32]'(Nat.mod_lt i (by decide))).toNat ≤ e.toNat * (2 ^ 8 - 1)) := by
    funext random
    simp only [drawAccepts_eq_of_before_pectra preset fork before random i e fits balance,
      Except.ok.injEq, decide_eq_true_eq]
  rw [same]
  have selected := (evalDist_uniform_bytes32_byte ⟨i % 32, Nat.mod_lt i (by decide)⟩).prEvent_eq
    (fun byte => preset.MAX_EFFECTIVE_BALANCE.toNat * byte.toNat ≤ e.toNat * (2 ^ 8 - 1))
  rw [prEvent_map] at selected
  rw [selected]
  rw [SampleableType.prEvent_uniformSample,
    card_filter_bytes (fun value => preset.MAX_EFFECTIVE_BALANCE.toNat * value ≤
      e.toNat * (2 ^ 8 - 1)),
    card_draw_values 8 _ _ positive balance]
  simp only [← FinEnum.card_eq_fintypeCard (α := UInt8), FinEnum.card_UInt8,
    Nat.cast_pow, Nat.cast_ofNat]

/-- From Electra, a uniform digest gives the accepted fraction of the 65536 byte pairs.

The largest balance is positive, the balance is at most it, and both products fit in 64 bits. -/
theorem prEvent_drawAccepts_uniform_of_pectra (preset : Preset) (fork : Base.Fork)
    (electra : .pectra ≤ fork) (i : Nat) (e : Gwei)
    (positive : 0 < preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (balance : e.toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (fits : preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat * (2 ^ 16 - 1) < 2 ^ 64) :
    Pr{let random ← $ᵗ Bytes32}[drawAccepts preset fork random i e = .ok true] =
      ((e.toNat * (2 ^ 16 - 1) / preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat + 1 : Nat) : ℝ≥0∞) /
        2 ^ 16 := by
  have small : i % 16 * 2 + 1 < 32 := by have := Nat.mod_lt i (by decide : 0 < 16); omega
  have same : (fun random : Bytes32 => drawAccepts preset fork random i e = .ok true) =
      (fun random => preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat *
        ((random[i % 16 * 2]'(by omega)).toNat +
          256 * random[i % 16 * 2 + 1].toNat) ≤ e.toNat * (2 ^ 16 - 1)) := by
    funext random
    simp only [drawAccepts_eq_of_pectra preset fork electra random i e fits balance,
      Except.ok.injEq, decide_eq_true_eq]
  rw [same]
  have selected := (evalDist_uniform_bytes32_pair ⟨i % 16 * 2, by omega⟩
    ⟨i % 16 * 2 + 1, small⟩ (by
      intro same
      have impossible : i % 16 * 2 = i % 16 * 2 + 1 := congrArg Fin.val same
      omega)).prEvent_eq
    (fun pair => preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat *
      (pair.1.toNat + 256 * pair.2.toNat) ≤ e.toNat * (2 ^ 16 - 1))
  rw [prEvent_map] at selected
  rw [selected]
  rw [SampleableType.prEvent_uniformSample,
    card_filter_byte_pairs (fun pair => preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat *
      (pair.1 + 256 * pair.2) ≤ e.toNat * (2 ^ 16 - 1)),
    card_draw_byte_pairs _ _ positive balance]
  rw [Fintype.card_prod]
  simp only [← FinEnum.card_eq_fintypeCard (α := UInt8), FinEnum.card_UInt8,
    Nat.cast_pow, Nat.cast_ofNat, ← pow_add]

end EthLib.Consensus
