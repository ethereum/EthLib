module

public import EthLib.Consensus.Proofs.Accessors.Draw
public import EthLib.Cryptography.Proofs.UniformReads

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Proofs: acceptance probability of one balance-weighted draw

A draw reads a random value of `b` bits from a digest: one byte before Electra, two from Electra.

It accepts a balance `e` when `M * value ≤ e * (2^b - 1)`.

Here `M` is the largest effective balance of the preset.

The digest is uniform among the 32-byte values.

The checked draw then accepts with probability `(⌊e * (2^b - 1) / M⌋ + 1) / 2^b`.

This needs `0 < M`, `e ≤ M`, and `M * (2^b - 1) < 2^64`.

Two draws whose numbers differ modulo the draws per digest read disjoint bytes.

So the two draws are independent.

The model samples one digest; it makes no claim about SHA-256 or a sequence of proposer draws.
-/

@[expose] public section

namespace EthLib.Consensus

open Base OracleComp OracleSpec ENNReal

private theorem evalDist_uniform_bytes32_byte (j : Fin 32) :
    ((fun random : Bytes32 => random[j.val]) <$> ($ᵗ Bytes32)) =ᵈ ($ᵗ UInt8) := by
  have selected := evalDistEq_uniformSample_vector_map_getElem_injective
    (R := UInt8) (m := 32) (e := fun _ : Fin 1 => j) (fun _ _ _ => Subsingleton.elim _ _)
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
  have selected := evalDistEq_uniformSample_vector_map_getElem_injective
    (R := UInt8) (m := 32) distinct
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

/-- Before Electra, the draw accepts with probability `(⌊e * (2^8 - 1) / M⌋ + 1) / 2^8`.

The digest is uniform, `e` is the balance and `M` the largest effective balance of the preset.

It needs `0 < M`, `e ≤ M`, and `M * (2^8 - 1) < 2^64`. -/
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

/-- From Electra, the draw accepts with probability `(⌊e * (2^16 - 1) / M⌋ + 1) / 2^16`.

The digest is uniform, `e` is the balance and `M` the largest effective balance of the preset.

It needs `0 < M`, `e ≤ M`, and `M * (2^16 - 1) < 2^64`. -/
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

/-- Events read from two disjoint ranges of a uniform vector have the product chance. -/
private theorem prEvent_uniformSample_vector_two_ranges_comp {R α β : Type} [Finite R]
    [Nonempty R] [SampleableType R] {m : Nat} (a k b l : Nat) (first : a + k ≤ m)
    (second : b + l ≤ m) (apart : a + k ≤ b ∨ b + l ≤ a) (F : Vector R k → α)
    (G : Vector R l → β) (P : α → Prop) (Q : β → Prop) :
    Pr{let v ← $ᵗ (Vector R m)}[P (F (Vector.ofFn fun j : Fin k => v[a + j.val])) ∧
        Q (G (Vector.ofFn fun j : Fin l => v[b + j.val]))] =
      Pr{let v ← $ᵗ (Vector R m)}[P (F (Vector.ofFn fun j : Fin k => v[a + j.val]))] *
        Pr{let v ← $ᵗ (Vector R m)}[Q (G (Vector.ofFn fun j : Fin l => v[b + j.val]))] := by
  refine (prEvent_uniformSample_vector_two_ranges a k b l first second apart
    (P ∘ F) (Q ∘ G)).trans ?_
  have first' := (evalDistEq_uniformSample_vector_range a k first).prEvent_eq (P ∘ F)
  have second' := (evalDistEq_uniformSample_vector_range b l second).prEvent_eq (Q ∘ G)
  rw [prEvent_map] at first' second'
  rw [← first', ← second']
  rfl

/-- Before Electra, a draw depends on the digest only through the byte it reads. -/
private theorem drawAccepts_eq_of_byte (preset : Preset) (fork : Base.Fork)
    (before : ¬ .pectra ≤ fork) (i : Nat) (e : Gwei) (random : Bytes32) :
    drawAccepts preset fork random i e = drawAccepts preset fork
      (Vector.replicate 32 (Vector.ofFn fun j : Fin 1 => random[i % 32 + j.val])[0]) i e := by
  simp only [drawAccepts, before, ↓reduceIte, Vector.getElem_replicate, Vector.getElem_ofFn]
  rfl

/-- From Electra, a draw depends on the digest only through the two bytes it reads. -/
private theorem drawAccepts_eq_of_byte_pair (preset : Preset) (fork : Base.Fork)
    (electra : .pectra ≤ fork) (i : Nat) (e : Gwei) (random : Bytes32) :
    drawAccepts preset fork random i e = drawAccepts preset fork
      (Vector.ofFn fun t : Fin 32 => if t.val = i % 16 * 2 then
        (Vector.ofFn fun j : Fin 2 => random[i % 16 * 2 + j.val])[0] else
        (Vector.ofFn fun j : Fin 2 => random[i % 16 * 2 + j.val])[1]) i e := by
  simp only [drawAccepts, electra, ↓reduceIte, Vector.getElem_ofFn]
  simp

/-- Two draws at different places of one uniform digest are independent.

Two draws are at different places when their numbers differ modulo the draws per digest.

So an event on the first and an event on the second have the product chance. -/
theorem prEvent_drawAccepts_pair_uniform (preset : Preset) (fork : Base.Fork) (i j : Nat)
    (e f : Gwei) (different : i % drawsPerHash fork ≠ j % drawsPerHash fork)
    (P Q : Except AccessorError Bool → Prop) :
    Pr{let random ← $ᵗ Bytes32}[P (drawAccepts preset fork random i e) ∧
        Q (drawAccepts preset fork random j f)] =
      Pr{let random ← $ᵗ Bytes32}[P (drawAccepts preset fork random i e)] *
        Pr{let random ← $ᵗ Bytes32}[Q (drawAccepts preset fork random j f)] := by
  by_cases electra : .pectra ≤ fork
  · have places : i % 16 ≠ j % 16 := by simpa [drawsPerHash, electra] using different
    obtain ⟨F, first⟩ : ∃ F : Vector UInt8 2 → Except AccessorError Bool, ∀ random : Bytes32,
        drawAccepts preset fork random i e =
          F (Vector.ofFn fun t : Fin 2 => random[i % 16 * 2 + t.val]) :=
      ⟨fun bytes => drawAccepts preset fork (Vector.ofFn fun t : Fin 32 =>
        if t.val = i % 16 * 2 then bytes[0] else bytes[1]) i e,
        drawAccepts_eq_of_byte_pair preset fork electra i e⟩
    obtain ⟨G, second⟩ : ∃ G : Vector UInt8 2 → Except AccessorError Bool, ∀ random : Bytes32,
        drawAccepts preset fork random j f =
          G (Vector.ofFn fun t : Fin 2 => random[j % 16 * 2 + t.val]) :=
      ⟨fun bytes => drawAccepts preset fork (Vector.ofFn fun t : Fin 32 =>
        if t.val = j % 16 * 2 then bytes[0] else bytes[1]) j f,
        drawAccepts_eq_of_byte_pair preset fork electra j f⟩
    simp only [first, second]
    exact prEvent_uniformSample_vector_two_ranges_comp _ _ _ _ (by omega) (by omega)
      (by omega) F G P Q
  · have places : i % 32 ≠ j % 32 := by simpa [drawsPerHash, electra] using different
    obtain ⟨F, first⟩ : ∃ F : Vector UInt8 1 → Except AccessorError Bool, ∀ random : Bytes32,
        drawAccepts preset fork random i e =
          F (Vector.ofFn fun t : Fin 1 => random[i % 32 + t.val]) :=
      ⟨fun bytes => drawAccepts preset fork (Vector.replicate 32 bytes[0]) i e,
        drawAccepts_eq_of_byte preset fork electra i e⟩
    obtain ⟨G, second⟩ : ∃ G : Vector UInt8 1 → Except AccessorError Bool, ∀ random : Bytes32,
        drawAccepts preset fork random j f =
          G (Vector.ofFn fun t : Fin 1 => random[j % 32 + t.val]) :=
      ⟨fun bytes => drawAccepts preset fork (Vector.replicate 32 bytes[0]) j f,
        drawAccepts_eq_of_byte preset fork electra j f⟩
    simp only [first, second]
    exact prEvent_uniformSample_vector_two_ranges_comp _ _ _ _ (by omega) (by omega)
      (by omega) F G P Q

end EthLib.Consensus
