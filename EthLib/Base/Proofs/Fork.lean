module

public import EthLib.Base.Fork

/-!
# Proofs: `Fork`

Forks are ordered by their position in the type, and the order is linear.

The comparison agrees with that order, as an ordered map needs.

The timeline pins each position, so a fork moved in the type fails the build.

A field that appears at a fork holds nothing before it, and one value from it on.
-/

@[expose] public section

namespace EthLib.Base.Fork

open Std

/-- Two forks at the same position are equal. -/
theorem ctorIdx_injective : Function.Injective Fork.ctorIdx := by
  intro a b h
  rw [← Fork.ofNat_ctorIdx a, ← Fork.ofNat_ctorIdx b, h]

instance : IsLinearOrder Fork := by
  apply IsLinearOrder.of_le
  case le_antisymm => exact ⟨fun _ _ h h' => ctorIdx_injective (Nat.le_antisymm h h')⟩
  case le_trans => exact ⟨fun h h' => Nat.le_trans h h'⟩
  case le_total => exact ⟨fun a b => Nat.le_total a.ctorIdx b.ctorIdx⟩

instance : LawfulOrderLT Fork where
  lt_iff a b := Nat.lt_iff_le_and_not_ge (m := a.ctorIdx) (n := b.ctorIdx)

instance : LawfulOrderOrd Fork where
  isLE_compare a b := LawfulOrderOrd.isLE_compare a.ctorIdx b.ctorIdx
  isGE_compare a b := LawfulOrderOrd.isGE_compare a.ctorIdx b.ctorIdx

/-- Frontier is the first fork. -/
theorem frontier_le (f : Fork) : frontier ≤ f := Nat.zero_le f.ctorIdx

/-- Hegotá is the last fork. -/
theorem le_hegota (f : Fork) : f ≤ hegota := by
  cases f <;> decide

/-! ## The comparison

Core derives these laws from the three instances above. -/

example : TransOrd Fork := inferInstance

example : LawfulEqOrd Fork := inferInstance

/-! ## The timeline -/

/-- Each fork of the timeline comes before the next. -/
theorem pairwise_lt_timeline :
    [frontier, homestead, daoFork, tangerineWhistle, spuriousDragon, byzantium, constantinople,
      petersburg, istanbul, muirGlacier, phase0, berlin, london, altair, arrowGlacier, grayGlacier,
      bellatrix, paris, shapella, dencun, pectra, fusaka, bpo1, bpo2, glamsterdam,
      hegota].Pairwise (· < ·) := by
  decide

/-- The timeline lists every fork. -/
theorem mem_timeline (f : Fork) :
    f ∈ [frontier, homestead, daoFork, tangerineWhistle, spuriousDragon, byzantium, constantinople,
      petersburg, istanbul, muirGlacier, phase0, berlin, london, altair, arrowGlacier, grayGlacier,
      bellatrix, paris, shapella, dencun, pectra, fusaka, bpo1, bpo2, glamsterdam, hegota] := by
  cases f <;> decide

end EthLib.Base.Fork

namespace EthLib.Base.Since

variable {f fork : Fork} {α : Type}

/-- Before its fork, a field has only one value. -/
theorem eq_of_not_le (h : ¬f ≤ fork) (x y : Since f fork α) : x = y :=
  funext fun h' => absurd h' h

/-- From its fork on, a field is the one value that it holds. -/
theorem eq_const (h : f ≤ fork) (x : Since f fork α) : x = fun _ => x h :=
  funext fun _ => rfl

end EthLib.Base.Since
