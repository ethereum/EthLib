module

public import EthLib.Execution.Blocks.Difficulty

/-!
# Proofs: the difficulty before Paris

Before Paris, the difficulty is never below the minimum, and from Paris on it is 0.

Each fork delays the bomb at least as much as the forks before it.

From Byzantium to Paris, a fork changes the difficulty only through its delay of the bomb.

So a later delay gives the difficulty of an earlier fork at a block number lowered by the change.

The official difficulty vectors are in the Python suite, through the bindings.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base

/-- Forks compare by the index of their constructor, the order of the timeline. -/
private theorem lt_iff {a b : Fork} : a < b ↔ a.ctorIdx < b.ctorIdx := Iff.rfl

/-- Forks compare by the index of their constructor, the order of the timeline. -/
private theorem le_iff {a b : Fork} : a ≤ b ↔ a.ctorIdx ≤ b.ctorIdx := Iff.rfl

/-! ## The minimum and Paris -/

/-- Before Paris, the difficulty is at least the minimum, whatever the parent. -/
theorem minimum_le_blockDifficulty {fork : Fork} (h : fork < .paris)
    (number timestamp parentTimestamp parentDifficulty : Nat) (parentHasOmmers : Bool) :
    MINIMUM_DIFFICULTY ≤
      blockDifficulty fork number timestamp parentTimestamp parentDifficulty parentHasOmmers := by
  have : ¬.paris ≤ fork := by simp only [lt_iff, le_iff, Fork.ctorIdx] at *; omega
  simp only [blockDifficulty, this, ite_false]
  exact Nat.le_max_left _ _

/-- From Paris on, the difficulty is 0, whatever the parent. -/
theorem blockDifficulty_of_paris_le {fork : Fork} (h : .paris ≤ fork)
    (number timestamp parentTimestamp parentDifficulty : Nat) (parentHasOmmers : Bool) :
    blockDifficulty fork number timestamp parentTimestamp parentDifficulty parentHasOmmers = 0 := by
  simp [blockDifficulty, h]

/-! ## The delay of the bomb -/

/-- A later fork delays the bomb at least as much as an earlier one. -/
theorem bombDelay_mono {f g : Fork} (h : f ≤ g) : bombDelay f ≤ bombDelay g := by
  -- Each branch compares the fork's index with the index of a fork of the timeline.
  simp only [bombDelay, lt_iff, le_iff, Fork.ctorIdx] at *
  repeat' split
  all_goals omega

/-- Before the delay plus two periods, the bomb is 0. -/
theorem bomb_eq_zero {fork : Fork} {number : Nat}
    (h : number < bombDelay fork + 2 * BOMB_PERIOD) : bomb fork number = 0 := by
  have : (number - bombDelay fork) / BOMB_PERIOD < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; simp only [BOMB_PERIOD] at *; omega
  simp only [bomb]
  exact ite_eq_right_iff.mpr fun h' => absurd h' (by omega)

/-- From Byzantium, the factor of the time since the parent is the same at every fork. -/
theorem timeFactor_of_byzantium_le {f g : Fork} (hf : .byzantium ≤ f) (hg : .byzantium ≤ g)
    (timestamp parentTimestamp : Nat) (parentHasOmmers : Bool) :
    timeFactor f timestamp parentTimestamp parentHasOmmers =
      timeFactor g timestamp parentTimestamp parentHasOmmers := by
  have hf' : ¬f < .homestead ∧ ¬f < .byzantium := by
    simp only [lt_iff, le_iff, Fork.ctorIdx] at *; omega
  have hg' : ¬g < .homestead ∧ ¬g < .byzantium := by
    simp only [lt_iff, le_iff, Fork.ctorIdx] at *; omega
  simp only [timeFactor, hf'.1, hf'.2, hg'.1, hg'.2, ite_false]

/-- From Byzantium to Paris, a fork changes the difficulty only through its delay of the bomb.

A fork with a longer delay gives the difficulty of a fork with a shorter one.

It does so at the block number lowered by the difference of the two delays. -/
theorem blockDifficulty_delay {f g : Fork} (hf : .byzantium ≤ f) (hg : .byzantium ≤ g)
    (hfp : f < .paris) (hgp : g < .paris) (hd : bombDelay g ≤ bombDelay f)
    (number timestamp parentTimestamp parentDifficulty : Nat) (parentHasOmmers : Bool) :
    blockDifficulty f number timestamp parentTimestamp parentDifficulty parentHasOmmers =
      blockDifficulty g (number - (bombDelay f - bombDelay g)) timestamp parentTimestamp
        parentDifficulty parentHasOmmers := by
  have hf' : ¬.paris ≤ f := by simp only [lt_iff, le_iff, Fork.ctorIdx] at *; omega
  have hg' : ¬.paris ≤ g := by simp only [lt_iff, le_iff, Fork.ctorIdx] at *; omega
  -- The lowered block number meets the shorter delay where the original meets the longer one.
  have hb : bomb f number = bomb g (number - (bombDelay f - bombDelay g)) := by
    simp only [bomb]
    rw [show number - (bombDelay f - bombDelay g) - bombDelay g = number - bombDelay f by omega]
  simp only [blockDifficulty, hf', hg', ite_false, hb,
    timeFactor_of_byzantium_le hf hg timestamp parentTimestamp parentHasOmmers]

end EthLib.Execution.Blocks
