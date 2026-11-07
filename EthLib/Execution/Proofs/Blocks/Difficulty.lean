module

public import EthLib.Execution.Blocks.Difficulty

/-!
# Proofs: the difficulty before Paris

Before Paris, the difficulty is never below the minimum, and from Paris on it is 0.

Each fork delays the bomb at least as much as the forks before it.

From Byzantium to Paris, a fork changes the difficulty only through its delay of the bomb.

So a later delay gives the difficulty of an earlier fork at a block number lowered by the change.

Before Paris, the difficulty of a block is at least the parent's less 99 steps.

For a block no earlier than its parent, it is at most the parent's plus two steps and the bomb.

The minimum still bounds it from below, so it is at most the larger of the two.

A step is the parent's difficulty over 2048.

A later timestamp never raises the difficulty.

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

/-! ## Bounds on a step -/

/-- The factor of the time since the parent is at least -99. -/
theorem neg_ninetyNine_le_timeFactor (fork : Fork) (timestamp parentTimestamp : Nat)
    (parentHasOmmers : Bool) : -99 ≤ timeFactor fork timestamp parentTimestamp parentHasOmmers := by
  simp only [timeFactor]
  split
  · split <;> omega
  split
  · exact Int.le_max_right _ _
  · exact Int.le_max_right _ _

/-- For a block no earlier than its parent, the factor of the time since the parent is at most 2. -/
theorem timeFactor_le_two (fork : Fork) {timestamp parentTimestamp : Nat}
    (parentHasOmmers : Bool) (h : parentTimestamp ≤ timestamp) :
    timeFactor fork timestamp parentTimestamp parentHasOmmers ≤ 2 := by
  simp only [timeFactor]
  split
  · split <;> omega
  split
  · exact Int.max_le.mpr ⟨by omega, by omega⟩
  · exact Int.max_le.mpr ⟨by cases parentHasOmmers <;> simp <;> omega, by omega⟩

/-- A later block lowers the factor of the time since the parent, or keeps it. -/
theorem timeFactor_antitone (fork : Fork) {timestamp timestamp' : Nat} (parentTimestamp : Nat)
    (parentHasOmmers : Bool) (h : timestamp ≤ timestamp') :
    timeFactor fork timestamp' parentTimestamp parentHasOmmers ≤
      timeFactor fork timestamp parentTimestamp parentHasOmmers := by
  simp only [timeFactor]
  split
  · split <;> split <;> omega
  split
  · exact Int.max_le.mpr ⟨Int.le_trans (by omega) (Int.le_max_left _ _), Int.le_max_right _ _⟩
  · exact Int.max_le.mpr ⟨Int.le_trans (by omega) (Int.le_max_left _ _), Int.le_max_right _ _⟩

/-- The difficulty is at most the parent's, plus two steps and the bomb.

This holds for a block no earlier than its parent.

A step is the parent's difficulty over 2048, rounded down.

The minimum still applies. -/
theorem blockDifficulty_le (fork : Fork) (number : Nat) {timestamp parentTimestamp : Nat}
    (parentDifficulty : Nat)
    (parentHasOmmers : Bool) (hts : parentTimestamp ≤ timestamp) :
    blockDifficulty fork number timestamp parentTimestamp parentDifficulty parentHasOmmers ≤
      max MINIMUM_DIFFICULTY
        (parentDifficulty + 2 * (parentDifficulty / DIFFICULTY_BOUND_DIVISOR) +
          bomb fork number) := by
  -- From Paris on, the difficulty is 0.
  by_cases this : .paris ≤ fork
  · simp [blockDifficulty, this]
  have hf := timeFactor_le_two fork parentHasOmmers hts
  simp only [blockDifficulty, this, ite_false, DIFFICULTY_BOUND_DIVISOR]
  generalize timeFactor fork timestamp parentTimestamp parentHasOmmers = factor at hf ⊢
  -- A step is not negative, so the factor scales it by at most 2.
  have hstep : (parentDifficulty : Int) / ((2048 : Nat) : Int) * factor ≤
      (parentDifficulty : Int) / ((2048 : Nat) : Int) * 2 :=
    Int.mul_le_mul_of_nonneg_left hf (Int.ediv_nonneg (Int.natCast_nonneg _) (by decide))
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans (by omega) (Nat.le_max_right _ _)⟩

/-- Before Paris, the difficulty is at least the parent's, less 99 steps.

A step is the parent's difficulty over 2048, rounded down. -/
theorem le_blockDifficulty {fork : Fork} (h : fork < .paris)
    (number timestamp parentTimestamp parentDifficulty : Nat) (parentHasOmmers : Bool) :
    parentDifficulty - 99 * (parentDifficulty / DIFFICULTY_BOUND_DIVISOR) ≤
      blockDifficulty fork number timestamp parentTimestamp parentDifficulty parentHasOmmers := by
  have : ¬.paris ≤ fork := by simp only [lt_iff, le_iff, Fork.ctorIdx] at *; omega
  have hf := neg_ninetyNine_le_timeFactor fork timestamp parentTimestamp parentHasOmmers
  simp only [blockDifficulty, this, ite_false, DIFFICULTY_BOUND_DIVISOR]
  generalize timeFactor fork timestamp parentTimestamp parentHasOmmers = factor at hf ⊢
  -- A step is not negative, so the factor scales it by at least -99.
  have hstep : (parentDifficulty : Int) / ((2048 : Nat) : Int) * -99 ≤
      (parentDifficulty : Int) / ((2048 : Nat) : Int) * factor :=
    Int.mul_le_mul_of_nonneg_left hf (Int.ediv_nonneg (Int.natCast_nonneg _) (by decide))
  exact Nat.le_trans (by omega) (Nat.le_max_right _ _)

/-- A later block gets at most the difficulty of an earlier one with the same parent. -/
theorem blockDifficulty_antitone (fork : Fork) (number : Nat) {timestamp timestamp' : Nat}
    (parentTimestamp parentDifficulty : Nat)
    (parentHasOmmers : Bool) (hts : timestamp ≤ timestamp') :
    blockDifficulty fork number timestamp' parentTimestamp parentDifficulty parentHasOmmers ≤
      blockDifficulty fork number timestamp parentTimestamp parentDifficulty parentHasOmmers := by
  -- From Paris on, both difficulties are 0.
  by_cases this : .paris ≤ fork
  · simp [blockDifficulty, this]
  have hf := timeFactor_antitone fork parentTimestamp parentHasOmmers hts
  simp only [blockDifficulty, this, ite_false, DIFFICULTY_BOUND_DIVISOR]
  generalize timeFactor fork timestamp parentTimestamp parentHasOmmers = factor at hf ⊢
  generalize timeFactor fork timestamp' parentTimestamp parentHasOmmers = factor' at hf ⊢
  -- A step is not negative, so a lower factor gives a lower sum.
  have hstep : (parentDifficulty : Int) / ((2048 : Nat) : Int) * factor' ≤
      (parentDifficulty : Int) / ((2048 : Nat) : Int) * factor :=
    Int.mul_le_mul_of_nonneg_left hf (Int.ediv_nonneg (Int.natCast_nonneg _) (by decide))
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans (by omega) (Nat.le_max_right _ _)⟩

end EthLib.Execution.Blocks
