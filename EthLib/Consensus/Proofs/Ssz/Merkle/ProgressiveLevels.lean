import EthLib.Consensus.Ssz.Merkle.Gindex

/-! Where each level of a progressive spine begins, and how deep its chunks sit. -/

namespace EthLib.Consensus.Ssz

/--
Chunks the levels before this one hold together, which is where this one starts.

Levels are counted from zero here, so level `n` of the specification is level `n - 1`.
-/
def levelStart : Nat → Nat
  | 0 => 0
  | level + 1 => levelStart level + 4 ^ level

/-- Level `level` holds four times as many chunks as the one before it. -/
theorem levelStart_succ (level : Nat) : levelStart (level + 1) = levelStart level + 4 ^ level :=
  rfl

/--
The levels up to one exhaust a third of the next power of four.

Written without division: three times the start, plus the one chunk of level zero.
-/
theorem levelStart_capacity : ∀ level : Nat, 3 * levelStart level + 1 = 4 ^ level
  | 0 => rfl
  | level + 1 => by
    have below := levelStart_capacity level
    simp only [levelStart_succ, Nat.pow_succ]
    omega

/-- Peeling one level off the front leaves the same chunk one level along. -/
theorem levelStart_peel (level : Nat) :
    levelStart (level + 1) = 1 + 4 * levelStart level := by
  have below := levelStart_capacity level
  simp only [levelStart_succ]
  omega

/-- A chunk inside the level the walk has reached sits on that level's own subtree. -/
theorem progressiveChunkGindex_here (chunk depth spine : Nat) (inside : chunk < 2 ^ depth) :
    progressiveChunkGindex chunk depth spine = spine * 2 * 2 ^ depth + chunk := by
  rw [progressiveChunkGindex]
  simp [inside]

/-- A chunk past the level the walk has reached is looked for one level further along. -/
theorem progressiveChunkGindex_peel (chunk depth spine : Nat) (past : 2 ^ depth ≤ chunk) :
    progressiveChunkGindex chunk depth spine
      = progressiveChunkGindex (chunk - 2 ^ depth) (depth + 2) (spine * 2 + 1) := by
  rw [progressiveChunkGindex]
  simp [Nat.not_lt.mpr past]

/--
The index of a chunk, in closed form, from any point of the walk.

The widths seen from a given depth are that depth's own width times one, four, sixteen, and
so on, which is why the level start is scaled by it.
-/
theorem progressiveChunkGindex_closed :
    ∀ (level position depth spine : Nat), position < 4 ^ level * 2 ^ depth →
      progressiveChunkGindex (levelStart level * 2 ^ depth + position) depth spine
        = (spine * 2 ^ level + (2 ^ level - 1)) * 2 * (4 ^ level * 2 ^ depth) + position
  | 0, position, depth, spine, inside => by
    simp only [levelStart, Nat.zero_mul, Nat.zero_add, Nat.pow_zero, Nat.one_mul] at inside ⊢
    rw [progressiveChunkGindex_here _ _ _ inside]
    grind
  | level + 1, position, depth, spine, inside => by
    -- The first level the walk sees is one width wide, and the rest is the same problem.
    have width : (1:Nat) ≤ 2 ^ depth := Nat.one_le_two_pow
    have one : (1:Nat) ≤ 2 ^ level := Nat.one_le_two_pow
    have grow : (2:Nat) ^ (depth + 2) = 4 * 2 ^ depth := by
      rw [Nat.pow_add]
      omega
    have front : 2 ^ depth ≤ levelStart (level + 1) * 2 ^ depth + position := by
      rw [levelStart_peel]
      grind
    have shifted : levelStart (level + 1) * 2 ^ depth + position - 2 ^ depth
        = levelStart level * 2 ^ (depth + 2) + position := by
      rw [levelStart_peel, grow]
      grind
    rw [progressiveChunkGindex_peel _ _ _ front, shifted, progressiveChunkGindex_closed level
      position (depth + 2) (spine * 2 + 1) (by rw [grow]; grind), grow]
    grind

/--
The index a chunk of a progressive collection sits at.

A chunk keeps this index however long the collection grows, since nothing in it depends on
the number of chunks held.
-/
theorem progressiveChunkGindex_level (level position : Nat) (inside : position < 4 ^ level) :
    progressiveChunkGindex (levelStart level + position)
      = (3 * 2 ^ level - 1) * 2 * 4 ^ level + position := by
  have closed := progressiveChunkGindex_closed level position 0 2 (by simpa using inside)
  have one : (1:Nat) ≤ 2 ^ level := Nat.one_le_two_pow
  simp only [Nat.pow_zero, Nat.mul_one] at closed
  rw [closed]
  grind

/--
Levels a chunk sits below the value's own root, which is the node count of its proof.

A chunk of level `level` sits three levels further down for each level along, plus the two
the spine root and the mixed-in word take.

This is what fixes the cost of a proof about a progressive collection: it grows with the
logarithm of the chunk number, at three hashes per factor of four.
-/
theorem progressiveChunkGindex_depth (level position : Nat) (inside : position < 4 ^ level) :
    Nat.log2 (progressiveChunkGindex (levelStart level + position)) = 3 * level + 2 := by
  -- Everything below is polynomial in one quantity: two to the level.
  have cube : (2:Nat) ^ (3 * level) = 2 ^ level * 2 ^ level * 2 ^ level := by
    rw [show 3 * level = level + level + level by omega, Nat.pow_add, Nat.pow_add]
  have square : (4:Nat) ^ level = 2 ^ level * 2 ^ level := by
    rw [show (4:Nat) = 2 * 2 from rfl, Nat.mul_pow]
  have floor : (2:Nat) ^ (3 * level + 2) = 4 * (2 ^ level * 2 ^ level * 2 ^ level) := by
    rw [Nat.pow_add, cube]
    grind
  have ceiling : (2:Nat) ^ (3 * level + 3) = 8 * (2 ^ level * 2 ^ level * 2 ^ level) := by
    rw [Nat.pow_add, cube]
    grind
  have one : (1:Nat) ≤ 2 ^ level := Nat.one_le_two_pow
  rw [progressiveChunkGindex_level level position inside, square]
  rw [square] at inside
  -- Writing the level's width as a successor clears the truncated subtraction away.
  generalize width : (2:Nat) ^ level = step at inside floor ceiling one ⊢
  obtain ⟨count, rfl⟩ : ∃ count, step = count + 1 := ⟨step - 1, by omega⟩
  refine (Nat.log2_eq_iff (by grind)).mpr ⟨?_, ?_⟩
  · rw [floor]
    grind
  · rw [show 3 * level + 2 + 1 = 3 * level + 3 from rfl, ceiling]
    grind

end EthLib.Consensus.Ssz
