import EthLib.Consensus.Proofs.Ssz.Codec.ProofTree
import EthLib.Consensus.Proofs.Ssz.Codec.RootLaws

/-! Progressive proof walks follow the same widening spine that computes the root. -/

namespace EthLib.Consensus.Ssz

/-- With no turns left, a progressive walk reads the remaining spine. -/
theorem progressiveNode_zero (budget : Nat) (layout : MerkleLayout)
    (index start capacity : Nat) :
    progressiveNode budget layout index 0 start capacity = (do
      let rest ← layoutChunksAt budget layout start
      return merkleizeProgressiveFrom rest capacity) := by
  -- No level has been entered, so the entire suffix belongs to this node.
  simp [progressiveNode, spineWalk, Bind.bind, Except.bind]

/-- One progressive turn enters the current level or advances to the next. -/
theorem progressiveNode_step (budget : Nat) (layout : MerkleLayout)
    (index depth start capacity : Nat) :
    progressiveNode budget layout index (depth + 1) start capacity =
      if start ≥ layout.leaves.count then .error .pathPastSpine
      else if !gindexBit index depth then boundedNode budget layout index depth start capacity
      else progressiveNode budget layout index depth (start + capacity) (capacity * 4) := by
  -- The left side is a bounded tree, and the right side repeats the same walk one level farther.
  rw [progressiveNode, spineWalk]
  split
  · rfl
  split
  · simp [Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases walked : spineWalk layout.leaves.count index depth (start + capacity) (capacity * 4)
    <;> simp [progressiveNode, walked, Bind.bind, Except.bind]

/-- Progressive capacities are powers of two with twice the level as their depth. -/
theorem four_pow_eq (level : Nat) : 4 ^ level = 2 ^ (2 * level) := by
  -- Multiplying the exponent by two squares the base before raising it to the level.
  rw [Nat.pow_mul]

/-- A power-of-four capacity starts the progressive root at its corresponding level. -/
theorem merkleizeProgressiveFrom_power (chunks : Array Bytes) (level : Nat) :
    merkleizeProgressiveFrom chunks (4 ^ level) = merkleizeProgressiveUnchecked chunks.toList level := by
  -- The executable conversion divides the binary depth by two.
  simp [merkleizeProgressiveFrom, four_pow_eq, Nat.log2_two_pow]

/-- A suffix read preserves the order and extent of the remaining leaves. -/
theorem extract_suffix_list (chunks : Array Bytes) (start : Nat) :
    (chunks.extract start chunks.size).toList = chunks.toList.drop start := by
  -- Extracting through the end takes every element left after the starting position.
  rw [Array.toList_extract, List.extract_eq_take_drop]
  simpa only [List.length_drop, Array.length_toList] using
    List.take_length (l := chunks.toList.drop start)

/-- A finite leaf interval is the matching prefix of the remaining suffix. -/
theorem extract_interval_list (chunks : Array Bytes) (start width : Nat) :
    (chunks.extract start (start + width)).toList = (chunks.toList.drop start).take width := by
  -- The right endpoint is exclusive, so subtracting the start leaves exactly the width.
  simp [Array.toList_extract]

/-- The first progressive level is its bounded subtree, followed by a four-times-wider suffix. -/
theorem progressive_suffix_split (chunks : Array Bytes) (start level : Nat)
    (occupied : start < chunks.size) :
    merkleizeProgressiveUnchecked (chunks.toList.drop start) level =
      combine (subtreeAt chunks (2 * level) start)
        (merkleizeProgressiveUnchecked (chunks.toList.drop (start + 4 ^ level)) (level + 1)) := by
  -- A nonempty suffix opens one level, and the next level starts after its capacity.
  rw [merkleizeProgressiveUnchecked, ite_eq_right (by simp; omega)]
  simp only [List.drop_drop]
  -- The current bounded segment is the prefix of the same suffix used by progressive merkleization.
  have interval := congrArg List.toArray (extract_interval_list chunks start (4 ^ level))
  simp only [Array.toArray_toList] at interval
  rw [← interval]
  have window := merkleizeBoundedUnchecked_window chunks (depth := 2 * level) start
  -- Extracting a segment cannot exceed its power-of-two capacity, including a partially filled final segment.
  have span : (chunks.extract start (start + 2 ^ (2 * level))).size ≤ 2 ^ (2 * level) := by
    simp only [Array.size_extract]
    generalize 2 ^ (2 * level) = width
    omega
  simp only [merkleizeBoundedUnchecked, ite_eq_right (Nat.not_lt.mpr span), depthFor_pow,
    Pure.pure, Except.pure, Except.ok.injEq] at window
  simpa only [four_pow_eq, depthFor_pow] using congrArg
    (fun left => combine left
      (merkleizeProgressiveUnchecked (chunks.toList.drop (start + 4 ^ level)) (level + 1))) window

/-- Positions within a progressive spine and its bounded levels, including their leaves. -/
def ProgressivePosition (count index : Nat) : Nat → Nat → Nat → Prop
  -- With no turns left, the suffix root is readable even when it is the zero terminator.
  | 0, _, _ => True
  | depth + 1, start, level =>
    start < count ∧ if !gindexBit index depth then depth ≤ 2 * level
      else ProgressivePosition count index depth (start + 4 ^ level) (level + 1)

/-- Positions having two children within the progressive spine or one of its bounded levels. -/
def ProgressiveInterior (count index : Nat) : Nat → Nat → Nat → Prop
  -- A spine position has children only when at least one payload leaf remains.
  | 0, start, _ => start < count
  | depth + 1, start, level =>
    start < count ∧ if !gindexBit index depth then depth < 2 * level
      else ProgressiveInterior count index depth (start + 4 ^ level) (level + 1)

/-- The root at a position in a progressive spine, expressed in terms of its leaf array. -/
def progressiveReading (chunks : Array Bytes) (index : Nat) : Nat → Nat → Nat → Bytes
  -- Stopping on the spine commits to the complete remaining suffix.
  | 0, start, level => merkleizeProgressiveUnchecked (chunks.toList.drop start) level
  | depth + 1, start, level =>
    -- A left turn selects the current bounded segment, while a right turn skips its full capacity.
    if !gindexBit index depth then boundedTreeNode chunks (2 * level) index depth start
    else progressiveReading chunks index depth (start + 4 ^ level) (level + 1)

/-- Materialized leaves determine every position within the progressive tree above them. -/
theorem progressiveNode_read {budget : Nat} {layout : MerkleLayout} {chunks : Array Bytes}
    (materialized : layoutChunksAt budget layout = .ok chunks) (index : Nat) :
    ∀ depth start level, ProgressivePosition chunks.size index depth start level →
      progressiveNode budget layout index depth start (4 ^ level) =
        .ok (progressiveReading chunks index depth start level) := by
  -- Left turns read bounded intervals, while right turns advance through the suffix.
  intro depth
  induction depth with
  | zero =>
    intro start level _
    rw [progressiveNode_zero, layoutChunksAt_suffix budget layout chunks materialized start]
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      merkleizeProgressiveFrom_power, extract_suffix_list, progressiveReading]
  | succ depth ih =>
    intro start level position
    obtain ⟨occupied, position⟩ := position
    -- The materialized array and the layout agree on where the finite spine ends.
    have count := layoutChunksAt_size budget layout chunks materialized
    rw [progressiveNode_step, ite_eq_right (by omega)]
    by_cases left : (!gindexBit index depth) = true
    · simp only [ite_eq_left left] at position ⊢
      have inside : depth ≤ depthFor (4 ^ level) := by
        simpa only [four_pow_eq, depthFor_pow] using position
      rw [boundedNode_window (layoutChunksAt_window budget layout chunks materialized)
        index depth start (4 ^ level) inside]
      simp only [four_pow_eq, depthFor_pow, progressiveReading, ite_eq_left left]
    · simp only [ite_eq_right left] at position ⊢
      rw [← Nat.pow_succ]
      simpa only [progressiveReading, ite_eq_right left] using ih _ _ position

/-- An internal progressive position hashes the two positions immediately below it. -/
theorem progressiveReading_split (chunks : Array Bytes) (index : Nat) :
    ∀ depth start level, ProgressiveInterior chunks.size index depth start level →
      progressiveReading chunks index depth start level =
        combine (progressiveReading chunks (2 * index) (depth + 1) start level)
          (progressiveReading chunks (2 * index + 1) (depth + 1) start level) := by
  -- At a spine node the two children are its current level and its suffix.
  intro depth
  induction depth with
  | zero =>
    intro start level occupied
    have left : gindexBit (2 * index) 0 = false := by simp [gindexBit, Nat.testBit_zero]
    have right : gindexBit (2 * index + 1) 0 = true := by simp [gindexBit, Nat.testBit_zero]
    simp only [progressiveReading, left, right, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
    simp only [boundedTreeNode, gindexBelow, Nat.sub_zero, Nat.pow_zero, Nat.mod_one,
      Nat.zero_mul, Nat.add_zero]
    exact progressive_suffix_split chunks start level occupied
  | succ depth ih =>
    intro start level interior
    obtain ⟨-, interior⟩ := interior
    -- Both child indices retain all higher turns, so they enter the same segment as their parent.
    obtain ⟨leftChild, rightChild⟩ := gindexBit_children index depth
    simp only [progressiveReading, leftChild, rightChild]
    by_cases left : (!gindexBit index depth) = true
    · simp only [ite_eq_left left] at interior ⊢
      exact boundedTreeNode_split chunks (2 * level) index depth start interior
    · simp only [ite_eq_right left] at interior ⊢
      exact ih _ _ interior

end EthLib.Consensus.Ssz
