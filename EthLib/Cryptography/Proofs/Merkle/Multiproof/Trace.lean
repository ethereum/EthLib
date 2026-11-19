module

public import EthLib.Cryptography.Proofs.Merkle.Multiproof.Binding

/-!
# Proofs: the inputs a multiproof verifier hashes

The rebuild, run with a hash that also records each pair it hashes, lists the verifier's inputs.

Every collision the search returns is a pair that the rebuild records.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

variable {α β : Type} (hash : Position → α → α → Id α) (message : Position → α → α → β)

/-- The node hash that also appends a message for each pair it hashes. -/
def recordingHash : Position → α → α → StateM (List β) α :=
  fun p a b => do
    modify (· ++ [message p a b])
    pure (hash p a b).run

/-- The recording rebuild returns what the rebuild returns, and only appends to the record. -/
theorem rebuild_go_recording : ∀ (l j : Nat) (nodes : List (Position × α)) (s : List β),
    ∃ t, ((rebuild.go (recordingHash hash message) nodes l j).run s).run =
      ((rebuild.go hash nodes l j).run, s ++ t) := by
  intro l
  induction l with
  | zero => intro j nodes s; exact ⟨[], by simp [rebuild.go]⟩
  | succ l ih =>
    intro j nodes s
    rw [rebuild_go_succ, rebuild_go_succ_run]
    cases nodes.lookup ⟨l + 1, j⟩ with
    | some node => exact ⟨[], by simp⟩
    | none =>
      dsimp only
      by_cases empty : nodes.isEmpty = true
      · exact ⟨[], by simp [empty]⟩
      simp only [empty, Bool.false_eq_true, ↓reduceIte]
      -- Each child appends to the record, and the hash appends one message.
      obtain ⟨t1, left⟩ := ih (2 * j)
        (nodes.filter fun e => (⟨l, 2 * j⟩ : Position).covers e.1) s
      cases leftNode : (rebuild.go hash
          (nodes.filter fun e => (⟨l, 2 * j⟩ : Position).covers e.1) l (2 * j)).run with
      | none => exact ⟨t1, by simp [StateT.run_bind, left, leftNode]⟩
      | some a =>
        obtain ⟨t2, right⟩ := ih (2 * j + 1)
          (nodes.filter fun e => !(⟨l, 2 * j⟩ : Position).covers e.1) (s ++ t1)
        cases rightNode : (rebuild.go hash
            (nodes.filter fun e => !(⟨l, 2 * j⟩ : Position).covers e.1) l (2 * j + 1)).run with
        | none => exact ⟨t1 ++ t2, by simp [StateT.run_bind, left, leftNode, right, rightNode]⟩
        | some b =>
          exact ⟨t1 ++ t2 ++ [message ⟨l + 1, j⟩ a b],
            by simp [StateT.run_bind, left, leftNode, right, rightNode, recordingHash]⟩

/-- The search reads only the nodes below its start, so a filter keeping them changes nothing. -/
theorem findMultiproofCollision_filter [DecidableEq α] {second : List (Position × α)} :
    ∀ (l j : Nat) (first : List (Position × α)) (P : Position × α → Bool),
      (∀ e ∈ first, (⟨l, j⟩ : Position).IsAncestor e.1 → P e = true) →
        findMultiproofCollision hash (first.filter P) second l j =
          findMultiproofCollision hash first second l j := by
  intro l
  induction l with
  | zero => intro j first P _; rfl
  | succ l ih =>
    intro j first P keep
    -- The node and its children read the same nodes after the filter.
    have keepLeft : ∀ e ∈ first, (⟨l, 2 * j⟩ : Position).IsAncestor e.1 → P e = true :=
      fun e he below => keep e he ((Position.isAncestor_left l j).trans below)
    have keepRight : ∀ e ∈ first, (⟨l, 2 * j + 1⟩ : Position).IsAncestor e.1 → P e = true :=
      fun e he below => keep e he ((Position.isAncestor_right l j).trans below)
    rw [findMultiproofCollision, findMultiproofCollision,
      lookup_filter P fun e he key => keep e he (key ▸ .refl _),
      rebuild_go_filter hash l (2 * j) first P keepLeft,
      rebuild_go_filter hash l (2 * j + 1) first P keepRight,
      ih (2 * j) first P keepLeft, ih (2 * j + 1) first P keepRight]

/-- The pair the search returns for the first rebuild is a message that rebuild records. -/
theorem findMultiproofCollision_recorded [DecidableEq α] {second : List (Position × α)} :
    ∀ (l j : Nat) (first : List (Position × α)) (s : List β) {c : Collision α},
      findMultiproofCollision hash first second l j = some c →
        message c.position c.x.1 c.x.2 ∈
          (((rebuild.go (recordingHash hash message) first l j).run s).run).2 := by
  intro l
  induction l with
  | zero => intro j first s c found; simp [findMultiproofCollision] at found
  | succ l ih =>
    intro j first s c found
    have search := found
    unfold findMultiproofCollision at found
    split at found
    · cases found
    rename_i notGiven
    simp only [Bool.or_eq_true, not_or, Option.not_isSome_iff_eq_none] at notGiven
    split at found
    case h_2 => cases found
    rename_i a a' b b' ha ha' hb hb'
    -- The rebuild of the first list hashes both children here, since both are determined.
    have full : first.isEmpty = false := by
      cases h : first.isEmpty
      · rfl
      · rw [List.isEmpty_iff.mp h, rebuild_go_nil] at ha
        cases ha
    have left := rebuild_go_filter hash l (2 * j) first
      (fun e => (⟨l, 2 * j⟩ : Position).covers e.1) fun e _ below => Position.covers_iff.mpr below
    have right := rebuild_go_filter hash l (2 * j + 1) first
      (fun e => !(⟨l, 2 * j⟩ : Position).covers e.1) fun e _ below => by
        cases covered : (⟨l, 2 * j⟩ : Position).covers e.1
        · rfl
        · exact ((Position.covers_iff.mp covered).not_both below).elim
    obtain ⟨t1, leftRun⟩ := rebuild_go_recording hash message l (2 * j)
      (first.filter fun e => (⟨l, 2 * j⟩ : Position).covers e.1) s
    obtain ⟨t2, rightRun⟩ := rebuild_go_recording hash message l (2 * j + 1)
      (first.filter fun e => !(⟨l, 2 * j⟩ : Position).covers e.1) (s ++ t1)
    rw [left, ha] at leftRun
    rw [right, ha'] at rightRun
    have run : (((rebuild.go (recordingHash hash message) first (l + 1) j).run s).run).2 =
        s ++ t1 ++ t2 ++ [message ⟨l + 1, j⟩ a a'] := by
      rw [rebuild_go_succ]
      simp [notGiven.1, full, StateT.run_bind, leftRun, rightRun, recordingHash]
    rw [run]
    split at found
    · -- The collision is here: its message is the last one recorded.
      cases found
      simp
    · -- The collision is below: the child's rebuild records it, with the filter of that side.
      rcases Option.or_eq_some_iff.mp found with below | ⟨-, below⟩
      · rw [← findMultiproofCollision_filter hash l (2 * j) first
          (fun e => (⟨l, 2 * j⟩ : Position).covers e.1)
          fun e _ under => Position.covers_iff.mpr under] at below
        have := ih (2 * j) _ s below
        rw [leftRun] at this
        simp only [List.mem_append] at this
        rcases this with h | h <;> simp [h]
      · rw [← findMultiproofCollision_filter hash l (2 * j + 1) first
          (fun e => !(⟨l, 2 * j⟩ : Position).covers e.1) fun e _ under => by
            cases covered : (⟨l, 2 * j⟩ : Position).covers e.1
            · rfl
            · exact ((Position.covers_iff.mp covered).not_both under).elim] at below
        have := ih (2 * j + 1) _ (s ++ t1) below
        rw [rightRun] at this
        simp only [List.mem_append] at this
        rcases this with (h | h) | h <;> simp [h]

/-- Searching the two rebuilds in the other order swaps the two pairs of the collision. -/
theorem findMultiproofCollision_swap [DecidableEq α] (first second : List (Position × α)) :
    ∀ l j, findMultiproofCollision hash second first l j =
      (findMultiproofCollision hash first second l j).map fun c => ⟨c.position, c.y, c.x⟩
  | 0, _ => rfl
  | l + 1, j => by
    rw [findMultiproofCollision, findMultiproofCollision, Bool.or_comm,
      findMultiproofCollision_swap first second l (2 * j),
      findMultiproofCollision_swap first second l (2 * j + 1)]
    -- The test is symmetric, and the recursion maps each side.
    split
    · rfl
    cases (rebuild.go hash first l (2 * j)).run <;>
      cases (rebuild.go hash first l (2 * j + 1)).run <;>
      cases (rebuild.go hash second l (2 * j)).run <;>
      cases (rebuild.go hash second l (2 * j + 1)).run <;> try rfl
    rename_i a a' b b'
    dsimp only
    by_cases collides : (a, a') ≠ (b, b') ∧
        (hash ⟨l + 1, j⟩ a a').run = (hash ⟨l + 1, j⟩ b b').run
    · rw [ite_eq_left ⟨Ne.symm collides.1, collides.2.symm⟩, ite_eq_left collides]
      rfl
    · rw [ite_eq_right fun swapped => collides ⟨Ne.symm swapped.1, swapped.2.symm⟩,
        ite_eq_right collides]
      cases findMultiproofCollision hash first second l (2 * j) <;> rfl

end EthLib.Cryptography.Merkle
