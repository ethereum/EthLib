module

public import EthLib.Cryptography.Merkle.Multiproof
public import EthLib.Cryptography.Proofs.Merkle.Completeness

/-!
# Proofs: completeness of Merkle multiproofs

An honest multiproof rebuilds the root.

The helpers are the siblings of path nodes that no path holds, each once, and form an antichain.

A multiproof of one node is the climb of its path.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

/-! ## Lists -/

/-- A lookup finds a key exactly when some entry has that key.

So the nodes given to a rebuild are found by their positions. -/
theorem lookup_isSome_iff_mem {β γ : Type} [BEq β] [LawfulBEq β] {l : List (β × γ)} {k : β} :
    (l.lookup k).isSome ↔ k ∈ l.map Prod.fst := by
  rw [List.lookup_isSome_iff, List.mem_map]
  -- A lawful equality test on keys is equality of keys.
  constructor
  · rintro ⟨e, he, same⟩
    exact ⟨e, he, (beq_iff_eq.mp same).symm⟩
  · rintro ⟨e, he, same⟩
    exact ⟨e, he, beq_iff_eq.mpr same.symm⟩

/-- A lookup returns the value of an entry with that key.

So a value read from the nodes given is one of the values supplied. -/
theorem mem_of_lookup_eq_some {β γ : Type} [BEq β] [LawfulBEq β] {l : List (β × γ)} {k : β}
    {v : γ} (found : l.lookup k = some v) : (k, v) ∈ l := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp found
  simp

/-- With no repeated key, a lookup finds the value of the entry with that key. -/
theorem lookup_of_mem_nodup {β γ : Type} [BEq β] [LawfulBEq β] {l : List (β × γ)} {k : β}
    {v : γ} (unique : (l.map Prod.fst).Nodup) (member : (k, v) ∈ l) : l.lookup k = some v := by
  induction l with
  | nil => simp at member
  | cons e rest ih =>
    obtain ⟨a, b⟩ := e
    obtain ⟨fresh, unique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | member
    · -- The entry is the first one.
      cases same
      simp
    · -- The entry is later, so its key is not the first key.
      have differ : (k == a) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun same => fresh (same ▸ List.mem_map.mpr ⟨_, member, rfl⟩)
      simp [List.lookup_cons, differ, ih unique member]

/-- A key with no repeat in a list of keys finds the value zipped with it.

So each opened node, opened once, is read back with its own value. -/
theorem lookup_zip_getElem {β γ : Type} [BEq β] [LawfulBEq β] {keys : List β} {values : List γ}
    (unique : keys.Nodup) (rest : List (β × γ)) {i : Nat} (hk : i < keys.length)
    (hv : i < values.length) :
    (keys.zip values ++ rest).lookup keys[i] = some values[i] := by
  induction keys generalizing values i with
  | nil => simp at hk
  | cons key keys ih =>
    cases values with
    | nil => simp at hv
    | cons value values =>
      obtain ⟨fresh, unique⟩ := List.nodup_cons.mp unique
      cases i with
      | zero => simp
      | succ i =>
        have hk' : i < keys.length := by simpa using hk
        have hv' : i < values.length := by simpa using hv
        -- The key sits later in the list, so it differs from the first key.
        have differ : (keys[i] == key) = false := by
          rw [beq_eq_false_iff_ne]
          exact fun same => fresh (same ▸ List.getElem_mem hk')
        simp only [List.zip_cons_cons, List.cons_append, List.getElem_cons_succ, List.lookup_cons,
          differ]
        exact ih unique hk' hv'

/-- Each entry of a list zipped with its own image pairs a key with the value of the map there.

So the nodes of an honest multiproof agree with the tree they are read from. -/
theorem mem_zip_map {β γ : Type} {l : List β} {f : β → γ} {e : β × γ}
    (member : e ∈ l.zip (l.map f)) : f e.1 = e.2 := by
  induction l with
  | nil => simp at member
  | cons x xs ih =>
    -- The first entry pairs the head with its image, and the rest is the same zip of the tail.
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at member
    rcases member with rfl | member
    · rfl
    · exact ih member

/-! ## Ancestors -/

namespace Position

/-- One node covers another exactly when it is that node or one of its ancestors. -/
theorem covers_iff {a p : Position} : a.covers p = true ↔ a.IsAncestor p := by
  -- The shift by the level difference is the division in the index of an ancestor.
  rw [isAncestor_iff]
  simp only [covers, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.shiftRight_eq_div_pow]
  exact and_congr_right fun _ => eq_comm

/-- A node is its own ancestor only at its own level.

So two nodes on one level, one an ancestor of the other, are the same node. -/
theorem IsAncestor.eq_of_level_le {a p : Position} (h : a.IsAncestor p) (le : a.level ≤ p.level) :
    a = p := by
  obtain ⟨k, rfl⟩ := h
  -- Climbing zero levels stays in place.
  have : k = 0 := by simp only [ancestor_level] at le; omega
  subst this
  exact ancestor_zero p

/-- An ancestor of a node strictly above it is an ancestor of its parent.

So an ancestor of a node is found again by climbing one level. -/
theorem IsAncestor.parent {a p : Position} (h : a.IsAncestor p) (lt : p.level < a.level) :
    a.IsAncestor p.parent := by
  obtain ⟨k, rfl⟩ := h
  -- The ancestor is at least one level up, so it is above the parent.
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [ancestor_level] at lt; omega⟩
  exact ⟨k, (ancestor_parent p k).symm⟩

/-- A parent is an ancestor of each of its children. -/
theorem isAncestor_of_parent {a p : Position} (h : p.parent = a) : a.IsAncestor p :=
  ⟨1, by simp [h]⟩

/-- Two nodes with one parent are the same node or siblings.

So the two children of a node on a path are the path node and its sibling. -/
theorem eq_or_eq_sibling_of_parent_eq {a b : Position} (h : a.parent = b.parent) :
    a = b ∨ a = b.sibling := by
  obtain ⟨la, ia⟩ := a
  obtain ⟨lb, ib⟩ := b
  simp only [parent_mk, mk.injEq] at h
  obtain ⟨levels, half⟩ := h
  obtain rfl : la = lb := by omega
  -- The sibling has the same half and the other parity, which pins down a different index.
  by_cases same : ia = ib
  · exact .inl (by rw [same])
  refine .inr ?_
  rw [sibling_mk, mk.injEq]
  refine ⟨rfl, ?_⟩
  have half' : (ib ^^^ 1) / 2 = ib / 2 := by simp [Nat.xor_div_two]
  have parity := Nat.xor_mod_two_eq_one (a := ib) (b := 1)
  have := Nat.mod_two_eq_zero_or_one ib
  have := Nat.mod_two_eq_zero_or_one ia
  have := Nat.mod_two_eq_zero_or_one (ib ^^^ 1)
  omega

end Position

/-- Flipping the low bit of an even number adds 1.

So the sibling of a left child is the next node of its level. -/
theorem xor_one_of_even {x : Nat} (even : x % 2 = 0) : x ^^^ 1 = x + 1 := by
  -- The flip keeps the half and makes the number odd.
  have half : (x ^^^ 1) / 2 = x / 2 := by simp [Nat.xor_div_two]
  have parity := Nat.xor_mod_two_eq_one (a := x) (b := 1)
  omega

/-- Flipping the low bit of an odd number subtracts 1.

So the sibling of a right child is the previous node of its level. -/
theorem xor_one_of_odd {x : Nat} (odd : x % 2 = 1) : x ^^^ 1 = x - 1 := by
  -- The flip keeps the half and makes the number even.
  have half : (x ^^^ 1) / 2 = x / 2 := by simp [Nat.xor_div_two]
  have parity := Nat.xor_mod_two_eq_one (a := x) (b := 1)
  omega

/-! ## Paths -/

/-- A path node of `p` in the tree of height `h` is an ancestor of `p` below level `h`.

So the paths of the opened nodes are the ancestors that a rebuild must compute. -/
theorem mem_pathTo {h : Nat} {p q : Position} :
    q ∈ pathTo h p ↔ q.IsAncestor p ∧ q.level < h := by
  simp only [pathTo, List.mem_map, List.mem_range]
  constructor
  · -- The ancestor `k` levels up sits at level `p.level + k`, below `h`.
    rintro ⟨k, lt, rfl⟩
    exact ⟨⟨k, rfl⟩, by simp; omega⟩
  · rintro ⟨⟨k, rfl⟩, lt⟩
    exact ⟨k, by simp at lt; omega, rfl⟩

/-- A node on some path is an ancestor of an opened node, below level `h`. -/
theorem mem_paths {h : Nat} {opened : List Position} {q : Position} :
    q ∈ opened.flatMap (pathTo h) ↔ ∃ p ∈ opened, q.IsAncestor p ∧ q.level < h := by
  simp [mem_pathTo]

/-! ## Children -/

namespace Position

/-- Two ancestors of one node on one level are the same node. -/
theorem IsAncestor.unique {a b p : Position} (ha : a.IsAncestor p) (hb : b.IsAncestor p)
    (level : a.level = b.level) : a = b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  simp only [ancestor_level] at level
  obtain rfl : m = n := by omega
  rfl

/-- Of two ancestors of one node, the higher one is an ancestor of the lower one. -/
theorem IsAncestor.of_both {a b p : Position} (ha : a.IsAncestor p) (hb : b.IsAncestor p)
    (le : b.level ≤ a.level) : a.IsAncestor b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  simp only [ancestor_level] at le
  exact ⟨m - n, by rw [ancestor_ancestor]; congr 1; omega⟩

/-- A node strictly above another is an ancestor of the other's sibling too. -/
theorem IsAncestor.sibling {a q : Position} (h : a.IsAncestor q) (lt : q.level < a.level) :
    a.IsAncestor q.sibling := by
  -- Both share the parent, which the ancestor sits above.
  have parent := h.parent lt
  rw [← sibling_parent] at parent
  exact parent.trans (isAncestor_of_parent rfl)

/-- A node is an ancestor of its left child. -/
theorem isAncestor_left (l j : Nat) : (⟨l + 1, j⟩ : Position).IsAncestor ⟨l, 2 * j⟩ :=
  isAncestor_of_parent (Position.ext rfl (by show 2 * j / 2 = j; omega))

/-- A node is an ancestor of its right child. -/
theorem isAncestor_right (l j : Nat) : (⟨l + 1, j⟩ : Position).IsAncestor ⟨l, 2 * j + 1⟩ :=
  isAncestor_of_parent (Position.ext rfl (by show (2 * j + 1) / 2 = j; omega))

/-- The sibling of the left child is the right child. -/
theorem sibling_left (l j : Nat) : (⟨l, 2 * j⟩ : Position).sibling = ⟨l, 2 * j + 1⟩ := by
  rw [sibling_mk, xor_one_of_even (by omega)]

/-- The sibling of the right child is the left child. -/
theorem sibling_right (l j : Nat) : (⟨l, 2 * j + 1⟩ : Position).sibling = ⟨l, 2 * j⟩ := by
  rw [sibling_mk, xor_one_of_odd (by omega)]
  rfl

/-- A node below another, at least one level lower, lies below one of its two children. -/
theorem IsAncestor.child {l j : Nat} {q : Position} (h : (⟨l + 1, j⟩ : Position).IsAncestor q)
    (low : q.level ≤ l) :
    (⟨l, 2 * j⟩ : Position).IsAncestor q ∨ (⟨l, 2 * j + 1⟩ : Position).IsAncestor q := by
  obtain ⟨m, hm⟩ := h
  have level := congrArg Position.level hm
  have index := congrArg Position.index hm
  simp only [ancestor_level, ancestor_index] at level index
  -- The ancestor of `q` one level below the node is the child on its side.
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have half : q.index / 2 ^ m / 2 = j := by rw [div_pow_div_two]; exact index.symm
  rcases Nat.mod_two_eq_zero_or_one (q.index / 2 ^ m) with even | odd
  · exact .inl ⟨m, Position.ext (by simp; omega) (by simp; omega)⟩
  · exact .inr ⟨m, Position.ext (by simp; omega) (by simp; omega)⟩

/-- No node lies below both children of a node. -/
theorem IsAncestor.not_both {l j : Nat} {q : Position}
    (left : (⟨l, 2 * j⟩ : Position).IsAncestor q)
    (right : (⟨l, 2 * j + 1⟩ : Position).IsAncestor q) : False := by
  have := congrArg Position.index (left.unique right rfl)
  simp at this

end Position

/-- The nodes of a list below a node, kept by a filter, are those of the list below it. -/
theorem mem_filter_covers {L : List Position} {c p : Position} :
    p ∈ L.filter (fun q => c.covers q) ↔ p ∈ L ∧ c.IsAncestor p := by
  simp [Position.covers_iff]

/-- A filter of the nodes below a node is empty exactly when no node of the list lies below it. -/
theorem filter_covers_isEmpty {L : List Position} {c : Position} :
    (L.filter (fun q => c.covers q)).isEmpty = true ↔ ∀ p ∈ L, ¬ c.IsAncestor p := by
  simp [Position.covers_iff]

/-! ## Helper nodes -/

/-- A helper found below a node lies below it, with an opened node below its sibling only. -/
theorem helpers_go_spec : ∀ (l j : Nat) (L : List Position) (q : Position),
    q ∈ helpers.go L l j →
      q.level < l ∧ (⟨l, j⟩ : Position).IsAncestor q ∧ (∃ p ∈ L, q.sibling.IsAncestor p) ∧
        ∀ p ∈ L, ¬ q.IsAncestor p := by
  intro l
  induction l with
  | zero => intro j L q member; simp [helpers.go] at member
  | succ l ih =>
    intro j L q member
    -- A helper found below a child keeps these facts, since the child's list is part of `L`.
    have below : ∀ j', (⟨l + 1, j⟩ : Position).IsAncestor ⟨l, j'⟩ →
        q ∈ helpers.go (L.filter fun p => (⟨l, j'⟩ : Position).covers p) l j' →
        q.level < l + 1 ∧ (⟨l + 1, j⟩ : Position).IsAncestor q ∧
          (∃ p ∈ L, q.sibling.IsAncestor p) ∧ ∀ p ∈ L, ¬ q.IsAncestor p := by
      intro j' child inner
      obtain ⟨low, under, ⟨p, hp, sp⟩, none⟩ := ih j' _ q inner
      refine ⟨by omega, child.trans under, ⟨p, (mem_filter_covers.mp hp).1, sp⟩,
        fun p hp above => none p (mem_filter_covers.mpr ⟨hp, under.trans above⟩) above⟩
    -- A child emitted as a helper has nothing below it, and its sibling has something.
    have emitted : ∀ c : Position, c.level = l → (⟨l + 1, j⟩ : Position).IsAncestor c →
        (L.filter fun p => c.covers p).isEmpty = true →
        (L.filter fun p => c.sibling.covers p).isEmpty = false →
        c.level < l + 1 ∧ (⟨l + 1, j⟩ : Position).IsAncestor c ∧
          (∃ p ∈ L, c.sibling.IsAncestor p) ∧ ∀ p ∈ L, ¬ c.IsAncestor p := by
      intro c level parent empty full
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil (L.filter fun p => c.sibling.covers p)
        (fun e => by rw [e] at full; simp at full)
      exact ⟨by omega, parent, ⟨p, (mem_filter_covers.mp hp).1, (mem_filter_covers.mp hp).2⟩,
        filter_covers_isEmpty.mp empty⟩
    simp only [helpers.go] at member
    split at member
    · simp at member
    · rename_i empty full
      rcases List.mem_cons.mp member with rfl | inner
      · exact emitted _ rfl (Position.isAncestor_left l j) empty
          (by rw [Position.sibling_left]; exact full)
      · exact below _ (Position.isAncestor_right l j) inner
    · rename_i full empty
      rcases List.mem_cons.mp member with rfl | inner
      · exact emitted _ rfl (Position.isAncestor_right l j) empty
          (by rw [Position.sibling_right]; exact full)
      · exact below _ (Position.isAncestor_left l j) inner
    · rcases List.mem_append.mp member with inner | inner
      · exact below _ (Position.isAncestor_left l j) inner
      · exact below _ (Position.isAncestor_right l j) inner

/-- Under a node holding the opened nodes, each node opened only below its sibling is a helper. -/
theorem mem_helpers_go : ∀ (l j : Nat) (L : List Position) (q : Position),
    (∀ p ∈ L, (⟨l, j⟩ : Position).IsAncestor p) → q.level < l →
      (⟨l, j⟩ : Position).IsAncestor q → (∃ p ∈ L, q.sibling.IsAncestor p) →
        (∀ p ∈ L, ¬ q.IsAncestor p) → q ∈ helpers.go L l j := by
  intro l
  induction l with
  | zero => intro j L q _ low; omega
  | succ l ih =>
    intro j L q inside low under ⟨p, hp, sp⟩ none
    -- A child of the node on the side of `q`, and the other child.
    have side : ∀ c c' : Position, c.level = l → c'.level = l → c.sibling = c' →
        (⟨l + 1, j⟩ : Position).IsAncestor c → c.IsAncestor q →
        (q = c ∧ (L.filter fun p => c.covers p).isEmpty = true ∧
            (L.filter fun p => c'.covers p).isEmpty = false) ∨
          ((L.filter fun p => c.covers p).isEmpty = false ∧
            q ∈ helpers.go (L.filter fun p => c.covers p) l c.index) := by
      intro c c' level level' sibling parent cq
      obtain ⟨cl, ci⟩ := c
      replace level : l = cl := level.symm
      subst level
      by_cases at_c : q.level = l
      · -- At the child's level, `q` is the child, and its sibling has the opened node below.
        have same := (cq.eq_of_level_le (by dsimp only; omega)).symm
        subst same
        refine .inl ⟨rfl, filter_covers_isEmpty.mpr none, ?_⟩
        rw [← sibling]
        simpa using List.ne_nil_of_mem (mem_filter_covers.mpr ⟨hp, sp⟩)
      · -- Strictly below the child, `q` and its sibling are both below the child.
        have cs := cq.sibling (by dsimp only; omega)
        have member := mem_filter_covers.mpr ⟨hp, cs.trans sp⟩
        refine .inr ⟨by simpa using List.ne_nil_of_mem member, ?_⟩
        exact ih ci _ q (fun p hp => (mem_filter_covers.mp hp).2) (by omega) cq ⟨p, member, sp⟩
          (fun p hp => none p (mem_filter_covers.mp hp).1)
    simp only [helpers.go]
    rcases under.child (by omega) with left | right
    · rcases side _ _ rfl rfl (Position.sibling_left l j) (Position.isAncestor_left l j) left with
        ⟨rfl, empty, full⟩ | ⟨full, inner⟩
      · simp [empty, full]
      · cases right : (L.filter fun p => (⟨l, 2 * j + 1⟩ : Position).covers p).isEmpty <;>
          simp [full, inner]
    · rcases side _ _ rfl rfl (Position.sibling_right l j) (Position.isAncestor_right l j)
        right with ⟨rfl, empty, full⟩ | ⟨full, inner⟩
      · simp [empty, full]
      · cases left : (L.filter fun p => (⟨l, 2 * j⟩ : Position).covers p).isEmpty <;>
          simp [full, inner]

/-- A helper sits below level `h`, has an opened node below its sibling, and none below itself. -/
theorem helpers_spec {h : Nat} {opened : List Position} {q : Position}
    (member : q ∈ helpers h opened) :
    q.level < h ∧ (∃ p ∈ opened, q.sibling.IsAncestor p) ∧ ∀ p ∈ opened, ¬ q.IsAncestor p := by
  obtain ⟨low, -, sibling, none⟩ :=
    helpers_go_spec h 0 opened q (List.mem_mergeSort.mp member)
  exact ⟨low, sibling, none⟩

/-- A path node of opened nodes in the tree is in the tree. -/
theorem paths_inside {h : Nat} {opened : List Position}
    (inside : ∀ p ∈ opened, (⟨h, 0⟩ : Position).IsAncestor p) {r : Position}
    (member : r ∈ opened.flatMap (pathTo h)) : (⟨h, 0⟩ : Position).IsAncestor r := by
  obtain ⟨p, hp, rp, low⟩ := mem_paths.mp member
  exact (inside p hp).of_both rp (Nat.le_of_lt low)

/-- A helper of opened nodes in the tree is in the tree. -/
theorem helpers_inside {h : Nat} {opened : List Position}
    (inside : ∀ p ∈ opened, (⟨h, 0⟩ : Position).IsAncestor p) {q : Position}
    (member : q ∈ helpers h opened) : (⟨h, 0⟩ : Position).IsAncestor q := by
  -- The root is above the sibling, so above the helper too.
  obtain ⟨low, ⟨p, hp, sp⟩, -⟩ := helpers_spec member
  have sibling := (inside p hp).of_both sp (by simpa using Nat.le_of_lt low)
  simpa using sibling.sibling (by simpa using low)

/-- A helper is a sibling of a path node that is not itself a path node.

It needs every opened node in the tree of height `h`. -/
theorem mem_helpers {h : Nat} {opened : List Position}
    (inside : ∀ p ∈ opened, (⟨h, 0⟩ : Position).IsAncestor p) {q : Position} :
    q ∈ helpers h opened ↔
      q ∈ (opened.flatMap (pathTo h)).map Position.sibling ∧ q ∉ opened.flatMap (pathTo h) := by
  constructor
  · -- The sibling is a path node, and no opened node lies below the helper.
    intro member
    obtain ⟨low, ⟨p, hp, sp⟩, none⟩ := helpers_spec member
    refine ⟨List.mem_map.mpr ⟨q.sibling, mem_paths.mpr ⟨p, hp, sp, by simpa using low⟩,
      Position.sibling_sibling q⟩, fun onPath => ?_⟩
    obtain ⟨p', hp', qp, -⟩ := mem_paths.mp onPath
    exact none p' hp' qp
  · -- The root lies above the path node, so above its sibling too.
    rintro ⟨sibling, outside⟩
    obtain ⟨r, onPath, rfl⟩ := List.mem_map.mp sibling
    obtain ⟨p, hp, rp, low⟩ := mem_paths.mp onPath
    have root := (inside p hp).of_both rp (Nat.le_of_lt low)
    refine List.mem_mergeSort.mpr (mem_helpers_go h 0 opened r.sibling inside (by simpa using low)
      (root.sibling low) ⟨p, hp, by simpa using rp⟩ fun p' hp' above => outside ?_)
    exact mem_paths.mpr ⟨p', hp', above, by simpa using low⟩

/-- The helpers found below a node repeat no position. -/
theorem helpers_go_nodup : ∀ (l j : Nat) (L : List Position), (helpers.go L l j).Nodup := by
  intro l
  induction l with
  | zero => intro j L; simp [helpers.go]
  | succ l ih =>
    intro j L
    -- Helpers found below one child are not below the other.
    have under : ∀ j' L' q, q ∈ helpers.go L' l j' → (⟨l, j'⟩ : Position).IsAncestor q :=
      fun j' L' q member => (helpers_go_spec l j' L' q member).2.1
    simp only [helpers.go]
    split
    · exact List.nodup_nil
    · refine List.nodup_cons.mpr ⟨fun member => ?_, ih _ _⟩
      exact (Position.IsAncestor.refl _).not_both (under _ _ _ member) |>.elim
    · refine List.nodup_cons.mpr ⟨fun member => ?_, ih _ _⟩
      exact (under _ _ _ member).not_both (Position.IsAncestor.refl _) |>.elim
    · exact List.nodup_append.mpr ⟨ih _ _, ih _ _,
        fun q left _ right same => (under _ _ _ left).not_both (same ▸ under _ _ _ right)⟩

/-- No helper position is repeated.

So the helper values of a proof match the helper positions one to one. -/
theorem helpers_nodup (h : Nat) (opened : List Position) : (helpers h opened).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (helpers_go_nodup h 0 opened)

/-- A helper sits below level `h`. -/
theorem helpers_level {h : Nat} {opened : List Position} {q : Position}
    (member : q ∈ helpers h opened) : q.level < h :=
  (helpers_spec member).1

/-- No helper is an ancestor of an opened node.

So no helper hides an opened node from a rebuild that walks down from the root. -/
theorem helper_not_isAncestor {h : Nat} {opened : List Position} {q p : Position}
    (member : q ∈ helpers h opened) (hp : p ∈ opened) : ¬ q.IsAncestor p :=
  (helpers_spec member).2.2 p hp

/-- An opened node is not a helper. -/
theorem helpers_disjoint {h : Nat} {opened : List Position} {p : Position} (hp : p ∈ opened) :
    p ∉ helpers h opened :=
  fun member => helper_not_isAncestor member hp (Position.IsAncestor.refl p)

/-- The opened nodes and the helpers repeat no position, when the opened nodes do not.

So each position of a multiproof carries exactly one value. -/
theorem nodup_opened_helpers {h : Nat} {opened : List Position} (unique : opened.Nodup) :
    (opened ++ helpers h opened).Nodup :=
  List.nodup_append.mpr ⟨unique, helpers_nodup h opened,
    fun _ hp _ hq same => helpers_disjoint hp (same ▸ hq)⟩

/-- The opened nodes and the helpers form an antichain, when the opened nodes do.

So a rebuild reads every node given, and none hides another below it. -/
theorem helpers_antichain {h : Nat} {opened : List Position}
    (antichain : ∀ a ∈ opened, ∀ b ∈ opened, a.IsAncestor b → a = b) :
    ∀ a ∈ opened ++ helpers h opened, ∀ b ∈ opened ++ helpers h opened, a.IsAncestor b → a = b := by
  -- A node strictly above a helper is above its sibling, so above an opened node.
  have climb : ∀ {a b : Position}, b ∈ helpers h opened → a.IsAncestor b → a ≠ b →
      ∃ p ∈ opened, a.IsAncestor p ∧ p.level ≤ b.level ∧ b.level < a.level := by
    intro a b hb above distinct
    obtain ⟨-, ⟨p, hp, sp⟩, -⟩ := helpers_spec hb
    have lt : b.level < a.level := Nat.lt_of_not_le fun le => distinct (above.eq_of_level_le le)
    exact ⟨p, hp, (above.sibling lt).trans (by simpa using sp), by simpa using sp.level_le, lt⟩
  intro a ha b hb above
  refine Classical.byContradiction fun distinct => ?_
  rcases List.mem_append.mp hb with hb | hb
  · rcases List.mem_append.mp ha with ha | ha
    · exact distinct (antichain a ha b hb above)
    · exact helper_not_isAncestor ha hb above
  · obtain ⟨p, hp, ap, low, lt⟩ := climb hb above distinct
    rcases List.mem_append.mp ha with ha | ha
    · -- The opened node above would be the opened node below the helper, which is too low.
      have same := antichain a ha p hp ap
      subst same
      omega
    · exact helper_not_isAncestor ha hp ap

/-- A node is never its own sibling. -/
theorem Position.sibling_ne (q : Position) : q.sibling ≠ q := by
  intro same
  have index : q.index ^^^ 1 = q.index := congrArg Position.index same
  have parity := Nat.xor_mod_two_eq_one (a := q.index) (b := 1)
  omega

/-- The helpers of one opened node in the tree are the siblings of its path, from the node up.

So a multiproof of one node carries the path of that node. -/
theorem helpers_singleton {h : Nat} {p : Position} (inside : (⟨h, 0⟩ : Position).IsAncestor p) :
    helpers h [p] = (pathTo h p).map Position.sibling := by
  -- The siblings of the path sit on increasing levels, one per level.
  have sorted : ((pathTo h p).map Position.sibling).Pairwise (fun a b => a.level < b.level) := by
    simp only [pathTo, List.map_map, List.pairwise_map]
    exact List.pairwise_lt_range.imp fun lt => by simp; omega
  -- A sibling of a path node is on that node's level, so it is not on the path.
  have outside : ∀ q ∈ (pathTo h p).map Position.sibling, q ∉ pathTo h p := by
    intro q hq onPath
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨⟨a, rfl⟩, -⟩ := mem_pathTo.mp hr
    obtain ⟨⟨b, hb⟩, -⟩ := mem_pathTo.mp onPath
    have : a = b := by
      have := congrArg Position.level hb
      simp only [Position.sibling_level, Position.ancestor_level] at this
      omega
    subst this
    exact Position.sibling_ne _ hb
  -- Both lists hold the same positions once each, in the same order.
  have paths : [p].flatMap (pathTo h) = pathTo h p := by simp
  refine List.Perm.eq_of_pairwise (le := fun a b => Position.helperBefore a b = true) ?_
    (List.pairwise_mergeSort ?_ ?_ _) (sorted.imp fun lt => by simp [Position.helperBefore, lt])
    ((List.perm_ext_iff_of_nodup (helpers_nodup h [p])
      (sorted.imp fun lt same => by subst same; omega)).mpr fun q => ?_)
  · -- The order is antisymmetric.
    intro a b _ _ ab ba
    simp only [Position.helperBefore, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      beq_iff_eq] at ab ba
    exact Position.ext (by omega) (by omega)
  · -- The order is transitive.
    intro a b c ab bc
    simp only [Position.helperBefore, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      beq_iff_eq] at ab bc ⊢
    omega
  · -- The order is total.
    intro a b
    simp only [Position.helperBefore, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      beq_iff_eq]
    omega
  · rw [mem_helpers (by simpa using inside), paths]
    exact ⟨fun member => member.1, fun member => ⟨member, outside q member⟩⟩

/-! ## Rebuilding -/

section Rebuild

variable {α : Type} (hash : Position → α → α → Id α)

/-- Two filters commute. -/
theorem filter_swap {β : Type} (l : List β) (P Q : β → Bool) :
    (l.filter P).filter Q = (l.filter Q).filter P := by
  simp only [List.filter_filter, Bool.and_comm]

/-- A rebuild takes a node given at its position as it is. -/
theorem rebuild_go_of_lookup {nodes : List (Position × α)} {l j : Nat} {v : α}
    (found : nodes.lookup ⟨l, j⟩ = some v) : (rebuild.go hash nodes l j).run = some v := by
  cases l with
  | zero => exact found
  | succ l => rw [rebuild.go, found]; rfl

/-- A lookup reads only the entries with its key, so a filter that keeps them changes nothing. -/
theorem lookup_filter {β γ : Type} [BEq β] [LawfulBEq β] {l : List (β × γ)} {k : β}
    (P : β × γ → Bool) (keep : ∀ e ∈ l, e.1 = k → P e = true) :
    (l.filter P).lookup k = l.lookup k := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨a, b⟩ := e
    have tail := ih fun e he => keep e (List.mem_cons_of_mem _ he)
    by_cases same : a = k
    · -- The first entry has the key, and the filter keeps it.
      subst same
      rw [List.filter_cons_of_pos (keep _ (by simp) rfl)]
      simp
    · -- The first entry has another key, so only the rest matters.
      have differ : (k == a) = false := by simpa using Ne.symm same
      cases kept : P (a, b) <;>
        simp [kept, List.lookup_cons, differ, tail]

/-- A rebuild above level 0, without the monad: the node given, or the hash of the children.

The left child receives the nodes below it, and the right child the others. -/
theorem rebuild_go_succ_run (nodes : List (Position × α)) (l j : Nat) :
    (rebuild.go hash nodes (l + 1) j).run =
      match nodes.lookup ⟨l + 1, j⟩ with
      | some node => some node
      | none =>
        if nodes.isEmpty then none else
          match (rebuild.go hash (nodes.filter fun e => (⟨l, 2 * j⟩ : Position).covers e.1)
              l (2 * j)).run,
            (rebuild.go hash (nodes.filter fun e => !(⟨l, 2 * j⟩ : Position).covers e.1)
              l (2 * j + 1)).run with
          | some a, some b => some (hash ⟨l + 1, j⟩ a b).run
          | _, _ => none := by
  rw [rebuild.go]
  cases nodes.lookup ⟨l + 1, j⟩ with
  | some node => rfl
  | none =>
    dsimp only
    split
    · rfl
    · simp only [List.partition_eq_filter_filter, Function.comp_def]
      show (match (rebuild.go hash (nodes.filter fun e => (⟨l, 2 * j⟩ : Position).covers e.1)
            l (2 * j)).run with
          | none => none
          | some leftNode =>
            match (rebuild.go hash (nodes.filter fun e => !(⟨l, 2 * j⟩ : Position).covers e.1)
                l (2 * j + 1)).run with
            | none => none
            | some rightNode => some (hash ⟨l + 1, j⟩ leftNode rightNode).run) = _
      cases (rebuild.go hash (nodes.filter fun e => (⟨l, 2 * j⟩ : Position).covers e.1)
          l (2 * j)).run <;>
        cases (rebuild.go hash (nodes.filter fun e => !(⟨l, 2 * j⟩ : Position).covers e.1)
          l (2 * j + 1)).run <;> rfl

/-- A rebuild from no node determines nothing. -/
theorem rebuild_go_nil : ∀ l j, (rebuild.go hash ([] : List (Position × α)) l j).run = none
  | 0, _ => rfl
  | l + 1, j => by rw [rebuild_go_succ_run]; rfl

/-- A rebuild at a node reads only the nodes given below it.

So a filter that keeps those nodes does not change the rebuild. -/
theorem rebuild_go_filter : ∀ (l j : Nat) (nodes : List (Position × α))
    (P : Position × α → Bool),
    (∀ e ∈ nodes, (⟨l, j⟩ : Position).IsAncestor e.1 → P e = true) →
      (rebuild.go hash (nodes.filter P) l j).run = (rebuild.go hash nodes l j).run := by
  intro l
  induction l with
  | zero =>
    intro j nodes P keep
    exact lookup_filter P fun e he key => keep e he (key ▸ .refl _)
  | succ l ih =>
    intro j nodes P keep
    rw [rebuild_go_succ_run, rebuild_go_succ_run,
      lookup_filter P fun e he key => keep e he (key ▸ .refl _)]
    cases nodes.lookup ⟨l + 1, j⟩ with
    | some node => rfl
    | none =>
      dsimp only
      -- The nodes below a child are below the node, so the filter keeps them.
      have keepLeft : ∀ e ∈ nodes, (⟨l, 2 * j⟩ : Position).IsAncestor e.1 → P e = true :=
        fun e he below => keep e he ((Position.isAncestor_left l j).trans below)
      have keepRight : ∀ e ∈ nodes, (⟨l, 2 * j + 1⟩ : Position).IsAncestor e.1 → P e = true :=
        fun e he below => keep e he ((Position.isAncestor_right l j).trans below)
      -- Each child of the filtered rebuild reads the same nodes as the child of the other one.
      have left : (rebuild.go hash ((nodes.filter P).filter fun e =>
          (⟨l, 2 * j⟩ : Position).covers e.1) l (2 * j)).run =
          (rebuild.go hash (nodes.filter fun e => (⟨l, 2 * j⟩ : Position).covers e.1)
            l (2 * j)).run := by
        rw [filter_swap]
        exact ih _ _ P fun e he below => keepLeft e (List.mem_filter.mp he).1 below
      have right : (rebuild.go hash ((nodes.filter P).filter fun e =>
          !(⟨l, 2 * j⟩ : Position).covers e.1) l (2 * j + 1)).run =
          (rebuild.go hash (nodes.filter fun e => !(⟨l, 2 * j⟩ : Position).covers e.1)
            l (2 * j + 1)).run := by
        rw [filter_swap]
        exact ih _ _ P fun e he below => keepRight e (List.mem_filter.mp he).1 below
      rw [left, right]
      by_cases empty : (nodes.filter P).isEmpty
      · -- With nothing kept, nothing lies below the left child, so both sides are missing.
        simp only [empty, ↓reduceIte]
        split
        · rfl
        · have none : nodes.filter (fun e => (⟨l, 2 * j⟩ : Position).covers e.1) = [] := by
            rw [List.filter_eq_nil_iff]
            intro e he below
            have kept := keepLeft e he (Position.covers_iff.mp (by simpa using below))
            have := List.isEmpty_iff.mp empty
            exact List.filter_eq_nil_iff.mp this e he (by simp [kept])
          rw [none, rebuild_go_nil]
      · have full : nodes.isEmpty = false := by
          cases h : nodes.isEmpty
          · rfl
          · simp [List.isEmpty_iff.mp h] at empty
        simp [empty, full]

/-- Without a node given at a position above level 0, a rebuild hashes the two children there.

The result is missing when a child is missing. -/
theorem rebuild_go_succ_of_lookup_none {nodes : List (Position × α)} {l j : Nat}
    (absent : nodes.lookup ⟨l + 1, j⟩ = none) :
    (rebuild.go hash nodes (l + 1) j).run =
      match (rebuild.go hash nodes l (2 * j)).run, (rebuild.go hash nodes l (2 * j + 1)).run with
      | some left, some right => some (hash ⟨l + 1, j⟩ left right).run
      | _, _ => none := by
  rw [rebuild_go_succ_run, absent]
  dsimp only
  split
  · -- No node at all: both children are missing.
    rename_i empty
    rw [List.isEmpty_iff.mp empty, rebuild_go_nil]
  · -- Each child reads only the nodes below it, which its filter keeps.
    rw [rebuild_go_filter hash l (2 * j) nodes _
        fun e _ below => Position.covers_iff.mpr below,
      rebuild_go_filter hash l (2 * j + 1) nodes _ fun e _ below => by
        cases c : (⟨l, 2 * j⟩ : Position).covers e.1
        · rfl
        · exact ((Position.covers_iff.mp c).not_both below).elim]

/-- A property of the nodes given that the hash carries to parents holds of every rebuilt node.

So a proof about a rebuild needs one step for the nodes given and one for the hash. -/
theorem rebuild_go_induction (P : Position → α → Prop) {nodes : List (Position × α)}
    (supplied : ∀ e ∈ nodes, P e.1 e.2)
    (step : ∀ (p : Position) (a b : α), 1 ≤ p.level → P p.left a → P p.right b →
      P p (hash p a b).run) :
    ∀ (l j : Nat) (v : α), (rebuild.go hash nodes l j).run = some v → P ⟨l, j⟩ v
  | 0, j, v, rebuilt => supplied _ (mem_of_lookup_eq_some rebuilt)
  | l + 1, j, v, rebuilt => by
    cases found : nodes.lookup ⟨l + 1, j⟩ with
    | some w =>
      -- A node given is returned as it is.
      rw [rebuild_go_of_lookup hash found] at rebuilt
      cases rebuilt
      exact supplied _ (mem_of_lookup_eq_some found)
    | none =>
      -- Otherwise the node is the hash of two rebuilt children, which have the property.
      rw [rebuild_go_succ_of_lookup_none hash found] at rebuilt
      split at rebuilt
      · rename_i a b left right
        cases rebuilt
        exact step ⟨l + 1, j⟩ a b (by simp)
          (rebuild_go_induction P supplied step l (2 * j) a left)
          (rebuild_go_induction P supplied step l (2 * j + 1) b right)
      · cases rebuilt

/-- A rebuild determines a region whose nodes are given or have both children in the region. -/
theorem rebuild_go_isSome {nodes : List (Position × α)} (S : Position → Prop)
    (frontier : ∀ r, S r → (nodes.lookup r).isSome ∨ (1 ≤ r.level ∧ S r.left ∧ S r.right)) :
    ∀ l j, S ⟨l, j⟩ → ((rebuild.go hash nodes l j).run).isSome
  | 0, j, inside => by
    -- At level 0 the node must be given, since it has no children.
    rcases frontier _ inside with found | ⟨low, -⟩
    · exact found
    · exact absurd low (by simp)
  | l + 1, j, inside => by
    cases found : nodes.lookup ⟨l + 1, j⟩ with
    | some w => simp [rebuild_go_of_lookup hash found]
    | none =>
      -- Both children lie in the region, so both are rebuilt, and so is their parent.
      rcases frontier _ inside with given | ⟨-, left, right⟩
      · simp [found] at given
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp
        (rebuild_go_isSome S frontier l (2 * j) left)
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
        (rebuild_go_isSome S frontier l (2 * j + 1) right)
      simp [rebuild_go_succ_of_lookup_none hash found, ha, hb]

/-- Nodes of the tree of height `h` where each node above level 0 hashes its two children. -/
def Consistent (h : Nat) (t : Position → α) : Prop :=
  ∀ p : Position, 1 ≤ p.level → (⟨h, 0⟩ : Position).IsAncestor p →
    t p = (hash p (t p.left) (t p.right)).run

/-- The nodes of a tree built from its leaves follow the hash.

So completeness applies to the tree built from the leaves. -/
theorem node_consistent (leaves : Nat → Id α) (h : Nat) :
    Consistent hash h (fun p => (node hash leaves p).run) :=
  fun _ low _ => node_children_run hash leaves (by omega)

/-- A rebuilt node agrees with any consistent tree that agrees with the nodes given.

So a rebuild from honest nodes returns honest nodes. -/
theorem rebuild_go_agrees {h : Nat} {t : Position → α} (consistent : Consistent hash h t)
    {nodes : List (Position × α)} (agree : ∀ e ∈ nodes, t e.1 = e.2) {l j : Nat} {v : α}
    (rebuilt : (rebuild.go hash nodes l j).run = some v)
    (inside : (⟨h, 0⟩ : Position).IsAncestor ⟨l, j⟩) : v = t ⟨l, j⟩ := by
  refine rebuild_go_induction hash (fun p v => (⟨h, 0⟩ : Position).IsAncestor p → v = t p)
    (fun e he _ => (agree e he).symm) ?_ l j v rebuilt inside
  -- A parent inside the tree has its children inside, where the rebuild agrees already.
  intro p a b low ha hb above
  have left := above.trans (Position.isAncestor_of_parent (Position.left_parent (by omega)))
  have right := above.trans (Position.isAncestor_of_parent (Position.right_parent (by omega)))
  rw [consistent p low above, ha left, hb right]

/-- Any values for one or more opened nodes in the tree and for their helpers rebuild a root. -/
theorem verify_isSome {h : Nat} {opened : List Position} {values helperValues : List α}
    (nonempty : opened ≠ []) (inside : ∀ p ∈ opened, (⟨h, 0⟩ : Position).IsAncestor p)
    (valueCount : values.length = opened.length)
    (helperCount : helperValues.length = (helpers h opened).length) :
    ((verify hash h opened values helperValues).run).isSome := by
  let nodes := opened.zip values ++ (helpers h opened).zip helperValues
  -- The zips keep every position, since the counts match.
  have keys : nodes.map Prod.fst = opened ++ helpers h opened := by
    simp [nodes, List.map_fst_zip, valueCount, helperCount]
  -- The region: the nodes given, and every ancestor of an opened node up to the root.
  let S : Position → Prop := fun r =>
    r ∈ opened ++ helpers h opened ∨ ∃ p ∈ opened, r.IsAncestor p ∧ r.level ≤ h
  refine rebuild_go_isSome hash S (fun r inS => ?_) h 0 ?_
  · by_cases given : r ∈ opened ++ helpers h opened
    · exact .inl (lookup_isSome_iff_mem.mpr (keys ▸ given))
    obtain ⟨p, hp, rp, top⟩ := inS.resolve_left given
    -- A path node that is not given sits strictly above its opened node.
    have distinct : r ≠ p := fun same => given (List.mem_append_left _ (same ▸ hp))
    have above : p.level < r.level :=
      Nat.lt_of_not_le fun le => distinct (rp.eq_of_level_le le)
    -- Its child on the side of the opened node is a path node below level `h`.
    obtain ⟨k, rfl⟩ := rp
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at above; omega⟩
    have onPath : p.ancestor k ∈ opened.flatMap (pathTo h) :=
      mem_paths.mpr ⟨p, hp, ⟨k, rfl⟩, by simp at top ⊢; omega⟩
    -- Each child is that path node or its sibling, which is a path node or a helper.
    have child : ∀ c : Position, c.parent = p.ancestor (k + 1) → S c := by
      intro c parent
      rcases Position.eq_or_eq_sibling_of_parent_eq (b := p.ancestor k) (by simpa using parent)
        with rfl | rfl
      · exact .inr ⟨p, hp, ⟨k, rfl⟩, by simp at top ⊢; omega⟩
      · by_cases path : (p.ancestor k).sibling ∈ opened.flatMap (pathTo h)
        · obtain ⟨q, hq, cq, low⟩ := mem_paths.mp path
          exact .inr ⟨q, hq, cq, Nat.le_of_lt low⟩
        · exact .inl (List.mem_append_right _
            ((mem_helpers inside).mpr ⟨List.mem_map_of_mem onPath, path⟩))
    have low : (p.ancestor (k + 1)).level ≠ 0 := by simp
    exact .inr ⟨by simp; omega, child _ (Position.left_parent low),
      child _ (Position.right_parent low)⟩
  · -- The root is an ancestor of any opened node.
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil opened nonempty
    exact .inr ⟨p, hp, inside p hp, Nat.le_refl h⟩

/-- Completeness: an honest multiproof, read from a consistent tree, rebuilds its root.

It needs at least one opened node, each in the tree. -/
theorem verify_complete {h : Nat} {t : Position → α} (consistent : Consistent hash h t)
    {opened : List Position} (nonempty : opened ≠ [])
    (inside : ∀ p ∈ opened, (⟨h, 0⟩ : Position).IsAncestor p) :
    (verify hash h opened (opened.map t) ((helpers h opened).map t)).run = some (t ⟨h, 0⟩) := by
  -- The rebuild succeeds, and what it returns agrees with the tree.
  obtain ⟨v, rebuilt⟩ := Option.isSome_iff_exists.mp
    (verify_isSome hash nonempty inside (List.length_map ..) (List.length_map ..))
  have agree : ∀ e ∈ opened.zip (opened.map t) ++ (helpers h opened).zip ((helpers h opened).map t),
      t e.1 = e.2 := fun e he => (List.mem_append.mp he).elim mem_zip_map mem_zip_map
  rw [rebuilt, rebuild_go_agrees hash consistent agree rebuilt (Position.IsAncestor.refl _)]

/-- Completeness in the tree built from its leaves: an honest multiproof rebuilds its root.

So an honest prover needs nothing but the tree. -/
theorem verify_node (leaves : Nat → Id α) {h : Nat} {opened : List Position}
    (nonempty : opened ≠ []) (inside : ∀ p ∈ opened, (⟨h, 0⟩ : Position).IsAncestor p) :
    (verify hash h opened (opened.map fun p => (node hash leaves p).run)
        ((helpers h opened).map fun p => (node hash leaves p).run)).run =
      some (root hash leaves h).run :=
  verify_complete hash (node_consistent hash leaves h) nonempty inside

/-- A multiproof of one node in the tree, with one value per level above it, is its climb.

So a single path is a multiproof. -/
theorem verify_singleton {h : Nat} {p : Position} (inside : (⟨h, 0⟩ : Position).IsAncestor p)
    (v : α) (s : List α) (count : s.length = h - p.level) :
    (verify hash h [p] [v] s).run = some (climb hash p v s).run := by
  have low : p.level ≤ h := inside.level_le
  let keys := (pathTo h p).map Position.sibling
  let nodes := [(p, v)] ++ keys.zip s
  have keysLength : keys.length = h - p.level := by simp [keys, pathTo]
  -- The siblings of the path are distinct, and none is the opened node.
  have unique : keys.Nodup := by
    have := helpers_nodup h [p]
    rwa [helpers_singleton inside] at this
  have keyLevel : ∀ i (hi : i < keys.length), keys[i] = (p.ancestor i).sibling := by
    intro i hi
    simp [keys, pathTo]
  -- Each node on the path holds the climb so far.
  have climbs : ∀ k, k ≤ h - p.level →
      (rebuild.go hash nodes (p.ancestor k).level (p.ancestor k).index).run =
        some (climb hash p v (s.take k)).run := by
    intro k
    induction k with
    | zero =>
      intro _
      -- The opened node is the first node given.
      exact rebuild_go_of_lookup hash (by simp [nodes])
    | succ k ih =>
      intro below
      have hk : k < keys.length := by omega
      have hs : k < s.length := by omega
      -- No node is given at the ancestor: it is above the opened node, and on no sibling's level.
      have absent : nodes.lookup ⟨p.level + k + 1, p.index / 2 ^ (k + 1)⟩ = none := by
        rw [List.lookup_eq_none_iff]
        intro e he
        simp only [bne_iff_ne, ne_eq]
        rintro same
        rcases List.mem_append.mp he with he | he
        · simp only [List.mem_singleton] at he
          subst he
          have := congrArg Position.level same
          simp at this
          omega
        · obtain ⟨i, hi, key⟩ := List.mem_iff_getElem.mp (List.of_mem_zip he).1
          rw [← key, keyLevel i hi] at same
          have levels := congrArg Position.level same
          simp only [Position.sibling_level, Position.ancestor_level] at levels
          obtain rfl : i = k + 1 := by omega
          exact Position.sibling_ne (p.ancestor (k + 1)) same.symm
      -- The sibling of the node held is given, with the proof value of this level.
      have sibling : nodes.lookup (p.ancestor k).sibling = some s[k] := by
        have found := lookup_zip_getElem unique [] hk hs
        rw [List.append_nil, keyLevel k hk] at found
        show List.lookup _ ((p, v) :: keys.zip s) = _
        rw [List.lookup_cons]
        have differ : ((p.ancestor k).sibling == p) = false := by
          rw [beq_eq_false_iff_ne]
          intro same
          cases k with
          | zero => exact Position.sibling_ne p (by simpa using same)
          | succ k =>
            have := congrArg Position.level same
            simp at this
        rw [differ]
        exact found
      have held := ih (by omega)
      simp only [Position.ancestor_level, Position.ancestor_index] at held
      have given := rebuild_go_of_lookup hash sibling
      simp only [Position.ancestor_level, Position.ancestor_index] at given
      have step := climb_take_succ hash p v s k hs
      show (rebuild.go hash nodes (p.level + k + 1) (p.index / 2 ^ (k + 1))).run = _
      rw [rebuild_go_succ_of_lookup_none hash absent, step]
      -- The parity of the node held says which child it is, and the sibling is the other.
      have half : p.index / 2 ^ k / 2 = p.index / 2 ^ (k + 1) := div_pow_div_two _ _
      have parent : (p.ancestor k).parent = ⟨p.level + k + 1, p.index / 2 ^ (k + 1)⟩ := by
        rw [Position.parent_ancestor]
        rfl
      rcases Nat.mod_two_eq_zero_or_one (p.index / 2 ^ k) with even | odd
      · -- The node held is the left child, and its sibling the right one.
        rw [xor_one_of_even even] at given
        rw [show 2 * (p.index / 2 ^ (k + 1)) = p.index / 2 ^ k by omega, held, given]
        simp [Position.isLeft, even, parent]
      · -- The node held is the right child, and its sibling the left one.
        rw [xor_one_of_odd odd] at given
        have positive : 1 ≤ p.index / 2 ^ k :=
          Nat.pos_of_ne_zero fun zero => by rw [zero] at odd; simp at odd
        rw [show 2 * (p.index / 2 ^ (k + 1)) = p.index / 2 ^ k - 1 by omega, given,
          Nat.sub_add_cancel positive, held]
        simp [Position.isLeft, odd, parent]
  -- At the top, the node held is the root, and the climb has used every value.
  have top := climbs (h - p.level) (Nat.le_refl _)
  have root : p.ancestor (h - p.level) = ⟨h, 0⟩ := by
    obtain ⟨-, zero⟩ := Position.isAncestor_iff.mp inside
    dsimp only at zero
    exact Position.ext (by simp; omega) (by simpa using zero.symm)
  rw [root, List.take_of_length_le (by omega)] at top
  simpa [verify, rebuild, helpers_singleton inside, nodes, keys] using top

/-- A climb whose hash ignores positions reads only the low bits of the start index.

It reads one bit per sibling, so a single path climbs alike from any index with those bits. -/
theorem climb_congr_index (ignores : ∀ p q : Position, hash p = hash q) :
    ∀ (s : List α) (l j j' : Nat) (v : α), j % 2 ^ s.length = j' % 2 ^ s.length →
      (climb hash ⟨l, j⟩ v s).run = (climb hash ⟨l, j'⟩ v s).run
  | [], _, _, _, _, _ => rfl
  | u :: s, l, j, j', v, same => by
    simp only [List.length_cons] at same
    -- The low bit picks the side, and the next bits are those of the halved index.
    have two : 2 ∣ 2 ^ (s.length + 1) := ⟨2 ^ s.length, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    have parity : j % 2 = j' % 2 := by
      rw [← Nat.mod_mod_of_dvd j two, ← Nat.mod_mod_of_dvd j' two, same]
    have half : j / 2 % 2 ^ s.length = j' / 2 % 2 ^ s.length := by
      rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← Nat.pow_succ', same]
    have side : ordered ⟨l, j⟩ v u = ordered ⟨l, j'⟩ v u := by
      simp only [ordered, Position.isLeft, parity]
      rfl
    rw [climb_cons, climb_cons, side,
      ignores (Position.parent ⟨l, j⟩) (Position.parent ⟨l, j'⟩)]
    exact climb_congr_index ignores s (l + 1) (j / 2) (j' / 2) _ half

/-! ## Lifting a rebuild -/

/-- Lifting every node given by `k` levels lifts what a lookup finds by `k` levels. -/
theorem lookup_lift (k : Nat) (nodes : List (Position × α)) (l j : Nat) :
    (nodes.map fun e => ((⟨e.1.level + k, e.1.index⟩ : Position), e.2)).lookup ⟨l + k, j⟩ =
      nodes.lookup ⟨l, j⟩ := by
  induction nodes with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨q, w⟩ := e
    -- Lifting both positions by `k` levels keeps them equal or different.
    have same : ((⟨l + k, j⟩ : Position) == ⟨q.level + k, q.index⟩) =
        ((⟨l, j⟩ : Position) == q) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, Position.ext_iff]
      omega
    simp only [List.map_cons, List.lookup_cons, same, ih]

end Rebuild

/-! ## Any monad -/

section Monad

variable {m : Type → Type} [Monad m] {α : Type} (hash : Position → α → α → m α)

/-- A rebuild above level 0: the node given, or the hash of its children rebuilt from each side. -/
theorem rebuild_go_succ (nodes : List (Position × α)) (l j : Nat) :
    rebuild.go hash nodes (l + 1) j =
      (match nodes.lookup ⟨l + 1, j⟩ with
      | some node => pure (some node)
      | none =>
        if nodes.isEmpty then pure none else do
          match ← rebuild.go hash (nodes.filter fun e => (⟨l, 2 * j⟩ : Position).covers e.1)
              l (2 * j) with
          | none => pure none
          | some a =>
            match ← rebuild.go hash
                (nodes.filter fun e => !(⟨l, 2 * j⟩ : Position).covers e.1) l (2 * j + 1) with
            | none => pure none
            | some b => some <$> hash ⟨l + 1, j⟩ a b) := by
  rw [rebuild.go]
  simp only [List.partition_eq_filter_filter, Function.comp_def]
  rfl

/-- A rebuild from no node determines nothing, in any monad. -/
theorem rebuild_go_nil_pure : ∀ l j, rebuild.go hash ([] : List (Position × α)) l j = pure none
  | 0, _ => rfl
  | l + 1, j => by rw [rebuild_go_succ]; rfl

/-- Lifting both positions by `k` levels keeps whether one covers the other. -/
theorem Position.covers_lift (k : Nat) (a p : Position) :
    (⟨a.level + k, a.index⟩ : Position).covers ⟨p.level + k, p.index⟩ = a.covers p := by
  simp only [Position.covers, Nat.add_sub_add_right, Nat.add_le_add_iff_right]

/-- Lifting every node given by `k` levels lifts the rebuild, for a hash that ignores levels.

So two multiproofs can be compared in the taller of their two trees, in any monad. -/
theorem rebuild_go_lift_monad [LawfulMonad m] (k : Nat)
    (ignores : ∀ p : Position, hash ⟨p.level + k, p.index⟩ = hash p)
    :
    ∀ l j (nodes : List (Position × α)),
      rebuild.go hash (nodes.map fun e => ((⟨e.1.level + k, e.1.index⟩ : Position), e.2))
        (l + k) j = rebuild.go hash nodes l j := by
  -- The lift commutes with the filter of each child.
  have filters : ∀ (nodes : List (Position × α)) (l j : Nat) (keep : Bool → Bool),
      (nodes.map fun e => ((⟨e.1.level + k, e.1.index⟩ : Position), e.2)).filter
          (fun e => keep ((⟨l + k, j⟩ : Position).covers e.1)) =
        (nodes.filter fun e => keep ((⟨l, j⟩ : Position).covers e.1)).map
          fun e => ((⟨e.1.level + k, e.1.index⟩ : Position), e.2) := by
    intro nodes l j keep
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro e _
    simp only [Function.comp_apply]
    rw [Position.covers_lift k ⟨l, j⟩ e.1]
  intro l
  induction l with
  | zero =>
    intro j nodes
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.zero_add, rebuild_go_succ]
      have lookup := lookup_lift (k + 1) nodes 0 j
      rw [Nat.zero_add] at lookup
      rw [lookup]
      show _ = pure (nodes.lookup ⟨0, j⟩)
      cases nodes.lookup ⟨0, j⟩ with
      | some v => rfl
      | none =>
        -- Nothing lifted lies below level `k + 1`, so the left child is missing.
        dsimp only
        split
        · rfl
        · have empty : (nodes.map fun e => ((⟨e.1.level + (k + 1), e.1.index⟩ : Position),
              e.2)).filter (fun e => (⟨k, 2 * j⟩ : Position).covers e.1) = [] := by
            rw [List.filter_eq_nil_iff]
            intro e member
            obtain ⟨e', -, rfl⟩ := List.mem_map.mp member
            simp only [Position.covers, Bool.and_eq_true, decide_eq_true_eq, not_and]
            omega
          rw [empty, rebuild_go_nil_pure, pure_bind]
  | succ l ih =>
    intro j nodes
    rw [show l + 1 + k = l + k + 1 by omega, rebuild_go_succ, rebuild_go_succ]
    have lookup := lookup_lift k nodes (l + 1) j
    rw [show l + 1 + k = l + k + 1 by omega] at lookup
    rw [lookup, List.isEmpty_map]
    -- The children of the lifted node are the lifted children.
    have left := filters nodes l (2 * j) id
    have right := filters nodes l (2 * j) (!·)
    simp only [id] at left right
    rw [left, right, ih (2 * j), ih (2 * j + 1)]
    have tweak := ignores ⟨l + 1, j⟩
    simp only [show l + 1 + k = l + k + 1 by omega] at tweak
    rw [tweak]

end Monad

/-- Lifting every node given by `k` levels lifts the rebuild, for a hash that ignores levels. -/
theorem rebuild_go_lift {α : Type} (hash : Position → α → α → Id α) (k : Nat)
    (ignores : ∀ p : Position, hash ⟨p.level + k, p.index⟩ = hash p)
    (nodes : List (Position × α)) (l j : Nat) :
    (rebuild.go hash (nodes.map fun e => ((⟨e.1.level + k, e.1.index⟩ : Position), e.2))
      (l + k) j).run = (rebuild.go hash nodes l j).run := by
  rw [rebuild_go_lift_monad hash k ignores l j nodes]

end EthLib.Cryptography.Merkle
