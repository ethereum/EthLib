module

public import EthLib.Cryptography.Proofs.Merkle.Completeness

/-!
# Proofs: a path binds its leaf

A path climbs from a leaf to the root, hashing one pair of nodes per level.

The theorems here show that a forged path forces a weakness of the node hash.

## Two forged climbs: a collision

Take two climbs from one position, with different leaves, that reach one root.

- At the bottom their nodes differ, and at the top they are equal.
- At the first level where they become equal, the two pairs hashed below differ.
- So two different pairs hash to one node: a collision.

## One climb against the built tree: a second preimage

Take one climb from a position of the built tree, with a wrong leaf, that reaches its root.

- At the bottom it differs from the tree, and at the top it agrees with it.
- At the first level where it agrees, it hashes another pair to a node of the tree.
- So it finds a new input for a node the tree already holds: a second preimage.

## The difference

A collision lets the forger choose both pairs.

A second preimage must match a node fixed before the forger acts, so it is the harder attack.

The theorems return each pair from an explicit search, since any compressing hash has some.

The searches run in any monad, so a random oracle can answer their hash calls.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

variable {α : Type} (hash : Position → α → α → Id α)

/-! ## Any two climbs -/

/-- Two pairs of children offered for the node at one position. -/
structure Collision (α : Type) where
  /-- The position of the parent. -/
  position : Position
  /-- The first pair, left child first. -/
  x : α × α
  /-- The second pair, left child first. -/
  y : α × α

/-- The two pairs differ, and hash to one parent at their position. -/
def Collision.Valid (c : Collision α) : Prop :=
  c.x ≠ c.y ∧ (hash c.position c.x.1 c.x.2).run = (hash c.position c.y.1 c.y.2).run

/-- The collision two climbs from one position run into, at the lowest level where one exists.

On each level, both climbs hash their held node with their sibling, in the order the position gives.

A level where the two pairs differ but the parents agree is a collision.

The search runs in any monad, so an oracle can answer its two hash calls per level. -/
def findCollision {m : Type → Type} [Monad m] [DecidableEq α]
    (hash : Position → α → α → m α) :
    (p : Position) → (a b : α) → (s t : List α) → m (Option (Collision α))
  | p, a, b, u :: s, v :: t => do
    let x := ordered p a u
    let y := ordered p b v
    let parentA ← hash p.parent x.1 x.2
    let parentB ← hash p.parent y.1 y.2
    if x ≠ y ∧ parentA = parentB then return some ⟨p.parent, x, y⟩
    else findCollision hash p.parent parentA parentB s t
  | _, _, _, _, _ => pure none

/-- In the identity monad, one level of the search compares the two pairs it hashes there. -/
theorem findCollision_cons [DecidableEq α] (p : Position) (a b u v : α) (s t : List α) :
    findCollision hash p a b (u :: s) (v :: t) =
      (let x := ordered p a u
       let y := ordered p b v
       let parentA := (hash p.parent x.1 x.2).run
       let parentB := (hash p.parent y.1 y.2).run
       if x ≠ y ∧ parentA = parentB then some ⟨p.parent, x, y⟩
       else findCollision hash p.parent parentA parentB s t : Option (Collision α)) :=
  rfl

/-- Every collision the search returns is valid, at an ancestor of the starting position.

The ancestor is `k + 1` levels up.

Its two pairs are the ones the two climbs hash there, after `k` levels. -/
theorem findCollision_valid [DecidableEq α] :
    ∀ (s t : List α) (p : Position) (a b : α) (c : Collision α),
      findCollision hash p a b s t = some c →
      c.Valid hash ∧ ∃ k u v, s[k]? = some u ∧ t[k]? = some v ∧
        c.position = p.ancestor (k + 1) ∧
        c.x = ordered (p.ancestor k) (climb hash p a (s.take k)).run u ∧
        c.y = ordered (p.ancestor k) (climb hash p b (t.take k)).run v := by
  intro s
  induction s with
  | nil => intro t p a b c h; simp [findCollision] at h
  | cons u rest ih =>
    intro t p a b c h
    cases t with
    | nil => simp [findCollision] at h
    | cons v rest' =>
      simp only [findCollision_cons] at h
      split at h
      · -- This level is the collision.
        rename_i hfound
        cases h
        exact ⟨hfound, 0, u, v, rfl, rfl, by simp, by simp, by simp⟩
      · -- The collision is further up: one level higher in the count.
        obtain ⟨hvalid, k, u', v', hu, hv, hposition, hx, hy⟩ :=
          ih rest' p.parent _ _ c h
        refine ⟨hvalid, k + 1, u', v', hu, hv, ?_, ?_, ?_⟩ <;>
          simp only [Position.ancestor_parent] at * <;> assumption

/-- One climb compared with itself runs into no collision. -/
theorem findCollision_self [DecidableEq α] :
    ∀ (s : List α) (p : Position) (a : α), findCollision hash p a a s s = none
  | [], _, _ => rfl
  | u :: rest, p, a => by
    -- The two pairs at each level are the same pair.
    simp only [findCollision_cons, ne_eq, not_true_eq_false, false_and, ↓reduceIte,
      findCollision_self rest]

/-- Binding: two climbs from one position over equally many siblings that meet are equal.

Otherwise the collision search finds a collision of the node hash. -/
theorem climb_binding [DecidableEq α] :
    ∀ (s t : List α) (p : Position) (a b : α), s.length = t.length →
      (climb hash p a s).run = (climb hash p b t).run →
      (a = b ∧ s = t) ∨ (findCollision hash p a b s t).isSome := by
  intro s
  induction s with
  | nil =>
    intro t p a b hl heq
    cases t with
    | nil => exact .inl ⟨heq, rfl⟩
    | cons _ _ => simp at hl
  | cons u rest ih =>
    intro t p a b hl heq
    cases t with
    | nil => simp at hl
    | cons v rest' =>
      rw [climb_cons, climb_cons] at heq
      simp only [findCollision_cons]
      -- When this level is a collision, the search stops here.
      by_cases hfound : ordered p a u ≠ ordered p b v ∧
          (hash p.parent (ordered p a u).1 (ordered p a u).2).run
            = (hash p.parent (ordered p b v).1 (ordered p b v).2).run
      · exact .inr (by simp [hfound])
      simp only [hfound, ↓reduceIte]
      rcases ih rest' p.parent _ _ (by simpa using hl) heq with
        ⟨hparent, hrest⟩ | hsome
      · -- Equal parents and no collision here: the pairs are equal, so the climbs are.
        have hpair : ordered p a u = ordered p b v :=
          Classical.byContradiction fun hne => hfound ⟨hne, hparent⟩
        obtain ⟨rfl, rfl⟩ := ordered_inj.mp hpair
        exact .inl ⟨rfl, by rw [hrest]⟩
      · exact .inr hsome

/-! ## What a climb hashes -/

/-- The pairs a climb from a position hashes, one per level, from the bottom up.

Each pair holds the climb's node and its sibling, in the order the position gives. -/
def climbPairs : (p : Position) → (a : α) → (s : List α) → List (α × α)
  | _, _, [] => []
  | p, a, u :: s =>
    let x := ordered p a u
    x :: climbPairs p.parent (hash p.parent x.1 x.2).run s

/-- The pair a climb hashes `k` levels up holds the node it reached there and the `k`-th sibling. -/
theorem climbPairs_getElem? :
    ∀ (s : List α) (p : Position) (a : α) (k : Nat),
      (climbPairs hash p a s)[k]?
        = s[k]?.map (ordered (p.ancestor k) (climb hash p a (s.take k)).run) := by
  intro s
  induction s with
  | nil => intro p a k; simp [climbPairs]
  | cons u rest ih =>
    intro p a k
    cases k with
    | zero => simp [climbPairs]
    | succ k =>
      -- One level up, the climb restarts from the parent.
      simp only [climbPairs, List.getElem?_cons_succ, List.take_succ_cons, ih, climb_cons,
        Position.ancestor_parent]

/-- Each pair of a collision the search returns is one its own climb hashes.

So the collision lies among the hash inputs of the two climbs. -/
theorem findCollision_mem_climbPairs [DecidableEq α] {s t : List α} {p : Position} {a b : α}
    {c : Collision α} (h : findCollision hash p a b s t = some c) :
    c.x ∈ climbPairs hash p a s ∧ c.y ∈ climbPairs hash p b t := by
  -- The search names the level of the collision and the two pairs hashed there.
  obtain ⟨-, k, u, v, hu, hv, -, hx, hy⟩ := findCollision_valid hash s t p a b c h
  have hX := climbPairs_getElem? hash s p a k
  have hY := climbPairs_getElem? hash t p b k
  rw [hu, Option.map_some, ← hx] at hX
  rw [hv, Option.map_some, ← hy] at hY
  exact ⟨List.mem_of_getElem? hX, List.mem_of_getElem? hY⟩

/-- Both nodes of every pair a climb hashes have any property its inputs have.

The inputs are the starting node, the siblings and every hash output.

For example, if every node has 32 bytes, so does every pair. -/
theorem climbPairs_children (P : α → Prop) (output : ∀ p x y, P (hash p x y).run) :
    ∀ (s : List α) (p : Position) (a : α), P a → (∀ u ∈ s, P u) →
      ∀ x ∈ climbPairs hash p a s, P x.1 ∧ P x.2 := by
  intro s
  induction s with
  | nil => intro p a _ _ x hx; simp [climbPairs] at hx
  | cons u rest ih =>
    intro p a ha hs x hx
    simp only [climbPairs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · -- The pair hashed here holds the climb's node and its sibling.
      have hu := hs u List.mem_cons_self
      unfold ordered
      split <;> exact ⟨‹_›, ‹_›⟩
    · -- The pairs further up start from a hash output.
      exact ih _ _ (output ..) (fun v hv => hs v (List.mem_cons_of_mem _ hv)) x hx

/-- Each child in a collision the search returns has any property the climbs' inputs have.

The collision is among the pairs the two climbs hash, and those pairs have the property. -/
theorem findCollision_children [DecidableEq α] (P : α → Prop)
    (output : ∀ p x y, P (hash p x y).run) {s t : List α} {p : Position} {a b : α}
    {c : Collision α} (ha : P a) (hb : P b) (hs : ∀ u ∈ s, P u) (ht : ∀ v ∈ t, P v)
    (h : findCollision hash p a b s t = some c) :
    P c.x.1 ∧ P c.x.2 ∧ P c.y.1 ∧ P c.y.2 := by
  obtain ⟨hx, hy⟩ := findCollision_mem_climbPairs hash h
  obtain ⟨x1, x2⟩ := climbPairs_children hash P output s p a ha hs c.x hx
  obtain ⟨y1, y2⟩ := climbPairs_children hash P output t p b hb ht c.y hy
  exact ⟨x1, x2, y1, y2⟩

/-! ## Against an honest tree -/

/-- A pair offered for an honest node above the leaves in place of its children. -/
structure SecondPreimage (α : Type) where
  /-- The position of the honest node. -/
  position : Position
  /-- The pair, left child first. -/
  y : α × α

/-- The node lies above the leaves, so it has children.

The pair is not those honest children, and hashes to the honest node. -/
def SecondPreimage.Valid (leaves : Nat → Id α) (w : SecondPreimage α) : Prop :=
  w.position.level ≠ 0 ∧
    w.y ≠ ((node hash leaves w.position.left).run, (node hash leaves w.position.right).run) ∧
    (hash w.position w.y.1 w.y.2).run = (node hash leaves w.position).run

/-- The second preimage a climb from a position runs into, at the lowest level where one exists.

On each level, the climb hashes its held node with its sibling, in the order the position gives.

A level where that pair is not the honest one but the parent is honest is a second preimage.

The search runs in any monad, so an oracle can answer its hash calls.

On each level it hashes the climb's pair, then computes the two honest children and their parent. -/
def findSecondPreimage {m : Type → Type} [Monad m] [DecidableEq α]
    (hash : Position → α → α → m α) (leaves : Nat → m α) :
    (p : Position) → (b : α) → (t : List α) → m (Option (SecondPreimage α))
  | p, b, v :: t => do
    let y := ordered p b v
    let parent ← hash p.parent y.1 y.2
    let left ← node hash leaves p.parent.left
    let right ← node hash leaves p.parent.right
    let honest ← node hash leaves p.parent
    if y ≠ (left, right) ∧ parent = honest then return some ⟨p.parent, y⟩
    else findSecondPreimage hash leaves p.parent parent t
  | _, _, [] => pure none

/-- In the identity monad, one level of the search compares its pair with the honest children. -/
theorem findSecondPreimage_cons [DecidableEq α] (leaves : Nat → Id α) (p : Position) (b v : α)
    (t : List α) :
    findSecondPreimage hash leaves p b (v :: t) =
      (let y := ordered p b v
       let parent := (hash p.parent y.1 y.2).run
       if y ≠ ((node hash leaves p.parent.left).run, (node hash leaves p.parent.right).run) ∧
           parent = (node hash leaves p.parent).run then
         some ⟨p.parent, y⟩
       else findSecondPreimage hash leaves p.parent parent t :
         Option (SecondPreimage α)) :=
  rfl

/-- Every second preimage the search returns is valid, for a strict ancestor of the position.

The ancestor is an ancestor of the parent, at most as many levels up as there are siblings. -/
theorem findSecondPreimage_valid [DecidableEq α] (leaves : Nat → Id α) :
    ∀ (t : List α) (p : Position) (b : α) (w : SecondPreimage α),
      findSecondPreimage hash leaves p b t = some w →
      w.Valid hash leaves ∧ w.position.IsAncestor p.parent ∧
        w.position.level ≤ p.level + t.length := by
  intro t
  induction t with
  | nil => intro p b w h; simp [findSecondPreimage] at h
  | cons v rest ih =>
    intro p b w h
    simp only [findSecondPreimage_cons] at h
    split at h
    · -- This level is the second preimage.
      rename_i hfound
      cases h
      exact ⟨⟨by simp, hfound⟩, Position.IsAncestor.refl _, by simp⟩
    · -- The second preimage is further up: one level higher in the count.
      obtain ⟨hvalid, hancestor, hlevel⟩ := ih p.parent _ w h
      refine ⟨hvalid, hancestor.trans ⟨1, by simp⟩, ?_⟩
      simp only [Position.parent_level, List.length_cons] at hlevel ⊢
      omega

/-- The honest climb from a position runs into no second preimage. -/
theorem findSecondPreimage_honest [DecidableEq α] (leaves : Nat → Id α) :
    ∀ (n : Nat) (p : Position), findSecondPreimage hash leaves p (node hash leaves p).run
      (siblings hash leaves p n).run.toList = none := by
  intro n
  induction n with
  | zero => intro p; simp [siblings, findSecondPreimage]; rfl
  | succ n ih =>
    intro p
    rw [siblings_succ_toList]
    simp only [findSecondPreimage_cons]
    -- On each level the climb hashes the honest children, so the first condition fails.
    rw [ordered_sibling (fun q => (node hash leaves q).run) p]
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    -- One level up, the climb holds the honest parent.
    rw [← node_children_run hash leaves (p := p.parent) (by simp)]
    exact ih p.parent

/-- Binding against an honest tree.

A climb over `n` siblings that reaches the honest ancestor `n` levels up is honest.

Otherwise the second-preimage search finds a second preimage. -/
theorem climb_binding_node [DecidableEq α] (leaves : Nat → Id α) :
    ∀ (n : Nat) (p : Position) (b : α) (t : List α), t.length = n →
      (climb hash p b t).run = (node hash leaves (p.ancestor n)).run →
      (b = (node hash leaves p).run ∧ t = (siblings hash leaves p n).run.toList) ∨
        (findSecondPreimage hash leaves p b t).isSome := by
  intro n
  induction n with
  | zero =>
    intro p b t hl heq
    -- No sibling: the climb is its start, which must be the honest node.
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact .inl ⟨by simpa using heq, by simp [siblings]⟩
  | succ n ih =>
    intro p b t hl heq
    cases t with
    | nil => simp at hl
    | cons v rest =>
      rw [climb_cons, ← Position.ancestor_parent] at heq
      simp only [findSecondPreimage_cons]
      -- The honest children, in order, are the honest node and its sibling.
      have honest := ordered_sibling (fun q => (node hash leaves q).run) p
      -- When this level is a second preimage, the search stops here.
      by_cases hfound : ordered p b v
            ≠ ((node hash leaves p.parent.left).run, (node hash leaves p.parent.right).run) ∧
          (hash p.parent (ordered p b v).1 (ordered p b v).2).run
            = (node hash leaves p.parent).run
      · exact .inr (by simp [hfound])
      simp only [hfound, ↓reduceIte]
      rcases ih p.parent _ rest (by simpa using hl) heq with
        ⟨hparent, hrest⟩ | hsome
      · -- An honest parent and no second preimage here: the pair is the honest one.
        have hpair : ordered p b v
            = ordered p (node hash leaves p).run (node hash leaves p.sibling).run := by
          rw [honest]
          exact Classical.byContradiction fun hne => hfound ⟨hne, hparent⟩
        obtain ⟨rfl, rfl⟩ := ordered_inj.mp hpair
        exact .inl ⟨rfl, by rw [siblings_succ_toList, hrest]⟩
      · exact .inr hsome

end EthLib.Cryptography.Merkle
