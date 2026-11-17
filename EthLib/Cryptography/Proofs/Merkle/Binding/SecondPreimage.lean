module

public import EthLib.Cryptography.Proofs.Merkle.Completeness

/-!
# Proofs: a climb against the honest tree

The honest tree is the tree built from the leaves, and its nodes are the honest nodes.

A climb that reaches an honest node is the honest climb, or it is forged.

At the first level where a forged climb agrees with the tree, it hashes another pair to a node.

That pair is a second preimage: a new input for a node fixed before the forger acts.

The search runs in any monad, so a random oracle can answer its hash calls.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

variable {α : Type} (hash : Position → α → α → Id α)

/-- A candidate second preimage: a pair offered as the children of an honest node.

It is a real second preimage only when the validity condition below holds. -/
structure SecondPreimage (α : Type) where
  /-- The position of the honest node. -/
  position : Position
  /-- The offered pair, left child first. -/
  y : α × α

/-- The pair is a new input for an honest node: a second preimage of the node hash.

- The node is above the leaves, so it has two honest children.
- The pair is not those honest children.
- At the node's position, the pair hashes to the honest node.

The honest children are the first preimage, fixed before the forger chooses the pair. -/
def SecondPreimage.Valid (leaves : Nat → Id α) (w : SecondPreimage α) : Prop :=
  w.position.level ≠ 0 ∧
    w.y ≠ ((node hash leaves w.position.left).run, (node hash leaves w.position.right).run) ∧
    (hash w.position w.y.1 w.y.2).run = (node hash leaves w.position).run

/-- Walk one climb up beside the honest tree, and stop at its first second preimage.

The climb starts at position `p`, from node `b`, with siblings `t`.

On each level:

- the climb orders its node with its next sibling and hashes the pair into the parent;
- the search computes the honest children of that parent, and the honest parent;
- if the pair is not the honest children but the parent is honest, the search returns it;
- otherwise the climb continues from its parent.

The result is `none` when the siblings run out first.

The search runs in any monad, so a random oracle can answer its hashes.

On each level it hashes the climb's pair first, then computes the honest nodes. -/
def findSecondPreimage {m : Type → Type} [Monad m] [DecidableEq α]
    (hash : Position → α → α → m α) (leaves : Nat → m α) :
    (p : Position) → (b : α) → (t : List α) → m (Option (SecondPreimage α))
  | p, b, v :: t => do
    -- The pair the climb hashes on this level, and the parent it gets.
    let y := ordered p b v
    let parent ← hash p.parent y.1 y.2
    -- The honest children of that parent, and the honest parent.
    let left ← node hash leaves p.parent.left
    let right ← node hash leaves p.parent.right
    let honest ← node hash leaves p.parent
    -- A wrong pair with an honest output: this level is the second preimage.
    if y ≠ (left, right) ∧ parent = honest then return some ⟨p.parent, y⟩
    -- Otherwise climb one level and compare again, from the climb's parent.
    else findSecondPreimage hash leaves p.parent parent t
  -- The siblings have run out, so no level is left to compare.
  | _, _, [] => pure none

/-- One level of the search, written without the monad, to rewrite with in proofs.

In the identity monad each hash call is a value, so the step is plain `let`s and an `if`.

It holds by definition. -/
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

/-- What the search returns is a real second preimage, at a node above the start of the climb.

- It is valid.
- Its node is the parent of `p` or an ancestor of that parent.
- It is at most as many levels above `p` as the climb has siblings. -/
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

/-- The honest climb never yields a second preimage.

It starts from the honest node at `p` and uses the honest siblings.

So on every level its pair is the honest children, and the first condition of the search fails. -/
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

/-- Binding against the honest tree: a climb that reaches an honest node is honest, or forged.

A forged climb exposes a second preimage.

The climb starts at position `p`, from node `b`, with `n` siblings.

It ends at the honest node `n` levels above `p`, for example the root.

- Either `b` is the honest node at `p`, and the siblings are the honest ones.
- Or the second-preimage search succeeds, and what it returns is valid by the theorem above.

So opening a leaf of a fixed tree to a wrong value finds a second preimage of the node hash. -/
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
      -- Otherwise the climb from the parent reaches the same honest node, one level shorter.
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
