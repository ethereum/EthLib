module

public import EthLib.Cryptography.Proofs.Indifferentiability
public import EthLib.Cryptography.Proofs.Sponge.Basic

/-!
# Proofs: the simulator of the sponge

It answers the permutation and its inverse with coins and a random oracle.

It simplifies Algorithm 3 of [Bertoni, Daemen, Peeters, Van Assche, Eurocrypt 2008][sponge], §4.3.

It draws each fresh answer from all states, and it never checks for saturation.

So its distance to the sponge is a collision bound, not the term of their Lemma 5.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec LazyPermutation Indifferentiability

variable {Dg E C Msg : Type}

/-- The state of the simulator.

A rooted state here is one recorded with a sponge path from the initial state. -/
structure SimState (Dg E C : Type) where
  /-- The pairs `(x, π x)` answered so far, forward or inverse, the most recent first. -/
  edges : PermCache (SpongeState Dg E C)
  /-- The rooted states with the blocks of their paths, the most recent first. -/
  chains : List (SpongeState Dg E C × List (Dg × E))

/-- The first state of the simulator: no pair yet, and the state `iv` with the empty path. -/
def SimState.init (iv : SpongeState Dg E C) : SimState Dg E C := ⟨[], [(iv, [])]⟩

/-- The state after a new pair `(x, y)`. -/
abbrev SimState.record (σ : SimState Dg E C) (x y : SpongeState Dg E C) : SimState Dg E C :=
  ⟨(x, y) :: σ.edges, σ.chains⟩

/-- The state after a new pair `(x, y)` whose answer is rooted with the path `β`. -/
abbrev SimState.recordRooted (σ : SimState Dg E C) (x y : SpongeState Dg E C)
    (β : List (Dg × E)) : SimState Dg E C :=
  ⟨(x, y) :: σ.edges, (y, β) :: σ.chains⟩

/-- The first rooted state whose capacity is that of `x`, with its path. -/
def chainOf [DecidableEq C] (chains : List (SpongeState Dg E C × List (Dg × E)))
    (x : SpongeState Dg E C) : Option (SpongeState Dg E C × List (Dg × E)) :=
  chains.find? fun p => decide (p.1.2 = x.2)

/-- The rooted state that the search finds is a rooted state. -/
theorem mem_of_chainOf_eq_some [DecidableEq C] {VC : List (SpongeState Dg E C × List (Dg × E))}
    {x s : SpongeState Dg E C} {β : List (Dg × E)} (h : chainOf VC x = some (s, β)) :
    (s, β) ∈ VC :=
  List.mem_of_find?_eq_some h

/-- The rooted state that the search finds has the capacity of the query. -/
theorem cap_eq_of_chainOf_eq_some [DecidableEq C]
    {VC : List (SpongeState Dg E C × List (Dg × E))} {x s : SpongeState Dg E C}
    {β : List (Dg × E)} (h : chainOf VC x = some (s, β)) : s.2 = x.2 := by
  simpa using List.find?_some h

/-- When the search finds no rooted state, none has the capacity of the query. -/
theorem cap_ne_of_chainOf_eq_none [DecidableEq C]
    {VC : List (SpongeState Dg E C × List (Dg × E))} {x : SpongeState Dg E C}
    (h : chainOf VC x = none) : ∀ p ∈ VC, p.1.2 ≠ x.2 := by
  intro p hp hpx
  have := List.find?_eq_none.mp h p hp
  simp [hpx] at this

variable [SampleableType Dg] [SampleableType E] [SampleableType C]

/-- The answer to a fresh query from a rooted state, where `β` is the path of the answer.

When `β` pads a message `m`, the digest part is the random oracle at `m`.

The rest of the state is uniform, and so is the whole state when `β` pads no message. -/
noncomputable def rootedAnswer (P : Padding Msg (Dg × E)) (β : List (Dg × E)) :
    OracleComp (RomSpec Msg Dg) (SpongeState Dg E C) :=
  match P.unpad β with
  | some m => do
    let d ← ((RomSpec Msg Dg).query (.inr m) : OracleComp (RomSpec Msg Dg) Dg)
    let ec ← (liftM ($ᵗ (E × C)) : OracleComp (RomSpec Msg Dg) (E × C))
    pure ((d, ec.1), ec.2)
  | none => liftM ($ᵗ (SpongeState Dg E C))

/-- A rooted answer asks the random oracle at most once. -/
theorem isQueryBoundP_rootedAnswer (P : Padding Msg (Dg × E)) (β : List (Dg × E)) :
    IsQueryBoundP (rootedAnswer (C := C) P β) (·.isRight = true) 1 := by
  unfold rootedAnswer
  split
  · exact isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
      fun _ _ => isQueryBoundP_bind (isQueryBoundP_liftM_isRight _) fun _ _ =>
        isQueryBoundP_pure _ _ 0
  · exact (isQueryBoundP_liftM_isRight _).mono (Nat.zero_le 1)

variable [XorOp Dg] [XorOp E] [DecidableEq Dg] [DecidableEq E] [DecidableEq C]

/-- **The simulator of the sponge.**

A query recorded in its direction gets the recorded answer again.

A fresh forward query at the capacity of a rooted state extends its path by one block.

Its answer is rooted with the longer path, and every other fresh answer is uniform. -/
noncomputable def simulator (P : Padding Msg (Dg × E)) :
    QueryImpl (PermSpec (SpongeState Dg E C))
      (StateT (SimState Dg E C) (OracleComp (RomSpec Msg Dg)))
  | .inl x => StateT.mk fun σ =>
    match σ.edges.lookup x with
    | some y => pure (y, σ)
    | none =>
      match chainOf σ.chains x with
      | some (s, β) => do
        let y ← rootedAnswer P (β ++ [blockTo s x])
        pure (y, σ.recordRooted x y (β ++ [blockTo s x]))
      | none => do
        let y ← (liftM ($ᵗ (SpongeState Dg E C)) : OracleComp (RomSpec Msg Dg) _)
        pure (y, σ.record x y)
  | .inr y => StateT.mk fun σ =>
    match (σ.edges.map Prod.swap).lookup y with
    | some x => pure (x, σ)
    | none => do
      let x ← (liftM ($ᵗ (SpongeState Dg E C)) : OracleComp (RomSpec Msg Dg) _)
      pure (x, σ.record x y)

/-- The simulator asks the random oracle at most once per call, from every state. -/
theorem asksOnce_simulator (P : Padding Msg (Dg × E)) :
    AsksOnce (simulator (C := C) P) := by
  -- Sampling a uniform state asks the random oracle nothing.
  have hu : IsQueryBoundP (liftM ($ᵗ (SpongeState Dg E C)) : OracleComp (RomSpec Msg Dg) _)
      (·.isRight = true) 0 := isQueryBoundP_liftM_isRight _
  intro t σ
  rcases t with x | y
  · change IsQueryBoundP (match σ.edges.lookup x with
      | some y => pure (y, σ)
      | none => _) _ 1
    split
    · exact isQueryBoundP_pure _ _ _
    · split
      · exact isQueryBoundP_bind (isQueryBoundP_rootedAnswer P _) fun _ _ =>
          isQueryBoundP_pure _ _ 0
      · exact (isQueryBoundP_bind hu fun _ _ => isQueryBoundP_pure _ _ 0).mono (Nat.zero_le 1)
  · change IsQueryBoundP (match (σ.edges.map Prod.swap).lookup y with
      | some x => pure (x, σ)
      | none => _) _ 1
    split
    · exact isQueryBoundP_pure _ _ _
    · exact (isQueryBoundP_bind hu fun _ _ => isQueryBoundP_pure _ _ 0).mono (Nat.zero_le 1)

end EthLib.Cryptography.Sponge
