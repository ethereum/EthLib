module

public import EthLib.Cryptography.Proofs.Merkle.RandomOracle.Basic
public import EthLib.Cryptography.Proofs.Merkle.Multiproof.Trace

/-!
# Proofs: Merkle multiproofs in the random-oracle model

A rebuild from `n` given nodes hashes at most `n - 1` times, so it makes at most `n - 1` calls.

A rebuild that a partial table replays to the end hashed only inputs that the table answers.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle.RandomOracle

open OracleSpec OracleComp

variable {α : Type}

/-- A rebuild from `n` given nodes makes at most `n - 1` calls, when each node hash makes one.

The hashed nodes form full binary trees whose leaves are the given nodes. -/
theorem isQueryBoundP_rebuild_go {ι : Type} {spec : OracleSpec ι} {p : ι → Prop}
    [DecidablePred p] {hash : Position → α → α → OracleComp spec α}
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ (l j : Nat) (nodes : List (Position × α)),
      IsQueryBoundP (rebuild.go hash nodes l j) p (nodes.length - 1) := by
  intro l
  induction l with
  | zero => intro j nodes; exact isQueryBoundP_pure _ _ _
  | succ l ih =>
    intro j nodes
    rw [rebuild_go_succ]
    cases nodes.lookup ⟨l + 1, j⟩ with
    | some node => exact isQueryBoundP_pure _ _ _
    | none =>
      dsimp only
      split
      · exact isQueryBoundP_pure _ _ _
      -- The nodes split between the two children.
      have split := List.length_eq_length_filter_add (l := nodes)
        fun e => (⟨l, 2 * j⟩ : Position).covers e.1
      generalize nodes.filter (fun e => (⟨l, 2 * j⟩ : Position).covers e.1) = left at split ⊢
      generalize nodes.filter (fun e => !(⟨l, 2 * j⟩ : Position).covers e.1) = right at split ⊢
      -- A child with no node given is missing, and no hash follows.
      cases left with
      | nil =>
        rw [rebuild_go_nil_pure, pure_bind]
        exact isQueryBoundP_pure _ _ _
      | cons first rest =>
        refine (isQueryBoundP_bind (m := right.length) (ih _ _) fun leftNode _ => ?_).mono
          (by simp only [List.length_cons] at split ⊢; omega)
        cases leftNode with
        | none => exact isQueryBoundP_pure _ _ _
        | some a =>
          dsimp only
          cases right with
          | nil =>
            rw [rebuild_go_nil_pure, pure_bind]
            exact isQueryBoundP_pure _ _ _
          | cons second others =>
            refine (isQueryBoundP_bind (m := 1) (ih _ _) fun rightNode _ => ?_).mono
              (by simp)
            cases rightNode with
            | none => exact isQueryBoundP_pure _ _ _
            | some b => exact (isQueryBoundP_map_iff _ _ _).mpr (hhash _ _ _)

/-- A rebuild that a partial table replays to the end is the rebuild with a full table.

It also meets `Q` on every message that the recording rebuild with the full table appends.

Each replayed node hash meets `Q` on its message and returns the node of the full table. -/
theorem rebuild_go_of_replay {β ι : Type} {spec : OracleSpec ι} {impl : QueryImpl spec Option}
    {hash : Position → α → α → OracleComp spec α} {table : Position → α → α → Id α}
    {message : Position → α → α → β} {Q : β → Prop}
    (hstep : ∀ p a b v, simulateQ impl (hash p a b) = some v →
      Q (message p a b) ∧ v = (table p a b).run) :
    ∀ (l j : Nat) (nodes : List (Position × α)) (s : List β) {result : Option α},
      simulateQ impl (rebuild.go hash nodes l j) = some result →
        result = (rebuild.go table nodes l j).run ∧
          ∀ x ∈ (((rebuild.go (recordingHash table message) nodes l j).run s).run).2,
            x ∈ s ∨ Q x := by
  intro l
  induction l with
  | zero =>
    intro j nodes s result hrun
    simp only [rebuild.go, simulateQ_pure, Option.pure_def, Option.some.injEq] at hrun
    subst hrun
    exact ⟨rfl, fun x hx => .inl (by simpa [rebuild.go] using hx)⟩
  | succ l ih =>
    intro j nodes s result hrun
    rw [rebuild_go_succ] at hrun
    rw [rebuild_go_succ_run, rebuild_go_succ]
    cases found : nodes.lookup ⟨l + 1, j⟩ with
    | some node =>
      -- A node given is taken as it is, and nothing is recorded.
      simp only [found, simulateQ_pure, Option.pure_def, Option.some.injEq] at hrun
      subst hrun
      exact ⟨rfl, fun x hx => .inl hx⟩
    | none =>
      simp only [found] at hrun ⊢
      by_cases empty : nodes.isEmpty = true
      · simp only [empty, ↓reduceIte, simulateQ_pure, Option.pure_def, Option.some.injEq] at hrun
        subst hrun
        exact ⟨by simp [empty], fun x hx => .inl (by simpa [empty] using hx)⟩
      simp only [empty, Bool.false_eq_true, ↓reduceIte, simulateQ_bind] at hrun ⊢
      generalize nodes.filter (fun e => (⟨l, 2 * j⟩ : Position).covers e.1) = left at hrun ⊢
      generalize nodes.filter (fun e => !(⟨l, 2 * j⟩ : Position).covers e.1) = right at hrun ⊢
      -- The left child replays as the rebuild with the table, and records what it hashes.
      obtain ⟨leftNode, hleft, hrun⟩ := Option.bind_eq_some_iff.mp hrun
      obtain ⟨leftEq, leftRecorded⟩ := ih (2 * j) left s hleft
      obtain ⟨t1, leftRun⟩ := rebuild_go_recording table message l (2 * j) left s
      rw [leftRun] at leftRecorded
      subst leftEq
      cases leftTable : (rebuild.go table left l (2 * j)).run with
      | none =>
        simp only [leftTable, simulateQ_pure, Option.pure_def, Option.some.injEq] at hrun
        subst hrun
        refine ⟨rfl, ?_⟩
        simpa [StateT.run_bind, leftRun, leftTable] using leftRecorded
      | some a =>
        simp only [leftTable, simulateQ_bind] at hrun
        -- The right child does the same, after the record of the left one.
        obtain ⟨rightNode, hright, hrun⟩ := Option.bind_eq_some_iff.mp hrun
        obtain ⟨rightEq, rightRecorded⟩ := ih (2 * j + 1) right (s ++ t1) hright
        obtain ⟨t2, rightRun⟩ := rebuild_go_recording table message l (2 * j + 1) right (s ++ t1)
        rw [rightRun] at rightRecorded
        subst rightEq
        -- Each message of a child is new to that child, or was there before it.
        have before : ∀ x ∈ s ++ t1 ++ t2, x ∈ s ∨ Q x := by
          intro x hx
          rcases rightRecorded x hx with old | new
          · exact leftRecorded x old
          · exact .inr new
        cases rightTable : (rebuild.go table right l (2 * j + 1)).run with
        | none =>
          simp only [rightTable, simulateQ_pure, Option.pure_def, Option.some.injEq] at hrun
          subst hrun
          refine ⟨rfl, ?_⟩
          simpa [StateT.run_bind, leftRun, leftTable, rightRun, rightTable] using before
        | some b =>
          -- The node hash replays as the table's, and its message meets `Q`.
          simp only [rightTable, simulateQ_map] at hrun
          obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hrun
          obtain ⟨hmessage, rfl⟩ := hstep _ _ _ _ hv
          refine ⟨rfl, fun x hx => ?_⟩
          -- The record is the children's records, then the message of this node.
          simp [leftRun, leftTable, rightRun, rightTable, StateT.run_bind, StateT.run_map,
            StateT.run_modify, recordingHash] at hx
          rcases hx with hx | hx | hx | rfl
          · exact .inl hx
          · exact before x (by simp [hx])
          · exact before x (by simp [hx])
          · exact .inr hmessage

end EthLib.Cryptography.Merkle.RandomOracle
