module

public import EthLib.Base.ChainConfig
public import EthLib.Base.Proofs.Fork

/-!
# Proofs: the active fork of a chain

The active fork is the greatest fork whose activation a block has reached.

A later block, with a number and a timestamp no smaller, has an active fork no earlier.

A fork that always activates with a later fork is never active.

On mainnet, some fork is always active, never Constantinople and never a fork of the consensus
layer alone.

A chain sets no blob schedule at a block exactly when the block reaches none of their activations.

The schedule that it sets is one of its schedules, and the block has reached its activation.

Mainnet and Hoodi set none.
-/

@[expose] public section

namespace EthLib.Base

namespace Activation

/-- A block that has reached an activation stays past it as the number and the time grow. -/
theorem reached_mono {a : Activation} {n n' t t' : Nat} (hn : n ≤ n') (ht : t ≤ t')
    (h : a.reached n t) : a.reached n' t' := by
  cases a <;> simp_all [reached] <;> omega

end Activation

namespace ChainConfig

variable {config : ChainConfig} {n t : Nat} {f : Fork}

/-- The active fork of a configuration with one more fork in front. -/
private theorem activeFork_cons (id : UInt64) (g : Fork) (a : Activation)
    (l : List (Fork × Activation)) (bs : List (Activation × BlobSchedule)) :
    activeFork ⟨id, (g, a) :: l, bs⟩ n t =
      if a.reached n t then
        match activeFork ⟨id, l, bs⟩ n t with
        | some other => if g ≤ other then some other else some g
        | none => some g
      else activeFork ⟨id, l, bs⟩ n t := rfl

/-- No fork is active exactly when the block has reached no activation. -/
theorem activeFork_eq_none_iff :
    config.activeFork n t = none ↔
      ∀ g a, (g, a) ∈ config.activations → a.reached n t = false := by
  obtain ⟨id, l, bs⟩ := config
  induction l with
  | nil => simp [activeFork]
  | cons x l ih =>
    obtain ⟨g, a⟩ := x
    rw [activeFork_cons]
    by_cases hr : a.reached n t
    · simp only [hr, ite_true]
      constructor
      · intro h
        split at h <;> (try split at h) <;> simp at h
      · intro h
        simp [h g a (by simp)] at hr
    · simp only [hr, Bool.false_eq_true, ite_false, ih, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro h g' a' (⟨rfl, rfl⟩ | hm)
        · simpa using hr
        · exact h g' a' hm
      · intro h g' a' hm
        exact h g' a' (Or.inr hm)

/-- The active fork has an activation that the block has reached, and it is the greatest such. -/
theorem activeFork_eq_some_iff :
    config.activeFork n t = some f ↔
      (∃ a, (f, a) ∈ config.activations ∧ a.reached n t) ∧
      ∀ g a, (g, a) ∈ config.activations → a.reached n t → g ≤ f := by
  obtain ⟨id, l, bs⟩ := config
  induction l generalizing f with
  | nil => simp [activeFork]
  | cons x l ih =>
    obtain ⟨g, a⟩ := x
    rw [activeFork_cons]
    simp only [List.mem_cons, Prod.mk.injEq]
    by_cases hr : a.reached n t
    · simp only [hr, ite_true]
      cases hl : activeFork ⟨id, l, bs⟩ n t with
      | none =>
        have hnone := activeFork_eq_none_iff.mp hl
        constructor
        · intro h
          cases h
          refine ⟨⟨a, Or.inl ⟨rfl, rfl⟩, hr⟩, ?_⟩
          rintro g' a' (⟨rfl, rfl⟩ | hm) hr'
          · exact Nat.le_refl _
          · simp [hnone g' a' hm] at hr'
        · rintro ⟨⟨a', (⟨rfl, rfl⟩ | hm), hr'⟩, -⟩
          · rfl
          · simp [hnone _ a' hm] at hr'
      | some o =>
        obtain ⟨⟨b, hb, hbr⟩, hmax⟩ := ih.mp hl
        by_cases hgo : g ≤ o
        · simp only [hgo, ite_true, Option.some.injEq]
          constructor
          · rintro rfl
            refine ⟨⟨b, Or.inr hb, hbr⟩, ?_⟩
            rintro g' a' (⟨rfl, rfl⟩ | hm) hr'
            · exact hgo
            · exact hmax g' a' hm hr'
          · rintro ⟨⟨a', ha', hr'⟩, hm⟩
            have h1 : o ≤ f := hm o b (Or.inr hb) hbr
            have h2 : f ≤ o := by
              rcases ha' with ⟨rfl, rfl⟩ | ha'
              · exact hgo
              · exact hmax f a' ha' hr'
            exact Fork.ctorIdx_injective (Nat.le_antisymm h1 h2)
        · have hog : o ≤ g := Nat.le_of_lt (Nat.lt_of_not_le hgo)
          simp only [hgo, ite_false, Option.some.injEq]
          constructor
          · rintro rfl
            refine ⟨⟨a, Or.inl ⟨rfl, rfl⟩, hr⟩, ?_⟩
            rintro g' a' (⟨rfl, rfl⟩ | hm) hr'
            · exact Nat.le_refl _
            · exact Nat.le_trans (hmax g' a' hm hr') hog
          · rintro ⟨⟨a', ha', hr'⟩, hm⟩
            have h1 : g ≤ f := hm g a (Or.inl ⟨rfl, rfl⟩) hr
            have h2 : f ≤ g := by
              rcases ha' with ⟨rfl, rfl⟩ | ha'
              · exact Nat.le_refl _
              · exact Nat.le_trans (hmax f a' ha' hr') hog
            exact Fork.ctorIdx_injective (Nat.le_antisymm h1 h2)
    · simp only [hr, Bool.false_eq_true, ite_false, ih]
      constructor
      · rintro ⟨⟨b, hb, hbr⟩, hm⟩
        refine ⟨⟨b, Or.inr hb, hbr⟩, ?_⟩
        rintro g' a' (⟨rfl, rfl⟩ | h) hr'
        · exact absurd hr' hr
        · exact hm g' a' h hr'
      · rintro ⟨⟨b, (⟨rfl, rfl⟩ | hb), hbr⟩, hm⟩
        · exact absurd hbr hr
        · exact ⟨⟨b, hb, hbr⟩, fun g' a' h hr' => hm g' a' (Or.inr h) hr'⟩

/-- A block no earlier in number and in time has an active fork no earlier. -/
theorem activeFork_mono {n' t' : Nat} (h : config.activeFork n t = some f) (hn : n ≤ n')
    (ht : t ≤ t') : ∃ f', config.activeFork n' t' = some f' ∧ f ≤ f' := by
  obtain ⟨⟨a, ha, hr⟩, -⟩ := activeFork_eq_some_iff.mp h
  have hr' := Activation.reached_mono hn ht hr
  cases h' : config.activeFork n' t' with
  | none => simp [activeFork_eq_none_iff.mp h' f a ha] at hr'
  | some f' => exact ⟨f', rfl, (activeFork_eq_some_iff.mp h').2 f a ha hr'⟩

/-- A fork that activates only where a later fork activates too is never active. -/
theorem activeFork_ne_of_shadowed {g : Fork} (hlt : f < g)
    (hf : ∀ a, (f, a) ∈ config.activations → (g, a) ∈ config.activations) :
    config.activeFork n t ≠ some f := by
  intro h
  obtain ⟨⟨a, ha, hr⟩, hmax⟩ := activeFork_eq_some_iff.mp h
  exact Nat.not_le_of_lt hlt (hmax g a (hf a ha) hr)

/-! ## Blob schedules -/

/-- A chain sets no blob schedule at a block exactly when the block reaches none of them. -/
theorem blobScheduleAt_eq_none_iff :
    config.blobScheduleAt n t = none ↔
      ∀ a s, (a, s) ∈ config.blobSchedules → a.reached n t = false := by
  simp [blobScheduleAt, List.find?_eq_none]

/-- The blob schedule that a chain sets at a block is one of its schedules.

The block has reached the activation of that schedule. -/
theorem mem_of_blobScheduleAt_eq_some {s : BlobSchedule}
    (h : config.blobScheduleAt n t = some s) :
    ∃ a, (a, s) ∈ config.blobSchedules ∧ a.reached n t = true := by
  simp only [blobScheduleAt, Option.map_eq_some_iff] at h
  obtain ⟨⟨a, s'⟩, hf, rfl⟩ := h
  have hr := List.find?_some hf
  exact ⟨a, List.mem_reverse.mp (List.mem_of_find?_eq_some hf), hr⟩

/-- A schedule at the end of the list that the block has reached holds, whatever comes before.
-/
theorem blobScheduleAt_append_of_reached {a : Activation} {s : BlobSchedule}
    (id : UInt64) (fs : List (Fork × Activation)) (l : List (Activation × BlobSchedule))
    (hr : a.reached n t = true) :
    blobScheduleAt ⟨id, fs, l ++ [(a, s)]⟩ n t = some s := by
  simp [blobScheduleAt, hr]

/-- The forks are ordered exactly when no fork by block is later than a fork by timestamp. -/
theorem activationsOrdered_eq_true_iff {activations : List (Fork × Activation)} :
    activationsOrdered activations = true ↔
      ∀ f t g n, (f, Activation.time t) ∈ activations → (g, Activation.block n) ∈ activations →
        ¬ f < g := by
  simp only [activationsOrdered, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Prod.forall]
  constructor
  · intro h f t g n hf hg
    rcases h g _ hg with h1 | h1
    · simp at h1
    · rcases h1 f _ hf with h2 | h2 <;> simp_all
  · intro h g b hg
    cases b with
    | block n =>
      right
      intro f a hf
      cases a with
      | block _ => left; simp
      | time t => right; exact h f t g n hf hg
    | time _ => left; simp

/-! ## Mainnet -/

/-- Mainnet lists its forks in the order of the timeline, with activations in order. -/
theorem mainnet_ordered : mainnet.Ordered := by
  decide

/-- Some fork is active at every block of mainnet, since Frontier holds from block 0. -/
theorem mainnet_activeFork_isSome (n t : Nat) : ∃ f, mainnet.activeFork n t = some f := by
  cases h : mainnet.activeFork n t with
  | none =>
    have := activeFork_eq_none_iff.mp h .frontier (.block 0) (by decide)
    simp [Activation.reached] at this
  | some f => exact ⟨f, rfl⟩

/-- Constantinople is never active on mainnet, since Petersburg activates at the same block. -/
theorem mainnet_activeFork_ne_constantinople (n t : Nat) :
    mainnet.activeFork n t ≠ some .constantinople := by
  refine activeFork_ne_of_shadowed (g := .petersburg) (by decide) fun a ha => ?_
  simp [mainnet] at ha
  subst ha
  decide

/-- The active fork of mainnet is never a fork of the consensus layer alone. -/
theorem mainnet_activeFork_ne_consensus (h : mainnet.activeFork n t = some f) :
    f ≠ .phase0 ∧ f ≠ .altair ∧ f ≠ .bellatrix := by
  obtain ⟨⟨a, ha, -⟩, -⟩ := activeFork_eq_some_iff.mp h
  have hf : f ∈ mainnet.activations.map Prod.fst := List.mem_map.mpr ⟨_, ha, rfl⟩
  revert hf
  cases f <;> decide

/-- Mainnet sets no blob schedule of its own, so each fork keeps the schedule of its EIPs. -/
theorem mainnet_blobScheduleAt (n t : Nat) : mainnet.blobScheduleAt n t = none := rfl

/-! ## Hoodi -/

/-- Hoodi lists its forks in the order of the timeline, with activations in order. -/
theorem hoodi_ordered : hoodi.Ordered := by
  decide

/-- Some fork is active at every block of Hoodi, since Frontier holds from block 0. -/
theorem hoodi_activeFork_isSome (n t : Nat) : ∃ f, hoodi.activeFork n t = some f := by
  cases h : hoodi.activeFork n t with
  | none =>
    have := activeFork_eq_none_iff.mp h .frontier (.block 0) (by decide)
    simp [Activation.reached] at this
  | some f => exact ⟨f, rfl⟩

/-- Every block of Hoodi has at least the rules of Dencun. -/
theorem hoodi_dencun_le (h : hoodi.activeFork n t = some f) : .dencun ≤ f := by
  have hDencun : (Fork.dencun, Activation.time 0) ∈ hoodi.activations := by decide
  obtain ⟨-, hmax⟩ := activeFork_eq_some_iff.mp h
  exact hmax .dencun (.time 0) hDencun (by simp [Activation.reached])

/-- Hoodi sets no blob schedule of its own, so each fork keeps the schedule of its EIPs. -/
theorem hoodi_blobScheduleAt (n t : Nat) : hoodi.blobScheduleAt n t = none := rfl

end ChainConfig

end EthLib.Base
