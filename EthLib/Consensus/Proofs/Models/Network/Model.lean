module

public import EthLib.Consensus.Proofs.Models.Stake

/-!
# A partially synchronous network of honest and Byzantine validators

The model follows the system model of the fast confirmation rule, §2 of
[arXiv 2405.00549v4](https://arxiv.org/abs/2405.00549v4).

Each validator is a node with a view: the set of messages that it has received.

Honest validators follow a protocol, and Byzantine validators send what they like.

No validator can forge the signature of an honest one.

An execution is a sequence of events from an initial world, each allowed in the world before it.

Partial synchrony bounds the delay after a global stabilisation time, written GST.

A message in the view of an honest validator at time `t` reaches every honest validator by
`max t GST + Δ`.

That is the network model of §2 together with its assumption that honest validators gossip.

It is the second form of partial synchrony of Dwork, Lynch and Stockmeyer, Section 1 of
[doi:10.1145/42282.42283](https://doi.org/10.1145/42282.42283).

There the bound `Δ` is known but holds only from an unknown time on.

Synchrony is the case where GST is zero.

Time counts milliseconds, the unit of the clock of the fork choice.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

/-- A protocol that validators run over the network.

Each message carries signed statements, each with the validator that signed it.

An honest validator sends and moves only as the protocol allows.

Both choices may read the time, the view and the state of the validator. -/
structure Protocol (ν μ σ κ : Type*) where
  /-- The statements that a message carries, each with the validator that signed it. -/
  signed : μ → Set (ν × κ)
  /-- The messages that an honest validator may send. -/
  Sends : ν → ℕ → Set μ → σ → μ → Prop
  /-- The states that an honest validator may move to. -/
  Moves : ν → ℕ → Set μ → σ → σ → Prop

/-- The network at one moment. -/
structure World (ν μ σ : Type*) where
  /-- The time, shared by the clocks of the honest validators. -/
  time : ℕ
  /-- The messages sent so far, by any validator. -/
  sent : Set μ
  /-- The messages that each validator has received. -/
  view : ν → Set μ
  /-- The state of each validator; only the states of honest validators matter. -/
  state : ν → σ

/-- An event of the network. -/
inductive Event (ν μ σ : Type*)
  /-- The time moves on to the given time. -/
  | wait (time : ℕ)
  /-- A validator sends a message, which enters its own view. -/
  | send (sender : ν) (message : μ)
  /-- Each validator receives the given messages. -/
  | deliver (received : ν → Set μ)
  /-- A validator moves to a new state. -/
  | move (validator : ν) (state : σ)

variable {ν μ σ κ : Type*} [DecidableEq ν]

namespace World

/-- The world after an event. -/
def apply (w : World ν μ σ) : Event ν μ σ → World ν μ σ
  | .wait time => { w with time }
  | .send sender message =>
    { w with
      sent := insert message w.sent
      view := Function.update w.view sender (insert message (w.view sender)) }
  | .deliver received => { w with view := fun v => w.view v ∪ received v }
  | .move validator state => { w with state := Function.update w.state validator state }

/-- The world at a time, before any message: every view is empty. -/
def initial (time : ℕ) (state : ν → σ) : World ν μ σ :=
  ⟨time, ∅, fun _ => ∅, state⟩

end World

/-- Whether an event may happen in a world, for a protocol and a set `J` of honest validators.

Time never goes back.

A sender may carry the statement of another honest validator only if a sent message had it.

An honest sender also follows the protocol.

Only sent messages are received.

Only honest validators move, as the protocol allows. -/
def Allowed (P : Protocol ν μ σ κ) (J : Set ν) (w : World ν μ σ) : Event ν μ σ → Prop
  | .wait time => w.time ≤ time
  | .send sender message =>
    (∀ x ∈ P.signed message, x.1 ∈ J → x.1 ≠ sender → ∃ m ∈ w.sent, x ∈ P.signed m) ∧
      (sender ∈ J → P.Sends sender w.time (w.view sender) (w.state sender) message)
  | .deliver received => ∀ v, received v ⊆ w.sent
  | .move validator state =>
    validator ∈ J ∧ P.Moves validator w.time (w.view validator) (w.state validator) state

/-- The world after the first `n` events of a sequence. -/
def worldAt (init : World ν μ σ) (events : ℕ → Event ν μ σ) : ℕ → World ν μ σ
  | 0 => init
  | n + 1 => (worldAt init events n).apply (events n)

/-- An execution of a protocol, with the set `J` of honest validators.

It starts from a world, and each event is allowed in the world before it. -/
structure Execution (P : Protocol ν μ σ κ) (J : Set ν) where
  /-- The world at the start. -/
  init : World ν μ σ
  /-- The events, in order. -/
  events : ℕ → Event ν μ σ
  /-- Each event is allowed in the world before it. -/
  allowed : ∀ n, Allowed P J (worldAt init events n) (events n)

variable {P : Protocol ν μ σ κ} {J : Set ν}

namespace Execution

/-- The world after the first `n` events. -/
def world (e : Execution P J) (n : ℕ) : World ν μ σ :=
  worldAt e.init e.events n

/-- Partial synchrony with a stabilisation time `GST` and a delay `Δ`.

A message in the view of an honest validator at time `t` is in the view of every honest validator
at each time from `max t GST + Δ` on. -/
def PartiallySynchronous (e : Execution P J) (GST Δ : ℕ) : Prop :=
  ∀ n k, ∀ v ∈ J, ∀ u ∈ J, ∀ m ∈ (e.world n).view v,
    max (e.world n).time GST + Δ ≤ (e.world k).time → m ∈ (e.world k).view u

/-- Synchrony with a delay `Δ`: partial synchrony from time zero. -/
def Synchronous (e : Execution P J) (Δ : ℕ) : Prop :=
  e.PartiallySynchronous 0 Δ

variable (e : Execution P J)

theorem world_zero : e.world 0 = e.init :=
  rfl

theorem world_succ (n : ℕ) : e.world (n + 1) = (e.world n).apply (e.events n) :=
  rfl

/-- Time never goes back. -/
theorem time_mono {n k : ℕ} (le : n ≤ k) : (e.world n).time ≤ (e.world k).time := by
  induction le with
  | refl => exact le_rfl
  | @step k _ ih =>
    refine ih.trans ?_
    have allowed := e.allowed k
    rw [world_succ]
    cases events : e.events k <;> rw [events] at allowed <;> simp [World.apply, Allowed] at *
    exact allowed

/-- The sent messages only grow. -/
theorem sent_mono {n k : ℕ} (le : n ≤ k) : (e.world n).sent ⊆ (e.world k).sent := by
  induction le with
  | refl => exact le_rfl
  | @step k _ ih =>
    refine ih.trans ?_
    rw [world_succ]
    cases e.events k <;> simp [World.apply, Set.subset_insert]

/-- The view of each validator only grows. -/
theorem view_mono {n k : ℕ} (le : n ≤ k) (v : ν) : (e.world n).view v ⊆ (e.world k).view v := by
  induction le with
  | refl => exact le_rfl
  | @step k _ ih =>
    refine ih.trans ?_
    rw [world_succ]
    cases e.events k with
    | send sender message =>
      by_cases same : v = sender
      · subst same
        simp [World.apply, Set.subset_insert]
      · simp [World.apply, Function.update_of_ne same]
    | _ => simp [World.apply]

/-- A validator receives only sent messages, when that holds at the start. -/
theorem view_subset_sent (start : ∀ v, e.init.view v ⊆ e.init.sent) (n : ℕ) (v : ν) :
    (e.world n).view v ⊆ (e.world n).sent := by
  induction n generalizing v with
  | zero => exact start v
  | succ n ih =>
    have allowed := e.allowed n
    rw [world_succ]
    cases events : e.events n with
    | wait time => exact ih v
    | send sender message =>
      by_cases same : v = sender
      · subst same
        simpa [World.apply] using Set.insert_subset_insert (ih v)
      · simpa [World.apply, Function.update_of_ne same] using (ih v).trans (Set.subset_insert _ _)
    | deliver received =>
      rw [events] at allowed
      exact Set.union_subset (ih v) (allowed v)
    | move validator state => exact ih v

/-- Only honest validators change their state, and each change follows the protocol. -/
theorem state_succ (n : ℕ) (v : ν) : (e.world (n + 1)).state v = (e.world n).state v ∨
    v ∈ J ∧ P.Moves v (e.world n).time ((e.world n).view v) ((e.world n).state v)
      ((e.world (n + 1)).state v) := by
  have allowed : Allowed P J (e.world n) (e.events n) := e.allowed n
  rw [world_succ]
  cases events : e.events n with
  | move validator state =>
    rw [events] at allowed
    by_cases same : v = validator
    · subst same
      exact .inr (by simpa [World.apply, Allowed] using allowed)
    · exact .inl (by simp [World.apply, Function.update_of_ne same])
  | _ => exact .inl rfl

/-- After GST, a message that an honest validator sends reaches every honest validator.

It is in their views at each time from the time of sending plus `Δ` on, or from GST plus `Δ`. -/
theorem delivered {GST Δ : ℕ} (sync : e.PartiallySynchronous GST Δ) {n k : ℕ} {v u : ν} {m : μ}
    (sends : e.events n = .send v m) (honest : v ∈ J) (receiver : u ∈ J)
    (late : max (e.world n).time GST + Δ ≤ (e.world k).time) : m ∈ (e.world k).view u := by
  have own : m ∈ (e.world (n + 1)).view v := by
    simp [world_succ, sends, World.apply]
  have same : (e.world (n + 1)).time = (e.world n).time := by
    simp [world_succ, sends, World.apply]
  exact sync (n + 1) k v honest u receiver m own (same ▸ late)

end Execution

open scoped Classical in
/-- The Byzantine validators of `V` hold at most `β` percent of its stake.

The validators outside `J` are the Byzantine ones. -/
def ByzantineStakeAtMost (w : ν → ℕ) (V : Finset ν) (J : Set ν) (β : ℕ) : Prop :=
  100 * stake w {v ∈ V | v ∉ J} ≤ β * stake w V

omit [DecidableEq ν] in
open scoped Classical in
/-- The honest validators of `V` then hold at least `100 - β` percent of its stake. -/
theorem ByzantineStakeAtMost.honest {w : ν → ℕ} {V : Finset ν} {β : ℕ}
    (bound : ByzantineStakeAtMost w V J β) :
    (100 - β) * stake w V ≤ 100 * stake w {v ∈ V | v ∈ J} := by
  have split : stake w {v ∈ V | v ∈ J} + stake w {v ∈ V | v ∉ J} = stake w V :=
    Finset.sum_filter_add_sum_filter_not V (· ∈ J) w
  unfold ByzantineStakeAtMost at bound
  rw [Nat.sub_mul]
  omega

omit [DecidableEq ν] in
open scoped Classical in
/-- The bound holds for every `β` when every validator of `V` is honest. -/
theorem ByzantineStakeAtMost.of_subset {w : ν → ℕ} {V : Finset ν} (β : ℕ) (all : ↑V ⊆ J) :
    ByzantineStakeAtMost w V J β := by
  have : ({v ∈ V | v ∉ J} : Finset ν) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun v member => not_not.mpr (all member)
  simp [ByzantineStakeAtMost, this, stake]

omit [DecidableEq ν] in
/-- The bound fails below 100 percent when every validator is Byzantine and `V` has stake. -/
theorem not_byzantineStakeAtMost_empty {w : ν → ℕ} {V : Finset ν} {β : ℕ} (below : β < 100)
    (positive : 0 < stake w V) : ¬ByzantineStakeAtMost w V ∅ β := by
  intro bound
  simp only [ByzantineStakeAtMost, Set.mem_empty_iff_false, not_false_eq_true,
    Finset.filter_true] at bound
  have := Nat.mul_lt_mul_of_pos_right below positive
  omega

/-! ## An execution that delivers a message -/

/-- The events of the witness: a validator sends a message, all receive it, then time goes on. -/
def floodEvents (time : ℕ) (v : ν) (m : μ) : ℕ → Event ν μ σ
  | 0 => .send v m
  | 1 => .deliver fun _ => {m}
  | n + 2 => .wait (time + n + 1)

private theorem worldAt_flood {time : ℕ} {state : ν → σ} {v : ν} {m : μ} (n : ℕ) :
    worldAt (World.initial time state) (floodEvents (σ := σ) time v m) (n + 2) =
      ⟨time + n, {m}, fun _ => {m}, state⟩ := by
  induction n with
  | zero =>
    simp only [worldAt, floodEvents, World.initial, World.apply, Nat.add_zero]
    congr 1
    · simp
    · funext u
      by_cases same : u = v
      · subst same
        simp
      · simp [Function.update_of_ne same]
  | succ n ih =>
    rw [worldAt, ih]
    simp [floodEvents, World.apply]
    omega

private theorem worldAt_flood_one {time : ℕ} {state : ν → σ} {v : ν} {m : μ} :
    worldAt (World.initial time state) (floodEvents (σ := σ) time v m) 1 =
      ⟨time, {m}, Function.update (fun _ => ∅) v {m}, state⟩ := by
  simp [worldAt, floodEvents, World.initial, World.apply]

/-- A protocol has an execution where an honest message reaches every validator in time.

An honest validator `v` sends a message `m` that the protocol allows from an empty view.

The message carries no statement of another honest validator.

Every validator then has `m`, and the execution is partially synchronous for every GST and every
positive delay.

Its time also grows without bound. -/
theorem exists_partiallySynchronous {time : ℕ} {state : ν → σ} {v : ν} {m : μ} (honest : v ∈ J)
    (sends : P.Sends v time ∅ (state v) m) (own : ∀ x ∈ P.signed m, x.1 ∈ J → x.1 = v)
    {Δ : ℕ} (positive : 0 < Δ) :
    ∃ e : Execution P J, e.init = World.initial time state ∧ e.events 0 = .send v m ∧
      (∀ u, m ∈ (e.world 2).view u) ∧ (∀ GST, e.PartiallySynchronous GST Δ) ∧
      ∀ T, ∃ n, T ≤ (e.world n).time := by
  let e : Execution P J :=
    { init := World.initial time state
      events := floodEvents (σ := σ) time v m
      allowed := fun n => by
        match n with
        | 0 =>
          refine ⟨fun x signs honestSigner other => (other (own x signs honestSigner)).elim,
            fun _ => ?_⟩
          simpa [worldAt, World.initial] using sends
        | 1 =>
          intro u
          simp [worldAt_flood_one]
        | n + 2 =>
          simp only [floodEvents, Allowed, worldAt_flood]
          omega }
  have later : ∀ n, 2 ≤ n → e.world n = ⟨time + (n - 2), {m}, fun _ => {m}, state⟩ := by
    intro n le
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' le
    rw [show n + 2 - 2 = n by omega]
    exact worldAt_flood n
  -- Before the third world the time is the start time, after it the time is later.
  have early : ∀ n, n < 2 → (e.world n).time = time := by
    intro n lt
    match n, lt with
    | 0, _ => rfl
    | 1, _ => exact congrArg World.time worldAt_flood_one
  refine ⟨e, rfl, rfl, fun u => by simp [later 2 le_rfl], fun GST => ?_, fun T => ?_⟩
  · intro n k w _ u _ m' member bound
    -- The view at `n` is empty before the send, so `n` is past it.
    have past : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with zero | pos
      · subst zero
        simp [Execution.world_zero, e, World.initial] at member
      · exact pos
    have sentIt : m' = m := by
      rcases Nat.lt_or_ge n 2 with lt | le
      · have one : n = 1 := by omega
        subst one
        simp only [Execution.world, worldAt_flood_one, e] at member
        by_cases same : w = v
        · subst same
          simpa using member
        · simp [Function.update_of_ne same] at member
      · simpa [later n le] using member
    subst sentIt
    have startTime : time ≤ (e.world n).time := by
      rcases Nat.lt_or_ge n 2 with lt | le
      · exact (early n lt).ge
      · simp [later n le]
    rcases Nat.lt_or_ge k 2 with lt | le
    · rw [early k lt] at bound
      omega
    · simp [later k le]
  · refine ⟨T + 2, ?_⟩
    simp [later (T + 2) (by omega)]

end EthLib.Consensus.Models.Network
