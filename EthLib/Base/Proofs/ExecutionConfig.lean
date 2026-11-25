module

public import EthLib.Base.ExecutionConfig
public import EthLib.Base.Proofs.ChainConfig
public import EthLib.Base.Proofs.Json

/-!
# Proofs: the fork times and blob schedules of a configuration file

Reading what the writer wrote gives the configuration back, when a file can hold it whole.

A file holds mainnet, Hoodi and Sepolia whole.

After a file is read, the blob schedule at a block is the latest entry that the block reached.

The forks of a configuration that the reader gives are in the order of the timeline.

Two errors of the reader with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Base.ExecutionConfig

open Lean (Json)

/-- A list of steps that each succeed succeeds, with the list of their results. -/
private theorem mapM_eq_ok {α β ε : Type} {g : α → Except ε β} {h : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, g a = .ok (h a)) → l.mapM g = .ok (l.map h)
  | [], _ => rfl
  | a :: l, hg => by
    rw [List.mapM_cons, hg a (by simp), mapM_eq_ok fun b hb => hg b (by simp [hb])]
    rfl

/-- The results of steps that keep the first part of each input keep the first parts. -/
private theorem map_fst_of_mapM_eq_ok {α β γ ε : Type} {g : α → Except ε (β × γ)} {k : α → β}
    (hg : ∀ a r, g a = .ok r → r.1 = k a) :
    ∀ {l : List α} {r : List (β × γ)}, l.mapM g = .ok r → r.map Prod.fst = l.map k
  | [], r, h => by
    cases h
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : g a with
    | error e => simp [ha, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM g with
      | error e => simp [ha, hl, bind, Except.bind] at h
      | ok bs =>
        simp [ha, hl, bind, Except.bind, pure, Except.pure] at h
        subst h
        simp [hg a b ha, map_fst_of_mapM_eq_ok hg hl]

/-- A list where no element failing a test precedes one passing it splits by the test. -/
private theorem eq_filter_append {α : Type} {R : α → α → Prop} {p : α → Bool}
    (hR : ∀ x y, p x = false → p y = true → ¬R x y) :
    ∀ {l : List α}, l.Pairwise R → l = l.filter p ++ l.filter (fun x => !p x)
  | [], _ => rfl
  | x :: l, hl => by
    rw [List.pairwise_cons] at hl
    have ih := eq_filter_append hR hl.2
    cases hx : p x
    · have : l.filter p = [] := List.filter_eq_nil_iff.2 fun y hy hpy =>
        hR x y hx (by simpa using hpy) (hl.1 y hy)
      rw [this] at ih
      simp [hx, this]
      exact ih
    · simp [hx]
      exact ih

/-- Appending the elements of a list that pass a test none of them passes appends nothing. -/
private theorem append_filter_of_forall_false {α : Type} {front l : List α} {p : α → Bool}
    (h : ∀ x ∈ l, p x = false) : front ++ l.filter p = front := by
  rw [List.filter_eq_nil_iff.2 fun x hx => by simp [h x hx], List.append_nil]

/-- Two maps that agree on a list keep the same elements of it. -/
private theorem filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp),
      filterMap_congr fun b hb => h b (by simp [hb])]

/-- Looking up each key of a sorted list of keys, in order, lists the elements back. -/
private theorem filterMap_find? {α : Type} {key : α → Fork} :
    ∀ {names : List (Fork × String)} {l : List α}, names.Pairwise (fun a b => a.1 < b.1) →
      l.Pairwise (fun x y => key x < key y) → (∀ x ∈ l, key x ∈ names.map Prod.fst) →
      names.filterMap (fun p => l.find? fun x => key x = p.1) = l
  | [], [], _, _, _ => rfl
  | [], x :: l, _, _, hm => absurd (hm x (by simp)) (by simp)
  | p :: names, l, hn, hl, hm => by
    rw [List.pairwise_cons] at hn
    cases l with
    | nil => simp
    | cons x l =>
      rw [List.pairwise_cons] at hl
      by_cases hx : key x = p.1
      · -- The first key is looked up first, and the later keys skip its element.
        have rest : names.filterMap (fun q => (x :: l).find? fun y => key y = q.1) =
            names.filterMap (fun q => l.find? fun y => key y = q.1) := by
          refine filterMap_congr fun q hq => ?_
          have : key x ≠ q.1 := fun e => Nat.lt_irrefl _ (e ▸ hx ▸ hn.1 q hq)
          simp [this]
        rw [List.filterMap_cons, List.find?_cons, rest]
        simp only [hx, decide_true]
        congr 1
        refine filterMap_find? hn.2 hl.2 fun y hy => ?_
        have hxy := hl.1 y hy
        rcases List.mem_cons.1 (hm y (by simp [hy])) with e | e
        · exact absurd (hx ▸ e ▸ hxy) (Nat.lt_irrefl _)
        · exact e
      · -- The first key has no element, and every element has a later key.
        have hp : ∀ y ∈ x :: l, key y ≠ p.1 := by
          intro y hy e
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hx e
          · rcases List.mem_cons.1 (hm x (by simp)) with e' | e'
            · exact hx e'
            · obtain ⟨q, hq, hq'⟩ := List.mem_map.1 e'
              exact Nat.lt_irrefl _ (e ▸ Nat.lt_trans (hn.1 q hq) (hq' ▸ hl.1 y hy))
        rw [List.filterMap_cons, List.find?_eq_none.2 (by simpa using hp)]
        refine filterMap_find? hn.2 (List.pairwise_cons.2 hl) fun y hy => ?_
        rcases List.mem_cons.1 (hm y hy) with e | e
        · exact absurd e (hp y hy)
        · exact e

/-- Reading a sorted list from its end finds the element of greatest key that passes a test. -/
private theorem find?_reverse_eq_some {α : Type} {key : α → Fork} {p : α → Bool} {x : α} :
    ∀ {l : List α}, l.Pairwise (fun x y => key x < key y) →
      (l.reverse.find? p = some x ↔ x ∈ l ∧ p x ∧ ∀ y ∈ l, p y → key y ≤ key x)
  | [], _ => by simp
  | a :: l, hl => by
    rw [List.pairwise_cons] at hl
    rw [List.reverse_cons, List.find?_append]
    cases hf : l.reverse.find? p with
    | some x' =>
      -- An element of the tail passes, and it has a later key than the head.
      obtain ⟨hx'm, hx'p, hx'max⟩ := (find?_reverse_eq_some (x := x') hl.2).1 hf
      simp only [Option.some_or, Option.some.injEq]
      constructor
      · rintro rfl
        refine ⟨List.mem_cons_of_mem _ hx'm, hx'p, fun y hy hpy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.le_of_lt (hl.1 x' hx'm)
        · exact hx'max y hy hpy
      · rintro ⟨hxm, hxp, hxmax⟩
        rcases List.mem_cons.1 hxm with rfl | hxm
        · exact absurd (hxmax x' (by simp [hx'm]) hx'p) (Nat.not_le.2 (hl.1 x' hx'm))
        · have := (find?_reverse_eq_some (x := x) hl.2).2
            ⟨hxm, hxp, fun y hy => hxmax y (List.mem_cons_of_mem _ hy)⟩
          rw [hf] at this
          exact Option.some.inj this
    | none =>
      -- No element of the tail passes, so only the head can.
      have hnone : ∀ y ∈ l, p y = false := by simpa using List.find?_eq_none.1 hf
      simp only [Option.none_or, List.find?_cons, List.find?_nil]
      constructor
      · intro h
        cases hpa : p a <;> simp only [hpa, reduceCtorEq, Option.some.injEq] at h
        subst h
        refine ⟨List.mem_cons_self, hpa, fun y hy hpy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.le_refl _
        · simp [hnone y hy] at hpy
      · rintro ⟨hxm, hxp, -⟩
        rcases List.mem_cons.1 hxm with rfl | hxm
        · simp [hxp]
        · simp [hnone x hxm] at hxp

/-- A fork activated by time has that time, when no fork appears twice. -/
private theorem timeOf_eq_some {config : ChainConfig} {f : Fork} {t : Nat}
    (sorted : config.activations.Pairwise fun x y => x.1 < y.1)
    (mem : (f, Activation.time t) ∈ config.activations) : timeOf config f = some t := by
  unfold timeOf
  generalize config.activations = l at sorted mem ⊢
  induction l with
  | nil => simp at mem
  | cons x l ih =>
    rw [List.pairwise_cons] at sorted
    rw [List.findSome?_cons]
    rcases List.mem_cons.1 mem with rfl | mem
    · simp
    · have hne : x.1 ≠ f := fun e => Nat.lt_irrefl _ (e ▸ sorted.1 _ mem)
      obtain ⟨g, a⟩ := x
      cases a <;> simp_all

/-- The time of a fork comes from its activation by time. -/
private theorem mem_of_timeOf_eq_some {config : ChainConfig} {f : Fork} {t : Nat}
    (h : timeOf config f = some t) : (f, Activation.time t) ∈ config.activations := by
  obtain ⟨⟨g, a⟩, hm, ha⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | block => simp at ha
  | time u =>
    by_cases e : g = f <;> simp [e] at ha
    subst e ha
    exact hm

/-- The time of a fork, as an activation, is the activation by time listed with it. -/
private theorem timeOf_map {config : ChainConfig} {f : Fork} :
    (timeOf config f).map (fun t => (f, Activation.time t)) =
      (config.activations.filter fun x => !(x.2 matches .block _)).find? fun x => x.1 = f := by
  unfold timeOf
  induction config.activations with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨g, a⟩ := x
    cases a with
    | block n => simpa using ih
    | time u =>
      by_cases e : g = f
      · subst e
        simp
      · simpa [e] using ih

/-- The schedule of a fork is the one listed with it, when each schedule has a fork. -/
private theorem scheduleOf_eq {config : ChainConfig} {f : Fork}
    (forks : ∀ x ∈ config.blobSchedules, x.1.isSome) :
    scheduleOf config f =
      (config.blobSchedules.find? fun x => x.1.getD .frontier = f).map (·.2.2) := by
  unfold scheduleOf
  generalize config.blobSchedules = l at forks ⊢
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨g, a, s⟩ := x
    obtain ⟨g, rfl⟩ := Option.isSome_iff_exists.1 (forks (g, a, s) List.mem_cons_self)
    by_cases e : g = f
    · subst e
      simp
    · simpa [e] using ih fun y hy => forks y (by simp [hy])

/-- The forks with a name in a file come in the order of the timeline. -/
private theorem forkNames_sorted : forkNames.Pairwise fun a b => a.1 < b.1 := by
  decide

/-- No two forks share a name, nor the key of their time. -/
private theorem forkNames_distinct :
    forkNames.Pairwise fun a b => a.2 ≠ b.2 ∧ a.2 ++ "Time" ≠ b.2 ++ "Time" := by
  decide

/-- No key of a time is the key of the blob schedules. -/
private theorem forkNames_time_ne : ∀ p ∈ forkNames, p.2 ++ "Time" ≠ "blobSchedule" := by
  decide

/-- Decoding a natural number from JSON reads it as one. -/
private theorem fromJson?_nat (j : Json) : (Lean.fromJson? j : Except String Nat) = j.getNat? :=
  rfl

/-- A name written into an object is read back with its default, when no name repeats. -/
private theorem getObjValD_mkObj {pairs : List (String × Json)} {name : String} {value : Json}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (member : (name, value) ∈ pairs) :
    (Json.mkObj pairs).getObjValD name = value := by
  rw [Toolchain.Json.getObjValD_eq, EthLib.Base.Json.getObjVal?_mkObj distinct member]
  rfl

/-- A natural number written as JSON is read back. -/
private theorem getNat?_toJson (n : Nat) : (Lean.toJson n).getNat? = .ok n := by
  rw [Toolchain.Json.getNat?_eq]
  rfl

/-- The entry written for a blob schedule is read back as that schedule. -/
private theorem readSchedule_scheduleJson (fork : Fork) (s : BlobSchedule) :
    readSchedule fork (scheduleJson s) = .ok s := by
  have d : [("target", Lean.toJson s.target.toNat), ("max", Lean.toJson s.max.toNat),
      ("baseFeeUpdateFraction", Lean.toJson s.baseFeeUpdateFraction)].Pairwise
        fun a b => a.1 ≠ b.1 := by
    simp
  unfold readSchedule scheduleJson
  simp only [Toolchain.Json.getObjValAs?_eq, fromJson?_nat]
  rw [getObjValD_mkObj (value := Lean.toJson s.target.toNat) d (by simp),
    getObjValD_mkObj (value := Lean.toJson s.max.toNat) d (by simp),
    getObjValD_mkObj (value := Lean.toJson s.baseFeeUpdateFraction) d (by simp),
    getNat?_toJson, getNat?_toJson, getNat?_toJson]
  simp only [BlobSchedule.ofNat?_toNat]
  rfl

/-- Two forks with one name are one fork. -/
private theorem forkNames_name_inj :
    ∀ p ∈ forkNames, ∀ q ∈ forkNames, p.2 = q.2 → p = q := by
  decide

/-- Two forks with one key of their time are one fork. -/
private theorem forkNames_time_inj :
    ∀ p ∈ forkNames, ∀ q ∈ forkNames, p.2 ++ "Time" = q.2 ++ "Time" → p = q := by
  decide

/-- The entries that the writer gives the blob schedules have distinct names. -/
private theorem schedulePairs_distinct (config : ChainConfig) :
    (forkNames.filterMap fun (fork, name) =>
      (scheduleOf config fork).map fun s => (name, scheduleJson s)).Pairwise
        fun a b => a.1 ≠ b.1 := by
  refine forkNames_distinct.filterMap _ fun ⟨f, n⟩ ⟨f', n'⟩ h b hb b' hb' => ?_
  simp only [Option.map_eq_some_iff] at hb hb'
  obtain ⟨_, -, rfl⟩ := hb
  obtain ⟨_, -, rfl⟩ := hb'
  exact h.1

/-- The keys that the writer gives the fork times are distinct. -/
private theorem timePairs_distinct (config : ChainConfig) :
    (forkNames.filterMap fun (fork, name) =>
      (timeOf config fork).map fun t => (name ++ "Time", Lean.toJson t)).Pairwise
        fun a b => a.1 ≠ b.1 := by
  refine forkNames_distinct.filterMap _ fun ⟨f, n⟩ ⟨f', n'⟩ h b hb b' hb' => ?_
  simp only [Option.map_eq_some_iff] at hb hb'
  obtain ⟨_, -, rfl⟩ := hb
  obtain ⟨_, -, rfl⟩ := hb'
  exact h.2

/-- The members of the written file have distinct names. -/
private theorem writePairs_distinct (config : ChainConfig) :
    (("blobSchedule", Json.mkObj (forkNames.filterMap fun (fork, name) =>
      (scheduleOf config fork).map fun s => (name, scheduleJson s))) ::
    forkNames.filterMap fun (fork, name) =>
      (timeOf config fork).map fun t => (name ++ "Time", Lean.toJson t)).Pairwise
        fun a b => a.1 ≠ b.1 := by
  refine List.pairwise_cons.2 ⟨fun x hx => ?_, timePairs_distinct config⟩
  obtain ⟨⟨f, n⟩, hm, hx⟩ := List.mem_filterMap.1 hx
  simp only [Option.map_eq_some_iff] at hx
  obtain ⟨_, -, rfl⟩ := hx
  exact (forkNames_time_ne _ hm).symm

/-- The time that the written file gives a fork is the time of the configuration. -/
private theorem readTime_write {config : ChainConfig} (h : Writable config) {fork : Fork}
    {name : String} (hm : (fork, name) ∈ forkNames) :
    readTime (writeExecutionConfig config) fork name = .ok (timeOf config fork) := by
  unfold readTime writeExecutionConfig
  cases ht : timeOf config fork with
  | some t =>
    rw [EthLib.Base.Json.getObjVal?_mkObj (value := Lean.toJson t) (writePairs_distinct config)
      (List.mem_cons_of_mem _ (List.mem_filterMap.2 ⟨_, hm, by simp [ht]⟩))]
    simp only [getNat?_toJson, (h.2.1 _ _ (mem_of_timeOf_eq_some ht)).2, ite_true]
    rfl
  | none =>
    -- No other fork has the key of this one, and this one has no time.
    have absent : name ++ "Time" ∉ (("blobSchedule", Json.mkObj (forkNames.filterMap
        fun (fork, name) => (scheduleOf config fork).map fun s => (name, scheduleJson s))) ::
        forkNames.filterMap fun (fork, name) =>
          (timeOf config fork).map fun t => (name ++ "Time", Lean.toJson t)).map Prod.fst := by
      simp only [List.map_cons, List.mem_cons, List.mem_map, List.mem_filterMap,
        Option.map_eq_some_iff, not_or]
      refine ⟨forkNames_time_ne _ hm, ?_⟩
      rintro ⟨_, ⟨⟨f, n⟩, hm', _, ht', rfl⟩, he⟩
      cases forkNames_time_inj _ hm' _ hm he
      simp [ht] at ht'
    rw [EthLib.Base.Json.getObjVal?_mkObj_of_not_mem absent]
    rfl

/-- The entry that the written file gives a fork is the schedule of the configuration. -/
private theorem getEntry_write {config : ChainConfig} {fork : Fork} {name : String}
    (hm : (fork, name) ∈ forkNames) :
    (Json.mkObj (forkNames.filterMap fun (fork, name) =>
        (scheduleOf config fork).map fun s => (name, scheduleJson s))).getObjVal? name =
      match scheduleOf config fork with
      | some s => .ok (scheduleJson s)
      | none => .error s!"property not found: {name}" := by
  cases hs : scheduleOf config fork with
  | some s =>
    exact EthLib.Base.Json.getObjVal?_mkObj (schedulePairs_distinct config)
      (List.mem_filterMap.2 ⟨_, hm, by simp [hs]⟩)
  | none =>
    -- No other fork has the name of this one, and this one has no schedule.
    have absent : name ∉ (forkNames.filterMap fun (fork, name) =>
        (scheduleOf config fork).map fun s => (name, scheduleJson s)).map Prod.fst := by
      simp only [List.mem_map, List.mem_filterMap, Option.map_eq_some_iff]
      rintro ⟨_, ⟨⟨f, n⟩, hm', _, hs', rfl⟩, he⟩
      cases forkNames_name_inj _ hm' _ hm he
      simp [hs] at hs'
    exact EthLib.Base.Json.getObjVal?_mkObj_of_not_mem absent

/-- Reading a fork from the written file gives its time and schedule in the configuration. -/
private theorem readFork_write {config base : ChainConfig} (h : Writable config)
    (untimed : ∀ f, timeOf base f = none) {fork : Fork} {name : String}
    (hm : (fork, name) ∈ forkNames) :
    readFork base (writeExecutionConfig config) (Json.mkObj (forkNames.filterMap
      fun (fork, name) => (scheduleOf config fork).map fun s => (name, scheduleJson s)))
      fork name = .ok (timeOf config fork, scheduleOf config fork) := by
  -- A schedule of the configuration belongs to a fork from Dencun on, with a time.
  have timed : ∀ s, scheduleOf config fork = some s →
      Fork.dencun ≤ fork ∧ ∃ t, timeOf config fork = some t := by
    intro s hs
    obtain ⟨⟨g, a, s⟩, hm', he⟩ := List.exists_of_findSome?_eq_some hs
    obtain ⟨f, t, rfl, hd, rfl, ha⟩ := h.2.2.2 g a s hm'
    by_cases e : f = fork
    · subst e
      exact ⟨hd, t, timeOf_eq_some (h.1.1.imp And.left) ha⟩
    · simp [e] at he
  unfold readFork
  rw [readTime_write h hm]
  simp only [untimed]
  by_cases hd : Fork.dencun ≤ fork
  · simp only [hd, ↓reduceIte, getEntry_write hm]
    cases hs : scheduleOf config fork <;> cases ht : timeOf config fork
    · rfl
    · rfl
    · obtain ⟨-, t, ht'⟩ := timed _ hs
      simp [ht] at ht'
    · simp [readSchedule_scheduleJson]
      rfl
  · -- Before Dencun the configuration keeps no schedule, and the file gives none.
    have hs : scheduleOf config fork = none := by
      cases hs : scheduleOf config fork with
      | none => rfl
      | some s => exact absurd (timed s hs).1 hd
    simp only [hd, ↓reduceIte, hs]
    cases timeOf config fork <;> rfl

/-- A choice that succeeds took its first branch, when the second never succeeds. -/
private theorem ok_of_ite {ε α : Type} {b : Prop} [Decidable b] {x y : Except ε α} {c : α}
    (fails : ∀ c, y ≠ .ok c) (h : (if b then x else y) = .ok c) : x = .ok c := by
  by_cases hb : b
  · simpa [hb] using h
  · exact absurd (by simpa [hb] using h) (fails c)

/-- A step followed by a pure result succeeds when the step does, with that result. -/
private theorem ok_of_bind_pure {ε α β : Type} {x : Except ε α} {f : α → β} {c : β}
    (h : (x >>= fun a => pure (f a)) = .ok c) : ∃ a, x = .ok a ∧ f a = c := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

/-- A step followed by another succeeds when the step does, and the rest succeeds after it. -/
private theorem ok_of_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {c : β}
    (h : (x >>= f) = .ok c) : ∃ a, x = .ok a ∧ f a = .ok c := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A configuration that passes the order check is the one given, and it is ordered. -/
private theorem ok_of_check {x c : ChainConfig} {y : Except ConfigError ChainConfig}
    (fails : ∀ c, y ≠ .ok c) (h : (if decide x.Ordered = true then pure x else y) = .ok c) :
    x = c ∧ c.Ordered := by
  by_cases hx : x.Ordered
  · have h' : (pure x : Except ConfigError ChainConfig) = .ok c := by simpa [hx] using h
    have e : x = c := Except.ok.inj h'
    exact ⟨e, e ▸ hx⟩
  · exact absurd (by simpa [hx] using h) (fails c)

/-- The order check passes a configuration that equals an ordered one, and gives it. -/
private theorem ite_ordered {x c : ChainConfig} {y : Except ConfigError ChainConfig}
    (e : x = c) (ordered : c.Ordered) :
    (if decide x.Ordered = true then pure x else y) = .ok c := by
  subst e
  simp [ordered]
  rfl

/-- Reading what the writer wrote gives the configuration back.

The configuration must be one that a file holds whole: each schedule with its fork, and so on.

The base of the reader keeps only the forks by block number, so each time comes from the file. -/
theorem readExecutionConfig_write {config : ChainConfig} (h : Writable config) :
    readExecutionConfig
        { config with activations := config.activations.filter (·.2 matches .block _),
                      blobSchedules := [] }
        (writeExecutionConfig config) = .ok config := by
  have schedules : (writeExecutionConfig config).getObjValD "blobSchedule" =
      Json.mkObj (forkNames.filterMap fun (fork, name) =>
        (scheduleOf config fork).map fun s => (name, scheduleJson s)) :=
    getObjValD_mkObj (writePairs_distinct config) List.mem_cons_self
  obtain ⟨⟨sorted, -⟩, named, scheduleSorted, scheduleForks⟩ := id h
  -- The file passes the check of its schedules, and each fork reads back.
  unfold readExecutionConfig
  rw [schedules]
  dsimp only
  rw [ite_eq_left (by unfold writeExecutionConfig; rw [Toolchain.Json.mkObj_eq]),
    ite_eq_left (by rw [Toolchain.Json.mkObj_eq]; rfl),
    mapM_eq_ok (h := fun p => (p.1, timeOf config p.1, scheduleOf config p.1)) fun p hp => ?_]
  rotate_left
  · obtain ⟨f, n⟩ := p
    -- The base keeps only the forks by block number, so it times no fork.
    refine (congrArg (· >>= fun l => (pure (f, l) : Except ConfigError _))
      (readFork_write (base := { config with
        activations := config.activations.filter (·.2 matches .block _), blobSchedules := [] })
        h (fun f => ?_) hp)).trans rfl
    · refine List.findSome?_eq_none_iff.2 fun ⟨g, a⟩ hx => ?_
      obtain ⟨-, ha⟩ := List.mem_filter.1 hx
      cases a <;> simp_all
  -- Each schedule has a fork.
  have forks : ∀ x ∈ config.blobSchedules, x.1.isSome := fun ⟨g, a, s⟩ hx => by
    obtain ⟨f, t, rfl, -, -⟩ := scheduleForks g a s hx
    rfl
  -- The activations by time are those that the writer lists, in the order of the names.
  have times : forkNames.filterMap (fun p => (timeOf config p.1).map fun t =>
      (p.1, Activation.time t)) =
        config.activations.filter fun x => !(x.2 matches .block _) := by
    rw [filterMap_congr fun p _ => timeOf_map]
    refine filterMap_find? forkNames_sorted
      ((sorted.sublist List.filter_sublist).imp And.left) fun ⟨f, a⟩ hx => ?_
    obtain ⟨hx, ha⟩ := List.mem_filter.1 hx
    cases a with
    | block n => simp at ha
    | time t => exact (named f t hx).1
  -- The schedules are those that the writer lists, in the order of the names.
  have entries : forkNames.filterMap (fun p => match timeOf config p.1, scheduleOf config p.1 with
      | some t, some s => some (some p.1, Activation.time t, s)
      | _, _ => none) = config.blobSchedules := by
    rw [filterMap_congr (g := fun p => config.blobSchedules.find? fun x =>
      x.1.getD .frontier = p.1) fun p _ => ?_]
    · refine filterMap_find? forkNames_sorted ?_ fun ⟨g, a, s⟩ hx => ?_
      · refine scheduleSorted.imp_of_mem fun {x y} hx hy hxy => ?_
        obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (forks x hx)
        obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 (forks y hy)
        simpa [hf, hg] using hxy f g hf hg
      · obtain ⟨f, t, rfl, -, rfl, ha⟩ := scheduleForks g a s hx
        exact (named f t ha).1
    · -- The schedule found for a fork activates with its time.
      rw [scheduleOf_eq forks]
      cases hf : config.blobSchedules.find? fun x => x.1.getD .frontier = p.1 with
      | none => cases timeOf config p.1 <;> rfl
      | some x =>
        obtain ⟨g, a, s⟩ := x
        have hk := List.find?_some hf
        obtain ⟨f, t, rfl, -, rfl, ha⟩ := scheduleForks g a s (List.mem_of_find?_eq_some hf)
        simp only [Option.getD_some, decide_eq_true_eq] at hk
        subst hk
        simp [timeOf_eq_some (sorted.imp And.left) ha]
  -- The activations by block come before those by time.
  have split : config.activations =
      config.activations.filter (fun x => x.2 matches .block _) ++
        config.activations.filter fun x => !(x.2 matches .block _) := by
    refine eq_filter_append (fun ⟨f, a⟩ ⟨g, b⟩ ha hb hab => ?_) sorted
    cases a <;> cases b <;> first | exact hab.2 | simp at ha hb
  simp only [bind, Except.bind, List.filterMap_map, Function.comp_def, List.filter_filter]
  refine ite_ordered ?_ h.1
  rw [times]
  cases config
  simp only [ChainConfig.mk.injEq, true_and]
  refine ⟨?_, entries⟩
  -- The base times no fork, so its activations by time add nothing.
  rw [append_filter_of_forall_false]
  rotate_left
  · intro ⟨f, a⟩ _
    cases a <;> simp
  refine Eq.trans ?_ split.symm
  congr 1
  refine List.filter_congr fun ⟨f, a⟩ _ => ?_
  cases a <;> rfl


/-- A configuration that the reader gives has its forks and schedules in the timeline's order. -/
theorem readExecutionConfig_ordered {base config : ChainConfig} {j : Json}
    (h : readExecutionConfig base j = .ok config) : config.Ordered := by
  -- The file passed its checks, and the last one is the order check.
  unfold readExecutionConfig at h
  obtain ⟨read, -, hc⟩ :=
    ok_of_bind (ok_of_ite (fun c hc => by cases hc) (ok_of_ite (fun c hc => by cases hc) h))
  exact (ok_of_check (fun c hc => by cases hc) hc).2

/-- A file holds mainnet whole, since mainnet sets no blob schedule of its own. -/
theorem writable_mainnet : Writable ChainConfig.mainnet := by
  refine ⟨by decide, ?_, by simp [ChainConfig.mainnet], by simp [ChainConfig.mainnet]⟩
  intro f t h
  simp [ChainConfig.mainnet] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    decide

/-- A file holds Hoodi whole, since Hoodi sets no blob schedule of its own. -/
theorem writable_hoodi : Writable ChainConfig.hoodi := by
  refine ⟨by decide, ?_, by simp [ChainConfig.hoodi], by simp [ChainConfig.hoodi]⟩
  intro f t h
  simp [ChainConfig.hoodi] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    decide

/-- A file holds Sepolia whole, since Sepolia sets no blob schedule of its own. -/
theorem writable_sepolia : Writable ChainConfig.sepolia := by
  refine ⟨by decide, ?_, by simp [ChainConfig.sepolia], by simp [ChainConfig.sepolia]⟩
  intro f t h
  simp [ChainConfig.sepolia] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> decide

/-- After a file is read, the blob schedule at a block is the latest entry that the block reached.

That entry belongs to a fork of the configuration, and activates with it.

Each other entry that the block has reached belongs to an earlier fork.

A fork without an entry so keeps the schedule of the latest fork before it that has one. -/
theorem blobScheduleAt_read {base config : ChainConfig} {j : Json} {n t : Nat}
    {s : BlobSchedule} (h : readExecutionConfig base j = .ok config) :
    config.blobScheduleAt n t = some s ↔
      ∃ f a, (f, a) ∈ config.activations ∧ (some f, a, s) ∈ config.blobSchedules ∧
        a.reached n t = true ∧
        ∀ g b s', (some g, b, s') ∈ config.blobSchedules → b.reached n t = true → g ≤ f := by
  -- The file passed the check of its schedules, and each fork was read.
  unfold readExecutionConfig at h
  obtain ⟨read, hread, hc⟩ :=
    ok_of_bind (ok_of_ite (fun c hc => by cases hc) (ok_of_ite (fun c hc => by cases hc) h))
  replace hc := (ok_of_check (fun c hc => by cases hc) hc).1
  clear h
  -- The forks read come in the order of the names.
  have hfst : read.map Prod.fst = forkNames.map Prod.fst := by
    refine map_fst_of_mapM_eq_ok (fun ⟨f, n⟩ r hr => ?_) hread
    obtain ⟨l, -, rfl⟩ := ok_of_bind_pure hr
    rfl
  have sorted : read.Pairwise fun a b => a.1 < b.1 :=
    List.pairwise_map.1 (hfst ▸ List.pairwise_map.2 forkNames_sorted)
  -- Each schedule read has a fork, and activates with it by time.
  have entries : ∀ y ∈ config.blobSchedules, ∃ f t s, y = (some f, Activation.time t, s) ∧
      (f, Activation.time t) ∈ config.activations := by
    rw [← hc]
    intro y hy
    obtain ⟨⟨f, time, schedule⟩, hr, hy⟩ := List.mem_filterMap.1 hy
    cases time <;> cases schedule <;> simp only [reduceCtorEq, Option.some.injEq] at hy
    subst hy
    exact ⟨_, _, _, rfl, List.mem_append_left _
      (List.mem_append_right _ (List.mem_filterMap.2 ⟨_, hr, rfl⟩))⟩
  -- The schedules read come in the order of their forks.
  have ordered : config.blobSchedules.Pairwise fun x y =>
      x.1.getD .frontier < y.1.getD .frontier := by
    rw [← hc]
    refine List.Pairwise.filterMap _
      (fun ⟨f, time, schedule⟩ ⟨g, time', schedule'⟩ hfg b hb b' hb' => ?_) sorted
    cases time <;> cases schedule <;> simp only [reduceCtorEq, Option.some.injEq] at hb
    cases time' <;> cases schedule' <;> simp only [reduceCtorEq, Option.some.injEq] at hb'
    subst hb hb'
    exact hfg
  clear hc hread hfst sorted
  -- The schedule found from the end is the reached one of the greatest fork.
  unfold ChainConfig.blobScheduleAt
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hm, hp, hmax⟩ := (find?_reverse_eq_some ordered).1 hx
    obtain ⟨f, u, s, rfl, ha⟩ := entries x hm
    exact ⟨f, _, ha, hm, hp, fun g b s' hg hb => hmax _ hg hb⟩
  · rintro ⟨f, a, -, hm, hp, hmax⟩
    refine ⟨(some f, a, s), (find?_reverse_eq_some ordered).2 ⟨hm, hp, fun y hy hpy => ?_⟩, rfl⟩
    obtain ⟨g, u, s', rfl, -⟩ := entries y hy
    exact hmax g _ s' hy hpy

/-- Two errors with one code come from one constructor. -/
theorem ConfigError.code_injective (e₁ e₂ : ConfigError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Each code is one more than the index of its constructor.
  have back : ∀ e : ConfigError, e.code.toNat - 1 = e.ctorIdx := by
    intro e
    cases e <;> rfl
  rw [← back e₁, ← back e₂, h]

end EthLib.Base.ExecutionConfig
