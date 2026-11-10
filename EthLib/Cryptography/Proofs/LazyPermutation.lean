module

public import EthLib.Cryptography.Proofs.EvalDistEq
public import VCVio.OracleComp.Constructions.UniformSelectMeasure
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Proofs: a random permutation sampled one answer at a time

A random permutation oracle draws a uniform permutation `π` of a finite set before the run.

The adversary then asks for `π a` and for the inverse `π⁻¹ b`.

The lazy oracle draws nothing up front.

It keeps the pairs `(a, π a)` answered so far.

A new forward query gets a uniform value that is no cached image.

A new inverse query gets a uniform value that is no cached preimage.

From the empty cache, the two oracles give the same output distribution to every run.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The permutation is their bijective random oracle, §4.

Theirs maps between two sets of one size; here both sets are `A`, as in the ECDSA game.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleComp OracleSpec ENNReal

/-! ## Uniform draws from a list -/

/-- A uniform entry of a list, counted with multiplicity, or `d` when the list is empty.

The framework's draw from a list fails on the empty list, and this one never fails. -/
def uniformFrom {X : Type} : List X → X → ProbComp X
  | [], d => pure d
  | b :: bs, _ => $! (List.Vector.cons b ⟨bs, rfl⟩)

/-- A draw from a list without repeats gives each entry the reciprocal of the length as chance. -/
theorem prEvent_uniformFrom_eq_of_mem {X : Type} {l : List X} (hl : l.Nodup) (d : X) {x : X}
    (hx : x ∈ l) : Pr{let y ← uniformFrom l d}[y = x] = (l.length : ℝ≥0∞)⁻¹ := by
  classical
  cases l with
  | nil => simp at hx
  | cons b bs =>
    rw [uniformFrom, ProbComp.prEvent_uniformSelectListVector]
    change ((List.countP (fun a => decide (a = x)) (b :: bs) : ℕ) : ℝ≥0∞) / _ = _
    have h1 := List.count_eq_one_of_mem hl hx
    rw [List.count_eq_countP] at h1
    simp only [beq_eq_decide] at h1
    simp [h1]

/-- A draw from a nonempty list never gives a value outside the list. -/
theorem prEvent_uniformFrom_eq_of_notMem {X : Type} {l : List X} (hne : l ≠ []) (d : X) {x : X}
    (hx : x ∉ l) : Pr{let y ← uniformFrom l d}[y = x] = 0 := by
  classical
  cases l with
  | nil => exact absurd rfl hne
  | cons b bs =>
    rw [uniformFrom, ProbComp.prEvent_uniformSelectListVector]
    change ((List.countP (fun a => decide (a = x)) (b :: bs) : ℕ) : ℝ≥0∞) / _ = _
    rw [List.countP_eq_zero.2 fun a ha h => hx (by
      simp only [decide_eq_true_eq] at h
      exact h ▸ ha)]
    simp

/-- A draw from a nonempty list only gives entries of the list. -/
theorem mem_of_mem_support_uniformFrom {X : Type} {l : List X} (hne : l ≠ []) (d : X) {x : X}
    (hx : x ∈ support (uniformFrom l d)) : x ∈ l := by
  by_contra h
  exact (mem_support_iff_prEvent_ne_zero _ x).1 hx (prEvent_uniformFrom_eq_of_notMem hne d h)

/-- A draw from a nonempty list meets an event with chance its entries that meet it over its length.

The entries are counted with repeats. -/
theorem prEvent_uniformFrom_eq_countP {X : Type} {l : List X} (hl : l ≠ []) (d : X)
    (p : X → Prop) [DecidablePred p] :
    Pr{let y ← uniformFrom l d}[p y] = (l.countP (fun y => decide (p y)) : ℝ≥0∞) / l.length := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b bs =>
    rw [uniformFrom, ProbComp.prEvent_uniformSelectListVector]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    rfl

/-- A finite set whose image lies in a list without repeats, with fibres of one size over it.

Its size is the length of the list times the size of each fibre. -/
private theorem card_eq_length_mul_card_filter {X Y : Type} [DecidableEq Y] {S : Finset X}
    (f : X → Y) {L : List Y} (hL : L.Nodup) (hmap : ∀ x ∈ S, f x ∈ L)
    (hcard : ∀ y ∈ L, ∀ y' ∈ L, (S.filter (f · = y)).card = (S.filter (f · = y')).card)
    {y : Y} (hy : y ∈ L) : S.card = L.length * (S.filter (f · = y)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (t := L.toFinset)
      fun x hx => List.mem_toFinset.2 (hmap x hx),
    Finset.sum_congr rfl fun y' hy' => hcard y' (List.mem_toFinset.1 hy') y hy, Finset.sum_const,
    List.toFinset_card_of_nodup hL, smul_eq_mul]

/-- A uniform draw from a finite set is a uniform draw of an image, then of its fibre.

The image must lie in a list without repeats, and the fibres over the list must have one size. -/
theorem uniformFrom_toList_evalDistEq_bind {X Y : Type} [DecidableEq Y] [Fintype Y]
    {S : Finset X} (hS : S.Nonempty) (f : X → Y) {L : List Y} (hL : L.Nodup)
    (hmap : ∀ x ∈ S, f x ∈ L)
    (hcard : ∀ y ∈ L, ∀ y' ∈ L, (S.filter (f · = y)).card = (S.filter (f · = y')).card)
    (d : X) (e : Y) :
    uniformFrom S.toList d =ᵈ
      (uniformFrom L e >>= fun y => uniformFrom (S.filter (f · = y)).toList d) := by
  obtain ⟨x₀, hx₀⟩ := hS
  have hSc := fun {y} (hy : y ∈ L) => card_eq_length_mul_card_filter f hL hmap hcard hy
  have hne : ∀ y ∈ L, (S.filter (f · = y)).toList ≠ [] := fun y hy h => by
    have := hSc hy
    rw [← Finset.length_toList (S.filter _), h, List.length_nil, mul_zero,
      Finset.card_eq_zero] at this
    simp [this] at hx₀
  have hzero : ∀ x y, x ∉ S.filter (f · = y) →
      Pr{let z ← uniformFrom L e}[z = y] *
        Pr{let z ← uniformFrom (S.filter (f · = y)).toList d}[z = x] = 0 := fun x y hxy => by
    by_cases hy : y ∈ L
    · rw [prEvent_uniformFrom_eq_of_notMem (hne y hy) d (by simpa using hxy), mul_zero]
    · rw [prEvent_uniformFrom_eq_of_notMem (List.ne_nil_of_mem (hmap x₀ hx₀)) e hy, zero_mul]
  refine evalDistEq_of_forall_prEvent_eq_output fun x => ?_
  rw [prEvent_bind_eq_sum_fintype]
  by_cases hx : x ∈ S
  · rw [prEvent_uniformFrom_eq_of_mem (Finset.nodup_toList S) d (Finset.mem_toList.2 hx),
      Finset.sum_eq_single (f x) (fun y _ hy => hzero x y (by simp [hx, Ne.symm hy]))
        (fun h => absurd (Finset.mem_univ _) h),
      prEvent_uniformFrom_eq_of_mem hL e (hmap x hx),
      prEvent_uniformFrom_eq_of_mem (Finset.nodup_toList _) d (by simp [hx]),
      Finset.length_toList, Finset.length_toList, hSc (hmap x hx), Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  · rw [prEvent_uniformFrom_eq_of_notMem (by simpa using Finset.ne_empty_of_mem hx₀) d
      (by simpa using hx)]
    exact (Finset.sum_eq_zero fun y _ => hzero x y (by simp [hx])).symm

end EthLib.Cryptography

namespace EthLib.Cryptography.LazyPermutation

open OracleComp OracleSpec ENNReal

variable {A : Type}

/-- The oracles of a permutation of `A`: forward and inverse. -/
abbrev PermSpec (A : Type) := (A →ₒ A) + (A →ₒ A)

/-- The pairs `(a, π a)` that the lazy oracle answered so far, the most recent first. -/
abbrev PermCache (A : Type) := List (A × A)

/-- The computations that draw coins and ask the permutation oracle. -/
abbrev PermComp (A : Type) := OracleComp (unifSpec + PermSpec A)

/-- The permutation `π` as an oracle: `π` and its inverse. -/
def permOracle (π : Equiv.Perm A) : QueryImpl (PermSpec A) ProbComp
  | .inl a => (pure (π a) : ProbComp A)
  | .inr b => (pure (π.symm b) : ProbComp A)

/-- The oracles with the permutation `π`: coins, passed through, then `π` and its inverse. -/
abbrev permImpl (π : Equiv.Perm A) : QueryImpl (unifSpec + PermSpec A) ProbComp :=
  unifSpec.passthrough + permOracle π

/-- Running a computation of coins alone with `π` leaves it unchanged. -/
theorem simulateQ_permImpl_liftM {α : Type} (π : Equiv.Perm A) (oa : ProbComp α) :
    simulateQ (permImpl π) (liftM oa : PermComp A α) = oa := by
  rw [QueryImpl.simulateQ_liftM_eq_of_query (permImpl π) (QueryImpl.id' unifSpec)
    (fun t => by simp [permImpl]) oa, simulateQ_id']

/-- A run of coins alone asks the permutation oracle nothing.

The queries to that oracle are the right part of the sum of oracles. -/
theorem isQueryBoundP_liftM_permComp {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : PermComp A α) (·.isRight = true) 0 := by
  rw [← liftComp_eq_liftM]
  exact isQueryBoundP_simulateQ_zero oa fun t => by
    change IsQueryBoundP (liftM ((unifSpec + PermSpec A).query (.inl t))) _ 0
    rw [isQueryBoundP_query_iff]
    simp

/-- With coins passed through beside a permutation oracle, a coin query keeps the state. -/
theorem passthrough_add_inl_run {σ : Type} (perm : QueryImpl (PermSpec A) (StateT σ ProbComp))
    (n : ℕ) (s : σ) :
    ((unifSpec.passthrough + perm) (.inl n)).run s =
      (·, s) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  simp [StateT.run_monadLift]

variable [FinEnum A]

/-- A uniform element of `A` outside the list, or `d` when there is none. -/
def uniformOutside (used : List A) (d : A) : ProbComp A :=
  uniformFrom ((FinEnum.toList A).filter fun b => b ∉ used) d

/-- The permutation sampled one answer at a time, as an oracle.

A query answered before gets its answer again.

A new forward query gets a uniform value that is no cached image.

A new inverse query gets a uniform value that is no cached preimage. -/
def lazyPermOracle : QueryImpl (PermSpec A) (StateT (PermCache A) ProbComp)
  | .inl a => fun c =>
    match c.lookup a with
    | some b => pure (b, c)
    | none => (fun b => (b, (a, b) :: c)) <$> (uniformOutside (c.map Prod.snd) a : ProbComp A)
  | .inr b => fun c =>
    match (c.map Prod.swap).lookup b with
    | some a => pure (a, c)
    | none => (fun a => (a, (a, b) :: c)) <$> (uniformOutside (c.map Prod.fst) b : ProbComp A)

/-- The lazy oracles: coins, passed through, then the permutation sampled one answer at a time. -/
abbrev lazyPermImpl : QueryImpl (unifSpec + PermSpec A) (StateT (PermCache A) ProbComp) :=
  unifSpec.passthrough + lazyPermOracle

/-- A run of coins alone against the lazy permutation leaves the cache unchanged. -/
theorem simulateQ_lazyPermImpl_liftM_run {α : Type} (oa : ProbComp α)
    (c : PermCache A) :
    (simulateQ lazyPermImpl (liftM oa : PermComp A α)).run c = (·, c) <$> oa := by
  rw [QueryImpl.simulateQ_liftM_eq_of_query lazyPermImpl
    ((QueryImpl.id' unifSpec).liftTarget (StateT (PermCache A) ProbComp))
    (fun t => by simp [lazyPermImpl]) oa]
  simp [StateT.run_monadLift]

/-- Whether the permutation agrees with every pair of the cache. -/
def Agrees (c : PermCache A) (π : Equiv.Perm A) : Prop :=
  ∀ p ∈ c, π p.1 = p.2

instance (c : PermCache A) (π : Equiv.Perm A) : Decidable (Agrees c π) :=
  inferInstanceAs (Decidable (∀ p ∈ c, π p.1 = p.2))

/-- The permutations that agree with the cache. -/
def extensions (c : PermCache A) : Finset (Equiv.Perm A) :=
  Finset.univ.filter (Agrees c)

/-- A uniform permutation among those that agree with the cache.

It gives the identity when no permutation agrees. -/
noncomputable def uniformExtension (c : PermCache A) : ProbComp (Equiv.Perm A) :=
  uniformFrom (extensions c).toList (Equiv.refl A)

/-- A cache is a partial bijection: no two pairs share a query or an answer.

The converse of the next theorem fails: a repeated pair keeps an agreeing permutation. -/
def PermCache.IsPartialBijection (c : PermCache A) : Prop :=
  (c.map Prod.fst).Nodup ∧ (c.map Prod.snd).Nodup

/-- A partial bijection has a permutation that agrees with it. -/
theorem PermCache.IsPartialBijection.extensions_nonempty {c : PermCache A}
    (hc : c.IsPartialBijection) : (extensions c).Nonempty := by
  induction c with
  | nil => exact ⟨Equiv.refl A, by simp [extensions, Agrees]⟩
  | cons p c ih =>
    obtain ⟨hf, hs⟩ := hc
    simp only [List.map_cons, List.nodup_cons] at hf hs
    obtain ⟨π, hπ⟩ := ih ⟨hf.2, hs.2⟩
    refine ⟨Equiv.swap (π p.1) p.2 * π, ?_⟩
    simp only [extensions, Finset.mem_filter, Finset.mem_univ, true_and, Agrees] at hπ ⊢
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · simp
    · rw [Equiv.Perm.mul_apply, hπ q hq]
      refine Equiv.swap_apply_of_ne_of_ne (fun h => ?_) (fun h => hs.1 (List.mem_map.2 ⟨q, hq, h⟩))
      exact hf.1 (List.mem_map.2 ⟨q, hq, π.injective ((hπ q hq).trans h)⟩)

/-! ## Permutations that agree with a cache -/

/-- A permutation agrees with a cache and one new pair when two facts hold.

It agrees with the cache, and it maps the new query to its answer. -/
theorem extensions_cons (p : A × A) (c : PermCache A) :
    extensions (p :: c) = (extensions c).filter fun π => π p.1 = p.2 := by
  ext π
  simp [extensions, Agrees, and_comm]

/-- A query found in the cache is the first entry of a pair with that answer. -/
private theorem mem_of_lookup_eq_some {c : PermCache A} {a b : A} (h : c.lookup a = some b) :
    (a, b) ∈ c := by
  induction c with
  | nil => simp at h
  | cons p c ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : a = k
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      simp [h]
    · simp only [List.lookup, beq_false_of_ne hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- A query missing from the cache is no query of the cache. -/
private theorem ne_of_lookup_eq_none {c : PermCache A} {a : A} (h : c.lookup a = none) :
    ∀ p ∈ c, p.1 ≠ a := fun p hp hpa => by
  have := List.lookup_eq_none_iff.1 h p hp
  simp [hpa] at this

/-- An agreeing permutation sends a query missing from the cache outside the answers. -/
private theorem apply_mem_outside {c : PermCache A} {a : A} (h : c.lookup a = none)
    {π : Equiv.Perm A} (hπ : π ∈ extensions c) :
    π a ∈ (FinEnum.toList A).filter fun b => b ∉ c.map Prod.snd := by
  simp only [List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq, List.mem_map]
  rintro ⟨p, hp, hpa⟩
  have hagree : π p.1 = p.2 := (Finset.mem_filter.1 hπ).2 p hp
  exact ne_of_lookup_eq_none h p hp (π.injective (hagree.trans hpa))

/-- Take two values outside the answers, and compose with their swap.

The agreeing permutations that send the query to one value go to those that send it to the other. -/
private theorem swap_mul_mem_filter {c : PermCache A} {a y y' : A} (hy : y ∉ c.map Prod.snd)
    (hy' : y' ∉ c.map Prod.snd) {π : Equiv.Perm A}
    (hπ : π ∈ (extensions c).filter fun σ => σ a = y) :
    Equiv.swap y y' * π ∈ (extensions c).filter fun σ => σ a = y' := by
  simp only [Finset.mem_filter, extensions, Finset.mem_univ, true_and, Agrees] at hπ ⊢
  refine ⟨fun p hp => ?_, by simp [hπ.2]⟩
  rw [Equiv.Perm.mul_apply, hπ.1 p hp]
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hy (List.mem_map.2 ⟨p, hp, h⟩))
    (fun h => hy' (List.mem_map.2 ⟨p, hp, h⟩))

/-- Fix a query, and take two values outside the answers.

Equally many agreeing permutations send the query to each of them. -/
private theorem card_filter_apply_eq {c : PermCache A} {a y y' : A} (hy : y ∉ c.map Prod.snd)
    (hy' : y' ∉ c.map Prod.snd) :
    ((extensions c).filter fun σ => σ a = y).card =
      ((extensions c).filter fun σ => σ a = y').card :=
  Finset.card_nbij' (Equiv.swap y y' * ·) (Equiv.swap y y' * ·)
    (fun _ hπ => swap_mul_mem_filter hy hy' hπ)
    (fun _ hπ => Equiv.swap_comm y y' ▸ swap_mul_mem_filter hy' hy hπ)
    (fun _ _ => Equiv.swap_mul_self_mul _ _ _) (fun _ _ => Equiv.swap_mul_self_mul _ _ _)

/-- A uniform agreeing permutation is a lazy forward answer, then a uniform agreeing extension.

The query must be missing from the cache. -/
private theorem uniformExtension_evalDistEq_forward {c : PermCache A} (hc : (extensions c).Nonempty)
    {a : A} (h : c.lookup a = none) :
    uniformExtension c =ᵈ
      (uniformOutside (c.map Prod.snd) a >>= fun b => uniformExtension ((a, b) :: c)) := by
  simp only [uniformExtension, uniformOutside, extensions_cons]
  exact uniformFrom_toList_evalDistEq_bind hc (fun π => π a)
    ((FinEnum.nodup_toList).filter _) (fun π hπ => apply_mem_outside h hπ)
    (fun y hy y' hy' => card_filter_apply_eq (by simpa using hy) (by simpa using hy')) _ _

/-- A lazy forward answer leaves a cache with an agreeing permutation. -/
private theorem extensions_cons_nonempty_forward {c : PermCache A} (hc : (extensions c).Nonempty)
    {a b : A} (h : c.lookup a = none)
    (hb : b ∈ (FinEnum.toList A).filter fun b => b ∉ c.map Prod.snd) :
    (extensions ((a, b) :: c)).Nonempty := by
  have := card_eq_length_mul_card_filter (fun π => π a) ((FinEnum.nodup_toList).filter _)
    (fun π hπ => apply_mem_outside h hπ)
    (fun y hy y' hy' => card_filter_apply_eq (by simpa using hy) (by simpa using hy')) hb
  rw [extensions_cons]
  refine Finset.card_pos.1 (Nat.pos_of_ne_zero fun h0 => ?_)
  rw [h0, mul_zero] at this
  exact hc.ne_empty (Finset.card_eq_zero.1 this)

/-- Take an answer missing from the cache and an agreeing permutation.

The inverse of the permutation sends that answer outside the queries. -/
private theorem symm_apply_mem_outside {c : PermCache A} {b : A}
    (h : (c.map Prod.swap).lookup b = none) {π : Equiv.Perm A} (hπ : π ∈ extensions c) :
    π.symm b ∈ (FinEnum.toList A).filter fun a => a ∉ c.map Prod.fst := by
  simp only [List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq, List.mem_map]
  rintro ⟨p, hp, hpb⟩
  have hagree : π p.1 = p.2 := (Finset.mem_filter.1 hπ).2 p hp
  exact ne_of_lookup_eq_none h p.swap (List.mem_map_of_mem hp)
    (by rw [Prod.fst_swap, ← hagree, hpb, Equiv.apply_symm_apply])

/-- Take two values outside the queries, and compose with their swap on the right.

The agreeing permutations with one preimage of the answer go to those with the other. -/
private theorem mul_swap_mem_filter {c : PermCache A} {b x x' : A} (hx : x ∉ c.map Prod.fst)
    (hx' : x' ∉ c.map Prod.fst) {π : Equiv.Perm A}
    (hπ : π ∈ (extensions c).filter fun σ => σ.symm b = x) :
    π * Equiv.swap x x' ∈ (extensions c).filter fun σ => σ.symm b = x' := by
  simp only [Finset.mem_filter, extensions, Finset.mem_univ, true_and, Agrees,
    Equiv.symm_apply_eq] at hπ ⊢
  refine ⟨fun p hp => ?_, by simp [Equiv.Perm.mul_apply, hπ.2]⟩
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
    (fun h => hx (List.mem_map.2 ⟨p, hp, h⟩)) (fun h => hx' (List.mem_map.2 ⟨p, hp, h⟩)),
    hπ.1 p hp]

/-- Fix an answer, and take two values outside the queries.

Equally many agreeing permutations send each of them to the answer. -/
private theorem card_filter_symm_apply_eq {c : PermCache A} {b x x' : A} (hx : x ∉ c.map Prod.fst)
    (hx' : x' ∉ c.map Prod.fst) :
    ((extensions c).filter fun σ => σ.symm b = x).card =
      ((extensions c).filter fun σ => σ.symm b = x').card :=
  Finset.card_nbij' (· * Equiv.swap x x') (· * Equiv.swap x x')
    (fun _ hπ => mul_swap_mem_filter hx hx' hπ)
    (fun _ hπ => Equiv.swap_comm x x' ▸ mul_swap_mem_filter hx' hx hπ)
    (fun _ _ => Equiv.mul_swap_mul_self _ _ _) (fun _ _ => Equiv.mul_swap_mul_self _ _ _)

/-- The agreeing permutations that map a query to an answer, read through the inverse. -/
private theorem extensions_cons_eq_filter_symm (c : PermCache A) (a b : A) :
    extensions ((a, b) :: c) = (extensions c).filter fun σ => σ.symm b = a := by
  rw [extensions_cons]
  exact Finset.filter_congr fun σ _ => by rw [Equiv.symm_apply_eq, eq_comm]

/-- A uniform agreeing permutation is a lazy inverse answer, then a uniform agreeing extension.

The answer must be missing from the cache. -/
private theorem uniformExtension_evalDistEq_inverse {c : PermCache A} (hc : (extensions c).Nonempty)
    {b : A} (h : (c.map Prod.swap).lookup b = none) :
    uniformExtension c =ᵈ
      (uniformOutside (c.map Prod.fst) b >>= fun a => uniformExtension ((a, b) :: c)) := by
  simp only [uniformExtension, uniformOutside, extensions_cons_eq_filter_symm]
  exact uniformFrom_toList_evalDistEq_bind hc (fun π => π.symm b)
    ((FinEnum.nodup_toList).filter _) (fun π hπ => symm_apply_mem_outside h hπ)
    (fun x hx x' hx' => card_filter_symm_apply_eq (by simpa using hx) (by simpa using hx')) _ _

/-- A lazy inverse answer leaves a cache with an agreeing permutation. -/
private theorem extensions_cons_nonempty_inverse {c : PermCache A} (hc : (extensions c).Nonempty)
    {a b : A} (h : (c.map Prod.swap).lookup b = none)
    (ha : a ∈ (FinEnum.toList A).filter fun a => a ∉ c.map Prod.fst) :
    (extensions ((a, b) :: c)).Nonempty := by
  have := card_eq_length_mul_card_filter (fun π => π.symm b) ((FinEnum.nodup_toList).filter _)
    (fun π hπ => symm_apply_mem_outside h hπ)
    (fun x hx x' hx' => card_filter_symm_apply_eq (by simpa using hx) (by simpa using hx')) ha
  rw [extensions_cons_eq_filter_symm]
  refine Finset.card_pos.1 (Nat.pos_of_ne_zero fun h0 => ?_)
  rw [h0, mul_zero] at this
  exact hc.ne_empty (Finset.card_eq_zero.1 this)

/-! ## The lazy oracle stays a partial bijection -/

/-- Two lists without repeats of one length, the first missing a value.

Some value of the type is then missing from the second list. -/
private theorem filter_notMem_ne_nil {l₁ l₂ : List A} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hlen : l₁.length = l₂.length) {a : A} (ha : a ∉ l₁) :
    (FinEnum.toList A).filter (fun b => b ∉ l₂) ≠ [] := by
  intro h
  have hall : ∀ b, b ∈ l₂ := fun b => by
    by_contra hb
    have : b ∈ (FinEnum.toList A).filter (fun b => b ∉ l₂) :=
      List.mem_filter.2 ⟨FinEnum.mem_toList b, by simpa using hb⟩
    rw [h] at this
    simp at this
  have h₂u : l₂.toFinset = Finset.univ := Finset.eq_univ_of_forall fun b => by simp [hall b]
  have h₁u : l₁.toFinset = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [List.toFinset_card_of_nodup h₁, hlen, ← List.toFinset_card_of_nodup h₂, h₂u,
      Finset.card_univ])
  exact ha (List.mem_toFinset.1 (h₁u ▸ Finset.mem_univ a))

omit [FinEnum A] in
/-- A permutation query goes to the permutation oracle. -/
private theorem permImpl_inr (π : Equiv.Perm A) (t : (PermSpec A).Domain) :
    permImpl π (.inr t) = permOracle π t := rfl

/-- A permutation query goes to the lazy permutation oracle. -/
theorem lazyPermImpl_inr (t : (PermSpec A).Domain) :
    (lazyPermImpl (.inr t) : StateT (PermCache A) ProbComp _) = lazyPermOracle t := rfl

/-- One lazy query only adds pairs to the cache, and keeps it a partial bijection. -/
private theorem lazyPermImpl_step {t : (unifSpec + PermSpec A).Domain} {c c₁ : PermCache A}
    {u : (unifSpec + PermSpec A).Range t} (h : (u, c₁) ∈ support ((lazyPermImpl t).run c)) :
    c <:+ c₁ ∧ (c.IsPartialBijection → c₁.IsPartialBijection) := by
  rcases t with n | a | b
  · simp only [lazyPermImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply, QueryImpl.id'_apply] at h
    simp at h
    subst h
    exact ⟨List.suffix_refl _, id⟩
  · simp only [lazyPermImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inr, lazyPermOracle,
      StateT.run] at h
    cases hl : c.lookup a with
    | some b =>
      rw [hl] at h
      simp at h
      rw [h.2]
      exact ⟨List.suffix_refl _, id⟩
    | none =>
      rw [hl] at h
      simp only [support_map, Set.mem_image, Prod.mk.injEq] at h
      obtain ⟨b, hb, -, rfl⟩ := h
      refine ⟨List.suffix_cons _ _, fun hc => ?_⟩
      have ha : a ∉ c.map Prod.fst := fun ha => by
        obtain ⟨p, hp, hpa⟩ := List.mem_map.1 ha
        exact ne_of_lookup_eq_none hl p hp hpa
      have hb' := mem_of_mem_support_uniformFrom
        (filter_notMem_ne_nil hc.1 hc.2 (by simp) ha) _ hb
      simp only [List.mem_filter, decide_eq_true_eq] at hb'
      exact ⟨List.nodup_cons.2 ⟨ha, hc.1⟩, List.nodup_cons.2 ⟨hb'.2, hc.2⟩⟩
  · simp only [lazyPermImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inr, lazyPermOracle,
      StateT.run] at h
    cases hl : (c.map Prod.swap).lookup b with
    | some a =>
      rw [hl] at h
      simp at h
      rw [h.2]
      exact ⟨List.suffix_refl _, id⟩
    | none =>
      rw [hl] at h
      simp only [support_map, Set.mem_image, Prod.mk.injEq] at h
      obtain ⟨a, ha, -, rfl⟩ := h
      refine ⟨List.suffix_cons _ _, fun hc => ?_⟩
      have hb : b ∉ c.map Prod.snd := fun hb => by
        obtain ⟨p, hp, hpb⟩ := List.mem_map.1 hb
        exact ne_of_lookup_eq_none hl p.swap (List.mem_map_of_mem hp) hpb
      have ha' := mem_of_mem_support_uniformFrom
        (filter_notMem_ne_nil hc.2 hc.1 (by simp) hb) _ ha
      simp only [List.mem_filter, decide_eq_true_eq] at ha'
      exact ⟨List.nodup_cons.2 ⟨ha'.2, hc.1⟩, List.nodup_cons.2 ⟨hb, hc.2⟩⟩

/-- A lazy run only adds pairs to the cache, and keeps it a partial bijection. -/
private theorem lazyPermImpl_run_support {α : Type} (oa : OracleComp (unifSpec + PermSpec A) α)
    {c c' : PermCache A} {a : α} (h : (a, c') ∈ support ((simulateQ lazyPermImpl oa).run c)) :
    c <:+ c' ∧ (c.IsPartialBijection → c'.IsPartialBijection) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x =>
    simp at h
    rw [h.2]
    exact ⟨List.suffix_refl _, id⟩
  | query_bind t k ih =>
    simp at h
    obtain ⟨u, c₁, h₁, h₂⟩ := h
    obtain ⟨hs₁, hi₁⟩ := lazyPermImpl_step h₁
    obtain ⟨hs₂, hi₂⟩ := ih u h₂
    exact ⟨hs₁.trans hs₂, hi₂ ∘ hi₁⟩

/-- The lazy oracle keeps the cache a partial bijection. -/
theorem isPartialBijection_of_mem_support_lazyPermImpl {α : Type}
    (oa : OracleComp (unifSpec + PermSpec A) α) {c c' : PermCache A} {a : α}
    (hc : c.IsPartialBijection) (h : (a, c') ∈ support ((simulateQ lazyPermImpl oa).run c)) :
    c'.IsPartialBijection :=
  (lazyPermImpl_run_support oa h).2 hc

/-- The lazy oracle only adds pairs to the cache. -/
theorem suffix_of_mem_support_lazyPermImpl {α : Type}
    (oa : OracleComp (unifSpec + PermSpec A) α) {c c' : PermCache A} {a : α}
    (h : (a, c') ∈ support ((simulateQ lazyPermImpl oa).run c)) : c <:+ c' :=
  (lazyPermImpl_run_support oa h).1

/-- Every permutation agrees with the empty cache. -/
theorem extensions_nil : extensions ([] : PermCache A) = Finset.univ := by
  ext π
  simp [extensions, Agrees]

/-- The empty cache has an agreeing permutation. -/
theorem extensions_nil_nonempty : (extensions ([] : PermCache A)).Nonempty :=
  ⟨Equiv.refl A, by simp [extensions, Agrees]⟩

/-- One lazy query keeps a cache that has an agreeing permutation. -/
private theorem extensions_nonempty_step {t : (unifSpec + PermSpec A).Domain}
    {c c₁ : PermCache A} {u : (unifSpec + PermSpec A).Range t} (hc : (extensions c).Nonempty)
    (h : (u, c₁) ∈ support ((lazyPermImpl t).run c)) : (extensions c₁).Nonempty := by
  rcases t with n | a | b
  · simp only [lazyPermImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply, QueryImpl.id'_apply] at h
    simp at h
    subst h
    exact hc
  · simp only [lazyPermImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inr, lazyPermOracle,
      StateT.run] at h
    cases hl : c.lookup a with
    | some b =>
      rw [hl] at h
      simp at h
      rw [h.2]
      exact hc
    | none =>
      rw [hl] at h
      simp only [support_map, Set.mem_image, Prod.mk.injEq] at h
      obtain ⟨b, hb, -, rfl⟩ := h
      exact extensions_cons_nonempty_forward hc hl (mem_of_mem_support_uniformFrom
        (List.ne_nil_of_mem (apply_mem_outside hl hc.choose_spec)) _ hb)
  · simp only [lazyPermImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inr, lazyPermOracle,
      StateT.run] at h
    cases hl : (c.map Prod.swap).lookup b with
    | some a =>
      rw [hl] at h
      simp at h
      rw [h.2]
      exact hc
    | none =>
      rw [hl] at h
      simp only [support_map, Set.mem_image, Prod.mk.injEq] at h
      obtain ⟨a, ha, -, rfl⟩ := h
      exact extensions_cons_nonempty_inverse hc hl (mem_of_mem_support_uniformFrom
        (List.ne_nil_of_mem (symm_apply_mem_outside hl hc.choose_spec)) _ ha)

/-- The lazy oracle keeps a cache that has an agreeing permutation. -/
theorem extensions_nonempty_of_mem_support_lazyPermImpl {α : Type}
    (oa : OracleComp (unifSpec + PermSpec A) α) {c c' : PermCache A} {a : α}
    (hc : (extensions c).Nonempty) (h : (a, c') ∈ support ((simulateQ lazyPermImpl oa).run c)) :
    (extensions c').Nonempty := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x =>
    simp at h
    rw [h.2]
    exact hc
  | query_bind t k ih =>
    simp at h
    obtain ⟨u, c₁, h₁, h₂⟩ := h
    exact ih u (extensions_nonempty_step hc h₁) h₂

/-! ## Lazy sampling is exact -/

/-- A draw of an agreeing permutation only gives agreeing permutations. -/
private theorem mem_extensions_of_mem_support_uniformExtension {c : PermCache A}
    (hc : (extensions c).Nonempty)
    {π : Equiv.Perm A} (hπ : π ∈ support (uniformExtension c)) : π ∈ extensions c :=
  Finset.mem_toList.1 (mem_of_mem_support_uniformFrom
    (by simpa using Finset.nonempty_iff_ne_empty.1 hc) _ hπ)

/-- The joint law of lazy sampling, with the permutation paired to the output on both sides. -/
private theorem uniformExtension_bind_map_evalDistEq {α : Type}
    (oa : OracleComp (unifSpec + PermSpec A) α) {c : PermCache A}
    (hc : (extensions c).Nonempty) :
    (uniformExtension c >>= fun π => (·, π) <$> simulateQ (permImpl π) oa) =ᵈ
      ((simulateQ lazyPermImpl oa).run c >>= fun z => Prod.mk z.1 <$> uniformExtension z.2) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, bind_assoc]
    rcases t with n | a | b
    · simp [permImpl, lazyPermImpl, StateT.run]
      exact (EvalDistEq.bind_bind_swap _ _ _).trans (EvalDistEq.bind_right _ fun u => ih u hc)
    · simp [permImpl_inr, lazyPermImpl_inr, permOracle, lazyPermOracle, StateT.run]
      cases hl : c.lookup a with
      | some b =>
        dsimp only
        rw [pure_bind]
        refine (EvalDistEq.bind_congr_of_support _ fun π hπ => ?_).trans (ih b hc)
        have : π a = b :=
          (Finset.mem_filter.1 (mem_extensions_of_mem_support_uniformExtension hc hπ)).2 _
            (mem_of_lookup_eq_some hl)
        rw [this]
        rfl
      | none =>
        dsimp only
        rw [bind_map_left]
        refine ((uniformExtension_evalDistEq_forward hc hl).bind_left _).trans ?_
        rw [bind_assoc]
        refine EvalDistEq.bind_congr_of_support _ fun b hb => ?_
        have hb' := mem_of_mem_support_uniformFrom
          (List.ne_nil_of_mem (apply_mem_outside hl hc.choose_spec)) _ hb
        have hne := extensions_cons_nonempty_forward hc hl hb'
        refine (EvalDistEq.bind_congr_of_support _ fun π hπ => ?_).trans (ih b hne)
        have : π a = b :=
          (Finset.mem_filter.1 (mem_extensions_of_mem_support_uniformExtension hne hπ)).2 _
            List.mem_cons_self
        rw [this]
        rfl
    · simp [permImpl_inr, lazyPermImpl_inr, permOracle, lazyPermOracle, StateT.run]
      cases hl : (c.map Prod.swap).lookup b with
      | some a =>
        dsimp only
        rw [pure_bind]
        refine (EvalDistEq.bind_congr_of_support _ fun π hπ => ?_).trans (ih a hc)
        obtain ⟨p, hp, hpe⟩ := List.mem_map.1 (mem_of_lookup_eq_some hl)
        obtain ⟨p₁, p₂⟩ := p
        simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hpe
        obtain ⟨rfl, rfl⟩ := hpe
        have : π.symm p₂ = p₁ := (Equiv.symm_apply_eq π).2
          ((Finset.mem_filter.1 (mem_extensions_of_mem_support_uniformExtension hc hπ)).2 _ hp).symm
        rw [this]
        rfl
      | none =>
        dsimp only
        rw [bind_map_left]
        refine ((uniformExtension_evalDistEq_inverse hc hl).bind_left _).trans ?_
        rw [bind_assoc]
        refine EvalDistEq.bind_congr_of_support _ fun a ha => ?_
        have ha' := mem_of_mem_support_uniformFrom
          (List.ne_nil_of_mem (symm_apply_mem_outside hl hc.choose_spec)) _ ha
        have hne := extensions_cons_nonempty_inverse hc hl ha'
        refine (EvalDistEq.bind_congr_of_support _ fun π hπ => ?_).trans (ih a hne)
        have : π.symm b = a := (Equiv.symm_apply_eq π).2
          ((Finset.mem_filter.1 (mem_extensions_of_mem_support_uniformExtension hne hπ)).2 _
            List.mem_cons_self).symm
        rw [this]
        rfl

/-- Drawing a permutation that agrees with the cache and running with it is the lazy run.

The lazy run starts from the cache, and draws the permutation at the end from its final cache.

The joint law of the output and the permutation is the same.

The cache must have a permutation that agrees with it. -/
theorem uniformExtension_bind_simulateQ_permImpl_evalDistEq {α : Type}
    (oa : OracleComp (unifSpec + PermSpec A) α) {c : PermCache A}
    (hc : (extensions c).Nonempty) :
    (do
      let π ← uniformExtension c
      let a ← simulateQ (permImpl π) oa
      pure (a, π)) =ᵈ
    (do
      let (a, c') ← (simulateQ lazyPermImpl oa).run c
      let π ← uniformExtension c'
      pure (a, π)) := by
  refine (EvalDistEq.of_eq ?_).trans
    ((uniformExtension_bind_map_evalDistEq oa hc).trans (EvalDistEq.of_eq ?_)) <;> simp

/-- A uniform permutation is a uniform permutation that agrees with the empty cache. -/
theorem uniformSample_evalDistEq_uniformExtension_nil :
    ($ᵗ (Equiv.Perm A)) =ᵈ uniformExtension ([] : PermCache A) :=
  evalDistEq_of_forall_prEvent_eq_output fun π => by
    rw [SampleableType.prEvent_uniformSample_eq_singleton, uniformExtension,
      prEvent_uniformFrom_eq_of_mem (Finset.nodup_toList _) _ (by simp [extensions, Agrees])]
    rw [Finset.length_toList, extensions,
      Finset.filter_true_of_mem fun _ _ _ hp => absurd hp List.not_mem_nil, Finset.card_univ]

/-- Run with a uniform permutation drawn up front, and keep the output and the permutation.

The lazy run from the empty cache, with the permutation drawn at the end, has the same law. -/
theorem uniformSample_bind_simulateQ_permImpl_joint_evalDistEq {α : Type}
    (oa : OracleComp (unifSpec + PermSpec A) α) :
    (do
      let π ← $ᵗ (Equiv.Perm A)
      let a ← simulateQ (permImpl π) oa
      pure (a, π)) =ᵈ
    (do
      let (a, c') ← (simulateQ lazyPermImpl oa).run []
      let π ← uniformExtension c'
      pure (a, π)) :=
  (uniformSample_evalDistEq_uniformExtension_nil.bind_left _).trans
    (uniformExtension_bind_simulateQ_permImpl_evalDistEq oa extensions_nil_nonempty)

/-- A uniform permutation drawn up front gives the output law of the lazy run from no cache. -/
theorem uniformSample_bind_simulateQ_permImpl_evalDistEq {α : Type}
    (oa : OracleComp (unifSpec + PermSpec A) α) :
    (do
      let π ← $ᵗ (Equiv.Perm A)
      simulateQ (permImpl π) oa) =ᵈ
    (simulateQ lazyPermImpl oa).run' [] := by
  have hu := uniformSample_evalDistEq_uniformExtension_nil (A := A)
  calc (do let π ← $ᵗ (Equiv.Perm A); simulateQ (permImpl π) oa)
      =ᵈ (uniformExtension [] >>= fun π => simulateQ (permImpl π) oa) := hu.bind_left _
    _ = Prod.fst <$> (uniformExtension [] >>= fun π => (·, π) <$> simulateQ (permImpl π) oa) := by
        simp
    _ =ᵈ Prod.fst <$> ((simulateQ lazyPermImpl oa).run [] >>= fun z =>
        Prod.mk z.1 <$> uniformExtension z.2) :=
        (uniformExtension_bind_map_evalDistEq oa extensions_nil_nonempty).map _
    _ = ((simulateQ lazyPermImpl oa).run [] >>= fun z =>
        (fun _ => z.1) <$> uniformExtension z.2) := by simp
    _ =ᵈ ((simulateQ lazyPermImpl oa).run [] >>= fun z => pure z.1) :=
        EvalDistEq.bind_right _ fun z => EvalDistEq.map_const _ _
    _ = (simulateQ lazyPermImpl oa).run' [] := by simp

/-- The first forward query to the lazy oracle is uniform over `A`. -/
theorem prEvent_lazyPermOracle_forward_nil (a b : A) :
    Pr{let x ← (lazyPermOracle (.inl a) : StateT (PermCache A) ProbComp A).run' []}[x = b] =
      (FinEnum.card A : ℝ≥0∞)⁻¹ := by
  simp only [lazyPermOracle, StateT.run', uniformOutside, List.lookup_nil, List.map_nil,
    List.not_mem_nil, not_false_eq_true, decide_true, List.filter_true, Functor.map_map]
  refine (prEvent_uniformFrom_eq_of_mem FinEnum.nodup_toList a (FinEnum.mem_toList b)).trans ?_
  simp [FinEnum.toList]

/-- The first inverse query to the lazy oracle is uniform over `A`. -/
theorem prEvent_lazyPermOracle_inverse_nil (a b : A) :
    Pr{let x ← (lazyPermOracle (.inr b) : StateT (PermCache A) ProbComp A).run' []}[x = a] =
      (FinEnum.card A : ℝ≥0∞)⁻¹ := by
  simp only [lazyPermOracle, StateT.run', uniformOutside, List.map_nil, List.lookup_nil,
    List.not_mem_nil, not_false_eq_true, decide_true, List.filter_true, Functor.map_map]
  refine (prEvent_uniformFrom_eq_of_mem FinEnum.nodup_toList b (FinEnum.mem_toList a)).trans ?_
  simp [FinEnum.toList]

end EthLib.Cryptography.LazyPermutation
