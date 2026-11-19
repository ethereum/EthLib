module

public import EthLib.Cryptography.Proofs.BadOnGrowth
public import EthLib.Cryptography.Proofs.IndependentAnswers

/-!
# Proofs: collisions and preimages of one call to a random permutation

A hash of this shape encodes the message as a point of `A`, permutes it, and reads an output.

The permutation is uniform, and the adversary evaluates it and its inverse.

Collisions and preimages are then rare, and this file bounds them.

The run with the permutation drawn up front has the law of the lazy run from no cache.

So the bounds are union bounds over the pairs that the lazy run adds to its cache.

Let `N` be the size of `A`, and `Q` the number of calls to the permutation, counted with the game's.

Let each output be shared by at most `F` points, and the encodings lie in a set of at most `K`.

A collision has chance at most `(Q (Q - 1) / 2 * F + Q K) / (N - Q)`.

A preimage of a fixed output has chance at most `Q (F + K) / (N - Q)`.

A new forward call draws its image among the `N - k` points that are no image yet.

So it shares an output with one of the `k` earlier answers with chance at most `k F / (N - k)`.

A new inverse call draws its preimage among the `N - k` points that are no preimage yet.

So it lands among the encodings with chance at most `K / (N - k)`.

The preimage bound holds for every output, which is stronger than for a uniform output.

For `Q ≥ N` the denominators are zero and the bounds are trivial.
-/

@[expose] public section

namespace EthLib.Cryptography.LazyPermutation

open OracleComp OracleSpec ENNReal

variable {A M D : Type}

/-! ## The games -/

/-- A forward call to the permutation. -/
abbrev forward (a : A) : PermComp A A :=
  liftM ((unifSpec + PermSpec A).query (.inr (.inl a)))

/-- A forward call, simulated, is the answer of the oracle to it. -/
theorem simulateQ_forward {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (unifSpec + PermSpec A) m) (a : A) :
    simulateQ impl (forward a) = impl (.inr (.inl a)) :=
  simulateQ_spec_query (spec := unifSpec + PermSpec A) (impl := impl) (.inr (.inl a))

/-- The hash of a message: encode it, permute it, and read the output. -/
def oneCallHash (encode : M → A) (output : A → D) (π : A → A) (m : M) : D :=
  output (π (encode m))

/-- The chance that the adversary returns two messages with one hash.

The permutation is uniform, and the adversary evaluates it and its inverse. -/
noncomputable def collisionAdvantage [FinEnum A] (encode : M → A) (output : A → D)
    (adversary : PermComp A (M × M)) : ℝ≥0∞ :=
  Pr{let π ← $ᵗ (Equiv.Perm A); let r ← simulateQ (permImpl π) adversary}[
    r.1 ≠ r.2 ∧ oneCallHash encode output π r.1 = oneCallHash encode output π r.2]

/-- The chance that the adversary, given an output, returns a message that hashes to it. -/
noncomputable def preimageAdvantage [FinEnum A] (encode : M → A) (output : A → D)
    (adversary : D → PermComp A M) (d : D) : ℝ≥0∞ :=
  Pr{let π ← $ᵗ (Equiv.Perm A); let m ← simulateQ (permImpl π) (adversary d)}[
    oneCallHash encode output π m = d]

/-! ## One step of the lazy permutation -/

/-- A forward call through the permutation `π` returns `π a`. -/
theorem simulateQ_permImpl_forward (π : Equiv.Perm A) (a : A) :
    simulateQ (permImpl π) (forward a) = pure (π a) := by
  rw [simulateQ_forward]
  rfl

variable [FinEnum A]

/-- A forward call to the lazy permutation leaves `(a, b)` in the cache, which only grows. -/
theorem mem_of_mem_support_lazy_forward {a b : A} {c c' : PermCache A}
    (h : (b, c') ∈ support ((simulateQ lazyPermImpl (forward a)).run c)) :
    (a, b) ∈ c' ∧ c <:+ c' := by
  rw [simulateQ_forward, lazyPermImpl_inr, lazyPermOracle_inl_run] at h
  split at h
  · rename_i b' hl
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨mem_of_lookup_eq_some hl, List.suffix_refl _⟩
  · simp only [support_map, Set.mem_image, Prod.mk.injEq] at h
    obtain ⟨_, -, rfl, rfl⟩ := h
    exact ⟨List.mem_cons_self, List.suffix_cons _ _⟩

/-- A step of the lazy permutation adds a pair only on a call to the permutation. -/
theorem length_le_of_mem_support_lazyPermImpl (t : (unifSpec + PermSpec A).Domain)
    (c : PermCache A) (z) (hz : z ∈ support ((lazyPermImpl t).run c)) :
    z.2.length ≤ c.length + if t.isRight = true then 1 else 0 := by
  rcases t with n | a | b
  · rw [passthrough_add_inl_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    simp
  · rw [lazyPermImpl_inr, lazyPermOracle_inl_run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      simp [hz]
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      simp
  · rw [lazyPermImpl_inr, lazyPermOracle_inr_run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      simp [hz]
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      simp

/-- A forward call to the lazy permutation adds at most one pair. -/
theorem length_le_of_mem_support_lazy_forward {a b : A} {c c' : PermCache A}
    (h : (b, c') ∈ support ((simulateQ lazyPermImpl (forward a)).run c)) :
    c'.length ≤ c.length + 1 := by
  rw [simulateQ_forward] at h
  simpa using length_le_of_mem_support_lazyPermImpl _ c _ h

/-- A run with at most `Q` calls to the permutation leaves at most `Q` pairs in a fresh cache. -/
theorem length_le_of_mem_support_lazy {α : Type} {oa : PermComp A α} {Q : ℕ}
    (hQ : IsQueryBoundP oa (·.isRight = true) Q) :
    ∀ z ∈ support ((simulateQ lazyPermImpl oa).run []), z.2.length ≤ Q := by
  intro z hz
  have := hQ.cost_le_of_mem_support_run_simulateQ (impl := lazyPermImpl) List.length
    (fun t ht c w hw => by simpa [ht] using length_le_of_mem_support_lazyPermImpl t c w hw)
    (fun t ht c w hw => by simpa [ht] using length_le_of_mem_support_lazyPermImpl t c w hw)
    [] z hz
  simpa using this

/-! ## A union bound over the new pairs -/

/-- A uniform value outside a list lies in a finite set with chance at most a ratio.

Let `n` be the length of the list: the ratio is the size of the set over `|A| - n`. -/
theorem prEvent_uniformOutside_mem_finset_le (used : List A) (S : Finset A) (d : A) :
    Pr{let y ← uniformOutside used d}[y ∈ S] ≤
      (S.card : ℝ≥0∞) / ((FinEnum.card A - used.length : ℕ) : ℝ≥0∞) := by
  have h := prEvent_uniformOutside_mem_le used S.toList d
  rw [Finset.length_toList] at h
  exact (le_of_eq (prEvent_congr_of_support _ _ _ fun x _ => Finset.mem_toList.symm)).trans h

/-- A property of the cache that a new pair `(a, b)` creates only with `b` and `a` in two sets.

The first set has at most `F k` points and the second at most `K k`, for a cache of `k` pairs.

Then a new pair creates it with chance at most `F k + K k` over `|A| - k`. -/
theorem badOnGrowthBy_lazyPermImpl {bad : PermCache A → Prop} (out inp : PermCache A → Finset A)
    (hnew : ∀ c a b, ¬bad c → bad ((a, b) :: c) → b ∈ out c ∧ a ∈ inp c) {F K : ℕ → ℕ}
    (hout : ∀ c, (out c).card ≤ F c.length) (hinp : ∀ c, (inp c).card ≤ K c.length) :
    BadOnGrowthBy (lazyPermImpl (A := A)) List.length bad
      fun k => ((F k + K k : ℕ) : ℝ≥0∞) / ((FinEnum.card A - k : ℕ) : ℝ≥0∞) := by
  refine ⟨fun t c z hz => ?_, fun t c hc => ?_⟩
  · exact (List.IsSuffix.length_le (by
      rcases t with n | a | b
      · rw [passthrough_add_inl_run] at hz
        simp only [support_map, Set.mem_image] at hz
        obtain ⟨_, -, rfl⟩ := hz
        exact List.suffix_refl _
      · rw [lazyPermImpl_inr, lazyPermOracle_inl_run] at hz
        split at hz
        · simp only [support_pure, Set.mem_singleton_iff] at hz
          rw [hz]
        · simp only [support_map, Set.mem_image] at hz
          obtain ⟨_, -, rfl⟩ := hz
          exact List.suffix_cons _ _
      · rw [lazyPermImpl_inr, lazyPermOracle_inr_run] at hz
        split at hz
        · simp only [support_pure, Set.mem_singleton_iff] at hz
          rw [hz]
        · simp only [support_map, Set.mem_image] at hz
          obtain ⟨_, -, rfl⟩ := hz
          exact List.suffix_cons _ _))
  have hle (S : Finset A) (n : ℕ) (hS : S.card ≤ n) (used : List A) (hused : used.length = c.length)
      (d : A) :
      Pr{let y ← uniformOutside used d}[y ∈ S] ≤
        ((n : ℕ) : ℝ≥0∞) / ((FinEnum.card A - c.length : ℕ) : ℝ≥0∞) := by
    refine (prEvent_uniformOutside_mem_finset_le used S d).trans ?_
    rw [hused]
    exact ENNReal.div_le_div_right (by exact_mod_cast hS) _
  rcases t with n | a | b
  · left
    intro z hz
    rw [passthrough_add_inl_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact ⟨rfl, hc⟩
  · rw [lazyPermImpl_inr, lazyPermOracle_inl_run]
    cases c.lookup a with
    | some b => exact Or.inl fun z hz => by simp_all
    | none =>
      refine Or.inr ⟨fun z hz => ?_, ?_⟩
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨_, -, rfl⟩ := hz
        simp
      · rw [prEvent_map]
        refine (prEvent_mono _ _ (· ∈ out c) fun b hb => (hnew c a b hc hb).1).trans ?_
        exact hle _ _ ((hout c).trans (Nat.le_add_right _ _)) _ (List.length_map _) a
  · rw [lazyPermImpl_inr, lazyPermOracle_inr_run]
    cases (c.map Prod.swap).lookup b with
    | some a => exact Or.inl fun z hz => by simp_all
    | none =>
      refine Or.inr ⟨fun z hz => ?_, ?_⟩
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨_, -, rfl⟩ := hz
        simp
      · rw [prEvent_map]
        refine (prEvent_mono _ _ (· ∈ inp c) fun a ha => (hnew c a b hc ha).2).trans ?_
        exact hle _ _ ((hinp c).trans (Nat.le_add_left _ _)) _ (List.length_map _) b

omit [FinEnum A] in
/-- The terms of the union bound share the smallest denominator, `N - Q`. -/
theorem sum_range_div_le (G : ℕ → ℕ) (N Q : ℕ) :
    ∑ i ∈ Finset.range Q, ((G i : ℕ) : ℝ≥0∞) / ((N - i : ℕ) : ℝ≥0∞) ≤
      ((∑ i ∈ Finset.range Q, G i : ℕ) : ℝ≥0∞) / ((N - Q : ℕ) : ℝ≥0∞) := by
  rw [Nat.cast_sum, ENNReal.sum_div]
  refine Finset.sum_le_sum fun i hi => ENNReal.div_le_div_left ?_ _
  have := Finset.mem_range.1 hi
  exact_mod_cast Nat.sub_le_sub_left this.le N

/-- A run from no cache that leaves at most `Q` pairs ends with the property rarely.

Its chance is at most a sum over `k < Q` of `F k + K k`, divided by `|A| - Q`. -/
theorem prEvent_bad_lazy_le {α : Type} {oa : PermComp A α} {Q : ℕ}
    (hQ : ∀ z ∈ support ((simulateQ lazyPermImpl oa).run []), z.2.length ≤ Q)
    {bad : PermCache A → Prop} (hbad : ¬bad [])
    (out inp : PermCache A → Finset A)
    (hnew : ∀ c a b, ¬bad c → bad ((a, b) :: c) → b ∈ out c ∧ a ∈ inp c) {F K : ℕ → ℕ}
    (hout : ∀ c, (out c).card ≤ F c.length) (hinp : ∀ c, (inp c).card ≤ K c.length) :
    Pr{let z ← (simulateQ lazyPermImpl oa).run []}[bad z.2] ≤
      ((∑ i ∈ Finset.range Q, (F i + K i) : ℕ) : ℝ≥0∞) / ((FinEnum.card A - Q : ℕ) : ℝ≥0∞) := by
  refine ((badOnGrowthBy_lazyPermImpl out inp hnew hout hinp).prEvent_bad_le oa [] hbad
    hQ).trans ?_
  rw [List.length_nil, ← Finset.range_eq_Ico]
  exact sum_range_div_le (fun i => F i + K i) _ Q

/-! ## Collisions -/

section Collision

variable (Z : Finset A) (output : A → D)

/-- Two pairs of the cache with different points of `Z` as queries, and one output. -/
def CollidesIn (c : PermCache A) : Prop :=
  ∃ p ∈ c, ∃ p' ∈ c, p.1 ≠ p'.1 ∧ p.1 ∈ Z ∧ p'.1 ∈ Z ∧ output p.2 = output p'.2

/-- The points whose output is the output of an answer of the cache. -/
def sharedOutputs [DecidableEq D] (c : PermCache A) : Finset A :=
  c.toFinset.biUnion fun p => Finset.univ.filter fun b => output b = output p.2

omit [FinEnum A] in
/-- A collision appears with a new pair only when its query is in `Z` and its answer collides. -/
theorem collidesIn_cons {c : PermCache A} {a b : A} (hc : ¬CollidesIn Z output c)
    (h : CollidesIn Z output ((a, b) :: c)) :
    (∃ p ∈ c, output b = output p.2) ∧ a ∈ Z := by
  obtain ⟨p, hp, p', hp', hne, hpZ, hp'Z, ho⟩ := h
  rcases List.mem_cons.1 hp with rfl | hp <;> rcases List.mem_cons.1 hp' with rfl | hp'
  · exact absurd rfl hne
  · exact ⟨⟨p', hp', ho⟩, hpZ⟩
  · exact ⟨⟨p, hp, ho.symm⟩, hp'Z⟩
  · exact absurd ⟨p, hp, p', hp', hne, hpZ, hp'Z, ho⟩ hc

/-- At most `k F` points share an output with the `k` answers of a cache.

Here each output is shared by at most `F` points. -/
theorem card_sharedOutputs_le [DecidableEq D] {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x => output x = output y).card ≤ F) (c : PermCache A) :
    (sharedOutputs output c).card ≤ c.length * F := by
  unfold sharedOutputs
  refine (Finset.card_biUnion_le).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ F fun p _ => ?_).trans ?_
  · exact hF p.2
  · rw [smul_eq_mul]
    exact Nat.mul_le_mul_right _ (List.toFinset_card_le c)

/-- The game of collisions as one run: the adversary, then the two calls that hash its messages. -/
def collisionRun (encode : M → A) (adversary : PermComp A (M × M)) :
    PermComp A ((M × M) × A × A) := do
  let r ← adversary
  let y₁ ← forward (encode r.1)
  let y₂ ← forward (encode r.2)
  pure (r, y₁, y₂)

/-- The collision game, with a uniform permutation drawn up front, is the lazy run of its calls. -/
theorem collisionAdvantage_eq_lazy (encode : M → A) (adversary : PermComp A (M × M)) :
    collisionAdvantage encode output adversary =
      Pr{let z ← (simulateQ lazyPermImpl (collisionRun encode adversary)).run' []}[
        z.1.1 ≠ z.1.2 ∧ output z.2.1 = output z.2.2] := by
  have h := (uniformSample_bind_simulateQ_permImpl_evalDistEq
    (collisionRun encode adversary)).prEvent_eq
    (fun z => z.1.1 ≠ z.1.2 ∧ output z.2.1 = output z.2.2)
  rw [← h, collisionAdvantage]
  simp only [collisionRun, simulateQ_bind, simulateQ_permImpl_forward, simulateQ_pure, pure_bind,
    oneCallHash]
  simp

/-- The collision game adds at most two pairs to those of the adversary. -/
theorem length_le_of_mem_support_collisionRun (encode : M → A) {adversary : PermComp A (M × M)}
    {q : ℕ} (hq : IsQueryBoundP adversary (·.isRight = true) q) :
    ∀ z ∈ support ((simulateQ lazyPermImpl (collisionRun encode adversary)).run []),
      z.2.length ≤ q + 2 := by
  intro z hz
  simp only [collisionRun, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨⟨r, c₁⟩, h₀, ⟨y₁, c₂⟩, h₁, ⟨y₂, c₃⟩, h₂, rfl⟩ := hz
  have := length_le_of_mem_support_lazy hq _ h₀
  have := length_le_of_mem_support_lazy_forward h₁
  have := length_le_of_mem_support_lazy_forward h₂
  simp only at *
  omega

/-- **Collisions of one call to a random permutation.**

The encoding is injective, into a set `Z` of at most `K` points.

Each output is shared by at most `F` points, and `|A| = N`.

An adversary with at most `q` calls to the permutation and its inverse finds a collision.

Its chance is at most `(Q (Q - 1) / 2 * F + Q K) / (N - Q)`, with `Q = q + 2`.

The two calls that hash its messages count in `Q`. -/
theorem collisionAdvantage_le [DecidableEq D] (encode : M → A) (henc : Function.Injective encode)
    (hZ : ∀ m, encode m ∈ Z) {K : ℕ} (hK : Z.card ≤ K) {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x => output x = output y).card ≤ F)
    (adversary : PermComp A (M × M)) {q : ℕ}
    (hq : IsQueryBoundP adversary (·.isRight = true) q) :
    collisionAdvantage encode output adversary ≤
      (((q + 2).choose 2 * F + (q + 2) * K : ℕ) : ℝ≥0∞) /
        ((FinEnum.card A - (q + 2) : ℕ) : ℝ≥0∞) := by
  rw [collisionAdvantage_eq_lazy, StateT.run'_eq, prEvent_map]
  refine (prEvent_mono_of_support _ _ (fun z => CollidesIn Z output z.2) fun z hz h => ?_).trans ?_
  · simp only [collisionRun, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨⟨r, c₁⟩, -, ⟨y₁, c₂⟩, h₁, ⟨y₂, c₃⟩, h₂, rfl⟩ := hz
    obtain ⟨hm₁, -⟩ := mem_of_mem_support_lazy_forward h₁
    obtain ⟨hm₂, hs⟩ := mem_of_mem_support_lazy_forward h₂
    exact ⟨(encode r.1, y₁), hs.subset hm₁, (encode r.2, y₂), hm₂, fun he => h.1 (henc he),
      hZ _, hZ _, h.2⟩
  · refine (prEvent_bad_lazy_le (length_le_of_mem_support_collisionRun encode hq)
      (by simp [CollidesIn])
      (sharedOutputs output) (fun _ => Z) (fun c a b hc hb => ?_)
      (card_sharedOutputs_le output hF) (fun _ => hK) (F := fun k => k * F)
      (K := fun _ => K)).trans (le_of_eq ?_)
    · obtain ⟨⟨p, hp, ho⟩, ha⟩ := collidesIn_cons Z output hc hb
      refine ⟨?_, ha⟩
      unfold sharedOutputs
      exact Finset.mem_biUnion.2 ⟨p, List.mem_toFinset.2 hp, by simp [ho]⟩
    · congr 2
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_range_id, Finset.sum_const,
        Finset.card_range, smul_eq_mul, Nat.choose_two_right]

end Collision

/-! ## Preimages -/

section Preimage

variable (Z : Finset A) (output : A → D)

/-- A pair of the cache with a point of `Z` as query and an answer of output `d`. -/
def HitsIn (d : D) (c : PermCache A) : Prop :=
  ∃ p ∈ c, p.1 ∈ Z ∧ output p.2 = d

/-- The game of preimages as one run: the adversary, then the call that hashes its message. -/
def preimageRun (encode : M → A) (adversary : D → PermComp A M) (d : D) :
    PermComp A (M × A) := do
  let m ← adversary d
  let y ← forward (encode m)
  pure (m, y)

/-- The preimage game, with a uniform permutation drawn up front, is the lazy run of its calls. -/
theorem preimageAdvantage_eq_lazy (encode : M → A) (adversary : D → PermComp A M) (d : D) :
    preimageAdvantage encode output adversary d =
      Pr{let z ← (simulateQ lazyPermImpl (preimageRun encode adversary d)).run' []}[
        output z.2 = d] := by
  have h := (uniformSample_bind_simulateQ_permImpl_evalDistEq
    (preimageRun encode adversary d)).prEvent_eq (fun z => output z.2 = d)
  rw [← h, preimageAdvantage]
  simp only [preimageRun, simulateQ_bind, simulateQ_permImpl_forward, simulateQ_pure, pure_bind,
    oneCallHash]
  simp

/-- The preimage game adds at most one pair to those of the adversary. -/
theorem length_le_of_mem_support_preimageRun (encode : M → A) {adversary : D → PermComp A M}
    {q : ℕ} (d : D) (hq : IsQueryBoundP (adversary d) (·.isRight = true) q) :
    ∀ z ∈ support ((simulateQ lazyPermImpl (preimageRun encode adversary d)).run []),
      z.2.length ≤ q + 1 := by
  intro z hz
  simp only [preimageRun, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨⟨m, c₁⟩, h₀, ⟨y, c₂⟩, h₁, rfl⟩ := hz
  have := length_le_of_mem_support_lazy hq _ h₀
  have := length_le_of_mem_support_lazy_forward h₁
  simp only at *
  omega

/-- **Preimages of one call to a random permutation.**

The encoding lies in a set `Z` of at most `K` points.

Each output is shared by at most `F` points, and `|A| = N`.

An adversary with at most `q` calls to the permutation and its inverse gets an output `d`.

It returns a message that hashes to `d` with chance at most `Q (F + K) / (N - Q)`, with `Q = q + 1`.

The call that hashes its message counts in `Q`. -/
theorem preimageAdvantage_le [DecidableEq D] (encode : M → A) (hZ : ∀ m, encode m ∈ Z) {K : ℕ}
    (hK : Z.card ≤ K) {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x => output x = output y).card ≤ F)
    (adversary : D → PermComp A M) (d : D) {q : ℕ}
    (hq : IsQueryBoundP (adversary d) (·.isRight = true) q) :
    preimageAdvantage encode output adversary d ≤
      (((q + 1) * (F + K) : ℕ) : ℝ≥0∞) / ((FinEnum.card A - (q + 1) : ℕ) : ℝ≥0∞) := by
  rw [preimageAdvantage_eq_lazy, StateT.run'_eq, prEvent_map]
  refine (prEvent_mono_of_support _ _ (fun z => HitsIn Z output d z.2) fun z hz h => ?_).trans ?_
  · simp only [preimageRun, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨⟨m, c₁⟩, -, ⟨y, c₂⟩, h₁, rfl⟩ := hz
    exact ⟨_, (mem_of_mem_support_lazy_forward h₁).1, hZ m, h⟩
  · refine (prEvent_bad_lazy_le (length_le_of_mem_support_preimageRun encode d hq)
      (by simp [HitsIn])
      (fun _ => Finset.univ.filter fun x => output x = d) (fun _ => Z)
      (fun c a b hc hb => ?_) (F := fun _ => F) (K := fun _ => K) (fun _ => ?_)
      (fun _ => hK)).trans (le_of_eq ?_)
    · obtain ⟨p, hp, hpZ, ho⟩ := hb
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨by simpa using ho, hpZ⟩
      · exact absurd ⟨p, hp, hpZ, ho⟩ hc
    · by_cases hd : ∃ y, output y = d
      · obtain ⟨y, rfl⟩ := hd
        exact hF y
      · push Not at hd
        simp [Finset.filter_false_of_mem fun x _ => hd x]
    · rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end Preimage

end EthLib.Cryptography.LazyPermutation
