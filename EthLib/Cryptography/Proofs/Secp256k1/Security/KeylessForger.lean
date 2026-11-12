module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.Keyless
public import EthLib.Cryptography.Proofs.Secp256k1.Security.KeyOnlyOutside
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# Proofs: a key-only forger from a chosen-message forger

The game with the signer that has no key never reads the key `x`, only `X = x g`.

So a key-only forger can run it, with its own oracle of `Π` in place of the lazy permutation.

It answers the queries of `Π` through the overlay, which relays new queries to its oracle.

It answers the signing queries with the signer that has no key, which programs the overlay.

It returns the forgery and leaves the check to the key-only game.

The game with the signer that has no key checks the forgery through the overlay.

The key-only game checks it through `Π` directly.

The two checks agree unless the most recent pair at the forgery's point is programmed.

That case gives the key.

Let the pair come from a nonce on the message `m'`, with `t = ψ(β)` and `U' = H(m') g + t X`.

When `U'` is `0`, the key is `-H(m') / t`.

Otherwise the point is `U' / c`, and the nonce signed `m'` with `(t, ±c)`.

The forgery `(m, t, s)` then has `(H(m) + x t) / s = ±(H(m') + x t) / c`.

That gives the key, unless `±s = c`.

Then `m` and `m'` have one hash, and `m'` was signed, which a win with no collision excludes.

The solver below tries each candidate for the key, and keeps the one that gives `X`.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The forger is their `F₀` of Figure 6.

Their line 30 signs the forgery's message with that key, by the signing of Figure 3, which may fail.

So their claim that `F₀` wins as often as the forger in Game G3 does not hold exactly.

Here the case of a programmed point is charged to a solver of the discrete logarithm instead.

That adds one term to the bound of their Theorem 1.

The solver runs the game with the signer that has no key, with the lazy permutation.

No theorem states the running time of the forger or of the solver.

Both run up to `fuel` nonces per signing query, and the solver also samples `Π` lazily.

The forger here also leaves out the aborts of their Figure 6, at lines 06, 12, 16 to 18, 21 and 26.

It returns every forgery, and the key-only game checks it.

That can only raise its chance to win, and the key-only check covers lines 18, 21 and 26.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

variable [Field F] [AddCommGroup G] [Module F G]

/-! ## The candidates for the key -/

/-- The candidates for the key from a forgery `(m, t, s)` and a signing cache.

Each message `m'` of the cache gives `-H(m') / t`.

Each signature `(t', s')` on `m'`, read with `t' = t`, also gives two candidates.

They solve `(H(m) + x t) / s = η (H(m') + x t) / s'`, for the signs `η = 1` and `η = -1`.

They are the keys from `(m, t, s)` and `(m', t, s')` on one point, for those signs.

When `η s'` is `s`, the division by `0` makes the candidate `-H(m) / t`.

That is harmless, since the solver keeps only a candidate that gives the public key. -/
def keyCandidates (scheme : Scheme F G A M) (m : M) (t s : F) (cache : Cache F M) : List F :=
  cache.flatMap fun e =>
    -scheme.hash e.1 / t :: match e.2 with
      | some (_, s') =>
        [forwardKey scheme (m, t, s) (e.1, t, s') 1, forwardKey scheme (m, t, s) (e.1, t, s') (-1)]
      | none => []

/-- A programmed pair `(a, β)` that a nonce on `m` could record, when signing `m` answered `σ`.

Let `t = ψ(β)` and `U = H(m) g + t X`.

Either `U` is `0`, or `a` encodes `U / c` for a nonzero `c`.

Then, when `t` is nonzero, the answer was `(t, c)` in normal form. -/
private def NonceOrigin (scheme : Scheme F G A M) (X : G) (m : M) (σ : Option (F × F))
    (a β : A) : Prop :=
  scheme.hash m • scheme.g + scheme.reduce β • X = 0 ∨
    ∃ c ≠ 0, a = scheme.encode (c⁻¹ • (scheme.hash m • scheme.g + scheme.reduce β • X)) ∧
      (scheme.reduce β ≠ 0 → σ = some (scheme.reduce β, scheme.normalize c))

/-- A forgery that passes at a programmed point gives the key among the candidates.

The pair at the point has its origin in a message of the signing cache.

The forged message has no signature, and no signed message shares its hash. -/
private theorem mem_keyCandidates [DecidableEq F] [DecidableEq M] {scheme : Scheme F G A M}
    (hg : scheme.g ≠ 0) (hsemi : scheme.SemiInjective) (hnorm : scheme.NormalizeSign)
    {x t s : F} {m m' : M} {cache : Cache F M} {σ' : Option (F × F)} {β : A} (ht : t ≠ 0)
    (hs : s ≠ 0) (hU : scheme.hash m • scheme.g + t • x • scheme.g ≠ 0)
    (hβ : scheme.reduce β = t) (hm' : cache.lookup m' = some σ')
    (ho : NonceOrigin scheme (x • scheme.g) m' σ' (forgeryPoint scheme (x • scheme.g) (m, t, s)) β)
    (hsig : signed cache m = false) (hcol : collisionOf scheme cache m = none) :
    x ∈ keyCandidates scheme m t s cache := by
  have hmem : (m', σ') ∈ cache := by
    obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 hm'
    simp
  have hsmul (h : F) : h • scheme.g + t • x • scheme.g = (h + t * x) • scheme.g := by
    rw [smul_smul, add_smul]
  have hu : scheme.hash m + t * x ≠ 0 := fun h0 => hU (by rw [hsmul, h0, zero_smul])
  simp only [keyCandidates, List.mem_flatMap]
  refine ⟨(m', σ'), hmem, ?_⟩
  unfold NonceOrigin at ho
  rw [hβ] at ho
  by_cases hu' : scheme.hash m' + t * x = 0
  · refine List.mem_cons.2 (Or.inl ?_)
    field_simp
    linear_combination hu'
  rcases ho with h0 | ⟨c, hc, hP, hσ⟩
  · exact absurd ((smul_eq_zero.1 (by rwa [hsmul] at h0)).resolve_right hg) hu'
  obtain rfl := hσ ht
  have hh : scheme.hash m ≠ scheme.hash m' := by
    intro hh
    have hne : m' ≠ m := by
      rintro rfl
      simp [signed, hm'] at hsig
    refine absurd hcol ?_
    simp only [collisionOf, Option.map_eq_none_iff, List.find?_eq_none]
    intro h
    exact h _ hmem (by simp [hne, hh])
  rw [forgeryPoint_smul, hsmul, smul_smul] at hP
  have hs' : scheme.normalize c ≠ 0 := by
    rcases hnorm c with hn | hn <;> rw [hn]
    exacts [hc, neg_ne_zero.2 hc]
  have key : (scheme.normalize c)⁻¹ * (scheme.hash m' + t * x) =
        1 * (s⁻¹ * (scheme.hash m + t * x)) ∨
      (scheme.normalize c)⁻¹ * (scheme.hash m' + t * x) =
        -1 * (s⁻¹ * (scheme.hash m + t * x)) := by
    rcases scheme.eq_or_eq_neg_of_encode_smul_eq hsemi hg (mul_ne_zero (inv_ne_zero hc) hu')
      (mul_ne_zero (inv_ne_zero hs) hu) hP with he | he <;> rcases hnorm c with hn | hn <;>
      rw [hn] <;> (try rw [inv_neg]) <;>
      first
      | exact Or.inl (by linear_combination -he)
      | exact Or.inr (by linear_combination he)
  have hdiv : scheme.hash m / t ≠ scheme.hash m' / t := fun h => hh ((div_left_inj' ht).1 h)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases key with k | k
  · exact Or.inr (Or.inl (forwardKey_eq_of (scheme := scheme) (z := (m, t, s))
      (z' := (m', t, scheme.normalize c)) ht hs ht hs' k hdiv).symm)
  · exact Or.inr (Or.inr (forwardKey_eq_of (scheme := scheme) (z := (m, t, s))
      (z' := (m', t, scheme.normalize c)) ht hs ht hs' k hdiv).symm)

/-- The first candidate `c` with `c g = x g` is `x`, when `x` is a candidate. -/
private theorem find?_getD_eq [DecidableEq G] {scheme : Scheme F G A M} (hg : scheme.g ≠ 0)
    {x : F} {l : List F} (h : x ∈ l) :
    (l.find? fun c => decide (c • scheme.g = x • scheme.g)).getD 0 = x := by
  have hsome : (l.find? fun c => decide (c • scheme.g = x • scheme.g)).isSome :=
    List.find?_isSome.2 ⟨x, h, by simp⟩
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hsome
  have hcx := List.find?_some hc
  simp only [decide_eq_true_eq] at hcx
  rw [hc, Option.getD_some]
  exact smul_left_injective F hg hcx

/-! ## Where the programmed pairs come from -/

/-- Each programmed pair has its origin in a message of the signing cache, with its answer. -/
private def KeylessOrigin [DecidableEq M] (scheme : Scheme F G A M) (X : G)
    (s : JointState F M (ProgrammedCache A × PermCache A)) : Prop :=
  ∀ e ∈ s.2.1, e.2 = true →
    ∃ m' σ', s.1.lookup m' = some σ' ∧ NonceOrigin scheme X m' σ' e.1.1 e.1.2

/-- A query to the overlay adds no programmed pair, so it keeps the origins. -/
private theorem keylessOrigin_of_overlay [FinEnum A] [DecidableEq M] {scheme : Scheme F G A M}
    {X : G} {cache : Cache F M} {pc : ProgrammedCache A} {l : PermCache A} {q : (PermSpec A).Domain}
    {z}
    (horig : KeylessOrigin scheme X (cache, (pc, l)))
    (hz : z ∈ support ((fun w => (w.1, (cache, w.2))) <$> (overlayLazyOracle q).run (pc, l))) :
    KeylessOrigin scheme X z.2 := by
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  intro e he ht
  rcases overlayLazyOracle_step q (pc, l) w hw with h | ⟨p, h₁, -⟩
  · rw [h] at he
    exact horig e he ht
  · change e ∈ w.2.1 at he
    rw [h₁] at he
    rcases List.mem_cons.1 he with rfl | he
    · simp at ht
    · exact horig e he ht

variable [DecidableEq F] [DecidableEq G] [FinEnum A] [SampleableType F]

/-- One nonce adds at most one pair, programmed, with its origin in the message.

The origin holds for every answer when the nonce fails, and for its own answer otherwise. -/
private theorem keylessNonce_origin (scheme : Scheme F G A M) (X : G) (m : M)
    (pc : ProgrammedCache A) (z) (hz : z ∈ support ((keylessNonce scheme X m).run pc)) :
    ∃ new, z.2 = new ++ pc ∧ ∀ e ∈ new, e.2 = true ∧
      ∀ σ, (z.1 = none ∨ σ = z.1) → NonceOrigin scheme X m σ e.1.1 e.1.2 := by
  simp only [keylessNonce, StateT.run, support_bind, Set.mem_iUnion] at hz
  obtain ⟨c, -, hc⟩ := hz
  split_ifs at hc with hc0
  · simp only [support_pure, Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨[], rfl, by simp⟩
  · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hc
    obtain ⟨β, -, rfl⟩ := hc
    refine ⟨[_], rfl, ?_⟩
    simp only [List.mem_singleton, forall_eq, true_and]
    intro σ hσ
    by_cases hU : scheme.hash m • scheme.g + scheme.reduce β • X = 0
    · exact Or.inl hU
    · refine Or.inr ⟨c, hc0, by simp [hU], fun ht => ?_⟩
      simpa [ht, hU] using hσ

/-- The signer with no key adds programmed pairs only, each with its origin in the message. -/
private theorem keylessSign_origin (scheme : Scheme F G A M) (X : G) (m : M) (fuel : ℕ)
    (pc : ProgrammedCache A) (z) (hz : z ∈ support ((keylessSign scheme X m fuel).run pc)) :
    ∃ new, z.2 = new ++ pc ∧ ∀ e ∈ new, e.2 = true ∧ NonceOrigin scheme X m z.1 e.1.1 e.1.2 := by
  induction fuel generalizing pc z with
  | zero =>
    simp only [keylessSign, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨[], rfl, by simp⟩
  | succ n ih =>
    simp only [keylessSign, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨w, hw, hz⟩ := hz
    obtain ⟨new₁, h₁, hnew₁⟩ := keylessNonce_origin scheme X m pc w hw
    rcases w with ⟨_ | σ, pc₁⟩ <;> dsimp only at h₁ hnew₁ hz
    · obtain ⟨new₂, h₂, hnew₂⟩ := ih pc₁ z hz
      refine ⟨new₂ ++ new₁, by rw [h₂, h₁, List.append_assoc], fun e he => ?_⟩
      rcases List.mem_append.1 he with he | he
      · exact hnew₂ e he
      · exact ⟨(hnew₁ e he).1, (hnew₁ e he).2 _ (Or.inl rfl)⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨new₁, h₁, fun e he => ⟨(hnew₁ e he).1, (hnew₁ e he).2 _ (Or.inr rfl)⟩⟩

variable [DecidableEq M]

/-! ## The key-only forger -/

/-- The oracles that the key-only forger gives the chosen-message forger, on the key `X`.

The state is the signing cache and the cache of the overlay.

Coins pass to the coins of the key-only forger.

`Π` and its inverse go through the overlay, which relays new queries to the oracle of `Π`.

A repeated message gets the answer it got first.

A new message goes to the signer with no key, and its answer joins the signing cache.

These are the joint oracles over the oracle of `Π`, with the overlay and that signer. -/
def forgerImpl (scheme : Scheme F G A M) (X : G) (fuel : ℕ) :
    QueryImpl (Spec F A M) (StateT (JointState F M (ProgrammedCache A)) (PermComp A)) :=
  jointImpl overlayPermOracle fun m pc => liftM ((keylessSign scheme X m fuel).run pc)

/-- The key-only forger built from a chosen-message forger, after `F₀` of Figure 6 of the source.

It runs the chosen-message forger on its key, with the oracles above from empty caches.

It returns the forgery. -/
def keylessForger (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    KeyOnlyAdversary F G A M where
  main X := Prod.fst <$> (simulateQ (forgerImpl scheme X fuel) (adversary.main X)).run ([], [])

/-- Each oracle of the key-only forger asks for `Π` at most once, and only for a query of `Π`. -/
private theorem isQueryBoundP_forgerImpl (scheme : Scheme F G A M) (X : G) (fuel : ℕ)
    (t : (Spec F A M).Domain) (s : JointState F M (ProgrammedCache A)) :
    IsQueryBoundP ((forgerImpl scheme X fuel t).run s) (·.isRight = true)
      (if isPermQuery t = true then 1 else 0) := by
  obtain ⟨cache, c⟩ := s
  rcases t with n | α | β | m
  · simp only [forgerImpl, jointImpl, isPermQuery, StateT.run, Bool.false_eq_true, ite_false,
      isQueryBoundP_map_iff]
    exact isQueryBoundP_liftM_permComp _
  · simp only [forgerImpl, jointImpl, isPermQuery, StateT.run, ite_true, isQueryBoundP_map_iff]
    change IsQueryBoundP (match (TaggedCache.untag c).lookup α with
      | some b => pure (b, c)
      | none => (fun b => (b, ((α, b), false) :: c)) <$>
        query (spec := unifSpec + PermSpec A) (.inr (.inl α))) _ 1
    split <;> simp [isQueryBoundP_query_iff]
  · simp only [forgerImpl, jointImpl, isPermQuery, StateT.run, ite_true, isQueryBoundP_map_iff]
    change IsQueryBoundP (match ((TaggedCache.untag c).map Prod.swap).lookup β with
      | some a => pure (a, c)
      | none => (fun a => (a, ((a, β), false) :: c)) <$>
        query (spec := unifSpec + PermSpec A) (.inr (.inr β))) _ 1
    split <;> simp [isQueryBoundP_query_iff]
  · simp only [forgerImpl, jointImpl, isPermQuery, StateT.run, Bool.false_eq_true, ite_false]
    split
    · simp
    · rw [isQueryBoundP_map_iff]
      exact isQueryBoundP_liftM_permComp _

/-- The key-only forger asks for `Π` or its inverse at most as often as the forger it runs.

That forger asks for them at most `qPerm` times, on every key. -/
theorem isQueryBoundP_keylessForger (scheme : Scheme F G A M) (fuel : ℕ)
    (adversary : Adversary F G A M) {qPerm : ℕ}
    (hPerm : ∀ X, IsQueryBoundP (adversary.main X) (isPermQuery · = true) qPerm) (X : G) :
    IsQueryBoundP ((keylessForger scheme fuel adversary).main X) (·.isRight = true) qPerm := by
  have h := isQueryBoundP_simulateQ_run_of_weighted_step (w := 0)
    (p := fun t => isPermQuery t = true) (r := fun t => isPermQuery t = true)
    (q := fun t : (unifSpec + PermSpec A).Domain => t.isRight = true) (hPerm X) (hPerm X)
    (fun t s => (isQueryBoundP_forgerImpl scheme X fuel t s).mono (by simp)) ([], [])
  rw [keylessForger, isQueryBoundP_map_iff]
  simpa using h

/-! ## The solver for a programmed point -/

/-- The solver of the discrete logarithm for a forgery on a programmed point.

It runs the game with the signer that has no key on its instance `X`, with the lazy permutation.

It reads the base point of the scheme, not its first argument.

It returns the first candidate `c` for the key with `c g = X`, or `0` when there is none. -/
def keylessSolver (scheme : Scheme F G A M) (fuel : ℕ) (adversary : Adversary F G A M) :
    DiffieHellman.DLogAdversary F G := fun _ X => do
  let z ← (simulateQ (jointImpl overlayLazyOracle (keylessFresh scheme X fuel))
    (runWithCheck scheme adversary X)).run ([], ([], []))
  pure <| ((keyCandidates scheme z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.2.1).find?
    fun c => decide (c • scheme.g = X)).getD 0

/-! ## The run of the key-only forger against the lazy permutation -/

/-- Run the key-only forger's oracles against the lazy permutation.

That is the run with the joint oracles of the game with the signer that has no key. -/
private theorem map_run_lazy_forgerImpl (scheme : Scheme F G A M) (X : G) (fuel : ℕ) {α : Type}
    (oa : OracleComp (Spec F A M) α) (cache : Cache F M) (pc : ProgrammedCache A)
    (l : PermCache A) :
    (fun y => (y.1.1, (y.1.2.1, (y.1.2.2, y.2)))) <$>
        (simulateQ lazyPermImpl ((simulateQ (forgerImpl scheme X fuel) oa).run (cache, pc))).run l =
      (simulateQ (jointImpl overlayLazyOracle (keylessFresh scheme X fuel)) oa).run
        (cache, (pc, l)) :=
  map_run_simulateQ_jointImpl lazyPermOracle _ _ _ _ (fun _ _ _ => rfl) (fun m pc l => by
    change (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ lazyPermImpl
      (liftM ((keylessSign scheme X m fuel).run pc) : PermComp A _)).run l = _
    rw [simulateQ_lazyPermImpl_liftM_run]
    simp only [Functor.map_map]
    rfl) oa cache pc l

/-! ## The invariant of the game with the signer that has no key -/

/-- The cache of the lazy permutation holds the relayed pairs. -/
private theorem preservesInv_keylessRelayed (scheme : Scheme F G A M) (X : G) (fuel : ℕ) :
    QueryImpl.PreservesInv (jointImpl overlayLazyOracle (keylessFresh scheme X fuel))
      fun s => s.2.2 = s.2.1.relayed :=
  preservesInv_jointImpl preservesInv_overlayLazyOracle_relayed fun m s hs z hz => by
    simp only [keylessFresh, StateT.run, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨new, hnew, hall⟩ := keylessSign_origin scheme X m fuel s.1 w hw
    dsimp only
    rw [hnew, ProgrammedCache.relayed_append_of_forall fun e he => (hall e he).1, hs]

/-- Each programmed pair keeps its origin in a message of the signing cache. -/
private theorem preservesInv_keylessOrigin (scheme : Scheme F G A M) (X : G) (fuel : ℕ) :
    QueryImpl.PreservesInv (jointImpl overlayLazyOracle (keylessFresh scheme X fuel))
      (KeylessOrigin scheme X) := by
  rintro q ⟨cache, pc, l⟩ horig z hz
  rcases q with n | α | β | m
  · change z ∈ support ((·, (cache, (pc, l))) <$>
      (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact horig
  · exact keylessOrigin_of_overlay (q := .inl α) horig hz
  · exact keylessOrigin_of_overlay (q := .inr β) horig hz
  · change z ∈ support (match cache.lookup m with
        | some a => pure (a, (cache, (pc, l)))
        | none => (fun w : Option (F × F) × (ProgrammedCache A × PermCache A) =>
            (w.1, (cache ++ [(m, w.1)], w.2))) <$>
          ((fun w : Option (F × F) × ProgrammedCache A => (w.1, (w.2, l))) <$>
            (keylessSign scheme X m fuel).run pc)) at hz
    rcases h : cache.lookup m with _ | a <;> rw [h] at hz
    · simp only [Functor.map_map, support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨new, hnew, hall⟩ := keylessSign_origin scheme X m fuel pc w hw
      intro e he ht
      dsimp only at he ⊢
      rw [hnew] at he
      rcases List.mem_append.1 he with he | he
      · exact ⟨m, w.1, by simp [List.lookup_append, h], (hall e he).2⟩
      · obtain ⟨m', σ', hm', ho⟩ := horig e he ht
        exact ⟨m', σ', by simp [List.lookup_append, hm'], ho⟩
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact horig

/-! ## The key from a forgery on a programmed point -/

/-- **A win on one key is charged to the key-only forger and to the solver, on that key.** -/
private theorem prEvent_win_le_of_key {scheme : Scheme F G A M} (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) (hnorm : scheme.NormalizeSign) (fuel : ℕ)
    (adversary : Adversary F G A M) (x : F) :
    Pr{let z ← (simulateQ (jointImpl overlayLazyOracle (keylessFresh scheme (x • scheme.g) fuel))
        (runWithCheck scheme adversary (x • scheme.g))).run ([], ([], []))}[
          ProgrammedWin scheme z] ≤
      Pr{let z ← (simulateQ lazyPermImpl
        (keyOnlyRunQ scheme (keylessForger scheme fuel adversary) (x • scheme.g))).run []}[
          z.1.2 = true] +
      Pr{let z ← (simulateQ (jointImpl overlayLazyOracle (keylessFresh scheme (x • scheme.g) fuel))
        (runWithCheck scheme adversary (x • scheme.g))).run ([], ([], []))}[
          ((keyCandidates scheme z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.2.1).find?
            fun c => decide (c • scheme.g = x • scheme.g)).getD 0 = x] := by
  set X := x • scheme.g with hX
  set D := (simulateQ lazyPermImpl
    ((simulateQ (forgerImpl scheme X fuel) (adversary.main X)).run ([], []))).run [] with hD
  have hKL : (simulateQ (jointImpl overlayLazyOracle (keylessFresh scheme X fuel))
      (runWithCheck scheme adversary X)).run ([], ([], [])) = D >>= fun y =>
        (fun w => ((y.1.1, w.1), (y.1.2.1, w.2))) <$>
          (simulateQ (unifSpec.passthrough + overlayLazyOracle)
            (verifyQ scheme X y.1.1.1 y.1.1.2.1 y.1.1.2.2)).run (y.1.2.2, y.2) := by
    rw [runWithCheck, simulateQ_bind, StateT.run_bind, ← map_run_lazy_forgerImpl, bind_map_left]
    refine bind_congr fun y => ?_
    rw [simulateQ_bind, StateT.run_bind, simulateQ_jointImpl_keyOnlyLift_run, bind_map_left]
    simp
  have hKO : (simulateQ lazyPermImpl
      (keyOnlyRunQ scheme (keylessForger scheme fuel adversary) X)).run [] = D >>= fun y =>
        (fun w => ((y.1.1, w.1), w.2)) <$>
          (simulateQ lazyPermImpl (verifyQ scheme X y.1.1.1 y.1.1.2.1 y.1.1.2.2)).run y.2 := by
    rw [keyOnlyRunQ, simulateQ_bind, StateT.run_bind, keylessForger]
    simp only [simulateQ_map, StateT.run_map, bind_map_left]
    refine bind_congr fun y => ?_
    simp
  rw [hKL, hKO]
  refine prEvent_bind_le_add_of_forall_le_of_support _ _ _ _ _ _ _ fun y hy => ?_
  have hinv : y.2 = y.1.2.2.relayed ∧ KeylessOrigin scheme X (y.1.2.1, (y.1.2.2, y.2)) := by
    refine simulateQ_run_preservesInv _ _ ((preservesInv_keylessRelayed scheme X fuel).and
      (preservesInv_keylessOrigin scheme X fuel)) (adversary.main X) ([], ([], []))
      ⟨rfl, by simp [KeylessOrigin]⟩ (y.1.1, (y.1.2.1, (y.1.2.2, y.2))) ?_
    rw [← map_run_lazy_forgerImpl, support_map]
    exact ⟨y, hy, rfl⟩
  obtain ⟨⟨⟨m, t, s⟩, cache, pc⟩, l⟩ := y
  obtain ⟨hrel, horig⟩ := hinv
  dsimp only at hrel horig ⊢
  subst hrel
  rw [simulateQ_verifyQ_run, simulateQ_verifyQ_run]
  set P := scheme.encode (s⁻¹ • (scheme.hash m • scheme.g + t • X))
  split_ifs with hguard
  · by_cases hprog : ∃ b, pc.lookupTagged P = some (b, true)
    · obtain ⟨β, hβ⟩ := hprog
      have hl : (TaggedCache.untag pc).lookup P = some β := by
        rw [← TaggedCache.map_fst_lookupTagged, hβ]
        rfl
      rw [overlayLazyOracle_inl_run, hl]
      refine le_add_left (prEvent_mono_of_support _ _ _ fun w hw hwin => ?_)
      simp only [map_pure, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      obtain ⟨hsig, hb, hcol⟩ := hwin
      dsimp only at hsig hb hcol ⊢
      obtain ⟨m', σ', hm', ho⟩ := horig _ (TaggedCache.mem_of_lookupTagged_eq_some hβ) rfl
      exact find?_getD_eq hg (mem_keyCandidates hg hsemi hnorm hguard.2.1 hguard.2.2.1
        hguard.2.2.2 (by simpa using hb) hm' ho hsig hcol)
    · simp only [not_exists] at hprog
      refine le_add_right ((prEvent_mono _ _ _ fun w hw => hw.2.1).trans (le_of_eq ?_))
      have h := congrArg (fun c => Pr{let a ← c}[decide (scheme.reduce a = t) = true])
        (map_fst_overlayLazyOracle_inl hprog)
      simp only [prEvent_map] at h ⊢
      exact h
  · refine le_trans (le_of_eq ((prEvent_eq_zero_iff _ _).2 fun w hw h => ?_)) zero_le
    simp only [map_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    simp [ProgrammedWin] at h

/-- **A win with no collision, with the signer that has no key, is charged to two adversaries.**

The first is the key-only forger above, in the key-only game.

The second is the solver above, in the game of the discrete logarithm.

The base point must be nonzero, and the encoding semi-injective.

The normal form must keep or negate `s`. -/
theorem prEvent_keylessExperiment_win_le {scheme : Scheme F G A M} (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) (hnorm : scheme.NormalizeSign) (fuel : ℕ)
    (adversary : Adversary F G A M) :
    Pr{let z ← keylessExperiment scheme fuel adversary}[ProgrammedWin scheme z] ≤
      keyOnlyAdvantage scheme (keylessForger scheme fuel adversary) +
        Pr{let b ← DiffieHellman.dlogExperiment scheme.g (keylessSolver scheme fuel adversary)}[
          b = true] := by
  rw [keyOnlyAdvantage_eq_lazy, keylessExperiment, DiffieHellman.dlogExperiment, keyOnlyExperimentQ,
    StateT.run'_eq, simulateQ_bind, StateT.run_bind, simulateQ_lazyPermImpl_liftM_run,
    bind_map_left]
  simp only [map_bind]
  rw [prEvent_bind_eq_tsum_prEvent, prEvent_bind_eq_tsum_prEvent, prEvent_bind_eq_tsum_prEvent,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← mul_add]
  refine mul_le_mul_right ((prEvent_win_le_of_key hg hsemi hnorm fuel adversary x).trans
    (add_le_add (le_of_eq ?_) (le_of_eq ?_))) _
  · simp only [simulateQ_map, StateT.run_map, prEvent_map]
  · simp only [keylessSolver, map_pure, decide_eq_true_eq, bind_pure_comp, prEvent_map]

end EthLib.Cryptography.Secp256k1.Security
