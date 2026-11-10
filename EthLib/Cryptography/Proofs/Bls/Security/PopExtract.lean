module

public import EthLib.Cryptography.Proofs.Bls.Security.Game

/-!
# Proofs: what a forged aggregate tells the reduction

This is the algebraic step of the reduction for aggregates with proofs of possession.

The game is in the module of the aggregate game; this step only needs the scheme.

Keys lie in `G1` and signatures in `G2`.

The co-CDH problem also gives `a • g2`, which signs on the honest key hash.

The reduction programs the hash of the forged message to an element `Z`.

It programs the key hash of every key `x` other than the honest key to `r x • Z`, with `r x` known.

A valid proof `π` on `x = sk • g1` is then `sk • (r x • Z)`, so `(r x)⁻¹ • π` is `sk • Z`.

A valid aggregate `σ` is the sum of the secrets of all keys, times `Z`.

Subtracting the share of the other keys leaves `n • (a • Z)`, for `n` copies of `pk = a • g1`.

Dividing by `n` gives `a • Z`; when `Z` is the challenge `c • g2`, this is `(a * c) • g2`.

The step needs three facts that the game does not give.

- Every key is a multiple of `g1`, so that it has a secret.
- No scalar `r x` is zero; a zero hash makes every proof on it the zero element.
- The count `n` is not zero in the scalars; it is at most the number of keys.

The count is nonzero when the honest key is a key and the characteristic exceeds the key count.

The characteristic zero also suffices.

The game checks each proof against the key hash at its position in a list.

The reduction will read `r x` from its table of key hashes, so a function of the key suffices here.

No bound is proved here; the planned one would pay three terms around this step.

- A factor `q` for guessing which message hash is `Z`.
- About `qK` over the number of scalars, for a key hash scalar that is zero.
- One over the number of scalars in the simulation, for `c = 0`, which zeroes every programmed hash.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security.Pop

variable {F G₁ G₂ : Type} [Field F] [DecidableEq G₁] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂]

/-- The share of the keys other than `pk`: the sum of `(r x)⁻¹ • π` over each such key `x`.

Here `π` is the proof of `x`, and `r x` is the scalar the reduction used for its key hash. -/
def otherShare (pk : G₁) (r : G₁ → F) (keys : List (G₁ × G₂)) : G₂ :=
  ((keys.filter fun k => k.1 ≠ pk).map fun k => (r k.1)⁻¹ • k.2).sum

/-- The reduction's answer from an aggregate `σ`.

It removes the share of the other keys and divides by the number of copies of `pk`. -/
def extractAggregate (pk : G₁) (r : G₁ → F) (keys : List (G₁ × G₂)) (σ : G₂) : G₂ :=
  ((keys.map Prod.fst).count pk : F)⁻¹ • (σ - otherShare pk r keys)

omit [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂] in
/-- A key sum is the sum of the secrets of its keys, times `g1`. -/
theorem sum_map_fst_eq_sum_smul (g₁ : G₁) (s : G₁ → F) {keys : List (G₁ × G₂)}
    (hs : ∀ k ∈ keys, k.1 = s k.1 • g₁) :
    (keys.map Prod.fst).sum = (keys.map fun k => s k.1).sum • g₁ := by
  induction keys with
  | nil => simp
  | cons k rest ih =>
    rw [List.map_cons, List.sum_cons, ih fun k' hk' => hs k' (List.mem_cons_of_mem _ hk'),
      List.map_cons, List.sum_cons, add_smul, ← hs k List.mem_cons_self]

/-- The sum of the secrets of the keys, times `Z`, splits into the honest copies and the others.

The honest key `a • g1` has the secret `a`, and every other key `x` a valid proof on `r x • Z`. -/
theorem sum_smul_eq_count_add_otherShare {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F)
    {a : F} {Z : G₂} {r : G₁ → F} {s : G₁ → F} {keys : List (G₁ × G₂)}
    (hs : ∀ k ∈ keys, k.1 = s k.1 • scheme.g₁) (ha : s (a • scheme.g₁) = a)
    (hproofs : ∀ k ∈ keys, k.1 ≠ a • scheme.g₁ →
      r k.1 ≠ 0 ∧ scheme.isDh k.1 (r k.1 • Z) k.2 = true) :
    (keys.map fun k => s k.1).sum • Z =
      ((keys.map Prod.fst).count (a • scheme.g₁) : F) • (a • Z) +
        otherShare (a • scheme.g₁) r keys := by
  induction keys with
  | nil => simp [otherShare]
  | cons k rest ih =>
    have ih := ih (fun k' hk' => hs k' (List.mem_cons_of_mem _ hk'))
      fun k' hk' => hproofs k' (List.mem_cons_of_mem _ hk')
    simp only [otherShare] at ih ⊢
    by_cases hk : k.1 = a • scheme.g₁
    · simp only [List.map_cons, List.sum_cons, add_smul, ih, List.count_cons, hk, ha,
        List.filter_cons, ne_eq, not_true_eq_false, decide_false]
      push_cast
      simp [add_smul]
      abel
    · obtain ⟨hr, hdh⟩ := hproofs k List.mem_cons_self hk
      -- A valid proof on `r x • Z` is `s x • (r x • Z)`, so `(r x)⁻¹` times it is `s x • Z`.
      have hπ : k.2 = s k.1 • (r k.1 • Z) := (hsound _ _ _).mp (by rwa [← hs k List.mem_cons_self])
      have hshare : (r k.1)⁻¹ • k.2 = s k.1 • Z := by
        rw [hπ, smul_smul, smul_smul]
        congr 1
        field_simp
      simp only [List.map_cons, List.sum_cons, add_smul, ih, List.count_cons, List.filter_cons,
        ne_eq, hk, not_false_eq_true, decide_true]
      simp only [beq_iff_eq, hk, ite_true, ite_false, add_zero, List.map_cons, List.sum_cons,
        hshare]
      abel

/-- The extraction step: a valid aggregate with valid proofs gives the reduction `a • Z`.

The honest key is `a • g1`, and every key in the list is a multiple of `g1`.

Every other key `x` carries a proof that verifies on `r x • Z`, with `r x ≠ 0`.

The aggregate verifies on `Z` under the sum of the keys.

The number of copies of the honest key among the keys is not zero in the scalars. -/
theorem extractAggregate_eq {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F) {a : F}
    {Z σ : G₂} {r : G₁ → F} {keys : List (G₁ × G₂)}
    (hkeys : ∀ k ∈ keys, ∃ sk : F, k.1 = sk • scheme.g₁)
    (hproofs : ∀ k ∈ keys, k.1 ≠ a • scheme.g₁ →
      r k.1 ≠ 0 ∧ scheme.isDh k.1 (r k.1 • Z) k.2 = true)
    (hcount : ((keys.map Prod.fst).count (a • scheme.g₁) : F) ≠ 0)
    (hagg : scheme.isDh (keys.map Prod.fst).sum Z σ = true) :
    extractAggregate (a • scheme.g₁) r keys σ = a • Z := by
  classical
  -- The secret of the honest key is `a`; any other key in the list gets a secret it has.
  let s : G₁ → F := fun x =>
    if x = a • scheme.g₁ then a else if h : ∃ sk : F, x = sk • scheme.g₁ then h.choose else 0
  have hs : ∀ k ∈ keys, k.1 = s k.1 • scheme.g₁ := by
    intro k hk
    by_cases hx : k.1 = a • scheme.g₁
    · simp only [s, hx, ite_true]
    · simp only [s, hx, ite_false, hkeys k hk, dite_true]
      exact (hkeys k hk).choose_spec
  have ha : s (a • scheme.g₁) = a := by simp [s]
  have hσ : σ = (keys.map fun k => s k.1).sum • Z := by
    rw [sum_map_fst_eq_sum_smul scheme.g₁ s hs] at hagg
    exact (hsound _ _ _).mp hagg
  rw [extractAggregate, hσ, sum_smul_eq_count_add_otherShare hsound hs ha hproofs,
    add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hcount, one_smul]

/-! ## The hypotheses can hold together -/

/-- Honest keys meet the hypotheses of the extraction step on keys, proofs, count and aggregate.

Each secret `sk` gives the key `sk • g1` and the proof `sk • (r (sk • g1) • Z)`.

The sum of `sk • Z` over the secrets then verifies on `Z` under the sum of the keys.

The honest secret `a` appears once among the secrets, so its key has a count of at least one. -/
theorem hypotheses_of_secrets {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F) (a : F)
    (r : G₁ → F) (Z : G₂) {sks : List F} (ha : a ∈ sks)
    (hr : ∀ sk ∈ sks, r (sk • scheme.g₁) ≠ 0) :
    let keys := sks.map fun sk => (sk • scheme.g₁, sk • (r (sk • scheme.g₁) • Z))
    (∀ k ∈ keys, ∃ sk : F, k.1 = sk • scheme.g₁) ∧
      (∀ k ∈ keys, r k.1 ≠ 0 ∧ scheme.isDh k.1 (r k.1 • Z) k.2 = true) ∧
      0 < (keys.map Prod.fst).count (a • scheme.g₁) ∧
      scheme.isDh (keys.map Prod.fst).sum Z (sks.map (· • Z)).sum = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨sk, -, rfl⟩ := List.mem_map.mp hk
    exact ⟨sk, rfl⟩
  · intro k hk
    obtain ⟨sk, hsk, rfl⟩ := List.mem_map.mp hk
    exact ⟨hr sk hsk, (hsound _ _ _).mpr rfl⟩
  · rw [List.count_pos_iff, List.map_map]
    exact List.mem_map_of_mem ha
  · have hkeys : ((sks.map fun sk => (sk • scheme.g₁, sk • (r (sk • scheme.g₁) • Z))).map
        Prod.fst).sum = sks.sum • scheme.g₁ := by
      simp [List.map_map, Function.comp_def, List.sum_smul]
    rw [hkeys, show (sks.map (· • Z)).sum = sks.sum • Z from List.sum_smul.symm]
    exact (hsound _ _ _).mpr rfl

/-- The scheme over the scalars themselves, with `g1 = g2 = 1`.

A tuple `(pk, h, σ)` verifies when `σ = pk * h`. -/
def scalarScheme (F : Type) [Field F] [DecidableEq F] : Scheme F F where
  g₁ := 1
  g₂ := 1
  isDh pk h σ := decide (σ = pk * h)

omit [DecidableEq G₁] in
/-- The scheme over the scalars decides co-Diffie-Hellman tuples.

So a sound scheme exists.

With the lemma above, every hypothesis of the step holds when the count is nonzero in `F`. -/
theorem scalarScheme_sound [DecidableEq F] : (scalarScheme F).Sound F := by
  intro a h σ
  simp [scalarScheme]

end EthLib.Cryptography.Bls.Security.Pop
