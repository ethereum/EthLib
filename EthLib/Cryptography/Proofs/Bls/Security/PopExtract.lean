module

public import EthLib.Cryptography.Proofs.Bls.Security.PopGame

/-!
# Proofs: what a forged aggregate tells the reduction

This is the algebraic step of the reduction for aggregates with proofs of possession.

It follows Ristenpart and Yilek, §5, where a proof of possession is a signature on the key.

<https://eprint.iacr.org/2007/264>

The reduction programs the hash of the forged message to an element `Z`.

It programs the key hash of every key `x` other than the honest key `pk` to `r • Z`, with `r` known.

A valid proof `π` on `x = sk • g1` is then `sk • (r • Z)`, so `r⁻¹ • π` is `sk • Z`.

A valid aggregate `σ` is the sum of the secrets of all keys, times `Z`.

Subtracting the share of the other keys leaves `n • (a • Z)`, for `n` copies of `pk = a • g1`.

Dividing by `n` gives `a • Z`; when `Z` is the challenge `c • g2`, this is `(a * c) • g2`.

The step needs three facts that the game does not give.

- Every key is a multiple of `g1`, so that it has a secret.
- No scalar `r` is zero; a zero hash makes every proof on it the zero element.
- The count `n` is not zero in the scalars; it is at most the number of keys.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security.Pop

variable {F G₁ G₂ : Type} [Field F] [DecidableEq G₁] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂]

/-- The share of the keys other than `pk`: `r⁻¹ • π` for each key and its proof `π`.

The scalar `r` of a key is the one the reduction used for its key hash. -/
def otherShare (pk : G₁) (r : G₁ → F) (keys : List (G₁ × G₂)) : G₂ :=
  ((keys.filter fun k => k.1 ≠ pk).map fun k => (r k.1)⁻¹ • k.2).sum

/-- The reduction's answer from an aggregate `σ`.

It removes the share of the other keys and divides by the number of copies of `pk`. -/
def extractAggregate (pk : G₁) (r : G₁ → F) (keys : List (G₁ × G₂)) (σ : G₂) : G₂ :=
  ((keys.map Prod.fst).count pk : F)⁻¹ • (σ - otherShare pk r keys)

omit [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂] in
/-- A key sum is the sum of the secrets of its keys, times `g1`. -/
theorem sum_keys_eq (g₁ : G₁) (s : G₁ → F) (hs : ∀ x, x = s x • g₁) (keys : List (G₁ × G₂)) :
    (keys.map Prod.fst).sum = (keys.map fun k => s k.1).sum • g₁ := by
  induction keys with
  | nil => simp
  | cons k rest ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons,
      add_smul, ← hs]

/-- The sum of the secrets of the keys, times `Z`, splits into the honest copies and the others.

The honest key `pk` has the secret `a`, and every other key a valid proof on `r • Z`. -/
theorem sum_smul_eq_count_add_otherShare {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F)
    {a : F} {Z : G₂} {r : G₁ → F} {s : G₁ → F} (hs : ∀ x, x = s x • scheme.g₁)
    (ha : s (a • scheme.g₁) = a) {keys : List (G₁ × G₂)}
    (hproofs : ∀ k ∈ keys, k.1 ≠ a • scheme.g₁ →
      r k.1 ≠ 0 ∧ scheme.isDh k.1 (r k.1 • Z) k.2 = true) :
    (keys.map fun k => s k.1).sum • Z =
      ((keys.map Prod.fst).count (a • scheme.g₁) : F) • (a • Z) +
        otherShare (a • scheme.g₁) r keys := by
  induction keys with
  | nil => simp [otherShare]
  | cons k rest ih =>
    have ih := ih fun k' hk' => hproofs k' (List.mem_cons_of_mem _ hk')
    simp only [otherShare] at ih ⊢
    by_cases hk : k.1 = a • scheme.g₁
    · simp only [List.map_cons, List.sum_cons, add_smul, ih, List.count_cons, hk, ha,
        List.filter_cons, ne_eq, not_true_eq_false, decide_false]
      push_cast
      simp [add_smul]
      abel
    · obtain ⟨hr, hdh⟩ := hproofs k List.mem_cons_self hk
      -- A valid proof on `r • Z` is `s • (r • Z)`, so `r⁻¹` times it is `s • Z`.
      have hπ : k.2 = s k.1 • (r k.1 • Z) := (hsound _ _ _).mp (by rwa [← hs k.1])
      have hshare : (r k.1)⁻¹ • k.2 = s k.1 • Z := by
        rw [hπ, smul_smul, smul_smul]
        congr 1
        field_simp
      simp only [List.map_cons, List.sum_cons, add_smul, ih, List.count_cons, List.filter_cons,
        ne_eq, hk, not_false_eq_true, decide_true]
      simp only [beq_iff_eq, hk, ite_true, ite_false, add_zero, List.map_cons, List.sum_cons,
        hshare]
      abel

/-- **The extraction step.** A valid aggregate with valid proofs gives the reduction `a • Z`.

The honest key is `a • g1`, and every key is a multiple of `g1`.

The hash of the message is `Z`; the key hash of every other key `x` is `r x • Z`, with `r x ≠ 0`.

The number of copies of the honest key among the keys is not zero in the scalars. -/
theorem extractAggregate_eq {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F)
    (hkeys : ∀ x : G₁, ∃ sk : F, x = sk • scheme.g₁) {a : F} {Z σ : G₂} {r : G₁ → F}
    {keys : List (G₁ × G₂)}
    (hproofs : ∀ k ∈ keys, k.1 ≠ a • scheme.g₁ →
      r k.1 ≠ 0 ∧ scheme.isDh k.1 (r k.1 • Z) k.2 = true)
    (hcount : ((keys.map Prod.fst).count (a • scheme.g₁) : F) ≠ 0)
    (hagg : scheme.isDh (keys.map Prod.fst).sum Z σ = true) :
    extractAggregate (a • scheme.g₁) r keys σ = a • Z := by
  choose sk hsk using hkeys
  -- The secret of the honest key is `a`; any other key gets the secret that `hkeys` chose.
  let s : G₁ → F := fun x => if x = a • scheme.g₁ then a else sk x
  have hs : ∀ x, x = s x • scheme.g₁ := by
    intro x
    by_cases hx : x = a • scheme.g₁
    · simp only [s, hx, ite_true]
    · simp only [s, hx, ite_false]
      exact hsk x
  have ha : s (a • scheme.g₁) = a := by simp [s]
  have hσ : σ = (keys.map fun k => s k.1).sum • Z := by
    rw [sum_keys_eq scheme.g₁ s hs] at hagg
    exact (hsound _ _ _).mp hagg
  rw [extractAggregate, hσ, sum_smul_eq_count_add_otherShare hsound hs ha hproofs,
    add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hcount, one_smul]

/-! ## The hypotheses can hold together -/

/-- The scheme over the scalars themselves, with `g1 = g2 = 1`.

A tuple `(pk, h, σ)` verifies when `σ = pk * h`. -/
def scalarScheme (F : Type) [Field F] [DecidableEq F] : Scheme F F where
  g₁ := 1
  g₂ := 1
  isDh pk h σ := decide (σ = pk * h)

omit [DecidableEq G₁] in
/-- The scheme over the scalars decides co-Diffie-Hellman tuples.

Every key is a multiple of `1` there.

So the hypotheses of the extraction step are not contradictory. -/
theorem scalarScheme_sound [DecidableEq F] :
    (scalarScheme F).Sound F ∧ ∀ x : F, ∃ sk : F, x = sk • (scalarScheme F).g₁ := by
  refine ⟨fun a h σ => ?_, fun x => ⟨x, by simp [scalarScheme]⟩⟩
  simp [scalarScheme]

end EthLib.Cryptography.Bls.Security.Pop
