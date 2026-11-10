module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.ForwardCase
public import EthLib.Cryptography.Proofs.Secp256k1.Security.InverseCase

/-!
# Proofs: two forgeries on one forward query give the discrete logarithm

A fork of the key-only run gives two forgeries `(m, t, s)` and `(m', t', s')` on the key `X = x g`.

Both checks passed at the same point, so `R = U / s` and `R' = U' / s'` have one encoding.

Here `U = H(m) g + t X` and `U' = H(m') g + t' X`.

With a semi-injective encoding, `R' = η R` for a sign `η`.

Let `r` be the discrete logarithm of `R`.

Then `s r = H(m) + t x` and `s' η r = H(m') + t' x`.

Divide by `t` and by `t'`, and subtract: `r (s / t - η s' / t') = H(m) / t - H(m') / t'`.

Say `H(m) / t ≠ H(m') / t'`.

Then `s / t - η s' / t'` is nonzero, so `r` and then `x = (s r - H(m)) / t` follow.

The sign is not known; the key from `η = 1` is kept if it gives `X`, and the other is taken if not.

So the solver below finds the key whenever the fork succeeds and the forgeries divide apart.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The solver is their Figure 9, and the key is recovered as in the text after their Figure 10.

Their text leaves the sign unknown; here both signs are tried, and the one that gives `X` is kept.

Their fork reuses the coins `ρ`; the fork here draws fresh coins after the forked query.

Their `Q` is `q + 1` here.

The discrete-logarithm game here draws the key from all scalars, as the key-only game does.

Their key generation draws it from the nonzero scalars.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The key from two forgeries `(m, t, s)` and `(m', t', s')` on one point, for a sign `η`.

It is `(s r - H(m)) / t`, where `r = (H(m) / t - H(m') / t') / (s / t - η s' / t')`. -/
def forwardKey (scheme : Scheme F G A M) (z z' : M × F × F) (η : F) : F :=
  let r := (scheme.hash z.1 / z.2.1 - scheme.hash z'.1 / z'.2.1) /
    (z.2.2 / z.2.1 - η * z'.2.2 / z'.2.1)
  (z.2.2 * r - scheme.hash z.1) / z.2.1

omit [DecidableEq F] [DecidableEq G] [AddCommGroup G] [Module F G] in
/-- The key for a sign `η` is the key when the second scalar is `η` times the first. -/
private theorem forwardKey_eq_of {scheme : Scheme F G A M} {x η : F} {z z' : M × F × F}
    (ht : z.2.1 ≠ 0) (hs : z.2.2 ≠ 0) (ht' : z'.2.1 ≠ 0) (hs' : z'.2.2 ≠ 0)
    (hη : z'.2.2⁻¹ * (scheme.hash z'.1 + z'.2.1 * x) =
      η * (z.2.2⁻¹ * (scheme.hash z.1 + z.2.1 * x)))
    (hdiv : scheme.hash z.1 / z.2.1 ≠ scheme.hash z'.1 / z'.2.1) :
    forwardKey scheme z z' η = x := by
  obtain ⟨m, t, s⟩ := z
  obtain ⟨m', t', s'⟩ := z'
  simp only at ht hs ht' hs' hη hdiv
  set r := s⁻¹ * (scheme.hash m + t * x) with hr
  have h1 : scheme.hash m = s * r - t * x := by rw [hr]; field_simp; ring
  have h2 : scheme.hash m' = s' * (η * r) - t' * x := by rw [← hη]; field_simp; ring
  have hden : s / t - η * s' / t' ≠ 0 := by
    intro h0
    apply hdiv
    have : (s * r - t * x) / t - (s' * (η * r) - t' * x) / t' = r * (s / t - η * s' / t') := by
      field_simp; ring
    rw [h1, h2]
    exact sub_eq_zero.mp (by rw [this, h0, mul_zero])
  have hrr : (scheme.hash m / t - scheme.hash m' / t') / (s / t - η * s' / t') = r := by
    rw [div_eq_iff hden, h1, h2]; field_simp; ring
  simp only [forwardKey]
  rw [hrr, h1]; field_simp; ring

/-- The key from two forgeries on one point and the key `X`.

The key for the sign `1` is kept if it gives `X`, and the key for the sign `-1` is taken if not. -/
def extractForward (scheme : Scheme F G A M) (X : G) (z z' : M × F × F) : F :=
  if forwardKey scheme z z' 1 • scheme.g = X then forwardKey scheme z z' 1
  else forwardKey scheme z z' (-1)

omit [DecidableEq F] in
/-- **Two valid forgeries on one point that divide apart give the key.**

Take the key `x g`, with a nonzero base point and a semi-injective encoding.

Take two forgeries `(m, t, s)` and `(m', t', s')` with `t`, `s`, `t'`, `s'` nonzero.

Say `U = H(m) g + t x g` and `U' = H(m') g + t' x g` are nonzero.

Say also that the points `U / s` and `U' / s'` share their encoding.

If `H(m) / t ≠ H(m') / t'`, the key from the two forgeries is `x`. -/
theorem extractForward_eq {scheme : Scheme F G A M} (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) {x : F} {z z' : M × F × F}
    (ht : z.2.1 ≠ 0) (hs : z.2.2 ≠ 0) (ht' : z'.2.1 ≠ 0) (hs' : z'.2.2 ≠ 0)
    (hU : scheme.hash z.1 • scheme.g + z.2.1 • x • scheme.g ≠ 0)
    (hU' : scheme.hash z'.1 • scheme.g + z'.2.1 • x • scheme.g ≠ 0)
    (hpt : forgeryPoint scheme (x • scheme.g) z = forgeryPoint scheme (x • scheme.g) z')
    (hdiv : scheme.hash z.1 / z.2.1 ≠ scheme.hash z'.1 / z'.2.1) :
    extractForward scheme (x • scheme.g) z z' = x := by
  have hinj := smul_left_injective F hg
  obtain ⟨m, t, s⟩ := z
  obtain ⟨m', t', s'⟩ := z'
  simp only at ht hs ht' hs' hU hU' hdiv
  have hR : (s⁻¹ * (scheme.hash m + t * x)) • scheme.g ≠ 0 := by
    rw [mul_smul, add_smul, mul_smul]; exact smul_ne_zero (inv_ne_zero hs) hU
  have hR' : (s'⁻¹ * (scheme.hash m' + t' * x)) • scheme.g ≠ 0 := by
    rw [mul_smul, add_smul, mul_smul]; exact smul_ne_zero (inv_ne_zero hs') hU'
  rw [forgeryPoint_smul, forgeryPoint_smul] at hpt
  have key : s'⁻¹ * (scheme.hash m' + t' * x) = 1 * (s⁻¹ * (scheme.hash m + t * x)) ∨
      s'⁻¹ * (scheme.hash m' + t' * x) = -1 * (s⁻¹ * (scheme.hash m + t * x)) := by
    rcases hsemi _ _ hR hR' hpt with h | h
    · exact Or.inl (by rw [one_mul]; exact hinj h)
    · exact Or.inr (hinj (show _ • _ = (-1 * _) • _ by rw [neg_one_mul, neg_smul]; exact h))
  simp only [extractForward]
  rcases key with h | h
  · have := forwardKey_eq_of (scheme := scheme) (z := (m, t, s)) (z' := (m', t', s'))
      ht hs ht' hs' h hdiv
    rw [this]; simp
  · split_ifs with hc
    · exact hinj hc
    · exact forwardKey_eq_of (scheme := scheme) (z := (m, t, s)) (z' := (m', t', s'))
        ht hs ht' hs' h hdiv

variable [FinEnum A] [SampleableType F] [SampleableType A]

/-- The solver of the discrete logarithm from a key-only forger, for forgeries on forward pairs.

It forks the key-only run on its instance `X` at the forgery's query, with uniform answers.

If the fork returns two forgeries, it returns the key they give, and `0` otherwise.

It runs the forger twice, so it is efficient when the forger, the hash and the encoding are.

No theorem states the running time.

It reads the base point of the scheme, not its first argument. -/
def forwardSolver (scheme : Scheme F G A M) (adversary : KeyOnlyAdversary F G A M) (q : ℕ) :
    DiffieHellman.DLogAdversary F G := fun _ X => do
  let r ← simulateQ outsideSample (contextFork (keyOnlyOutsideRun scheme adversary X)
    (forkBound q) (.inr ()) (forkIndex scheme X q))
  pure <| match r with
    | some (tr₁, tr₂) => extractForward scheme X tr₁.forgery tr₂.forgery
    | none => 0

variable [UniformAnswerMeasure (Unit →ₒ A)]

/-- **A fork whose forgeries divide apart gives the discrete logarithm.**

Draw the key uniformly, and fork the key-only run at the forgery's query.

Say the fork returns forgeries `(m, t, s)` and `(m', t', s')` with `H(m) / t ≠ H(m') / t'`.

That happens at most as often as the solver above finds the discrete logarithm of the key.

Here `q` bounds only the fork index, so no bound on the queries of the forger is assumed.

The base point must be nonzero, and the encoding semi-injective. -/
theorem prEvent_contextFork_div_ne_le_dlog {scheme : Scheme F G A M} (hg : scheme.g ≠ 0)
    (hsemi : scheme.SemiInjective) (adversary : KeyOnlyAdversary F G A M) (q : ℕ) :
    Pr{let x ← liftComp ($ᵗ F : ProbComp F) (OutsideSpec A)
       let r ← contextFork (keyOnlyOutsideRun scheme adversary (x • scheme.g)) (forkBound q)
         (.inr ()) (forkIndex scheme (x • scheme.g) q)}[
      ∃ tr₁ tr₂, r = some (tr₁, tr₂) ∧
        scheme.hash tr₁.forgery.1 / tr₁.forgery.2.1 ≠
          scheme.hash tr₂.forgery.1 / tr₂.forgery.2.1] ≤
      Pr{let b ← DiffieHellman.dlogExperiment scheme.g (forwardSolver scheme adversary q)}[
        b = true] := by
  have hrun : ∀ x : F, EvalDistEq
      (simulateQ outsideSample (contextFork (keyOnlyOutsideRun scheme adversary (x • scheme.g))
        (forkBound q) (.inr ()) (forkIndex scheme (x • scheme.g) q)))
      (contextFork (keyOnlyOutsideRun scheme adversary (x • scheme.g))
        (forkBound q) (.inr ()) (forkIndex scheme (x • scheme.g) q)) := fun x =>
    simulateQ_outsideSample_evalDistEq _
  have hL := (((evalDistEq_liftComp_uniform (superSpec := OutsideSpec A) ($ᵗ F : ProbComp F)).symm
    ).bind hrun).prEvent_eq (fun r => ∃ tr₁ tr₂, r = some (tr₁, tr₂) ∧
        scheme.hash tr₁.forgery.1 / tr₁.forgery.2.1 ≠
          scheme.hash tr₂.forgery.1 / tr₂.forgery.2.1)
  simp only [map_bind] at hL
  rw [← hL]
  simp only [DiffieHellman.dlogExperiment, forwardSolver, bind_assoc, pure_bind]
  simp only [map_bind, map_pure, decide_eq_true_eq]
  refine prEvent_bind_mono_of_support _ _ _ fun x _ => ?_
  simp only [bind_pure_comp]
  refine prEvent_mono_of_support _ _ _ fun r hr hE => ?_
  rw [support_simulateQ_outsideSample] at hr
  obtain ⟨tr₁, tr₂, rfl, hne⟩ := hE
  obtain ⟨hm₁, hm₂⟩ := mem_support_keyOnlyOutsideRun_of_mem_support_contextFork scheme adversary
    _ q hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpt, hv₁, hv₂⟩ :=
    forward_eq_of_mem_support_contextFork scheme adversary _ q hr
  obtain ⟨-, ht, hs, hU, -⟩ :=
    of_verified_of_mem_support_keyOnlyOutsideRun scheme adversary _ hm₁ hv₁
  obtain ⟨-, ht', hs', hU', -⟩ :=
    of_verified_of_mem_support_keyOnlyOutsideRun scheme adversary _ hm₂ hv₂
  exact extractForward_eq hg hsemi ht hs ht' hs' hU hU' hpt hne
