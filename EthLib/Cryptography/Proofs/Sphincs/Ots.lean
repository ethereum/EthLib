import EthLib.Cryptography.Sphincs.Ots

/-!
# Proofs: `Sphincs.Ots`

Correctness of the one-time signature.

- The counter search returns the least counter whose encoding is a codeword.
- An honest one-time signature leads back to the key's own leaf.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {pp : PublicParam} {key : OtsKey} {i : Fin V} {start s₁ s₂ : Nat} {value : Digest}

/-! ## Chains -/

/-- Walking no steps leaves the value alone. -/
@[simp] theorem chain_zero (h : start + 0 < CHAIN_LENGTH) :
    chain pp key i start 0 h value = value := rfl

/-- Walking `s₁` steps then `s₂` more is walking `s₁ + s₂` steps. -/
theorem chain_add (h₁ : start + s₁ < CHAIN_LENGTH) (h : start + s₁ + s₂ < CHAIN_LENGTH) :
    chain pp key i (start + s₁) s₂ h (chain pp key i start s₁ h₁ value)
      = chain pp key i start (s₁ + s₂) (by omega) value := by
  induction s₂ with
  | zero => rfl
  | succ s ih =>
    -- The last step leaves `start + s₁ + s`, the same as `start + (s₁ + s)`.
    show chainStep pp key i ⟨start + s₁ + s, _⟩ _ = _
    rw [ih (by omega)]
    show _ = chainStep pp key i ⟨start + (s₁ + s), _⟩ _
    -- The position carries its bound, so the rewrite goes through a congruence.
    congr 1
    exact Fin.ext (Nat.add_assoc _ _ _)

/-- The bound on a walk is a proof, so walks of equal length agree. -/
theorem chain_steps_congr {steps steps' : Nat} (hs : steps = steps')
    (h : start + steps < CHAIN_LENGTH) (h' : start + steps' < CHAIN_LENGTH) :
    chain pp key i start steps h value = chain pp key i start steps' h' value := by
  subst hs
  rfl

/-! ## The counter search -/

/-- The search returns a counter in its window whose encoding is a codeword, and no earlier one is.

So the signer's counter is a function of its inputs: the least admissible one. -/
theorem findCounter_spec {msg : ByteArray} :
    ∀ {fuel c : Nat} {counter : UInt32} {x : Codeword},
      Internal.findCounter pp key msg c fuel = some (counter, x) →
      ∃ k, c ≤ k ∧ k < c + fuel ∧ counter = UInt32.ofNat k ∧
        encode pp key msg counter = some x ∧
        ∀ k', c ≤ k' → k' < k → encode pp key msg (UInt32.ofNat k') = none := by
  intro fuel
  induction fuel with
  | zero => intro c counter x h; simp [Internal.findCounter] at h
  | succ fuel ih =>
    intro c counter x h
    simp only [Internal.findCounter] at h
    cases hx : encode pp key msg (UInt32.ofNat c) with
    -- Counter `c` itself is admissible: it is the least.
    | some x' =>
      rw [hx, Option.elim_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp h)
      exact ⟨c, Nat.le_refl _, by omega, rfl, hx, fun k' h₁ h₂ => absurd h₂ (by omega)⟩
    -- Counter `c` fails, so the answer comes from the counters after it.
    | none =>
      rw [hx, Option.elim_none] at h
      obtain ⟨k, hk₁, hk₂, hcounter, hcw, hmin⟩ := ih h
      refine ⟨k, by omega, by omega, hcounter, hcw, fun k' h₁ h₂ => ?_⟩
      rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
      · exact hx
      · exact hmin k' h₁ h₂

/-- A one-time signature carries the least admissible counter below `2^32`.

Its encoding is a codeword, and the encoding of every smaller counter is not. -/
theorem otsSign_counter {seed : Seed} {msg : ByteArray} {counter : UInt32} {y : Vector Digest V}
    (h : otsSign pp seed key msg = some (counter, y)) :
    (∃ x, encode pp key msg counter = some x) ∧
      ∀ k < counter.toNat, encode pp key msg (UInt32.ofNat k) = none := by
  simp only [otsSign, Option.bind_eq_bind] at h
  cases hfind : Internal.findCounter pp key msg 0 MAX_COUNTER_TRIALS with
  | none => simp [hfind] at h
  | some found =>
    obtain ⟨counter', x⟩ := found
    simp only [hfind, Option.bind_some, Option.pure_def, Option.some_inj, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨k, -, hk, rfl, hcw, hmin⟩ := findCounter_spec hfind
    -- The counter is `k < 2^32`, so it reads back as `k`.
    have hk' : (UInt32.ofNat k).toNat = k := by
      simp only [MAX_COUNTER_TRIALS] at hk
      exact UInt32.toNat_ofNat_of_lt' (by omega)
    refine ⟨⟨x, hcw⟩, fun k' hk'' => hmin k' (Nat.zero_le _) (by omega)⟩

/-! ## An honest signature leads to the key's leaf -/

/-- A one-time signature from the seed recovers the leaf the seed gives the key.

The verifier walks each revealed value from position `x_i` to 3.

The signer walked it from 0 to `x_i`, so together they walk the whole chain. -/
theorem otsLeaf_otsSign {seed : Seed} {msg : ByteArray} {counter : UInt32} {y : Vector Digest V}
    (h : otsSign pp seed key msg = some (counter, y)) :
    otsLeaf pp key msg counter y = some (otsPublicLeaf pp seed key) := by
  simp only [otsSign, Option.bind_eq_bind] at h
  -- Name the search result: a counter and its codeword.
  cases hfind : Internal.findCounter pp key msg 0 MAX_COUNTER_TRIALS with
  | none => simp [hfind] at h
  | some found =>
    obtain ⟨counter', x⟩ := found
    simp only [hfind, Option.bind_some, Option.pure_def, Option.some_inj, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, -, -, -, hcw, -⟩ := findCounter_spec hfind
    -- The verifier recomputes the same codeword.
    simp only [otsLeaf, hcw, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some_inj, otsPublicLeaf]
    refine congrArg (otsLeafHash pp key) (Vector.ext fun j hj => ?_)
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
    -- Signer's steps plus verifier's steps make the whole chain.
    have hx := (x[j]'hj).isLt
    have hsplit := chain_add (pp := pp) (key := key) (i := ⟨j, hj⟩) (start := 0)
      (s₁ := (x[j]'hj : Nat)) (s₂ := CHAIN_LENGTH - 1 - (x[j]'hj : Nat))
      (value := (chainStarts pp seed key)[j]'hj)
      (by simp only [CHAIN_LENGTH] at *; omega) (by simp only [CHAIN_LENGTH] at *; omega)
    simp only [Nat.zero_add] at hsplit
    -- Steps revealed plus steps walked is the whole chain.
    exact hsplit.trans (chain_steps_congr (by simp only [CHAIN_LENGTH] at *; omega) _ _)

end EthLib.Cryptography.Sphincs
