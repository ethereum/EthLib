import EthLib.Cryptography.Xmss.Ots

/-!
# Proofs: `Xmss.Ots`

Correctness of the one-time signature.

- Grinding returns the least trial whose digest is a codeword.
- An honest one-time signature leads back to the key's own leaf.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {pp : PublicParam} {layer : Layer} {e : UInt32} {i : Fin V}
  {start s₁ s₂ : Nat} {value : Digest}

/-! ## Chains -/

/-- Walking no steps leaves the value alone. -/
@[simp] theorem chain_zero (h : start + 0 < CHAIN_LENGTH) :
    chain pp layer e i start 0 h value = value := rfl

/-- Walking `s₁` steps then `s₂` more is walking `s₁ + s₂` steps. -/
theorem chain_add (h₁ : start + s₁ < CHAIN_LENGTH) (h : start + s₁ + s₂ < CHAIN_LENGTH) :
    chain pp layer e i (start + s₁) s₂ h (chain pp layer e i start s₁ h₁ value)
      = chain pp layer e i start (s₁ + s₂) (by omega) value := by
  induction s₂ with
  | zero => rfl
  | succ s ih =>
    -- The last step leaves `start + s₁ + s`, the same as `start + (s₁ + s)`.
    show chainStep pp layer e i ⟨start + s₁ + s, _⟩ _ = _
    rw [ih (by omega)]
    show _ = chainStep pp layer e i ⟨start + (s₁ + s), _⟩ _
    -- The position carries its bound, so the rewrite goes through a congruence.
    congr 1
    exact Fin.ext (Nat.add_assoc _ _ _)

/-- The bound on a walk is a proof, so walks of equal length agree. -/
theorem chain_steps_congr {steps steps' : Nat} (hs : steps = steps')
    (h : start + steps < CHAIN_LENGTH) (h' : start + steps' < CHAIN_LENGTH) :
    chain pp layer e i start steps h value = chain pp layer e i start steps' h' value := by
  subst hs
  rfl

/-! ## Grinding -/

/-- Grinding returns a trial in its window, whose digest is a codeword, and no earlier one is.

So the signer's randomizer is a function of its inputs: the least admissible trial. -/
theorem findCodeword_spec {msg : ByteArray} {base : Randomizer} :
    ∀ {fuel c : Nat} {rho : Randomizer} {x : Vector (Fin CHAIN_LENGTH) V},
      Internal.findCodeword pp layer e msg base c fuel = some (rho, x) →
      ∃ k, c ≤ k ∧ k < c + fuel ∧ rho = trialRandomizer base k ∧
        codeword? (messageDigest pp layer e msg rho) = some x ∧
        ∀ k', c ≤ k' → k' < k →
          codeword? (messageDigest pp layer e msg (trialRandomizer base k')) = none := by
  intro fuel
  induction fuel with
  | zero => intro c rho x h; simp [Internal.findCodeword] at h
  | succ fuel ih =>
    intro c rho x h
    simp only [Internal.findCodeword] at h
    split at h
    -- Trial `c` itself is admissible: it is the least.
    · rename_i x' hx
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp h)
      exact ⟨c, Nat.le_refl _, by omega, rfl, hx, fun k' h₁ h₂ => absurd h₂ (by omega)⟩
    -- Trial `c` fails, so the answer comes from the trials after it.
    · rename_i hx
      obtain ⟨k, hk₁, hk₂, hrho, hcw, hmin⟩ := ih h
      refine ⟨k, by omega, by omega, hrho, hcw, fun k' h₁ h₂ => ?_⟩
      rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
      · exact hx
      · exact hmin k' h₁ h₂

/-! ## An honest signature leads to the key's leaf -/

/-- A one-time signature from the seed recovers the leaf the seed gives the key.

The verifier walks each revealed value from position `x_i` to 3.

The signer walked it from 0 to `x_i`, so together they walk the whole chain. -/
theorem otsLeaf_otsSign {seed : Seed} {msg : ByteArray} {rho : Randomizer} {y : Vector Digest V}
    (h : otsSign pp seed layer e msg = some (rho, y)) :
    otsLeaf pp layer e msg rho y = some (otsPublicLeaf pp seed layer e) := by
  simp only [otsSign, Option.bind_eq_bind] at h
  -- Name the grinding result: a randomizer and its codeword.
  cases hfind : Internal.findCodeword pp layer e msg (randomizerBase pp seed layer e msg) 0
      MAX_RANDOMIZER_TRIALS with
  | none => simp [hfind] at h
  | some found =>
    obtain ⟨rho', x⟩ := found
    simp only [hfind, Option.bind_some, Option.pure_def, Option.some_inj, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, -, -, -, hcw, -⟩ := findCodeword_spec hfind
    -- The verifier recomputes the same codeword.
    simp only [otsLeaf, hcw, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some_inj, otsPublicLeaf]
    refine congrArg (otsLeafHash pp layer e) (Vector.ext fun j hj => ?_)
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
    -- Signer's steps plus verifier's steps make the whole chain.
    have hx := (x[j]'hj).isLt
    have hsplit := chain_add (pp := pp) (layer := layer) (e := e) (i := ⟨j, hj⟩) (start := 0)
      (s₁ := (x[j]'hj : Nat)) (s₂ := CHAIN_LENGTH - 1 - (x[j]'hj : Nat))
      (value := (chainStarts pp seed layer e)[j]'hj)
      (by simp only [CHAIN_LENGTH] at *; omega) (by simp only [CHAIN_LENGTH] at *; omega)
    simp only [Nat.zero_add] at hsplit
    -- Steps revealed plus steps walked is the whole chain.
    exact hsplit.trans (chain_steps_congr (by simp only [CHAIN_LENGTH] at *; omega) _ _)

/-! ## A key's leaf in pieces -/

/-- A key's leaf, from its chain starts, its chain ends and its leaf hash.

A known answer checks each piece on its own. -/
theorem otsPublicLeaf_eq {seed : Seed} {starts ends : Vector Digest V} {leaf : Digest}
    (hstarts : chainStarts pp seed layer e = starts)
    (hends : ∀ i : Fin V, chain pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i] = ends[i])
    (hleaf : otsLeafHash pp layer e ends = leaf) :
    otsPublicLeaf pp seed layer e = leaf := by
  -- The walked chains are the stated ends, chain by chain.
  have hv : (Vector.ofFn fun i => chain pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i])
      = ends := Vector.ext fun i hi => by simpa using hends ⟨i, hi⟩
  simp only [otsPublicLeaf, hstarts, hv, hleaf]

end EthLib.Cryptography.Xmss
