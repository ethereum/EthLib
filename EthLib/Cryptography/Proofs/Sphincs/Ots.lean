module

public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Sphincs.Ots

/-!
# Proofs: WOTS+C one-time signatures

Correctness of the one-time signature.

- The counter search returns the least counter whose encoding is a codeword.
- An honest one-time signature leads back to the key's own leaf.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {pp : PublicParam} {key : OtsKey} {i : Fin V} {start s₁ s₂ : Nat} {value : Digest}

/-! ## Chains -/

/-- Walking no steps leaves the value alone. -/
@[simp] theorem chain_zero (h : start + 0 < CHAIN_LENGTH) :
    chain pp key i start 0 h value = value := rfl

/-! ## The counter search -/

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
    rw [Internal.findCounter] at hfind
    obtain ⟨k, -, hk, rfl, hcw, hmin⟩ := Wots.findFirst_spec hfind
    unfold Id.run at hcw hmin
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
    rw [Internal.findCounter] at hfind
    obtain ⟨-, -, -, -, hcw, -⟩ := Wots.findFirst_spec hfind
    unfold Id.run at hcw
    -- The verifier recomputes the same codeword.
    simp only [otsLeaf, hcw, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some_inj, otsPublicLeaf]
    refine congrArg (otsLeafHash pp key) (Vector.ext fun j hj => ?_)
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
    -- Signer's steps plus verifier's steps make the whole chain.
    have hx := (x[j]'hj).isLt
    have hsplit := Wots.chain_add (m := Id) (step := chainStep pp key ⟨j, hj⟩) (start := 0)
      (s₁ := (x[j]'hj : Nat)) (s₂ := CHAIN_LENGTH - 1 - (x[j]'hj : Nat))
      (value := (chainStarts pp seed key)[j]'hj) (Nat.zero_add _).symm
      (by simp only [CHAIN_LENGTH] at *; omega) (by simp only [CHAIN_LENGTH] at *; omega)
    -- Steps revealed plus steps walked is the whole chain.
    exact hsplit.trans (Wots.chain_steps_congr (by simp only [CHAIN_LENGTH] at *; omega) _ _)

end EthLib.Cryptography.Sphincs
