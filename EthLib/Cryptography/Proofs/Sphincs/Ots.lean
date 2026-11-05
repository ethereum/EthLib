module

public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Sphincs.Ots
public import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: WOTS+C one-time signatures

Correctness of the one-time signature.

- The counter search returns the least counter whose encoding is a codeword.
- An honest one-time signature leads back to the key's own leaf.

Each theorem holds for every hash function `f`, run in the identity monad.

Keccak-256 is one such function, so the theorems cover the specification as it runs.

A variable `f` also keeps every proof from unfolding the hash on a concrete input.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {f : ByteArray → Vector UInt8 32} {pp : PublicParam} {key : OtsKey} {i : Fin V}
  {start : Nat} {value : Digest}

/-! ## Chains -/

/-- Walking no steps leaves the value alone. -/
@[simp] theorem chain_zero (h : start + 0 < CHAIN_LENGTH) :
    (chain (pureHash f) pp key i start 0 h value).run = value := rfl

/-! ## The signer as a value -/

/-- What the one-time signer computes: the counter search, with each chain walked to its digit.

`rw` unfolds the signer, not `simp`.

`simp` rewrites with `rfl` lemmas, and checking those makes Lean unfold the counter search.

That search runs up to `2^32` trials. -/
theorem otsSign_run {seed : Seed} {msg : ByteArray} :
    (otsSign (pureHash f) pp seed key msg).run =
      ((Internal.findCounter (pureHash f) pp key msg 0 MAX_COUNTER_TRIALS).run).map
        fun found => (found.1, Vector.ofFn fun i => (chain (pureHash f) pp key i 0
          (found.2[i]).val (by have := (found.2[i]).isLt; omega)
          (chainStarts (pureHash f) pp seed key).run[i]).run) := by
  rw [otsSign, Id.run_bind]
  cases (Internal.findCounter (pureHash f) pp key msg 0 MAX_COUNTER_TRIALS).run with
  | none => rfl
  | some found =>
    obtain ⟨counter, x⟩ := found
    -- The signer reveals the chains in order, which is the vector of the walked chains.
    rw [Option.map_some, ← Xmss.ofFnInOrder_run]
    rfl

/-! ## The counter search -/

/-- A one-time signature carries the least admissible counter below `2^32`.

Its encoding is a codeword, and the encoding of every smaller counter is not. -/
theorem otsSign_counter {seed : Seed} {msg : ByteArray} {counter : UInt32} {y : Vector Digest V}
    (h : (otsSign (pureHash f) pp seed key msg).run = some (counter, y)) :
    (∃ x, (encode (pureHash f) pp key msg counter).run = some x) ∧
      ∀ k < counter.toNat, (encode (pureHash f) pp key msg (UInt32.ofNat k)).run = none := by
  rw [otsSign_run, Option.map_eq_some_iff] at h
  obtain ⟨⟨counter', x⟩, hfind, hxy⟩ := h
  dsimp only at hxy
  obtain ⟨rfl, -⟩ := Prod.mk.inj hxy
  rw [Internal.findCounter] at hfind
  obtain ⟨k, -, hk, rfl, hcw, hmin⟩ := Wots.findFirst_spec hfind
  -- The counter is `k < 2^32`, so it reads back as `k`.
  have hk' : (UInt32.ofNat k).toNat = k := by
    simp only [MAX_COUNTER_TRIALS] at hk
    exact UInt32.toNat_ofNat_of_lt' (by omega)
  exact ⟨⟨x, hcw⟩, fun k' hk'' => hmin k' (Nat.zero_le _) (by omega)⟩

/-! ## An honest signature leads to the key's leaf -/

/-- A one-time signature from the seed recovers the leaf the seed gives the key.

The verifier walks each revealed value from position `x_i` to 3.

The signer walked it from 0 to `x_i`, so together they walk the whole chain. -/
theorem otsLeaf_otsSign {seed : Seed} {msg : ByteArray} {counter : UInt32} {y : Vector Digest V}
    (h : (otsSign (pureHash f) pp seed key msg).run = some (counter, y)) :
    (otsLeaf (pureHash f) pp key msg counter y).run
      = some (otsPublicLeaf (pureHash f) pp seed key).run := by
  -- Name the search result: a counter and its codeword.
  rw [otsSign_run, Option.map_eq_some_iff] at h
  obtain ⟨⟨counter', x⟩, hfind, hxy⟩ := h
  dsimp only at hxy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
  rw [Internal.findCounter] at hfind
  obtain ⟨-, -, -, -, hcw, -⟩ := Wots.findFirst_spec hfind
  -- The verifier recomputes the same codeword.
  simp only [otsLeaf, otsPublicLeaf, Id.run_bind, Id.run_pure, hcw, Xmss.ofFnInOrder_run]
  refine congrArg (fun ends => some (otsLeafHash (pureHash f) pp key ends).run)
    (Vector.ext fun j hj => ?_)
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  -- Signer's steps plus verifier's steps make the whole chain.
  have hx := (x[j]'hj).isLt
  have hsplit := Wots.chain_add (m := Id) (step := chainStep (pureHash f) pp key ⟨j, hj⟩)
    (start := 0) (s₁ := (x[j]'hj : Nat)) (s₂ := CHAIN_LENGTH - 1 - (x[j]'hj : Nat))
    (value := (chainStarts (pureHash f) pp seed key).run[j]'hj) (Nat.zero_add _).symm
    (by simp only [CHAIN_LENGTH] at *; omega) (by simp only [CHAIN_LENGTH] at *; omega)
  -- Steps revealed plus steps walked is the whole chain.
  exact hsplit.trans (Wots.chain_steps_congr (by simp only [CHAIN_LENGTH] at *; omega) _ _)

end EthLib.Cryptography.Sphincs
