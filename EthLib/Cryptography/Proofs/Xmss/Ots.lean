module

public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: WOTS+C one-time signatures

Correctness of the one-time signature: an honest one leads back to the key's own leaf.

Each theorem holds for every hash function `f`, run in the identity monad.

Keccak-256 is one such function, so the theorems cover the specification as it runs.

A variable `f` also keeps every proof from unfolding the hash on a concrete input.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {f : ByteArray → Vector UInt8 32} {pp : PublicParam} {layer : Layer} {e : UInt32}
  {i : Fin V}
  {start s₁ s₂ : Nat} {value : Digest}

/-! ## Chains -/

/-- Walking no steps leaves the value alone. -/
@[simp] theorem chain_zero (h : start + 0 < CHAIN_LENGTH) :
    (chain (pureHash f) pp layer e i start 0 h value).run = value := rfl

/-! ## An honest signature leads to the key's leaf -/

/-- What the one-time signer computes: the grinding result, with each chain walked to its digit.

`rw` unfolds the signer, not `simp`.

`simp` rewrites with `rfl` lemmas, and checking those makes Lean unfold the grinding loop.

That loop runs up to `2^32` trials. -/
theorem otsSign_run {seed : Seed} {msg : ByteArray} :
    (otsSign (pureHash f) pp seed layer e msg).run =
      ((Internal.findCodeword (pureHash f) pp layer e msg
          (randomizerBase (pureHash f) pp seed layer e msg).run 0 MAX_RANDOMIZER_TRIALS).run).map
        fun found => (found.1, Vector.ofFn fun i => (chain (pureHash f) pp layer e i 0
          (found.2[i]).val (by have := (found.2[i]).isLt; omega)
          (chainStarts (pureHash f) pp seed layer e).run[i]).run) := by
  rw [otsSign, Id.run_bind, Id.run_bind]
  cases (Internal.findCodeword (pureHash f) pp layer e msg
      (randomizerBase (pureHash f) pp seed layer e msg).run 0 MAX_RANDOMIZER_TRIALS).run with
  | none => rfl
  | some found =>
    obtain ⟨rho, x⟩ := found
    -- The signer reveals the chains in order, which is the vector of the walked chains.
    rw [Option.map_some, ← ofFnInOrder_run]
    rfl

/-- A one-time signature from the seed recovers the leaf the seed gives the key.

The verifier walks each revealed value from position `x_i` to 3.

The signer walked it from 0 to `x_i`, so together they walk the whole chain. -/
theorem otsLeaf_otsSign {seed : Seed} {msg : ByteArray} {rho : Randomizer} {y : Vector Digest V}
    (h : (otsSign (pureHash f) pp seed layer e msg).run = some (rho, y)) :
    (otsLeaf (pureHash f) pp layer e msg rho y).run
      = some (otsPublicLeaf (pureHash f) pp seed layer e).run := by
  -- Name the grinding result: a randomizer and its codeword.
  rw [otsSign_run, Option.map_eq_some_iff] at h
  obtain ⟨⟨rho', x⟩, hfind, hxy⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
  rw [Internal.findCodeword] at hfind
  obtain ⟨-, -, -, -, hcw, -⟩ := Wots.findFirst_spec hfind
  unfold Id.run at hcw
  replace hcw : codeword? (messageDigest (pureHash f) pp layer e msg rho').run = some x := hcw
  -- The verifier recomputes the same codeword.
  simp only [otsLeaf, otsPublicLeaf, Id.run_bind, Id.run_pure, hcw, ofFnInOrder_run]
  refine congrArg (fun ends => some (otsLeafHash (pureHash f) pp layer e ends).run)
    (Vector.ext fun j hj => ?_)
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  -- Signer's steps plus verifier's steps make the whole chain.
  have hx := (x[j]'hj).isLt
  have hsplit := Wots.chain_add (m := Id) (step := chainStep (pureHash f) pp layer e ⟨j, hj⟩)
    (start := 0) (s₁ := (x[j]'hj : Nat)) (s₂ := CHAIN_LENGTH - 1 - (x[j]'hj : Nat))
    (value := (chainStarts (pureHash f) pp seed layer e).run[j]'hj) (Nat.zero_add _).symm
    (by simp only [CHAIN_LENGTH] at *; omega) (by simp only [CHAIN_LENGTH] at *; omega)
  -- Steps revealed plus steps walked is the whole chain.
  exact hsplit.trans (Wots.chain_steps_congr (by simp only [CHAIN_LENGTH] at *; omega) _ _)

/-! ## A key's leaf in pieces -/

/-- A key's leaf, from its chain starts, its chain ends and its leaf hash.

A known answer checks each piece on its own. -/
theorem otsPublicLeaf_eq {seed : Seed} {starts ends : Vector Digest V} {leaf : Digest}
    (hstarts : (chainStarts (pureHash f) pp seed layer e).run = starts)
    (hends : ∀ i : Fin V,
      (chain (pureHash f) pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i]).run = ends[i])
    (hleaf : (otsLeafHash (pureHash f) pp layer e ends).run = leaf) :
    (otsPublicLeaf (pureHash f) pp seed layer e).run = leaf := by
  -- The walked chains are the stated ends, chain by chain.
  have hv : (Vector.ofFn fun i =>
      (chain (pureHash f) pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i]).run) = ends :=
    Vector.ext fun i hi => by simpa using hends ⟨i, hi⟩
  simp only [otsPublicLeaf, Id.run_bind, hstarts, ofFnInOrder_run, hv, hleaf]

end EthLib.Cryptography.Xmss
