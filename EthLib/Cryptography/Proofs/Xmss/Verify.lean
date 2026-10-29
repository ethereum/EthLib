import EthLib.Cryptography.Xmss.Verify
import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: `Xmss.Verify`

What an accepting verifier has checked.

Each theorem holds for every hash function `f`, run in the identity monad.

`verify` is the case `f = hash`.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {f : ByteArray → Vector UInt8 32}

/-! ## The verifier as a value -/

/-- What `Ots.leaf` computes.

Nothing unless the digest is a codeword, else the leaf of the walked chains. -/
theorem otsLeaf_run {pp : PublicParam} {layer : Layer} {e : UInt32} {msg : ByteArray}
    {rho : Randomizer} {y : Vector Digest V} :
    (otsLeaf (pureHash f) pp layer e msg rho y).run
      = (codeword? (messageDigest (pureHash f) pp layer e msg rho).run).map
        fun (x : Vector (Fin CHAIN_LENGTH) V) =>
          (otsLeafHash (pureHash f) pp layer e (Vector.ofFn fun i =>
            (chain (pureHash f) pp layer e i x[i] (CHAIN_LENGTH - 1 - x[i])
              (by have := x[i].isLt; omega) y[i]).run)).run := by
  rw [otsLeaf, Id.run_bind]
  cases codeword? (messageDigest (pureHash f) pp layer e msg rho).run with
  | none => rfl
  | some x =>
    -- The chains are walked in order, which is the vector of the walked chains.
    rw [Option.map_some, ← ofFnInOrder_run]
    rfl

/-- What a layer's root computes: the recovered leaf, folded up the path. -/
theorem layerRoot_run {pp : PublicParam} {layer : Layer} {e : Nat} {msg : ByteArray}
    {sig : LayerSignature} :
    (layerRoot (pureHash f) pp layer e msg sig).run
      = (otsLeaf (pureHash f) pp layer (UInt32.ofNat e) msg sig.randomizer sig.chainValues).run.map
          fun leaf => (fold (pureHash f) pp layer e leaf sig.path).run := by
  rw [layerRoot, Id.run_bind]
  cases (otsLeaf (pureHash f) pp layer (UInt32.ofNat e) msg sig.randomizer sig.chainValues).run with
  | none => rfl
  | some leaf => rfl

/-- What the verifier computes.

Whether both layers succeed and the top one reaches the key's root. -/
theorem verifyWith_run {pk : PublicKey} {m : Message} {sig : Signature} :
    (verifyWith (pureHash f) pk m sig).run
      = decide (((layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat (packBytes m)
          sig.bottom).run.bind fun bottomRoot =>
            (layerRoot (pureHash f) pk.publicParam .top (bottomTree sig.leafIndex)
              (packBytes bottomRoot) sig.top).run) = some pk.root) := by
  rw [verifyWith, Id.run_bind]
  cases (layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat (packBytes m)
      sig.bottom).run with
  | none => rfl
  | some bottomRoot =>
    rw [Id.run_bind, Option.bind_some]
    cases (layerRoot (pureHash f) pk.publicParam .top (bottomTree sig.leafIndex)
        (packBytes bottomRoot) sig.top).run with
    | none => rfl
    -- The two sides decide the same equality, one inside `some`.
    | some root => simp

/-! ## Acceptance -/

/-- Acceptance, unfolded.

The bottom layer leads to some root, the top layer signs that root, and its path reaches the key's root. -/
theorem verify_iff {pk : PublicKey} {m : Message} {sig : Signature} :
    (verifyWith (pureHash f) pk m sig).run = true ↔
      ∃ bottomRoot,
        (layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat (packBytes m)
          sig.bottom).run = some bottomRoot ∧
        (layerRoot (pureHash f) pk.publicParam .top (bottomTree sig.leafIndex)
          (packBytes bottomRoot) sig.top).run = some pk.root := by
  rw [verifyWith_run]
  simp only [decide_eq_true_eq, Option.bind_eq_some_iff]

/-- A signature whose bottom digest is not a codeword rejects, whatever the rest. -/
theorem verify_of_layerRoot_none {pk : PublicKey} {m : Message} {sig : Signature}
    (h : (layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat (packBytes m)
      sig.bottom).run = none) :
    (verifyWith (pureHash f) pk m sig).run = false := by
  rw [verifyWith_run, h]
  simp

/-! ## Verifying in pieces

A known answer evaluates the verifier hash by hash.

These lemmas let each piece be checked on its own, with its value stated. -/

/-- Chain `i` walked from the position its digit names to position 3. -/
def chainEnd (f : ByteArray → Vector UInt8 32) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) (y : Vector Digest V) (i : Fin V) : Digest :=
  (chain (pureHash f) pp layer e i x[i] (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega)
    y[i]).run

/-- A layer's root, from its codeword, its chain ends, its leaf and its path. -/
theorem layerRoot_eq {pp : PublicParam} {layer : Layer} {e : Nat} {msg : ByteArray}
    {sig : LayerSignature} {x : Vector (Fin CHAIN_LENGTH) V} {ends : Vector Digest V}
    {leaf root : Digest}
    (hx : codeword? (messageDigest (pureHash f) pp layer (UInt32.ofNat e) msg sig.randomizer).run
      = some x)
    (hends : ∀ i : Fin V, chainEnd f pp layer (UInt32.ofNat e) x sig.chainValues i = ends[i])
    (hleaf : (otsLeafHash (pureHash f) pp layer (UInt32.ofNat e) ends).run = leaf)
    (hroot : (fold (pureHash f) pp layer e leaf sig.path).run = root) :
    (layerRoot (pureHash f) pp layer e msg sig).run = some root := by
  -- The recovered ends are the stated ones, chain by chain.
  have hv : (Vector.ofFn fun i => (chain (pureHash f) pp layer (UInt32.ofNat e) i x[i]
      (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega) sig.chainValues[i]).run) = ends :=
    Vector.ext fun i hi => by simpa [chainEnd] using hends ⟨i, hi⟩
  rw [layerRoot_run, otsLeaf_run, hx, Option.map_some, hv, hleaf, Option.map_some, hroot]

/-- Acceptance, from the two layers' roots. -/
theorem verify_of_layerRoot {pk : PublicKey} {m : Message} {sig : Signature} {bottomRoot : Digest}
    (hb : (layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat (packBytes m)
      sig.bottom).run = some bottomRoot)
    (ht : (layerRoot (pureHash f) pk.publicParam .top (bottomTree sig.leafIndex)
      (packBytes bottomRoot) sig.top).run = some pk.root) :
    (verifyWith (pureHash f) pk m sig).run = true :=
  verify_iff.mpr ⟨bottomRoot, hb, ht⟩

/-- Rejection, when the top layer leads to some other root. -/
theorem verify_of_layerRoot_ne {pk : PublicKey} {m : Message} {sig : Signature}
    {bottomRoot root : Digest}
    (hb : (layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat (packBytes m)
      sig.bottom).run = some bottomRoot)
    (ht : (layerRoot (pureHash f) pk.publicParam .top (bottomTree sig.leafIndex)
      (packBytes bottomRoot) sig.top).run = some root)
    (hne : root ≠ pk.root) :
    (verifyWith (pureHash f) pk m sig).run = false := by
  rw [verifyWith_run, hb, Option.bind_some, ht]
  simp [hne]

end EthLib.Cryptography.Xmss
