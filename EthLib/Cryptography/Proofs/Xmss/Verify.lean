module

public import EthLib.Cryptography.Xmss.Verify
public import EthLib.Cryptography.Proofs.Xmss.Types

/-!
# Proofs: leanXMSS verification

What an accepting verifier has checked.

Each theorem holds for every hash function `f`, run in the identity monad.

`verify` is the case `f = hash`.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {f : Array UInt64 → Lanes4}

/-! ## The two layers' keys

The bottom key of a leaf index `idx` is `idx` itself, and the top key is `b = floor(idx / 2^16)`. -/

/-- The top key of a leaf index is its integer divided by `2^16`. -/
theorem bottomTree_eq_div (idx : LeafIndex) : bottomTree idx = idx.toNat / 2 ^ LAYER_HEIGHT :=
  rfl

/-- The bottom tree of a leaf index is a key of the top tree: it is below `2^16`. -/
theorem bottomTree_lt (idx : LeafIndex) : bottomTree idx < 2 ^ LAYER_HEIGHT := by
  have := idx.toNat_lt_size
  simp only [bottomTree, LAYER_HEIGHT, UInt32.size] at *
  omega

/-- The top key, as a 32-bit word, does not wrap. -/
theorem toNat_ofNat_bottomTree (idx : LeafIndex) :
    (UInt32.ofNat (bottomTree idx)).toNat = bottomTree idx := by
  have := bottomTree_lt idx
  simp only [LAYER_HEIGHT] at this
  exact UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)

/-! ## The verifier as a value -/

/-- What the one-time leaf recovery computes.

Nothing unless the digest is a codeword, else the leaf of the walked chains. -/
theorem otsLeaf_run {publicParam : PublicParam} {layer : Layer} {e : UInt32} {msg : Array UInt64}
    {rho : Randomizer} {y : Vector Digest V} :
    (otsLeaf (pureHash f) publicParam layer e msg rho y).run
      = (codeword? (messageDigest (pureHash f) publicParam layer e msg rho).run).map
        fun (x : Vector (Fin CHAIN_LENGTH) V) =>
          (otsLeafHash (pureHash f) publicParam layer e (Vector.ofFn fun i =>
            (chain (pureHash f) publicParam layer e i x[i] (CHAIN_LENGTH - 1 - x[i])
              (by have := x[i].isLt; omega) y[i]).run)).run := by
  rw [otsLeaf, Id.run_bind]
  cases codeword? (messageDigest (pureHash f) publicParam layer e msg rho).run with
  | none => rfl
  | some x =>
    -- The chains are walked in order, which is the vector of the walked chains.
    rw [Option.map_some, ← HashSig.ofFnInOrder_run]
    rfl

/-- What a layer's root computes: the recovered leaf, folded up the path. -/
theorem layerRoot_run {publicParam : PublicParam} {layer : Layer} {e : Nat} {msg : Array UInt64}
    {sig : LayerSignature} :
    (layerRoot (pureHash f) publicParam layer e msg sig).run
      = (otsLeaf (pureHash f) publicParam layer
        (UInt32.ofNat e) msg sig.randomizer sig.chainValues).run.map
          fun leaf => (fold (pureHash f) publicParam layer e leaf sig.path).run := by
  rw [layerRoot, Id.run_bind]
  cases (otsLeaf (pureHash f) publicParam layer
    (UInt32.ofNat e) msg sig.randomizer sig.chainValues).run with
  | none => rfl
  | some leaf => rfl

/-- What the verifier computes.

Whether both layers succeed and the top one reaches the key's root. -/
theorem verifyWith_run {pk : PublicKey} {m : Message} {sig : Signature} :
    (verifyWith (pureHash f) pk m sig).run
      = decide (((layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat m.toArray
          sig.bottom).run.bind fun bottomRoot =>
            (layerRoot (pureHash f) pk.publicParam .top (bottomTree sig.leafIndex)
              bottomRoot.toArray sig.top).run) = some pk.root) := by
  rw [verifyWith, Id.run_bind]
  cases (layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat m.toArray
      sig.bottom).run with
  | none => rfl
  | some bottomRoot =>
    rw [Id.run_bind, Option.bind_some]
    cases (layerRoot (pureHash f) pk.publicParam .top (bottomTree sig.leafIndex)
        bottomRoot.toArray sig.top).run with
    | none => rfl
    -- The two sides decide the same equality, one inside `some`.
    | some root => simp

/-- `Ver(pk, m, sigma)` is the verifier over a hash, at Keccak-256 in the identity monad.

So every theorem proved for any hash applies to the deployed verifier. -/
theorem verify_eq_verifyWith (pk : PublicKey) (m : Message) (sig : Signature) :
    verify pk m sig = (verifyWith hashId pk m sig).run :=
  rfl

/-! ## Acceptance -/

/-- Acceptance, unfolded.

The bottom layer leads to some root, and the top layer signs that root.

The path of the top layer reaches the key's root. -/
theorem verify_iff {pk : PublicKey} {m : Message} {sig : Signature} :
    (verifyWith (pureHash f) pk m sig).run = true ↔
      ∃ bottomRoot,
        (layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat m.toArray
          sig.bottom).run = some bottomRoot ∧
        (layerRoot (pureHash f) pk.publicParam .top (bottomTree sig.leafIndex)
          bottomRoot.toArray sig.top).run = some pk.root := by
  rw [verifyWith_run]
  simp only [decide_eq_true_eq, Option.bind_eq_some_iff]

/-- A signature whose bottom digest is not a codeword rejects, whatever the rest. -/
theorem verify_of_layerRoot_none {pk : PublicKey} {m : Message} {sig : Signature}
    (h : (layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat m.toArray
      sig.bottom).run = none) :
    (verifyWith (pureHash f) pk m sig).run = false := by
  rw [verifyWith_run, h]
  simp

/-! ## A layer in pieces

A layer's root is stated through its codeword, its chain ends, its leaf and its path.

So a proof that computes each piece, such as a circuit's, reaches the root by rewriting. -/

/-- Chain `i` walked from the position its digit names to position 3. -/
def chainEnd (f : Array UInt64 → Lanes4) (publicParam : PublicParam) (layer : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) (y : Vector Digest V) (i : Fin V) : Digest :=
  (chain (pureHash f) publicParam layer e i x[i] (CHAIN_LENGTH - 1 - x[i])
    (by have := x[i].isLt; omega)
    y[i]).run

/-- A chain end is the chain walked from its digit, for the step count that reaches position 3.

A circuit fixes the count from the digit: `3 - x_i` steps. -/
theorem chainEnd_eq_chain {publicParam : PublicParam} {layer : Layer} {e : UInt32}
    {x : Vector (Fin CHAIN_LENGTH) V} {y : Vector Digest V} {i : Fin V} {k : Nat}
    (hk : (x[i] : Nat) + k = CHAIN_LENGTH - 1) :
    chainEnd f publicParam layer e x y i
      = (chain (pureHash f) publicParam layer e i x[i] k (by simp only [CHAIN_LENGTH] at *; omega)
          y[i]).run := by
  -- Both walks start at the digit, and their step counts agree.
  unfold chainEnd
  congr 2
  omega

/-- A layer reaches a root exactly when its digest is a codeword and the path leads its leaf there.

The leaf is the hash of the chains walked from the codeword's digits to their ends. -/
theorem layerRoot_eq_some_iff {publicParam : PublicParam} {layer : Layer} {e : Nat}
    {msg : Array UInt64} {sig : LayerSignature} {root : Digest} :
    (layerRoot (pureHash f) publicParam layer e msg sig).run = some root ↔
      ∃ x, codeword? (messageDigest (pureHash f) publicParam layer
          (UInt32.ofNat e) msg sig.randomizer).run = some x ∧
        (fold (pureHash f) publicParam layer e
          (otsLeafHash (pureHash f) publicParam layer (UInt32.ofNat e)
            (Vector.ofFn (chainEnd f publicParam layer (UInt32.ofNat e) x sig.chainValues))).run
          sig.path).run = root := by
  rw [layerRoot_run, otsLeaf_run, Option.map_map, Option.map_eq_some_iff]
  -- The walked chains are the chain ends, by their definition.
  exact Iff.rfl

/-- A layer reaches no root exactly when its digest is not a codeword.

Climbing the path never fails, so only the codeword test can. -/
theorem layerRoot_eq_none_iff {publicParam : PublicParam} {layer : Layer} {e : Nat}
    {msg : Array UInt64} {sig : LayerSignature} :
    (layerRoot (pureHash f) publicParam layer e msg sig).run = none ↔
      codeword? (messageDigest (pureHash f) publicParam layer
        (UInt32.ofNat e) msg sig.randomizer).run = none := by
  rw [layerRoot_run, otsLeaf_run, Option.map_map, Option.map_eq_none_iff]

/-- A layer's root, from its codeword, its chain ends, its leaf and its path, each named.

It is the converse direction of the equivalence above, with every piece given its value. -/
theorem layerRoot_eq {publicParam : PublicParam} {layer : Layer} {e : Nat} {msg : Array UInt64}
    {sig : LayerSignature} {x : Vector (Fin CHAIN_LENGTH) V} {ends : Vector Digest V}
    {leaf root : Digest}
    (hx : codeword? (messageDigest (pureHash f) publicParam layer
      (UInt32.ofNat e) msg sig.randomizer).run
      = some x)
    (hends : ∀ i : Fin V, chainEnd f publicParam layer
      (UInt32.ofNat e) x sig.chainValues i = ends[i])
    (hleaf : (otsLeafHash (pureHash f) publicParam layer (UInt32.ofNat e) ends).run = leaf)
    (hroot : (fold (pureHash f) publicParam layer e leaf sig.path).run = root) :
    (layerRoot (pureHash f) publicParam layer e msg sig).run = some root := by
  -- The recovered ends are the stated ones, chain by chain.
  have hv : Vector.ofFn (chainEnd f publicParam layer (UInt32.ofNat e) x sig.chainValues) = ends :=
    Vector.ext fun i hi => by simpa using hends ⟨i, hi⟩
  exact layerRoot_eq_some_iff.mpr ⟨x, hx, by rw [hv, hleaf, hroot]⟩

/-- Acceptance, from the two layers' roots. -/
theorem verify_of_layerRoot {pk : PublicKey} {m : Message} {sig : Signature} {bottomRoot : Digest}
    (hb : (layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat m.toArray
      sig.bottom).run = some bottomRoot)
    (ht : (layerRoot (pureHash f) pk.publicParam .top (bottomTree sig.leafIndex)
      bottomRoot.toArray sig.top).run = some pk.root) :
    (verifyWith (pureHash f) pk m sig).run = true :=
  verify_iff.mpr ⟨bottomRoot, hb, ht⟩

/-- Rejection, when the top layer leads to some other root. -/
theorem verify_of_layerRoot_ne {pk : PublicKey} {m : Message} {sig : Signature}
    {bottomRoot root : Digest}
    (hb : (layerRoot (pureHash f) pk.publicParam .bottom sig.leafIndex.toNat m.toArray
      sig.bottom).run = some bottomRoot)
    (ht : (layerRoot (pureHash f) pk.publicParam .top (bottomTree sig.leafIndex)
      bottomRoot.toArray sig.top).run = some root)
    (hne : root ≠ pk.root) :
    (verifyWith (pureHash f) pk m sig).run = false := by
  rw [verifyWith_run, hb, Option.bind_some, ht]
  simp [hne]

end EthLib.Cryptography.Xmss
