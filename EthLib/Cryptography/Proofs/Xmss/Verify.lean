import EthLib.Cryptography.Xmss.Verify

/-!
# Proofs: `Xmss.Verify`

What an accepting verifier has checked.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- Acceptance, unfolded.

The bottom layer leads to some root, the top layer signs that root, and its path reaches the key's root. -/
theorem verify_iff {pk : PublicKey} {m : Message} {sig : Signature} :
    verify pk m sig = true ↔
      ∃ bottomRoot,
        layerRoot pk.publicParam .bottom sig.leafIndex.toNat (packBytes m) sig.bottom
          = some bottomRoot ∧
        layerRoot pk.publicParam .top (bottomTree sig.leafIndex) (packBytes bottomRoot) sig.top
          = some pk.root := by
  simp only [verify, decide_eq_true_eq, Option.bind_eq_bind, Option.bind_eq_some_iff]

/-- A signature whose bottom digest is not a codeword rejects, whatever the rest. -/
theorem verify_of_layerRoot_none {pk : PublicKey} {m : Message} {sig : Signature}
    (h : layerRoot pk.publicParam .bottom sig.leafIndex.toNat (packBytes m) sig.bottom = none) :
    verify pk m sig = false := by
  simp [verify, h]

/-! ## Verifying in pieces

A known answer evaluates the verifier hash by hash.

These lemmas let each piece be checked on its own, with its value stated. -/

/-- Chain `i` walked from the position its digit names to position 3. -/
def chainEnd (pp : PublicParam) (layer : Layer) (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V)
    (y : Vector Digest V) (i : Fin V) : Digest :=
  chain pp layer e i x[i] (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega) y[i]

/-- A layer's root, from its codeword, its chain ends, its leaf and its path. -/
theorem layerRoot_eq {pp : PublicParam} {layer : Layer} {e : Nat} {msg : ByteArray}
    {sig : LayerSignature} {x : Vector (Fin CHAIN_LENGTH) V} {ends : Vector Digest V}
    {leaf root : Digest}
    (hx : codeword? (messageDigest pp layer (UInt32.ofNat e) msg sig.randomizer) = some x)
    (hends : ∀ i : Fin V, chainEnd pp layer (UInt32.ofNat e) x sig.chainValues i = ends[i])
    (hleaf : otsLeafHash pp layer (UInt32.ofNat e) ends = leaf)
    (hroot : fold pp layer e leaf sig.path = root) :
    layerRoot pp layer e msg sig = some root := by
  -- The recovered ends are the stated ones, chain by chain.
  have hv : (Vector.ofFn fun i => chain pp layer (UInt32.ofNat e) i x[i]
      (CHAIN_LENGTH - 1 - x[i]) (by have := x[i].isLt; omega) sig.chainValues[i]) = ends :=
    Vector.ext fun i hi => by simpa [chainEnd] using hends ⟨i, hi⟩
  simp only [layerRoot, otsLeaf, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    hv, hleaf, hroot]

/-- Acceptance, from the two layers' roots. -/
theorem verify_of_layerRoot {pk : PublicKey} {m : Message} {sig : Signature} {bottomRoot : Digest}
    (hb : layerRoot pk.publicParam .bottom sig.leafIndex.toNat (packBytes m) sig.bottom
      = some bottomRoot)
    (ht : layerRoot pk.publicParam .top (bottomTree sig.leafIndex) (packBytes bottomRoot) sig.top
      = some pk.root) :
    verify pk m sig = true :=
  verify_iff.mpr ⟨bottomRoot, hb, ht⟩

/-- Rejection, when the top layer leads to some other root. -/
theorem verify_of_layerRoot_ne {pk : PublicKey} {m : Message} {sig : Signature}
    {bottomRoot root : Digest}
    (hb : layerRoot pk.publicParam .bottom sig.leafIndex.toNat (packBytes m) sig.bottom
      = some bottomRoot)
    (ht : layerRoot pk.publicParam .top (bottomTree sig.leafIndex) (packBytes bottomRoot) sig.top
      = some root)
    (hne : root ≠ pk.root) :
    verify pk m sig = false := by
  simp [verify, hb, ht, hne]

end EthLib.Cryptography.Xmss
