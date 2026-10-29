import EthLib.Cryptography.Sphincs.Verify

/-!
# Proofs: `Sphincs.Verify`

What verification checks, as one statement.

```text
    D   = the digest of m and R,  idx and the leaves read from D
    K   = Fts.recover(idx, leaves, fors)
    accept  iff  the three layers, from K up, lead to the public key's root
```

Verification returns a yes or a no.

Here that answer is unfolded into the chain of checks behind it.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- The root the three layers of a signature lead to, from the FORS key its openings recover.

Nothing when a layer's counter does not encode its message as a codeword. -/
def signatureRoot (pk : PublicKey) (m : Message) (sig : Signature) : Option Digest :=
  let pp := pk.publicParam
  let d := messageDigest pp m sig.randomizer
  let idx := digestIndex d
  (layerRoot pp .bottom idx (forsKeyBytes (forsRecover pp idx (digestLeaves d) sig.fors)) sig.bottom).bind
    fun bottomRoot => (layerRoot pp .middle idx (packBytes bottomRoot) sig.middle).bind
      fun middleRoot => layerRoot pp .top idx (packBytes middleRoot) sig.top

/-- Verification accepts exactly when the layers lead to the public key's root. -/
theorem verify_iff (pk : PublicKey) (m : Message) (sig : Signature) :
    verify pk m sig = true ↔ signatureRoot pk m sig = some pk.root := by
  -- The verifier is a decision of that equation, written step by step.
  delta verify
  exact decide_eq_true_iff

/-- A layer leads to a root exactly when its counter encodes the message as a codeword. -/
theorem layerRoot_isSome_iff (pp : PublicParam) (layer : Layer) (idx : Nat) (msg : ByteArray)
    (sig : LayerSignature layer) :
    (layerRoot pp layer idx msg sig).isSome ↔
      (encode pp (OtsKey.ofIndex layer idx) msg sig.counter).isSome := by
  simp only [layerRoot, otsLeaf, Option.bind_eq_bind, Option.pure_def]
  cases encode pp (OtsKey.ofIndex layer idx) msg sig.counter <;> simp

end EthLib.Cryptography.Sphincs
