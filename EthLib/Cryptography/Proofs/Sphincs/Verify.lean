module

public import EthLib.Cryptography.Sphincs.Verify
public import EthLib.Cryptography.Proofs.HashSig

/-!
# Proofs: leanSPHINCS verification

What verification checks, as one statement.

```text
    D   = the digest of m and R,  idx and the leaves read from D
    K   = Fts.recover(idx, leaves, fors)
    accept  iff  the three layers, from K up, lead to the public key's root
```

Verification returns a yes or a no.

Here that answer is unfolded into the chain of checks behind it.

Each theorem holds for every hash function `f`, run in the identity monad.

`verify` is the case `f = hash`.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {f : ByteArray → Vector UInt8 32}

/-! ## The verifier as a value -/

/-- What the one-time leaf recovery computes.

Nothing unless the counter gives a codeword, else the leaf of the walked chains. -/
theorem otsLeaf_run {pp : PublicParam} {key : OtsKey} {msg : ByteArray} {counter : UInt32}
    {y : Vector Digest V} :
    (otsLeaf (pureHash f) pp key msg counter y).run
      = (encode (pureHash f) pp key msg counter).run.map fun (x : Codeword) =>
          (otsLeafHash (pureHash f) pp key (Vector.ofFn fun i =>
            (chain (pureHash f) pp key i x[i] (CHAIN_LENGTH - 1 - x[i])
              (by have := x[i].isLt; omega) y[i]).run)).run := by
  rw [otsLeaf, Id.run_bind]
  cases (encode (pureHash f) pp key msg counter).run with
  | none => rfl
  | some x =>
    -- The chains are walked in order, which is the vector of the walked chains.
    rw [Option.map_some, ← HashSig.ofFnInOrder_run]
    rfl

/-- What a layer's root computes: the recovered leaf, folded up the path. -/
theorem layerRoot_run {pp : PublicParam} {layer : Layer} {idx : Nat} {msg : ByteArray}
    {sig : LayerSignature layer} :
    (layerRoot (pureHash f) pp layer idx msg sig).run
      = (otsLeaf (pureHash f) pp (OtsKey.ofIndex layer idx) msg sig.counter
          sig.chainValues).run.map fun leaf =>
        (fold (pureHash f) pp layer (OtsKey.ofIndex layer idx).tree
          (OtsKey.ofIndex layer idx).leaf leaf sig.path).run := by
  rw [layerRoot, Id.run_bind]
  cases (otsLeaf (pureHash f) pp (OtsKey.ofIndex layer idx) msg sig.counter
      sig.chainValues).run with
  | none => rfl
  | some leaf => rfl

/-- The root the three layers of a signature lead to, from the FORS key its openings recover.

Nothing when a layer's counter does not encode its message as a codeword. -/
def signatureRoot (f : ByteArray → Vector UInt8 32) (pk : PublicKey) (m : Message)
    (sig : Signature) : Option Digest :=
  let pp := pk.publicParam
  let d := (messageDigest (pureHash f) pp m sig.randomizer).run
  let idx := digestIndex d
  let key := (forsRecover (pureHash f) pp idx (digestLeaves d) sig.fors).run
  (layerRoot (pureHash f) pp .bottom idx (forsKeyBytes key) sig.bottom).run.bind
    fun bottomRoot =>
      (layerRoot (pureHash f) pp .middle idx (packBytes bottomRoot) sig.middle).run.bind
      fun middleRoot => (layerRoot (pureHash f) pp .top idx (packBytes middleRoot) sig.top).run

/-! ## Acceptance -/

/-- Verification accepts exactly when the layers lead to the public key's root. -/
theorem verify_iff (pk : PublicKey) (m : Message) (sig : Signature) :
    (verifyWith (pureHash f) pk m sig).run = true ↔ signatureRoot f pk m sig = some pk.root := by
  -- The verifier decides that equation, one layer at a time.
  rw [verifyWith, Id.run_bind, Id.run_bind, Id.run_bind, signatureRoot]
  cases (layerRoot (pureHash f) pk.publicParam .bottom
      (digestIndex (messageDigest (pureHash f) pk.publicParam m sig.randomizer).run)
      (forsKeyBytes (forsRecover (pureHash f) pk.publicParam
        (digestIndex (messageDigest (pureHash f) pk.publicParam m sig.randomizer).run)
        (digestLeaves (messageDigest (pureHash f) pk.publicParam m sig.randomizer).run)
        sig.fors).run) sig.bottom).run with
  | none => simp
  | some bottomRoot =>
    rw [Id.run_bind, Option.bind_some]
    cases (layerRoot (pureHash f) pk.publicParam .middle
        (digestIndex (messageDigest (pureHash f) pk.publicParam m sig.randomizer).run)
        (packBytes bottomRoot) sig.middle).run with
    | none => simp
    | some middleRoot =>
      rw [Id.run_bind, Option.bind_some]
      cases (layerRoot (pureHash f) pk.publicParam .top
          (digestIndex (messageDigest (pureHash f) pk.publicParam m sig.randomizer).run)
          (packBytes middleRoot) sig.top).run with
      | none => simp
      -- The two sides decide the same equality, one inside `some`.
      | some root => simp

/-- A layer leads to a root exactly when its counter encodes the message as a codeword. -/
theorem layerRoot_isSome_iff (pp : PublicParam) (layer : Layer) (idx : Nat) (msg : ByteArray)
    (sig : LayerSignature layer) :
    (layerRoot (pureHash f) pp layer idx msg sig).run.isSome ↔
      (encode (pureHash f) pp (OtsKey.ofIndex layer idx) msg sig.counter).run.isSome := by
  rw [layerRoot_run, otsLeaf_run]
  cases (encode (pureHash f) pp (OtsKey.ofIndex layer idx) msg sig.counter).run <;> simp

end EthLib.Cryptography.Sphincs
