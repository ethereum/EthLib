import EthLib.Cryptography.Sphincs.Verify
import EthLib.Cryptography.Proofs.Sphincs.Sign
import EthLib.Cryptography.Proofs.Sphincs.Tree
import EthLib.Cryptography.Proofs.Sphincs.Fors
import EthLib.Cryptography.Proofs.Sphincs.Verify
import EthLib.Cryptography.Proofs.Sphincs.Digest

/-!
# Proofs: leanSPHINCS correctness

A signature this specification produces is one it accepts.

- The FORS openings recover the FORS key of instance `idx`.
- The bottom layer leads to the root of bottom tree `idx >> 7`.
- The middle layer leads to the root of middle tree `idx >> 14`.
- The top layer leads to the root of the top tree, which is the public key's.

Each layer's key signs exactly what the layer below leads to, so the verifier walks the signer's path back.

# Assumption

Every theorem here assumes that signing succeeded.

Signing fails only when a one-time key finds no codeword in `2^32` counters.

How often that happens is not proved: it needs the random oracle model.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Indices -/

/-- A key's leaf index is a leaf of its tree. -/
theorem OtsKey.ofIndex_leaf_lt (layer : Layer) (idx : Nat) :
    (OtsKey.ofIndex layer idx).leaf < 2 ^ layer.height :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- An index of 26 bits leads to the one top tree, tree 0. -/
theorem OtsKey.ofIndex_top_tree {idx : Nat} (h : idx < 2 ^ HEIGHT) :
    (OtsKey.ofIndex .top idx).tree = 0 := by
  -- The top tree number is the bits above all three layers, of which there are none.
  simp only [OtsKey.ofIndex, Layer.below, Layer.height, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (by simpa [HEIGHT, TOP_HEIGHT, LOWER_HEIGHT] using h)

/-- Each key's leaf, read below its own tree, is the tree the layer under it uses.

- For the middle key, `tree * 2^8 + leaf = idx >> 8`, the bottom key's tree.
- For the top key, `tree * 2^10 + leaf = idx >> 16`, the middle key's tree.

So the middle and top keys sign the roots of the trees on the index's own path. -/
theorem OtsKey.ofIndex_child (idx : Nat) :
    (OtsKey.ofIndex .middle idx).tree * 2 ^ Layer.middle.height + (OtsKey.ofIndex .middle idx).leaf
        = (OtsKey.ofIndex .bottom idx).tree ∧
      (OtsKey.ofIndex .top idx).tree * 2 ^ Layer.top.height + (OtsKey.ofIndex .top idx).leaf
        = (OtsKey.ofIndex .middle idx).tree := by
  simp only [OtsKey.ofIndex, Layer.below, Layer.height, LOWER_HEIGHT, TOP_HEIGHT,
    Nat.shiftRight_eq_div_pow]
  -- A quotient and a remainder by `2^8` or `2^10` rebuild the number they came from.
  show idx / 65536 * 256 + idx / 256 % 256 = idx / 256 ∧
    idx / 67108864 * 1024 + idx / 65536 % 1024 = idx / 65536
  omega

/-! ## One layer -/

/-- An honest layer signature leads to the root of its key's tree. -/
theorem layerRoot_signLayer {pp : PublicParam} {seed : Seed} {layer : Layer} {idx : Nat}
    {msg : ByteArray} {sig : LayerSignature layer} (h : signLayer pp seed layer idx msg = .ok sig) :
    layerRoot pp layer idx msg sig = some (treeRoot pp seed layer (OtsKey.ofIndex layer idx).tree) := by
  obtain ⟨hots, hpath⟩ := signLayer_eq_ok h
  -- The one-time signature recovers the key's leaf, and the honest path climbs to the root.
  rw [layerRoot, otsLeaf_otsSign hots, hpath]
  exact congrArg some (fold_path_root (OtsKey.ofIndex_leaf_lt layer idx))

/-! ## Correctness -/

/-- Verification accepts every signature the secret key produces. -/
theorem verify_sign {sk : SecretKey} {m : Message} {σ : Signature} (h : sign sk m = .ok σ) :
    verify sk.publicKey m σ = true := by
  obtain ⟨-, hfors, hbottom, hmiddle, htop⟩ := sign_eq_ok h
  simp only [layerMessage] at hbottom hmiddle htop
  rw [verify_iff, signatureRoot]
  -- The public key's parameter is the secret key's.
  rw [show sk.publicKey.publicParam = sk.publicParam from rfl]
  -- Step 1: the FORS openings recover the FORS key the bottom key signed.
  rw [hfors, forsRecover_forsSign]
  -- Step 2: each layer leads to the root of its key's tree, which the layer above signed.
  rw [layerRoot_signLayer hbottom, Option.bind_some, layerRoot_signLayer hmiddle, Option.bind_some,
    layerRoot_signLayer htop]
  -- Step 3: the top key's tree is the one top tree, whose root is the public key's.
  rw [OtsKey.ofIndex_top_tree (digestIndex_lt _)]
  rfl

/-- Correctness: a generated key pair verifies every signature it makes. -/
theorem verify_keyGen_sign {seed : Seed} {sk : SecretKey} {pk : PublicKey} {m : Message}
    {σ : Signature} (hk : keyGen seed = (sk, pk)) (hs : sign sk m = .ok σ) :
    verify pk m σ = true := by
  -- The public key is the one the secret key derives.
  simp only [keyGen, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  exact verify_sign hs

end EthLib.Cryptography.Sphincs
