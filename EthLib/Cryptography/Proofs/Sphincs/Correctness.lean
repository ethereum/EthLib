module

public import EthLib.Cryptography.Sphincs.Verify
public import EthLib.Cryptography.Proofs.Sphincs.Sign
public import EthLib.Cryptography.Proofs.Sphincs.Tree
public import EthLib.Cryptography.Proofs.Sphincs.Fors
public import EthLib.Cryptography.Proofs.Sphincs.Verify
public import EthLib.Cryptography.Proofs.Sphincs.Digest

/-!
# Proofs: leanSPHINCS correctness

A signature this specification produces is one it accepts.

The signer rebuilds the public key as key generation computes it.

So the signer and the verifier hash the message into the same digest, and read the same `idx`.

- The FORS openings recover the FORS public key of instance `idx`.
- The bottom layer leads to the root of bottom tree `idx >> 8`.
- The middle layer leads to the root of middle tree `idx >> 16`.
- The top layer leads to the root of the top tree, which is `PK.root`.

Each layer's key signs exactly what the layer below leads to.

So the verifier walks the signer's path back.

# Assumption

Every theorem here assumes that signing succeeded.

Signing fails only when a one-time key finds no codeword in `2^32` counters.

This file does not bound how often that happens, since a bound needs the random oracle model.
-/

@[expose] public section

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

variable {f : ByteArray → Vector UInt8 32}

/-- An honest layer signature leads to the root of its key's tree. -/
theorem layerRoot_signLayer {pkSeed : PkSeed} {prf : Prf Id} {layer : Layer} {idx : Nat}
    {msg : Digest} {sig : LayerSignature layer}
    (h : (signLayer (pureHash f) pkSeed prf layer idx msg).run = .ok sig) :
    (layerRoot (pureHash f) pkSeed layer idx msg sig).run
      = some (treeRoot (pureHash f) pkSeed prf layer (OtsKey.ofIndex layer idx).tree).run := by
  obtain ⟨hots, hpath⟩ := signLayer_eq_ok h
  -- The one-time signature recovers the key's leaf, and the honest path climbs to the root.
  rw [layerRoot_run, otsLeaf_otsSign hots, Option.map_some, hpath]
  exact congrArg some (fold_path_root (OtsKey.ofIndex_leaf_lt layer idx))

/-! ## Correctness -/

/-- Verification accepts every signature the secret key produces.

The public key is the one key generation gives `SK.seed`. -/
theorem verify_sign {sk : SecretKey} {m : Message} {σ : Signature}
    (h : (signWith (pureHash f) sk m).run = .ok σ) :
    (verifyWith (pureHash f) (keyGenWith (pureHash f) sk.seed).run.2 m σ).run = true := by
  obtain ⟨-, hfors, hbottom, hmiddle, htop⟩ := sign_eq_ok rfl h
  simp only [layerMessage_run] at hbottom hmiddle htop
  rw [verify_iff, signatureRoot]
  -- Step 1: the FORS openings recover the FORS public key the bottom key signed.
  rw [hfors, forsRecover_forsSign]
  -- Step 2: each layer leads to the root of its key's tree, which the layer above signed.
  rw [layerRoot_signLayer hbottom, Option.bind_some, layerRoot_signLayer hmiddle, Option.bind_some,
    layerRoot_signLayer htop]
  -- Step 3: the top key's tree is the one top tree, whose root key generation computed.
  rw [OtsKey.ofIndex_top_tree (digestIndex_lt _)]
  rfl

/-- Correctness over any hash: a generated key pair verifies every signature it makes. -/
theorem verifyWith_keyGenWith_signWith {seed : Seed} {sk : SecretKey} {pk : PublicKey}
    {m : Message} {σ : Signature}
    (hk : (keyGenWith (pureHash f) seed).run = (sk, pk))
    (hs : (signWith (pureHash f) sk m).run = .ok σ) :
    (verifyWith (pureHash f) pk m σ).run = true := by
  -- The secret key is the seed, and the public key is the one it derives.
  have hsk : sk = ⟨seed⟩ := (congrArg Prod.fst hk).symm.trans rfl
  have hpk : pk = (keyGenWith (pureHash f) seed).run.2 := (congrArg Prod.snd hk).symm
  subst hsk hpk
  exact verify_sign hs

/-- Correctness: a generated key pair verifies every signature it makes. -/
theorem verify_keyGen_sign {seed : Seed} {sk : SecretKey} {pk : PublicKey} {m : Message}
    {σ : Signature} (hk : keyGen seed = (sk, pk)) (hs : sign sk m = .ok σ) :
    verify pk m σ = true :=
  verifyWith_keyGenWith_signWith (f := hash) hk hs

end EthLib.Cryptography.Sphincs
