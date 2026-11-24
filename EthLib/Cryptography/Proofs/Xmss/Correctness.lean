module

public import EthLib.Cryptography.Proofs.Xmss.Sign
public import EthLib.Cryptography.Proofs.Xmss.Tree
public import EthLib.Cryptography.Proofs.Xmss.Verify

/-!
# Proofs: leanXMSS correctness

A signature this specification produces is one it accepts.

- Bottom layer: the one-time signature of the message gives leaf `idx`, in bottom tree `b`.
- The bottom tree is `b = floor(idx / 2^16)`.
- Its path folds that leaf to the root of tree `b`, the root that the top key signed.
- Top layer: the one-time signature of that root gives leaf `b` of the top tree.
- Its path folds that leaf to the root of the public key.

Correctness holds for every hash function `f`, run in the identity monad.

The case `f = hash` is the specification as it runs.

# Assumption

Every theorem here assumes that signing succeeded.

Signing fails only when a one-time key finds no codeword in `2^32` trials.

In the random oracle model, signing fails with probability at most `2 exp(-4000)`.

The bound assumes that the oracle's cache holds no trial input of the two keys that sign.

It also assumes that a bottom tree the key kept for this leaf holds a top signature.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {f : Array UInt64 → Lanes4}

/-- An honest one-time signature, with any path, leads to the root its key's leaf and path give. -/
theorem layerRoot_of_otsSign {publicParam : PublicParam} {prf : SeedPrf Id}
    {layer : Layer} {e : Nat}
    {msg : Array UInt64} {sig : LayerSignature}
    (hots : (otsSign (pureHash f) publicParam prf layer (UInt32.ofNat e) msg).run
      = some (sig.randomizer, sig.chainValues)) :
    (layerRoot (pureHash f) publicParam layer e msg sig).run
      = some (fold (pureHash f) publicParam layer e
          (otsPublicLeaf (pureHash f) publicParam prf layer
            (UInt32.ofNat e)).run sig.path).run := by
  rw [layerRoot_run, otsLeaf_otsSign hots, Option.map_some]

/-- Correctness: the public key of a seed verifies every signature of a key it reaches.

The key is the one key generation gives, or one that signing updated any number of times. -/
theorem verifyWith_keyGenWith_signWith {seed : Seed} {sk : SecretKey} {idx : LeafIndex}
    {m : Message} {σ : Signature} (hsk : sk.Reachable (pureHash f) seed)
    (hs : (signWith (pureHash f) sk idx m).run.1 = .ok σ) :
    (verifyWith (pureHash f) (keyGenWith (pureHash f) seed).run.1 m σ).run = true := by
  obtain ⟨rfl, hbottom, hbpath, htop, htpath⟩ := hsk.signWith_eq_ok rfl rfl hs
  rw [keyGenWith_fst]
  -- Step 1: the bottom layer leads to the root of bottom tree `b`, which the top key signed.
  have hb := layerRoot_of_otsSign hbottom
  rw [hbpath] at hb
  have hbroot := fold_path (f := f) (publicParam := (publicParamOf
    (seedPrf (pureHash f) (schemeSeed (pureHash f) seed).run)).run)
    (prf := seedPrf (pureHash f) (schemeSeed (pureHash f) seed).run)
    (layer := .bottom) σ.leafIndex.toNat
  -- The bottom tree of `idx` is `idx` shifted down by one layer.
  rw [Nat.shiftRight_eq_div_pow] at hbroot
  -- Step 2: the top layer leads from that root's signature to the top root.
  have ht := layerRoot_of_otsSign htop
  rw [htpath] at ht
  -- Step 3: the top key's leaf and honest path reach the root of the top tree.
  have hroot := fold_path_top (f := f) (publicParam := (publicParamOf
    (seedPrf (pureHash f) (schemeSeed (pureHash f) seed).run)).run)
    (prf := seedPrf (pureHash f) (schemeSeed (pureHash f) seed).run)
    (bottomTree_lt σ.leafIndex)
  -- A key's leaf is the level-0 node of its index, by definition.
  exact verify_of_layerRoot (hb.trans (congrArg some hbroot)) (ht.trans (congrArg some hroot))

/-- Correctness, with Keccak-256: the public key of a seed verifies what its keys sign. -/
theorem verify_keyGen_sign {seed : Seed} {sk : SecretKey} {idx : LeafIndex} {m : Message}
    {σ : Signature} (hsk : sk.Reachable hashId seed) (hs : (sign sk idx m).1 = .ok σ) :
    verify (keyGen seed).1 m σ = true := by
  rw [sign_eq] at hs
  exact verifyWith_keyGenWith_signWith (f := hash) hsk hs

end EthLib.Cryptography.Xmss
