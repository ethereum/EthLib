import EthLib.Cryptography.Proofs.Xmss.Sign
import EthLib.Cryptography.Proofs.Xmss.Tree
import EthLib.Cryptography.Proofs.Xmss.Verify

/-!
# Proofs: leanXMSS correctness

A signature this specification produces is one it accepts.

```text
    bottom:  Ots.leaf(0, idx, m, rho^0, y^0)   = X^0_{0,idx}     honest leaf
             Tree.fold(0, idx, X^0_{0,idx}, pi^0) = X^0_{16,b}   the root the top key signed
    top:     Ots.leaf(1, b, root, rho^1, y^1)  = X^1_{0,b}       honest leaf
             Tree.fold(1, b, X^1_{0,b}, pi^1)  = X^1_{16,0}      the public key's root
```

Correctness holds for every hash function `f`, run in the identity monad.

`verify_keyGen_sign` is the case `f = hash`, the specification as it runs.

# Assumption

Every theorem here assumes that signing succeeded.

Signing fails only when a one-time key finds no codeword in `2^32` trials.

How often that happens is not proved: it needs the random oracle model.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- The bottom tree of a leaf index is a key of the top tree: it is below `2^16`. -/
theorem bottomTree_lt (idx : LeafIndex) : bottomTree idx < 2 ^ LAYER_HEIGHT := by
  have := idx.toNat_lt_size
  simp only [bottomTree, LAYER_HEIGHT, UInt32.size] at *
  omega

variable {f : ByteArray → Vector UInt8 32}

/-- An honest layer signature leads to the root its key's leaf and path give. -/
theorem layerRoot_signLayer {pp : PublicParam} {s : Seed} {layer : Layer} {e : Nat}
    {msg : ByteArray} {sig : LayerSignature}
    (h : (signLayer (pureHash f) pp s layer e msg).run = .ok sig) :
    (layerRoot (pureHash f) pp layer e msg sig).run
      = some (fold (pureHash f) pp layer e
          (otsPublicLeaf (pureHash f) pp s layer (UInt32.ofNat e)).run sig.path).run := by
  obtain ⟨hots, -⟩ := signLayer_eq_ok h
  rw [layerRoot_run, otsLeaf_otsSign hots, Option.map_some]

/-- What key generation computes: the top tree's root, under the derived public parameter. -/
theorem keyGenWith_run {seed : Seed} {s : Seed} {pp : PublicParam}
    (hs : (schemeSeed (pureHash f) seed).run = s) (hpp : (publicParamOf (pureHash f) s).run = pp) :
    (keyGenWith (pureHash f) seed).run
      = (⟨seed⟩, ⟨(node (pureHash f) pp s .top LAYER_HEIGHT (Nat.le_refl _) 0).run, pp⟩) := by
  subst hs hpp
  rfl

/-- Verification accepts every signature the secret key produces, under the key's public key. -/
theorem verifyWith_signWith {sk : SecretKey} {idx : LeafIndex} {m : Message} {σ : Signature}
    (h : (signWith (pureHash f) sk idx m).run = .ok σ) :
    (verifyWith (pureHash f) (keyGenWith (pureHash f) sk.seed).run.2 m σ).run = true := by
  obtain ⟨rfl, hbottom, htop⟩ := sign_eq_ok rfl rfl h
  -- Step 1: the bottom layer leads to the root of bottom tree `b`, which the top key signed.
  have hb := layerRoot_signLayer hbottom
  rw [(signLayer_eq_ok hbottom).2] at hb
  have hbroot := fold_path (f := f) (pp := (publicParamOf (pureHash f)
    (schemeSeed (pureHash f) sk.seed).run).run) (seed := (schemeSeed (pureHash f) sk.seed).run)
    (layer := .bottom) σ.leafIndex.toNat
  -- The bottom tree of `idx` is `idx` shifted down by one layer.
  rw [Nat.shiftRight_eq_div_pow] at hbroot
  -- Step 2: the top layer leads from that root's signature to the top root.
  have ht := layerRoot_signLayer htop
  rw [(signLayer_eq_ok htop).2] at ht
  -- Step 3: the top key's leaf and honest path reach the root of the top tree.
  have hroot := fold_path_top (f := f) (pp := (publicParamOf (pureHash f)
    (schemeSeed (pureHash f) sk.seed).run).run) (seed := (schemeSeed (pureHash f) sk.seed).run)
    (bottomTree_lt σ.leafIndex)
  -- A key's leaf is the level-0 node of its index, by definition.
  exact verify_of_layerRoot (hb.trans (congrArg some hbroot)) (ht.trans (congrArg some hroot))

/-- Correctness: a generated key pair verifies every signature it makes. -/
theorem verifyWith_keyGenWith_signWith {seed : Seed} {sk : SecretKey} {pk : PublicKey}
    {idx : LeafIndex} {m : Message} {σ : Signature}
    (hk : (keyGenWith (pureHash f) seed).run = (sk, pk))
    (hs : (signWith (pureHash f) sk idx m).run = .ok σ) :
    (verifyWith (pureHash f) pk m σ).run = true := by
  -- The secret key is the seed, and the public key is the one it derives.
  have hsk : sk = ⟨seed⟩ := (congrArg Prod.fst hk).symm.trans rfl
  have hpk : pk = (keyGenWith (pureHash f) seed).run.2 := (congrArg Prod.snd hk).symm
  subst hsk hpk
  exact verifyWith_signWith hs

/-- Correctness, with Keccak-256: a generated key pair verifies every signature it makes. -/
theorem verify_keyGen_sign {seed : Seed} {sk : SecretKey} {pk : PublicKey} {idx : LeafIndex}
    {m : Message} {σ : Signature} (hk : keyGen seed = (sk, pk))
    (hs : sign sk idx m = .ok σ) : verify pk m σ = true :=
  verifyWith_keyGenWith_signWith (f := hash) hk hs

end EthLib.Cryptography.Xmss
