import EthLib.Cryptography.Proofs.Xmss.Sign
import EthLib.Cryptography.Proofs.Xmss.Tree

/-!
# Proofs: leanXMSS correctness

A signature this specification produces is one it accepts.

```text
    bottom:  Ots.leaf(0, idx, m, rho^0, y^0)   = X^0_{0,idx}     honest leaf
             Tree.fold(0, idx, X^0_{0,idx}, pi^0)                the root the top key signed
    top:     Ots.leaf(1, b, root, rho^1, y^1)  = X^1_{0,b}       honest leaf
             Tree.fold(1, b, X^1_{0,b}, pi^1)  = X^1_{16,0}      the public key's root
```

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

/-- An honest layer signature leads to the root its key's leaf and path give. -/
theorem layerRoot_signLayer {pp : PublicParam} {s : Seed} {layer : Layer} {e : Nat}
    {msg : ByteArray} {sig : LayerSignature} (h : signLayer pp s layer e msg = .ok sig) :
    layerRoot pp layer e msg sig
      = some (fold pp layer e (otsPublicLeaf pp s layer (UInt32.ofNat e)) sig.path) := by
  obtain ⟨hots, -⟩ := signLayer_eq_ok h
  rw [layerRoot, otsLeaf_otsSign hots]
  rfl

/-- Verification accepts every signature the secret key produces. -/
theorem verify_sign {sk : SecretKey} {idx : LeafIndex} {m : Message} {σ : Signature}
    (h : sign sk idx m = .ok σ) : verify sk.publicKey m σ = true := by
  obtain ⟨rfl, hbottom, htop⟩ := sign_eq_ok h
  -- Step 1: the bottom layer leads to the root the top key signed.
  have hb := layerRoot_signLayer hbottom
  rw [UInt32.ofNat_toNat] at hb
  -- Step 2: the top layer leads from that root's signature to the top root.
  have ht := layerRoot_signLayer htop
  -- Step 3: the top key's leaf and honest path reach the root of the top tree.
  have hpath := (signLayer_eq_ok htop).2
  have hroot := fold_path_top (pp := sk.publicParam) (seed := sk.schemeSeed)
    (bottomTree_lt σ.leafIndex)
  simp only [verify, SecretKey.publicKey, hb, Option.bind_eq_bind, Option.bind_some, ht, hpath]
  exact decide_eq_true (congrArg some hroot)

/-- Correctness: a generated key pair verifies every signature it makes. -/
theorem verify_keyGen_sign {seed : Seed} {sk : SecretKey} {pk : PublicKey} {idx : LeafIndex}
    {m : Message} {σ : Signature} (hk : keyGen seed = (sk, pk))
    (hs : sign sk idx m = .ok σ) : verify pk m σ = true := by
  -- The public key is the one the secret key derives.
  simp only [keyGen, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  exact verify_sign hs

end EthLib.Cryptography.Xmss
