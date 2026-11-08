module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.VerificationCost

/-!
# Signature size and verification cost at height 26

The configuration has total height 26 over three layers, and FORS with 24 trees of height 10.

The parameters give both lower layers the same height, 6, 7 or 8, so the top layer has 14, 12 or 10.

The results hold for each of these three splits.

They also hold for every signature limit.
-/

@[expose] public section

open OracleComp

namespace SphincsSecurity.Configurations

variable [Params]

open Concrete Cost

section h26_layered_k24

variable (hH : totalHeight = 26) (hd : numLayers = 3) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- A signature serializes to 7740 bytes. -/
theorem size_h26_layered_k24 (signature : Signature) :
    (serializeSignature signature).length = 7740 := by
  rw [signature_size, hH, hd, hk, ha]

/-- With Keccak-256, the verification of an accepted signature runs 515 Keccak-f permutations. -/
theorem keccak256_h26_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 515 := by
  have hcalls : digestCalls = 2 := by
    have hℓ := Params.lowerHeight_ge
    have hle := Params.lower_le
    have hbottom : bottomHeight = lowerHeight := by
      unfold bottomHeight layerHeight
      rw [ite_eq_right (by simp only [hd]; omega)]
    unfold digestCalls digestBytes mdBytes treeIndexBytes leafIndexBytes
    rw [hbottom, hH, hk, ha]
    rw [hH, hd] at hle
    omega
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, hcalls,
    hH, hd, hk, ha]
  rfl

end h26_layered_k24

end SphincsSecurity.Configurations
