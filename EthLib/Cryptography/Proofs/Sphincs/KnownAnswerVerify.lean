import EthLib.Cryptography.Proofs.Sphincs.KnownAnswerForsLow
import EthLib.Cryptography.Proofs.Sphincs.KnownAnswerForsHigh
import EthLib.Cryptography.Proofs.Sphincs.KnownAnswerBottom
import EthLib.Cryptography.Proofs.Sphincs.KnownAnswerMiddle
import EthLib.Cryptography.Proofs.Sphincs.KnownAnswerTop

/-!
# Proofs: the known answer verifies

The digest, the FORS openings and the three layers join into one accepting verification.

Two tamperings each reject:

- a changed FORS secret, which changes the FORS key the bottom key must have signed;
- a changed top sibling, which sends the top fold to another root.
-/

namespace EthLib.Cryptography.Sphincs.KnownAnswer

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

set_option maxRecDepth 100000

/-! ## The FORS key -/

/-- Every FORS opening leads to its tree's part of the FORS key. -/
theorem forsKey_known_answer :
    forsRecover publicKey.publicParam 65963065 leaves signature.fors = forsKey := by
  refine forsRecover_eq fun kappa => ?_
  have := kappa.isLt
  simp only [FORS_TREES] at this
  -- Each tree falls in one of the six groups of four.
  by_cases h4 : kappa.val < 4
  · exact forsTrees_0 kappa (Nat.zero_le _) h4
  by_cases h8 : kappa.val < 8
  · exact forsTrees_4 kappa (by omega) h8
  by_cases h12 : kappa.val < 12
  · exact forsTrees_8 kappa (by omega) h12
  by_cases h16 : kappa.val < 16
  · exact forsTrees_12 kappa (by omega) h16
  by_cases h20 : kappa.val < 20
  · exact forsTrees_16 kappa (by omega) h20
  exact forsTrees_20 kappa (by omega) (by omega)

/-! ## Acceptance -/

/-- The three layers, from the recovered FORS key up, lead to the top root. -/
theorem signatureRoot_known_answer : signatureRoot publicKey message signature = some topRoot := by
  simp only [signatureRoot]
  -- Step 1: the digest names the index and the leaves, and the openings lead to the FORS key.
  rw [digest_known_answer, digestIndex_known_answer, digestLeaves_known_answer, forsKey_known_answer]
  -- Step 2: each layer leads to the root the layer above signs.
  rw [bottomLayerRoot_known_answer, Option.bind_some, middleLayerRoot_known_answer, Option.bind_some,
    topLayerRoot_known_answer]

/-- The decoded signature verifies under the decoded public key. -/
theorem verify_signature : verify publicKey message signature = true := by
  -- The top root is the public key's root.
  rw [verify_iff, signatureRoot_known_answer]
  decide

/-- The signature's bytes verify under the public key's bytes. -/
theorem verify_known_answer : verifyBytes publicKeyBytes message signatureBytes = true := by
  simp only [verifyBytes, decode_publicKey, decode_signature, verify_signature]

/-! ## A changed top sibling -/

/-- The top layer with its topmost sibling zeroed. -/
def tamperedTop : LayerSignature .top :=
  { signature.top with path := signature.top.path.set 9 (Vector.replicate N 0) }

/-- The root the tampered top path leads to: not the public key's. -/
theorem tamperedTopFold_ne :
    fold publicKey.publicParam .top (OtsKey.ofIndex .top 65963065).tree
      (OtsKey.ofIndex .top 65963065).leaf topLeaf tamperedTop.path ≠ publicKey.root := by
  rw [Kernel.fold_eq]
  decide +kernel

/-- Changing the topmost sibling of the top layer rejects.

A fold that ignored one side of a node would still accept. -/
theorem verify_tampered_top_path :
    verify publicKey message { signature with top := tamperedTop } = false := by
  rw [Bool.eq_false_iff, ne_eq, verify_iff]
  simp only [signatureRoot]
  rw [digest_known_answer, digestIndex_known_answer, digestLeaves_known_answer, forsKey_known_answer,
    bottomLayerRoot_known_answer, Option.bind_some, middleLayerRoot_known_answer, Option.bind_some]
  -- The top layer's codeword, chains and leaf do not read the path.
  rw [layerRoot_eq (sig := tamperedTop) topCodeword_known_answer topChains topLeaf_known_answer rfl,
    Option.some_inj]
  exact tamperedTopFold_ne

/-! ## A changed FORS secret -/

/-- The FORS openings with the secret of tree 0 zeroed. -/
def tamperedFors : Vector TreeOpening FORS_TREES :=
  signature.fors.set 0 { signature.fors[0] with secret := Vector.replicate N 0 }

/-- The level-9 nodes tree 0's tampered opening leads to. -/
def tamperedTree0 : Digest × Digest :=
  Kernel.treeRecover publicKey.publicParam 65963065 0 leaves[0] tamperedFors[0]

/-- The FORS key the tampered openings lead to: tree 0's part changes, the others stay. -/
theorem tamperedForsKey :
    forsRecover publicKey.publicParam 65963065 leaves tamperedFors = forsKey.set 0 tamperedTree0 := by
  refine forsRecover_eq fun kappa => ?_
  by_cases h : kappa.val = 0
  -- Tree 0 is recomputed from its tampered secret.
  · have hk : kappa = 0 := Fin.ext (by rw [h]; rfl)
    subst hk
    rw [Kernel.treeRecover_eq]
    rfl
  -- Every other tree keeps its opening, so its part of the key.
  · have hset : tamperedFors[kappa] = signature.fors[kappa] := by
      simp only [tamperedFors, Fin.getElem_fin]
      exact Vector.getElem_set_ne _ _ (by omega)
    have hkey : (forsKey.set 0 tamperedTree0)[kappa] = forsKey[kappa] := by
      simp only [Fin.getElem_fin]
      exact Vector.getElem_set_ne _ _ (by omega)
    rw [hset, hkey, forsKey_known_answer.symm, forsRecover]
    simp

/-- The bottom counter encodes no codeword for the changed FORS key. -/
theorem tamperedEncode_none :
    encode publicKey.publicParam (OtsKey.ofIndex .bottom 65963065)
      (forsKeyBytes (forsKey.set 0 tamperedTree0)) signature.bottom.counter = none := by
  simp only [encode, forsKeyBytes, tamperedTree0, Kernel.th_eq, Kernel.toList_append,
    Kernel.toList_packBytes, Kernel.toList_packDigests]
  decide +kernel

/-- Changing one FORS secret rejects: the bottom key signed another FORS key. -/
theorem verify_tampered_fors_secret :
    verify publicKey message { signature with fors := tamperedFors } = false := by
  rw [Bool.eq_false_iff, ne_eq, verify_iff]
  simp only [signatureRoot]
  rw [digest_known_answer, digestIndex_known_answer, digestLeaves_known_answer, tamperedForsKey]
  -- The bottom layer fails, so nothing reaches the root.
  rw [layerRoot, otsLeaf, tamperedEncode_none]
  simp

end EthLib.Cryptography.Sphincs.KnownAnswer
