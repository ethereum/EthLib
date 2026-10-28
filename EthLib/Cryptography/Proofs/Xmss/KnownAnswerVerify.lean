import EthLib.Cryptography.Proofs.Xmss.KnownAnswerBottom
import EthLib.Cryptography.Proofs.Xmss.KnownAnswerTop

/-!
# Proofs: the known answer verifies

The two layers join into one accepting verification.
-/

namespace EthLib.Cryptography.Xmss.KnownAnswer

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

set_option maxRecDepth 100000

/-- The decoded signature verifies under the decoded public key. -/
theorem verify_signature : verify publicKey message signature = true :=
  verify_of_layerRoot bottomLayerRoot_known_answer topLayerRoot_known_answer

/-- The signature's bytes verify under the public key's bytes. -/
theorem verify_known_answer : verifyBytes publicKeyBytes message signatureBytes = true := by
  simp only [verifyBytes, decode_publicKey, decode_signature, verify_signature]

/-- The top layer with its topmost sibling zeroed. -/
def tamperedTop : LayerSignature :=
  { signature.top with path := signature.top.path.set 15 (Vector.replicate DIGEST_LEN 0) }

/-- The root the tampered top layer leads to. -/
def tamperedRoot : Digest := #v[0x36, 0xf1, 0x3f, 0x87, 0x1d, 0x37, 0x6d, 0x54, 0x65, 0xd3, 0x28, 0xa2, 0x58, 0x63, 0xef, 0x33]

/-- The tampered path leads to another root. -/
theorem tamperedFold_known_answer :
    fold publicKey.publicParam .top (bottomTree leafIndex) topLeaf tamperedTop.path
      = tamperedRoot := by
  rw [Kernel.fold_eq]
  decide +kernel

/-- Changing the topmost sibling of the top layer rejects.

A root computation that ignored one side of a node would still accept. -/
theorem verify_tampered_path :
    verify publicKey message { signature with top := tamperedTop } = false := by
  -- The top layer's codeword, chains and leaf do not read the path.
  have hroot : layerRoot publicKey.publicParam .top (bottomTree leafIndex) (packBytes bottomRoot)
      tamperedTop = some tamperedRoot :=
    layerRoot_eq topCodeword_known_answer topChains topLeaf_known_answer tamperedFold_known_answer
  exact verify_of_layerRoot_ne bottomLayerRoot_known_answer hroot (by decide +kernel)

end EthLib.Cryptography.Xmss.KnownAnswer
