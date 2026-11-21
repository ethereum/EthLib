module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CanonicalChain
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CanonicalPath
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CanonicalPath
import EthLib.Cryptography.Proofs.HashSig.Option

/-!
# The values in a verified leanXMSS layer

The leanXMSS verifier climbs from the one-time key's recovered leaf.

See the draft, section "The scheme".

A match at the root fixes the authentication path and all submitted WOTS+C values.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe

open EthLib.Cryptography OracleSpec OracleComp Constants HashSig TwoLayerGraph
open ChainGraph (digestEquiv)

attribute [local irreducible] Xmss.fold HashSig.ofFnInOrder Xmss.otsLeafHash
attribute [local irreducible] Xmss.chain Xmss.messageDigest Xmss.codeword?

/-- The actual accepted layer opens a valid codeword and every component of the signature. -/
theorem verified_layer_rows (pp : PublicParam) (st : Honest.SharedState) (l : Layer)
    (e : Nat) (msg : ByteArray) (sig : LayerSignature) (root : Digest)
    (safe : ¬(keys pp).TCHazard ((subgraph pp).project st))
    (verified : layerRoot (hashAt pp st) pp l e msg sig = some (some root))
    (anchor : AtPosition st l ⟨LAYER_HEIGHT, e / 2 ^ LAYER_HEIGHT⟩ root) :
    ∃ d digits, messageDigest (hashAt pp st) pp l (UInt32.ofNat e) msg sig.randomizer = some d ∧
      codeword? d = some digits ∧
      (∀ i : Fin V, st.2 (inLayer l (LayerGraph.position (UInt32.ofNat e) i digits[i].val)) =
        some (digestEquiv sig.chainValues[i])) ∧
      ∀ k : Fin LAYER_HEIGHT, AtPosition st l ⟨k.val, (e / 2 ^ k.val) ^^^ 1⟩ sig.path[k] := by
  rw [layerRoot] at verified
  obtain ⟨leaf, readLeaf, climb⟩ := Option.bind_eq_some_iff.mp verified
  cases leaf with
  | none => cases climb
  | some leaf =>
    obtain ⟨r, up, same⟩ := Option.bind_eq_some_iff.mp climb
    obtain rfl := Option.some.inj (Option.some.inj same)
    have height : sig.path.toList.length = LAYER_HEIGHT := by simp
    rw [Xmss.fold] at up
    have rows := climb_opening pp st l safe sig.path.toList ⟨0, e⟩ leaf r
      (by simp) up (by simpa [height, Merkle.Position.ancestor] using anchor)
    rw [otsLeaf] at readLeaf
    obtain ⟨d, readMessage, rest⟩ := Option.bind_eq_some_iff.mp readLeaf
    cases parsed : codeword? d with
    | none => rw [parsed] at rest; cases rest
    | some x =>
      rw [parsed] at rest
      obtain ⟨ends, walked, hashed⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨leaf', readHash, same⟩ := Option.bind_eq_some_iff.mp hashed
      obtain rfl := Option.some.inj (Option.some.inj same)
      refine ⟨d, x, readMessage, parsed, fun i => ?_, fun k => ?_⟩
      · have suffix := ofFnInOrder_eq_some_get _ _ ends walked i
        have index := x[i].isLt
        have reached : x[i].val + (CHAIN_LENGTH - 1 - x[i].val) = CHAIN_LENGTH - 1 := by omega
        rw [Xmss.chain] at suffix
        have terminal := leaf_ends pp st l (UInt32.ofNat e) ends leaf' safe rows.1 readHash i
        rw [← reached] at terminal
        exact chain_opening _ _ _ _ i safe _ _ _ _ _ suffix terminal
      · have sibling := rows.2 ⟨k.val, by rw [height]; exact k.isLt⟩
        simpa [Merkle.Position.ancestor, Merkle.Position.sibling] using sibling

end EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe
