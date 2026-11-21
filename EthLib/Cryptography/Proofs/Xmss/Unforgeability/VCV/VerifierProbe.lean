module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerHonest
import EthLib.Cryptography.Proofs.HashSig.Option

/-!
# The first raw query in a verified chain suffix

The verifier uses the submitted chain value as its first predecessor.

The leanXMSS draft, section "WOTS+C", gives the chain index in the input after its 16 digest bytes.

A candidate digest at any nonterminal position therefore tests a particular physical hash point.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe

open EthLib.Cryptography OracleSpec OracleComp Constants HashSig TwoLayerGraph
open ChainGraph (Word digestEquiv)

private theorem first_step {α : Type} {n : Nat} (step : Fin n → α → Option α)
    (start steps : Nat) (positive : 0 < steps) (bound : start + steps ≤ n) (v last : α)
    (run : Wots.chain step start steps bound v = some last) :
    ∃ first, step ⟨start, by omega⟩ v = some first := by
  cases steps with
  | zero => omega
  | succ steps =>
    induction steps generalizing last with
    | zero => exact ⟨last, by simpa [Wots.chain] using run⟩
    | succ d ih =>
      rw [Wots.chain] at run
      obtain ⟨earlier, walked, _⟩ := Option.bind_eq_some_iff.mp run
      apply ih (last := earlier) <;> first | exact walked | omega

/-- Bytes of the physical query made by the verifier at the candidate's decoded position. -/
def point (pp : PublicParam) (l : Layer) (e : UInt32) (i : Fin V)
    (d : Fin (CHAIN_LENGTH - 1)) (v : Digest) : ByteArray :=
  thInput pp (addrChain l e d) (packBytes v ++ packBytes (uintToBytes 16 i.val))

attribute [local irreducible] Xmss.fold HashSig.ofFnInOrder Xmss.otsLeafHash Xmss.chain
  Xmss.messageDigest Xmss.codeword?

/-- At every nonterminal position the actual verifier needs the raw hash of its submitted value.

The proof also applies to an incomplete, deterministic public hash table.
-/
theorem first_probe (H : ByteArray → Option (Vector UInt8 32)) (pp : PublicParam)
    (l : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature)
    (root : Digest) (digits : Vector (Fin CHAIN_LENGTH) V)
    (decoded : (messageDigest H pp l (UInt32.ofNat e) msg sig.randomizer).bind codeword?
      = some digits)
    (verified : layerRoot H pp l e msg sig = some (some root))
    (i : Fin V) (nonterminal : digits[i].val < CHAIN_LENGTH - 1) :
    (H (point pp l (UInt32.ofNat e) i ⟨digits[i].val, nonterminal⟩ sig.chainValues[i])).isSome := by
  obtain ⟨digest, readDigest, code⟩ := Option.bind_eq_some_iff.mp decoded
  rw [layerRoot] at verified
  obtain ⟨leaf, readLeaf, climb⟩ := Option.bind_eq_some_iff.mp verified
  cases leaf with
  | none =>
    change some none = some (some root) at climb
    cases climb
  | some leaf =>
    unfold otsLeaf at readLeaf
    rw [readDigest] at readLeaf
    rw [show (some digest : Option Digest) = pure digest from rfl, pure_bind, code] at readLeaf
    obtain ⟨ends, walked, _⟩ := Option.bind_eq_some_iff.mp readLeaf
    have suffix := ofFnInOrder_eq_some_get _ _ ends walked i
    rw [Xmss.chain] at suffix
    obtain ⟨v, first⟩ := first_step _ _ _ (by omega) _ _ _ suffix
    change (H (point pp l (UInt32.ofNat e) i ⟨digits[i].val,
      nonterminal⟩ sig.chainValues[i]) >>= _) = some v at first
    exact Option.isSome_iff_exists.mpr ⟨_, (Option.bind_eq_some_iff.mp first).choose_spec.1⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe
