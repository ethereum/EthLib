module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedOpening
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifiedPositions
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifiedPositions

/-!
# An accepted candidate at an opened chain position

Both candidate layers are replayed from the public cache after completion.

A matching nonterminal value came from a successful signature on the same chain.

That signature released a value at this position or an earlier one.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleComp OracleSpec VerifierProbe

/-- Identify the signing request that revealed the submitted value in the completed graph. -/
@[expose] def SignedOpenings (pp : PublicParam) (before final : SharedState) (raw : RawLog)
    (l : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature) : Prop :=
  ∀ (digits : Vector (Fin CHAIN_LENGTH) V),
    (messageDigest (hashAt pp final) pp l (UInt32.ofNat e) msg sig.randomizer).bind codeword? =
      some digits →
    ∀ i : Fin V, digits[i].val < CHAIN_LENGTH - 1 →
      final.2 (inLayer l (LayerGraph.position (UInt32.ofNat e) i digits[i].val)) =
        some (ChainGraph.digestEquiv sig.chainValues[i]) →
      ReleasedBefore pp before raw l (UInt32.ofNat e) i digits[i]

attribute [local irreducible] simulateQ graph mixedGame Xmss.verifyWith layerRoot

/-- An unused key or chain prefix cannot account for a nonterminal opening in a clean game. -/
theorem accepted_openings (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    (obs : Outcome) (out : ResidualCache pp) (t : DeferredState) (final : SharedState)
    (actual : (some (obs,out),t) ∈ support ((simulateQ (graph pp).deferredImpl
      (guardedGraph left ((mixedGame pp A).run r))).run ((∅,∅),[])))
    (accepted : obs.verified = true) (later : t.1 ≤ final) (clean : ¬ (graph pp).Conflict final) :
    let sig := obs.candidate.signature
    ∃ b : Digest,
      layerRoot (hashAt pp final) pp .bottom sig.leafIndex.toNat
        (packBytes obs.candidate.message) sig.bottom =
        some (some b) ∧
      layerRoot (hashAt pp final) pp .top (bottomTree sig.leafIndex) (packBytes b) sig.top =
        some (some obs.key.root) ∧
      SignedOpenings pp t.1 final obs.log .bottom sig.leafIndex.toNat
        (packBytes obs.candidate.message) sig.bottom ∧
      SignedOpenings pp t.1 final obs.log .top (bottomTree sig.leafIndex)
        (packBytes b) sig.top := by
  obtain ⟨key, _, before, _, _, _, _, verify⟩ := mixed_verifier_cut pp A left r
    ((∅,∅),[]) obs out t actual
  subst pp
  rw [accepted] at verify
  obtain ⟨b, bottom, top, low, high⟩ := verify_drawn_positions obs.key obs.candidate.message
    obs.candidate.signature before t final verify later clean
  refine ⟨b, bottom, top, ?_, ?_⟩
  · intro digits decoded i nonterminal matched
    exact release_of_present _ A left r obs out t actual .bottom _ i digits[i] nonterminal _
      (low digits decoded i nonterminal matched)
  · intro digits decoded i nonterminal matched
    exact release_of_present _ A left r obs out t actual .top _ i digits[i] nonterminal _
      (high digits decoded i nonterminal matched)

/-- The lower signing key is the leaf index.

The upper key is the bottom-tree index. -/
def signingEpoch (l : Layer) (req : SignRequest) : UInt32 :=
  match l with
  | .bottom => UInt32.ofNat req.leafIndex.toNat
  | .top => UInt32.ofNat (bottomTree req.leafIndex)

/-- A nonterminal opening at an unsigned key cannot match its canonical cell. -/
theorem SignedOpenings.unsigned {pp before final raw l e msg sig}
    (openings : SignedOpenings pp before final raw l e msg sig)
    (unsigned : ∀ req candidate, (req, .ok candidate) ∈ raw → signingEpoch l req ≠ UInt32.ofNat e)
    (digits : Vector (Fin CHAIN_LENGTH) V)
    (decoded : (messageDigest (hashAt pp final) pp l (UInt32.ofNat e) msg sig.randomizer).bind
      codeword? = some digits)
    (i : Fin V) (nonterminal : digits[i].val < CHAIN_LENGTH - 1) :
    final.2 (inLayer l (LayerGraph.position (UInt32.ofNat e) i digits[i].val)) ≠
      some (ChainGraph.digestEquiv sig.chainValues[i]) := by
  intro matched
  obtain ⟨req, candidate, member, _, _, _, _, _, _, _, key⟩ :=
    openings digits decoded i nonterminal matched
  rcases key with ⟨rfl, same, _⟩ | ⟨rfl, same, _⟩
  · exact unsigned req candidate member same.symm
  · exact unsigned req candidate member same.symm

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
