module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifierConflict

/-!
# What an accepted two-layer signature had already disclosed

The leanXMSS draft, section "The scheme", passes the bottom root to the top verifier.

Suppose both layers verify without a public conflict.

Each submitted nonterminal value that matches after the fill occupied its canonical cell before it.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe

open EthLib.Cryptography OracleSpec OracleComp Constants HashSig TwoLayerGraph
open ChainGraph (Word Public digestEquiv)

/-- An accepted verifier passes its bottom root to the top layer in the same run. -/
theorem verifier_layers (pk : PublicKey) (msg : Message) (sig : Xmss.Signature)
    (initial finish : Honest.SharedState × List Cell)
    (run : (true, finish) ∈ support ((simulateQ (graph pk.publicParam).deferredImpl
      (verifyWith Honest.hash pk msg sig)).run initial)) :
    ∃ (b : Digest) (middle : Honest.SharedState × List Cell),
      (some b, middle) ∈ support ((simulateQ (graph pk.publicParam).deferredImpl
        (layerRoot Honest.hash pk.publicParam .bottom sig.leafIndex.toNat
          (packBytes msg) sig.bottom)).run initial) ∧
      (some pk.root, finish) ∈ support ((simulateQ (graph pk.publicParam).deferredImpl
        (layerRoot Honest.hash pk.publicParam .top (bottomTree sig.leafIndex)
          (packBytes b) sig.top)).run middle) ∧ middle.1 ≤ finish.1 := by
  rw [verifyWith] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨⟨result, middle⟩, bot, tail⟩ := run
  cases result with
  | none => simp [simulateQ_pure] at tail
  | some b =>
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at tail
    obtain ⟨⟨result, out⟩, top, done⟩ := tail
    cases result with
    | none => simp [simulateQ_pure] at done
    | some r =>
      have eqn : (true, finish) = (decide (r = pk.root), out) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using done
      obtain ⟨rtrue, rfl⟩ := Prod.mk.inj eqn
      obtain rfl := of_decide_eq_true rtrue.symm
      exact ⟨b, middle, bot, top, (graph pk.publicParam).le_of_mem_support_simulateQ_deferredImpl _
        top⟩

/--
A nonterminal candidate that matches in the clean filled state was drawn before verification ended.
-/
def DrawnPositions (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature)
    (before final : Honest.SharedState) : Prop :=
  ∀ (digits : Vector (Fin CHAIN_LENGTH) V),
    (messageDigest (hashAt pp final) pp l (UInt32.ofNat e) msg sig.randomizer).bind codeword?
      = some digits →
    ∀ i : Fin V, digits[i].val < CHAIN_LENGTH - 1 →
      let c := inLayer l (LayerGraph.position (UInt32.ofNat e) i digits[i].val)
      let v := digestEquiv sig.chainValues[i]
      final.2 c = some v → before.2 c = some v

private theorem drawn (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature) (root : Digest) (initial finish : Honest.SharedState × List Cell)
    (before final : Honest.SharedState)
    (run : (some root, finish) ∈ support ((simulateQ (graph pp).deferredImpl
      (layerRoot Honest.hash pp l e msg sig)).run initial))
    (cut : finish.1 ≤ before) (later : before ≤ final) (clean : ¬ (graph pp).Conflict final) :
    DrawnPositions pp l e msg sig before final := by
  intro digits decoded i nonterminal c v matched
  cases stored : before.2 c with
  | none => exact (clean (conflict_of_supported_opening pp l e msg sig root digits initial finish
      before final run cut later decoded i nonterminal stored matched)).elim
  | some old => exact (later.2 stored).symm.trans matched

/--
One clean extension fixes both roots and both chain disclosures of the shared public-hash verifier.
-/
theorem verify_drawn_positions (pk : PublicKey) (msg : Message) (sig : Xmss.Signature)
    (initial finish : Honest.SharedState × List Cell) (final : Honest.SharedState)
    (run : (true, finish) ∈ support ((simulateQ (graph pk.publicParam).deferredImpl
      (verifyWith Honest.hash pk msg sig)).run initial))
    (later : finish.1 ≤ final) (clean : ¬ (graph pk.publicParam).Conflict final) :
    ∃ b : Digest, layerRoot (hashAt pk.publicParam final) pk.publicParam .bottom sig.leafIndex.toNat
        (packBytes msg) sig.bottom = some (some b) ∧
      layerRoot (hashAt pk.publicParam final) pk.publicParam .top (bottomTree sig.leafIndex)
        (packBytes b) sig.top = some (some pk.root) ∧
      DrawnPositions pk.publicParam .bottom sig.leafIndex.toNat
        (packBytes msg) sig.bottom finish.1 final ∧
      DrawnPositions pk.publicParam .top (bottomTree sig.leafIndex)
        (packBytes b) sig.top finish.1 final := by
  obtain ⟨b, middle, bot, top, ordered⟩ := verifier_layers pk msg sig initial finish run
  exact ⟨b, layer_replay _ _ _ _ _ bot (ordered.trans later) clean,
    layer_replay _ _ _ _ _ top later clean,
    drawn _ _ _ _ _ _ initial middle _ _ bot ordered later clean,
    drawn _ _ _ _ _ _ middle finish _ _ top le_rfl later clean⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe
