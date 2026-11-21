module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerSignerLog
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifierConflict

/-!
# The successful signing digits in a later public table

Every supported signing success records the two actual grind results and the bottom root.

In a conflict-free extension the ordinary public words decode to those same digits.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants HashSig OracleComp LayerGraph.Hidden

private theorem winner {κ β : Type} (trial : Nat → κ) (test : κ → Option (Option β)) :
    ∀ fuel c k x, Wots.findFirst trial test c fuel = some (some (k, x)) →
      test k = some (some x)
  | 0, _, _, _, win => by cases win
  | fuel + 1, c, k, x, win => by
    rw [Wots.findFirst] at win
    cases answer : test (trial c) with
    | none => simp [answer] at win
    | some found =>
      cases found with
      | none =>
        simp only [answer] at win
        exact winner trial test fuel (c + 1) k x win
      | some d =>
        simp only [answer, Option.pure_def] at win
        obtain ⟨rfl, rfl⟩ := win
        exact answer

/-- A completed search decodes to the returned digits at the returned randomizer. -/
theorem decode_finder {hash : ByteArray → Option (Vector UInt8 32)} {pp l e msg base c fuel rho x}
    (replay : Xmss.Internal.findCodeword hash pp l e msg base c fuel = some (some (rho, x))) :
    (messageDigest hash pp l e msg rho).bind codeword? = some x := by
  rw [Xmss.Internal.findCodeword_eq] at replay
  have good := winner _ _ _ _ _ _ replay
  cases found : messageDigest (hash) pp l e msg rho with
  | none => simp [found] at good
  | some d => simpa [found] using good

/-- Decode the returned randomizer under the public hash in any later conflict-free state. -/
theorem Trial.decoded {pp l e msg rho x s t} (trial : Trial pp l e msg rho x s)
    (extended : s ≤ t) (clean : ¬ (graph pp).Conflict t) :
    (messageDigest (VerifierProbe.hashAt pp t) pp l e msg rho).bind codeword? = some x := by
  obtain ⟨base, initial, finish, actual, cut⟩ := trial
  have replay := VerifierProbe.finder_replay pp l e msg base 0 MAX_RANDOMIZER_TRIALS actual
    (cut.trans extended) clean
  exact decode_finder replay

/-- A signing error authorizes no direct chain read.

Each permitted chain read of a successful reply belongs to the position its actual message decodes.

Both layers use one conflict-free public table and the bottom root in its original shared row. -/
theorem released_positions (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (residual : ResidualReads pp cb) (idx : LeafIndex) (msg : Message) {s ans log t}
    (ran : Logged pp (releasedSchedule pp cb idx msg) s ans log t) (last : SharedState)
    (extended : t.1 ≤ last) (clean : ¬ (graph pp).Conflict last) :
    match ans with
    | .error _ => LogWithin ∅ log
    | .ok sig => sig.leafIndex = idx ∧ ∃ (root : Digest) (x y : Vector (Fin CHAIN_LENGTH) V),
        last.2 (.inr (.inl (.bottom, LayerGraph.treeRole LAYER_HEIGHT (bottomTree idx)))) =
          some (ChainGraph.digestEquiv root) ∧
        (messageDigest (VerifierProbe.hashAt pp last) pp .bottom (UInt32.ofNat idx.toNat)
          (packBytes msg) sig.bottom.randomizer).bind codeword? = some x ∧
        (messageDigest (VerifierProbe.hashAt pp last) pp .top (UInt32.ofNat (bottomTree idx))
          (packBytes root) sig.top.randomizer).bind codeword? = some y ∧
        LogWithin (positions .bottom (UInt32.ofNat idx.toNat) x ∪
          positions .top (UInt32.ofNat (bottomTree idx)) y) log := by
  have reported := releasedSchedule_logged pp cb residual idx msg ran
  cases ans with
  | error _ => exact reported
  | ok sig =>
    obtain ⟨same, root, x, y, stored, low, high, reads⟩ := reported
    exact ⟨same, root, x, y, extended.2 stored, low.decoded extended clean,
      high.decoded extended clean, reads⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
