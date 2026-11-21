module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderReceiptAgreement
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderChronicleGraph

/-!
# The registrations belonging to an actual logged signature

The two signed digests in a completed physical run are unambiguous at their respective keys.

The query history records each notice and its incoming state to price matches.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleComp OracleSpec Constants TwoLayerGraph Honest TrialGraphWatch CachedCodeword

attribute [local irreducible] mixedGame graph guardedGraph simulateQ game chronicleGame

/-- Registrations at either key agree on the physical trial bytes and selected low digest. -/
theorem registered_inputs (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    {obs : Outcome} {out : ResidualCache pp} {t : ChronicleState} {last : SharedState}
    (actual : (some (obs,out),t) ∈ support (chronicleGame pp A left r))
    (later : (physical t.1).1 ≤ last) (clean : ¬ (graph pp).Conflict last)
    (valid : Valid (eraseLog obs.log)) {req sig} (logged : (req, Except.ok sig) ∈ obs.log) :
    ∃ c : Receipt pp left req.leafIndex req.message sig,
      Arrival.note (selectedNotice pp .bottom (UInt32.ofNat req.leafIndex.toNat)
        (packBytes req.message) sig.bottom.randomizer c.x) c.lowerPrior ∈ t.2 ∧
      Arrival.note (selectedNotice pp .top (UInt32.ofNat (bottomTree req.leafIndex))
        (packBytes c.root) sig.top.randomizer c.y) c.upperPrior ∈ t.2 ∧
      (∀ b d st, Arrival.note (.register .bottom (UInt32.ofNat req.leafIndex.toNat) b d) st ∈ t.2 →
        b = trialInput pp .bottom (UInt32.ofNat req.leafIndex.toNat)
          (packBytes req.message) sig.bottom.randomizer ∧
          d = selectedDigest c.x) ∧
      (∀ b d st, Arrival.note (.register .top (UInt32.ofNat (bottomTree req.leafIndex)) b d)
        st ∈ t.2 →
        b = trialInput pp .top (UInt32.ofNat (bottomTree req.leafIndex))
          (packBytes c.root) sig.top.randomizer ∧
          d = selectedDigest c.y) := by
  have receipts := completed_receipts pp A left r actual
  obtain ⟨c, both⟩ := receipts.of_success logged
  have raw : (some (obs,out),physical t.1) ∈ support ((simulateQ (graph pp).deferredImpl
    (guardedGraph left ((mixedGame pp A).run r))).run ((∅,∅),[])) := by
    rw [← project_graph pp A left r, support_map]
    exact ⟨_,actual,rfl⟩
  have facts := signed_history pp A left r _ obs out _ raw last later
  have run := actual
  unfold chronicleGame at run
  have ext (a : Arrival) (ha : a ∈ t.2) : (physical a.prior).1 ≤ last :=
    (arrivals_extend pp left (WeightedCap.capCompOpt fee left ((game pp A).run r)) initial.1
      (z := (some (obs,out), t)) run a ha).trans later
  refine ⟨c,(member_register _).mp ?_,(member_register _).mp ?_,
    lower_input_agreement receipts valid logged c both ext clean,
      upper_input_agreement receipts logged c both ext clean facts⟩
  · exact both (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact both List.mem_cons_self

/-- Each registration at either key carries the digest recorded by its finder. -/
theorem registered_keys (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    {obs : Outcome} {out : ResidualCache pp} {t : ChronicleState} {last : SharedState}
    (actual : (some (obs,out),t) ∈ support (chronicleGame pp A left r))
    (later : (physical t.1).1 ≤ last) (clean : ¬ (graph pp).Conflict last)
    (valid : Valid (eraseLog obs.log)) {req sig} (logged : (req, Except.ok sig) ∈ obs.log) :
    ∃ c : Receipt pp left req.leafIndex req.message sig,
      Arrival.note (selectedNotice pp .bottom (UInt32.ofNat req.leafIndex.toNat)
        (packBytes req.message) sig.bottom.randomizer c.x) c.lowerPrior ∈ t.2 ∧
      Arrival.note (selectedNotice pp .top (UInt32.ofNat (bottomTree req.leafIndex))
        (packBytes c.root) sig.top.randomizer c.y) c.upperPrior ∈ t.2 ∧
      (∀ b d st, Arrival.note (.register .bottom (UInt32.ofNat req.leafIndex.toNat) b d) st ∈ t.2 →
        d = selectedDigest c.x) ∧
      (∀ b d st, Arrival.note (.register .top (UInt32.ofNat (bottomTree req.leafIndex)) b d)
        st ∈ t.2 →
        d = selectedDigest c.y) := by
  obtain ⟨c, lower, upper, bottomKey, topKey⟩ := registered_inputs pp A left r
    actual later clean valid logged
  exact ⟨c,lower,upper,fun b d st found => (bottomKey b d st found).2,
    fun b d st found => (topKey b d st found).2⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
