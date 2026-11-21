module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderReceiptMatch
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealClient

/-!
# Classifying a winning run at its authentic registration

A partner observed after registration sets the hit flag.

Otherwise both answers were present when the signer registered its selected word.

The incoming state here belongs to the same invocation that produced the logged signature.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography HashSig Constants OracleComp OracleSpec TwoLayerGraph Honest
open CachedCodeword TrialGraphWatch VerifierProbe PostSigning EarlierDigest
open ChainGraph (digestEquiv)

/-- A signed input, its notice and its earlier or later collision in the same run. -/
structure RegisteredPair (pp : PublicParam) (s : ChronicleState) (l : Layer) (e : UInt32)
    (m n : ByteArray) (a b : LayerSignature) (x : Vector (Fin CHAIN_LENGTH) V)
      (prior : JointState) : Prop where
  first : FirstPair pp s l e m n a b x
  notice : Arrival.note (selectedNotice pp l e n b.randomizer x) prior ∈ s.2
  agrees : Agrees s.2 l e (selectedDigest x)
  sameInput : ∀ input digest st, Arrival.note (.register l e input digest) st ∈ s.2 →
    input = trialInput pp l e n b.randomizer
  charged : s.1.2 = true ∨ Partner pp (live prior) (trialInput pp l e n b.randomizer)

/-- Each registration sees the earlier partner unless the later-hit flag fires. -/
theorem RegisteredPair.at_registration {pp s l e m n a b x prior}
    (p : RegisteredPair pp s l e m n a b x prior)
    (order : Ordered s.2 (live s.1) (targets s.1)) (seen : SeenPost pp s)
    {input digest} {st : JointState} (entry : Arrival.note (.register l e input digest) st ∈ s.2) :
    s.1.2 = true ∨ Partner pp (live st) (trialInput pp l e n b.randomizer) := by
  have addr := p.sameInput input digest st entry
  have value := p.agrees input digest st entry
  subst input digest
  exact p.first.partner_at_notice order seen st entry p.agrees

attribute [local irreducible] mixedGame graph guardedGraph simulateQ game chronicleGame

/-- A clean win produces a collision at the selected finder of an actual signer. -/
theorem registered_collision (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    {obs : Outcome} {out : ResidualCache pp} {s : ChronicleState} {last : SharedState}
    (actual : (some (obs,out),s) ∈ support (chronicleGame pp A left r))
    (fill : last ∈ support (RelabelState.endFill (physical s.1)))
    (win : wins obs = true) (clean : ¬ (graph pp).Conflict last)
    (safe : ¬ (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project last)) :
    let sig := obs.candidate.signature
    ∃ req issued, (req,Except.ok issued) ∈ obs.log ∧
      ∃ c : Receipt pp left req.leafIndex req.message issued,
      (req.leafIndex = sig.leafIndex ∧
        RegisteredPair pp s .bottom (UInt32.ofNat req.leafIndex.toNat)
          (packBytes obs.candidate.message)
          (packBytes req.message) sig.bottom issued.bottom c.x c.lowerPrior) ∨
      (bottomTree req.leafIndex = bottomTree sig.leafIndex ∧ ∃ candidateRoot,
        layerRoot (hashAt pp last) pp .bottom sig.leafIndex.toNat
          (packBytes obs.candidate.message) sig.bottom =
          some (some candidateRoot) ∧
        last.2 (.inr (.inl (.bottom,LayerGraph.treeRole LAYER_HEIGHT (bottomTree req.leafIndex)))) =
          some (digestEquiv c.root) ∧
        RegisteredPair pp s .top (UInt32.ofNat (bottomTree req.leafIndex)) (packBytes candidateRoot)
          (packBytes c.root) sig.top issued.top c.y c.upperPrior) := by
  dsimp only
  have raw : (some (obs,out),physical s.1) ∈ support ((simulateQ (graph pp).deferredImpl
      (guardedGraph left ((mixedGame pp A).run r))).run ((∅,∅),[])) := by
    rw [← project_graph pp A left r, support_map]
    exact ⟨_,actual,rfl⟩
  have later := RelabelState.le_of_mem_support_endFill fill
  have collision := forgery_collision pp A left r obs out _ last raw win later clean safe
  have facts := signed_history pp A left r _ obs out _ raw last later
  have valid : (Valid (eraseLog obs.log) ∧ ¬Contains (eraseLog obs.log) obs.candidate) ∧
    obs.verified = true := by
    simpa only [wins, Bool.and_eq_true, decide_eq_true_eq] using win
  let body := WeightedCap.capCompOpt fee left ((game pp A).run r)
  have run := actual
  unfold chronicleGame at run
  have origin := origin_run pp left body (fun _ => none) (z := (some (obs,out),s)) run
  have seen := seen_run pp left body initial.1 (z := (some (obs,out),s)) run
  have order := ordered_run pp left body initial.1 (z := (some (obs,out),s)) run
  have prior_le (a : Arrival) (ha : a ∈ s.2) : (physical a.prior).1 ≤ last :=
    (arrivals_extend pp left body initial.1 (z := (some (obs,out),s)) run a ha).trans later
  obtain ⟨req,issued,logged,hit⟩ := collision_arrivals origin seen fill clean facts collision
  obtain ⟨c,lower,upper,lowerAgree,upperAgree⟩ := registered_inputs pp A left
    r actual later clean valid.1.1 logged
  refine ⟨req,issued,logged,c,?_⟩
  rcases hit with ⟨idx,x,pair⟩ | ⟨idx,candidate,signed,y,read,row,pair⟩
  · rw [← idx] at pair
    have equal := pair.digits_of_read origin order fill (c.lower_digits (prior_le _ lower) clean)
    subst x
    have agrees : Agrees s.2 .bottom (UInt32.ofNat req.leafIndex.toNat) (selectedDigest c.x) :=
      fun b d st entry => (lowerAgree b d st entry).2
    exact Or.inl ⟨idx,pair,lower,agrees,fun b d st entry => (lowerAgree b d st entry).1,
      pair.partner_at_notice order seen _ lower agrees⟩
  · rw [← idx] at pair row
    have stored := c.bottom_root (prior_le _ lower)
    have eq := digestEquiv.injective (Option.some.inj (row.symm.trans stored))
    subst signed
    have equal := pair.digits_of_read origin order fill (c.upper_digits (prior_le _ upper) clean)
    subst y
    have agrees : Agrees s.2 .top (UInt32.ofNat (bottomTree req.leafIndex)) (selectedDigest c.y) :=
      fun b d st entry => (upperAgree b d st entry).2
    exact Or.inr ⟨idx,candidate,read,stored,pair,upper,agrees,fun b d st entry =>
      (upperAgree b d st entry).1,
      pair.partner_at_notice order seen _ upper agrees⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
