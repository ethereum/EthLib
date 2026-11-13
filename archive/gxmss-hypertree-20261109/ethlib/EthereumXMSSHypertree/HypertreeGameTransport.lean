/- Authors: Matthias Meijers -/

module
public import EthereumXMSSHypertree.HypertreeSourceGame
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
import all VCVio.OracleComp.ProbComp.Basic

/-!
# Source-signature game transport to the concrete reviewed hypertree

Source answers are reconstructed at their requested epochs. The named lifted
adversary strips the final embedded index. Malformed source forgeries reject;
only winning mass is intended to be bounded by the generic game.
-/

public section

namespace EthereumXMSSHypertree.HypertreeGameTransport

open EthLib.Cryptography.Xmss ConcreteHypertree
open OracleComp OracleSpec SyncSignatureUnforgeability

/-- The actual reviewed generic two-layer signature type. -/
abbrev GenericSignature := GXMSS.Hypertree.Signature Randomizer Digest shape

/-- The actual reviewed generic public-key type. -/
abbrev GenericPublicKey := GXMSS.PublicKey PublicParam Digest

/-- Exact equality on the finite concrete generic signature representation. -/
noncomputable instance : DecidableEq GenericSignature := Classical.decEq _

/-- Retain unused and failed epochs while packing every successful answer at its own epoch. -/
@[expose] def projectHistory (history : History Epoch Message GenericSignature) :
    History Epoch Message Signature := fun ep =>
  (history ep).map fun entry => (entry.1, entry.2.map (signatureToSource ep))

/-- Strip the source signature fields while retaining the forged epoch and message. -/
@[expose] def stripForgery (forgery : Forgery Epoch Message Signature) :
    Forgery Epoch Message GenericSignature :=
  (forgery.1, forgery.2.1, signatureToGeneric forgery.2.2)

/-- Source queries forward ambient requests and pack signing answers at the requested epoch. -/
@[expose] def signingAdapter :
    QueryImpl (unifSpec + signingSpec Epoch Message Signature)
      (OracleComp (unifSpec + signingSpec Epoch Message GenericSignature))
  | .inl query =>
    liftM ((unifSpec + signingSpec Epoch Message GenericSignature).query (Sum.inl query))
  | .inr (ep, msg) =>
    Option.map (signatureToSource ep) <$>
      (liftM ((unifSpec + signingSpec Epoch Message GenericSignature).query (Sum.inr (ep, msg))) :
        OracleComp (unifSpec + signingSpec Epoch Message GenericSignature) _)

/-- The named generic adversary receives source fields and strips its final source signature. -/
@[expose] def liftedAdversary
    (adv : Adversary unifSpec PublicKey Epoch Message Signature) :
    Adversary unifSpec GenericPublicKey Epoch Message GenericSignature where
  forge pk := stripForgery <$> simulateQ signingAdapter (adv.forge (publicKeyToSource pk))

/-- Empty generic histories project to empty source histories. -/
@[simp] theorem projectHistory_empty :
    projectHistory (emptyHistory : History Epoch Message GenericSignature) = emptyHistory := rfl

/-- Projection preserves exactly whether an epoch has ever been consumed. -/
theorem projectHistory_none_iff (history : History Epoch Message GenericSignature) (ep : Epoch) :
    projectHistory history ep = none ↔ history ep = none := by
  simp [projectHistory]

/-- A failed eligible request is retained as a failed consumed source epoch. -/
theorem projectHistory_failed (history : History Epoch Message GenericSignature)
    (ep : Epoch) (msg : Message) (h : history ep = some (msg, none)) :
    projectHistory history ep = some (msg, none) := by
  simp [projectHistory, h]

/-- Recording one optional generic answer commutes with exact source history projection. -/
theorem projectHistory_update (history : History Epoch Message GenericSignature)
    (ep : Epoch) (msg : Message) (answer : Option GenericSignature) :
    projectHistory (Function.update history ep (some (msg, answer))) =
      Function.update (projectHistory history) ep
        (some (msg, answer.map (signatureToSource ep))) := by
  funext other
  by_cases h : other = ep
  · subst other
    simp [projectHistory, Function.update]
  · simp [projectHistory, Function.update, h]

/-- At a coherent forged epoch, packing equality is exactly generic signature equality. -/
theorem packed_signature_eq_iff (ep : Epoch) (generic : GenericSignature) (sig : Signature)
    (coherent : leafIndexEquiv sig.leafIndex = ep) :
    signatureToSource ep generic = sig ↔ generic = signatureToGeneric sig := by
  constructor
  · intro h
    simpa only [signatureToGeneric_signatureToSource] using congrArg signatureToGeneric h
  · intro h
    rw [h, signatureToSource_signatureToGeneric ep sig coherent]

/-- Coherent exact message/signature-pair freshness is preserved in both directions. -/
theorem strongFresh_projectHistory (history : History Epoch Message GenericSignature)
    (forgery : Forgery Epoch Message Signature)
    (coherent : leafIndexEquiv forgery.2.2.leafIndex = forgery.1) :
    strongFresh (projectHistory history) forgery = strongFresh history (stripForgery forgery) := by
  rcases forgery with ⟨ep, msg, sig⟩
  cases hh : history ep with
  | none => simp [strongFresh, projectHistory, stripForgery, hh]
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none => simp [strongFresh, projectHistory, stripForgery, hh]
    | some generic =>
      simp [strongFresh, projectHistory, stripForgery, hh,
        packed_signature_eq_iff ep generic sig coherent]

/-- Source success implies generic success after stripping, including exact pair freshness. -/
theorem strongValid_imp (H : Pure.Hash) (seedGen : ProbComp PublicParam)
    (pk : GenericPublicKey) (forgery : Forgery Epoch Message Signature)
    (history : History Epoch Message GenericSignature)
    (h : strongValid (hypertreeSourceScheme H seedGen)
      (publicKeyToSource pk, forgery, projectHistory history) = true) :
    strongValid (concreteHypertreeScheme H seedGen) (pk, stripForgery forgery, history) = true := by
  have hparts :
      (hypertreeSourceScheme H seedGen).verify (publicKeyToSource pk) forgery.1
        forgery.2.1 forgery.2.2 = true ∧
      strongFresh (projectHistory history) forgery = true := by
    simpa only [strongValid, Bool.and_eq_true] using h
  obtain ⟨hv, hf⟩ := hparts
  change (if leafIndexEquiv forgery.2.2.leafIndex = forgery.1 then
    (concreteHypertreeScheme H seedGen).verify (publicKeyToGeneric (publicKeyToSource pk))
      forgery.1 forgery.2.1 (signatureToGeneric forgery.2.2) else false) = true at hv
  by_cases hc : leafIndexEquiv forgery.2.2.leafIndex = forgery.1
  · rw [ite_eq_left hc] at hv
    have hpk : publicKeyToGeneric (publicKeyToSource pk) = pk :=
      genericPublicKeyEquiv.apply_symm_apply pk
    rw [hpk] at hv
    rw [strongFresh_projectHistory history forgery hc] at hf
    simpa only [strongValid, stripForgery, Bool.and_eq_true] using And.intro hv hf
  · simp [hc] at hv

/-- The actual generic game's stateful ambient/signing handler for a fixed raw key. -/
@[expose] def genericHandler (H : Pure.Hash) (seedGen : ProbComp PublicParam) (raw : Seed) :
    QueryImpl (unifSpec + signingSpec Epoch Message GenericSignature)
      (StateT (History Epoch Message GenericSignature) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (History Epoch Message GenericSignature) ProbComp) +
      signingOracle (E := Epoch) (concreteHypertreeScheme H seedGen) raw

/-- The actual source wrapper game's stateful ambient/signing handler for that same raw key. -/
@[expose] def sourceHandler (H : Pure.Hash) (seedGen : ProbComp PublicParam) (raw : Seed) :
    QueryImpl (unifSpec + signingSpec Epoch Message Signature)
      (StateT (History Epoch Message Signature) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (History Epoch Message Signature) ProbComp) +
      signingOracle (E := Epoch) (hypertreeSourceScheme H seedGen) (⟨raw⟩ : SecretKey)

/-- Route source adversary queries through the actual generic handler and pack answers. -/
@[expose] def routedHandler (H : Pure.Hash) (seedGen : ProbComp PublicParam) (raw : Seed) :
    QueryImpl (unifSpec + signingSpec Epoch Message Signature)
      (StateT (History Epoch Message GenericSignature) ProbComp) :=
  fun query => simulateQ (genericHandler H seedGen raw) (signingAdapter query)

/-- One actual signing request preserves projected history, including duplicates and failures. -/
theorem signingOracle_projection (H : Pure.Hash) (seedGen : ProbComp PublicParam) (raw : Seed)
    (history : History Epoch Message GenericSignature) (ep : Epoch) (msg : Message) :
    (fun result => (result.1.map (signatureToSource ep), projectHistory result.2)) <$>
      (signingOracle (E := Epoch) (concreteHypertreeScheme H seedGen) raw (ep, msg)).run history =
      (signingOracle (E := Epoch) (hypertreeSourceScheme H seedGen) (⟨raw⟩ : SecretKey)
        (ep, msg)).run (projectHistory history) := by
  simp only [StateT.run]
  cases hh : history ep with
  | some entry =>
    rcases entry with ⟨first, answer⟩
    have hp : projectHistory history ep = some (first, answer.map (signatureToSource ep)) := by
      simp [projectHistory, hh]
    rw [signingOracle_used _ _ _ _ _ _ _ hh, signingOracle_used _ _ _ _ _ _ _ hp]
    simp
  | none =>
    have hp : projectHistory history ep = none := (projectHistory_none_iff history ep).mpr hh
    rw [signingOracle_unused _ _ _ _ _ hh, signingOracle_unused _ _ _ _ _ hp]
    simp only [hypertreeSourceScheme, bind_pure_comp,
      Functor.map_map, projectHistory_update]

/-- One routed request commutes with complete history projection. -/
theorem handler_projection (H : Pure.Hash) (seedGen : ProbComp PublicParam) (raw : Seed)
    (query : (unifSpec + signingSpec Epoch Message Signature).Domain)
    (history : History Epoch Message GenericSignature) :
    Prod.map id projectHistory <$> (routedHandler H seedGen raw query).run history =
      (sourceHandler H seedGen raw query).run (projectHistory history) := by
  cases query with
  | inl query =>
    simp [routedHandler, signingAdapter, genericHandler, sourceHandler,
      QueryImpl.add_apply_inl, QueryImpl.liftTarget, Functor.map_map]
  | inr request =>
    rcases request with ⟨ep, msg⟩
    simpa [ProbComp, routedHandler, signingAdapter, genericHandler, sourceHandler,
      QueryImpl.add_apply_inr, StateT.run_map, Functor.map_map] using
      signingOracle_projection H seedGen raw history ep msg

/-- Every adaptive query program retains its full output and projected first-request history. -/
theorem adaptive_projection (H : Pure.Hash) (seedGen : ProbComp PublicParam) (raw : Seed)
    {A : Type} (program : OracleComp (unifSpec + signingSpec Epoch Message Signature) A)
    (history : History Epoch Message GenericSignature) :
    Prod.map id projectHistory <$>
      (simulateQ (routedHandler H seedGen raw) program).run history =
      (simulateQ (sourceHandler H seedGen raw) program).run (projectHistory history) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ projectHistory
    (handler_projection H seedGen raw) program history

/-- One joint execution retains the source forgery and the actual generic first-request history. -/
@[expose] def jointInteraction (H : Pure.Hash) (seedGen : ProbComp PublicParam)
    (adv : Adversary unifSpec PublicKey Epoch Message Signature) :
    ProbComp (GenericPublicKey × Forgery Epoch Message Signature ×
      History Epoch Message GenericSignature) := do
  let (pk, raw) ← (concreteHypertreeScheme H seedGen).keygen
  let (forgery, history) ← (simulateQ (routedHandler H seedGen raw)
    (adv.forge (publicKeyToSource pk))).run emptyHistory
  pure (pk, forgery, history)

/-- The source view of the common execution reconstructs all recorded source signatures. -/
@[expose] def sourceView
    (out : GenericPublicKey × Forgery Epoch Message Signature ×
      History Epoch Message GenericSignature) :
    ExperimentResult PublicKey Epoch Message Signature :=
  (publicKeyToSource out.1, out.2.1, projectHistory out.2.2)

/-- The generic view strips the final forgery without changing the actual generic history. -/
@[expose] def genericView
    (out : GenericPublicKey × Forgery Epoch Message Signature ×
      History Epoch Message GenericSignature) :
    ExperimentResult GenericPublicKey Epoch Message GenericSignature :=
  (out.1, stripForgery out.2.1, out.2.2)

/-- The whole source interaction is the exact source projection of the common adaptive run. -/
theorem interaction_source (H : Pure.Hash) (seedGen : ProbComp PublicParam)
    (adv : Adversary unifSpec PublicKey Epoch Message Signature) :
    interaction (hypertreeSourceScheme H seedGen) adv =
      sourceView <$> jointInteraction H seedGen adv := by
  unfold interaction jointInteraction
  rw [show (hypertreeSourceScheme H seedGen).keygen =
    (fun keys => (publicKeyToSource keys.1, (⟨keys.2⟩ : SecretKey))) <$>
      (concreteHypertreeScheme H seedGen).keygen from rfl]
  simp only [bind_map_left, map_bind, map_pure]
  apply bind_congr
  rintro ⟨pk, raw⟩
  change ((simulateQ (sourceHandler H seedGen raw)
    (adv.forge (publicKeyToSource pk))).run emptyHistory >>= fun result =>
      pure (publicKeyToSource pk, result.1, result.2)) = _
  have hp := adaptive_projection H seedGen raw (adv.forge (publicKeyToSource pk)) emptyHistory
  rw [projectHistory_empty] at hp
  rw [← hp]
  simp only [bind_map_left]
  rfl

/-- The actual named lifted adversary gives the generic projection of the same adaptive run. -/
theorem interaction_generic (H : Pure.Hash) (seedGen : ProbComp PublicParam)
    (adv : Adversary unifSpec PublicKey Epoch Message Signature) :
    interaction (concreteHypertreeScheme H seedGen) (liftedAdversary adv) =
      genericView <$> jointInteraction H seedGen adv := by
  unfold interaction jointInteraction liftedAdversary
  simp only [map_bind, map_pure]
  apply bind_congr
  rintro ⟨pk, raw⟩
  change ((simulateQ (genericHandler H seedGen raw)
    (stripForgery <$> simulateQ signingAdapter (adv.forge (publicKeyToSource pk)))).run
      emptyHistory >>= fun result => pure (pk, result.1, result.2)) = _
  rw [simulateQ_map]
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := routedHandler H seedGen raw) (fun _ => rfl)]
  simp only [StateT.run_map, bind_map_left]
  rfl

/-- Source-wrapper strong winning mass is bounded by the actual generic game of the named lift. -/
theorem strong_success_mass_le (H : Pure.Hash) (seedGen : ProbComp PublicParam)
    (adv : Adversary unifSpec PublicKey Epoch Message Signature) :
    hypertreeSourceStrongGame H seedGen adv {true} ≤
      strongUnforgeableExp (concreteHypertreeScheme H seedGen) ProbCompRuntime.probComp
        (liftedAdversary adv) {true} := by
  simp only [hypertreeSourceStrongGame, strongUnforgeableExp, outputMeasure,
    interaction_source, interaction_generic, Functor.map_map]
  let : MeasurableSpace (GenericPublicKey × Forgery Epoch Message Signature ×
      History Epoch Message GenericSignature) := ⊤
  rw [ProbCompRuntime.probComp.evalDist_map _ Measurable.of_discrete,
    ProbCompRuntime.probComp.evalDist_map _ Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  exact MeasureTheory.measure_mono fun out h =>
    strongValid_imp H seedGen out.1 out.2.1 out.2.2 h

end EthereumXMSSHypertree.HypertreeGameTransport
