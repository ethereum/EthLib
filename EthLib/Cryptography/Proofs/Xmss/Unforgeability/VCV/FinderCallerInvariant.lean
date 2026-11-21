module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedProjection

/-!
# An invariant for the marked adaptive caller

Each finder, the clock and parameter derivation may update the private table.

Every other physical operation leaves the private table unchanged.

The statement includes the genuine client and final verifier.
-/

@[expose] public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open EthLib.Cryptography HashSig Constants OracleComp OracleSpec TwoLayerGraph Honest

/-- A completed segment preserves the relation between the residual table and the observed state. -/
def Maintains {pp : PublicParam} (I : ResidualCache pp → State pp → Prop)
    {α : Type} (p : Body pp α) : Prop :=
  ∀ q r s a out t, I r s → Done q p r s a out t → I out t

variable {pp : PublicParam} {I : ResidualCache pp → State pp → Prop}

theorem Maintains.bind {α β : Type} {p : Body pp α} {f : α → Body pp β}
    (h : Maintains I p) (g : ∀ a, Maintains I (f a)) : Maintains I (p >>= f) := by
  intro q r s a out t prior ran
  obtain ⟨b,mid,v,first,tail⟩ := ran.bind
  exact g b q mid v a out t (h q r s b mid v prior first) tail

theorem Maintains.pure {α : Type} (a : α) : Maintains I (pure a : Body pp α) := by
  intro q r s b out t prior ran
  obtain ⟨rfl,rfl,rfl⟩ := ran.pure_result
  exact prior

theorem Maintains.map {α β : Type} {p : Body pp α} (f : α → β) (h : Maintains I p) :
    Maintains I (f <$> p) := by
  rw [map_eq_pure_bind]
  exact Maintains.bind h fun _ => Maintains.pure _

/-- The physical operation returns the entire incoming residual table. -/
def Unchanged {pp : PublicParam} {α : Type} (p : Program pp α) : Prop :=
  ∀ r z, z ∈ support (p.run r) → z.2 = r

private theorem unchanged_bind {pp} {α β : Type} {p : Program pp α} {f : α → Program pp β}
    (h : Unchanged p) (k : ∀ a, Unchanged (f a)) : Unchanged (p >>= f) := by
  intro r z ran
  rw [StateT.run_bind,mem_support_bind_iff] at ran
  obtain ⟨⟨a,mid⟩,first,tail⟩ := ran
  exact (k a mid z tail).trans (h r _ first)

theorem unchanged_lift {pp} {α : Type} (p : OracleComp MixedWorld α) :
    Unchanged (carry (liftM p : MixedLocal pp α)) := by
  intro r z ran
  have source := support_simulateQ_subset raw _ ran
  simp only [StateT.run_monadLift,monadLift_self,mem_support_bind_iff,mem_support_pure_iff]
    at source
  obtain ⟨_,_,rfl⟩ := source
  rfl

private theorem unchanged_notice {pp} (n : FinderNotice) : Unchanged (emit (pp := pp) n) := by
  intro r z ran
  simp only [emit,StateT.run_mk,support_map] at ran
  obtain ⟨_,_,rfl⟩ := ran
  rfl

theorem unchanged_afterUpper (pp : PublicParam) (i : LeafIndex) (m n : ByteArray)
    (rho tau : Randomizer) (x y : Vector (Fin CHAIN_LENGTH) V) :
    Unchanged (afterUpper pp i m n rho tau x y) := by
  unfold afterUpper
  apply unchanged_bind (unchanged_lift _)
  intro _
  apply unchanged_bind (unchanged_lift _)
  intro _
  apply unchanged_bind (unchanged_lift _)
  intro _
  apply unchanged_bind (unchanged_lift _)
  intro _
  apply unchanged_bind (unchanged_notice _)
  intro _
  apply unchanged_bind (unchanged_notice _)
  intro _ r z ran
  rw [StateT.run_pure,mem_support_pure_iff] at ran
  exact congrArg Prod.snd ran

/-- Local preservation obligations for the two-layer signer and its client. -/
structure Steps (pp : PublicParam) (I : ResidualCache pp → State pp → Prop) : Prop where
  search : ∀ l e m, Maintains I (Searches.search pp l e m)
  physical : ∀ {α : Type} (p : Program pp α), Unchanged p → Maintains I (Searches.physical p)
  tick : Maintains I (Searches.physical (carry (mixedTick pp)))
  parameter : Maintains I (Searches.physical (carry (mixedParameter pp)))

private theorem Steps.lift (h : Steps pp I) {α : Type} (p : OracleComp MixedWorld α) :
    Maintains I (Searches.physical (carry (liftM p : MixedLocal pp α))) :=
  h.physical _ (unchanged_lift p)

private theorem regular_signing (h : Steps pp I) (idx : LeafIndex) (msg : Message) :
    Maintains I (signing pp idx msg) := by
  unfold signing
  apply Maintains.bind (h.search _ _ _)
  rintro (_ | ⟨rho,x⟩)
  · exact Maintains.pure _
  · apply Maintains.bind (h.lift _)
    intro _
    apply Maintains.bind (h.lift _)
    intro root
    apply Maintains.bind (h.search _ _ _)
    rintro (_ | ⟨tau,y⟩)
    · exact Maintains.pure _
    · exact h.physical _
        (unchanged_afterUpper pp idx (packBytes msg) (packBytes root) rho tau x y)

private theorem regular_request (h : Steps pp I) (t : (World + SigningSpec).Domain) :
    Maintains I ((clientOracle pp t).run) := by
  rcases t with q | req
  · change Maintains I ((fun x => (x,([] : RawLog))) <$> physical (carry (mixedWorldPass pp q)))
    apply Maintains.map
    cases q <;> apply h.lift
  · change Maintains I (_ >>= _)
    apply Maintains.bind (h.tick)
    intro _
    apply Maintains.bind (h.parameter)
    intro _
    apply Maintains.bind (regular_signing h req.leafIndex req.message)
    exact fun _ => Maintains.pure _

private theorem regular_client {α : Type} (h : Steps pp I)
    (p : OracleComp (World + SigningSpec) α) :
    Maintains I ((simulateQ (clientOracle pp) p).run) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp only [simulateQ_pure,WriterT.run_pure]; apply Maintains.pure
  | query_bind t k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,WriterT.run_bind']
    exact Maintains.bind (regular_request h t) fun z => Maintains.map _ (ih z.1)

/-- The signing operations preserve the invariant on every physically complete caller run. -/
theorem Steps.caller (h : Steps pp I) (A : Adversary) : Maintains I (Searches.caller pp A) := by
  unfold Searches.caller
  apply Maintains.bind (h.lift _)
  intro _
  apply Maintains.bind (regular_client h _)
  rintro ⟨_,_⟩
  apply Maintains.bind (h.lift _)
  exact fun _ => Maintains.pure _

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
