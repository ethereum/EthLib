module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerSign

/-!
# Chain values released by a successful two-layer signature

The bottom one-time signer may find a codeword while the top layer later fails.

The final error reply contains no bottom chain values.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants HashSig OracleComp LayerGraph.Hidden
open ChainGraph (digestEquiv)

private theorem grows {α : Type} (pp : PublicParam) (op : OracleComp SharedSpec α)
    (s : SharedState) {z} (ran : z ∈ support ((simulateQ (graph pp).eagerImpl op).run s)) :
    s ≤ z.2 :=
  simulateQ_run_preservesInv _ (s ≤ ·)
    (fun _ _ prev _ hz => prev.trans ((graph pp).le_of_mem_support_eagerImpl hz))
    op s le_rfl z ran

/-- Marking the bottom signer establishes one value which all later reads can return unchanged. -/
def StableRead {α : Type} (pp : PublicParam) (mark : OracleComp SharedSpec Unit)
    (read : OracleComp SharedSpec α) : Prop :=
  ∀ s z, z ∈ support ((simulateQ (graph pp).eagerImpl mark).run s) →
    ∃ a, ∀ t : SharedState, z.2 ≤ t →
      (simulateQ (graph pp).eagerImpl read).run t = pure (a, t)

private theorem delay {α β γ ε : Type} (pp : PublicParam)
    (mark : OracleComp SharedSpec Unit) (read : OracleComp SharedSpec α)
    (next : OracleComp SharedSpec (Except ε β)) (pack : α → β → γ)
    (ready : StableRead pp mark read) :
    simulateQ (graph pp).eagerImpl (do
      mark
      let a ← read
      let result ← next
      return result.map (pack a)) =
    simulateQ (graph pp).eagerImpl (do
      mark
      match ← next with
      | .error e => return .error e
      | .ok b => return .ok (pack (← read) b)) := by
  ext s : 1
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro w marked
  obtain ⟨a, stable⟩ := ready s w marked
  rw [stable w.2 le_rfl, pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨r, t⟩ later
  have keep := stable t (grows pp next w.2 later)
  cases r with
  | error err => rfl
  | ok b => simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      keep, pure_bind, Except.map]

private theorem stable_values (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) : StableRead pp
      (simulateQ (selection pp l).liftQuery (beforeValues pp l e x))
      (simulateQ (selection pp l).liftQuery (revealValues e x)) := by
  let v := selection pp l
  have marks : v.Exact (beforeValues pp l e x) :=
    beforeValues_pred (fun p => v.Exact p) (v.exact_pure ())
      (fun _ _ a b => v.exact_bind a fun _ => b) v.exact_touchCell pp l e x
  have reads : v.Exact (revealValues e x) :=
    exact_collect pp l _ _ fun i => v.exact_map _ (v.exact_readCell _)
  intro s z hz
  rw [marks s, support_map] at hz
  obtain ⟨⟨u, last⟩, old, same⟩ := hz
  cases u
  subst z
  obtain ⟨ys, stored⟩ := beforeValues_stored pp l e x (v.project s) last old
  refine ⟨ys, fun t later => ?_⟩
  have projected : last ≤ v.project t := by
    rw [← v.project_extend s last]
    exact v.project_mono later
  rw [reads t, reveal_cached pp l e x ys (v.project t) (fun i => projected.2 (stored i))]
  simp [v.extend_project]

/-- After the bottom build, the top signer authenticates its root. -/
noncomputable def finishTree (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (idx : LeafIndex) : OracleComp SharedSpec (Except XmssError
      (Vector Digest LAYER_HEIGHT × LayerSignature)) := do
  let both ← builtPathSchedule pp .bottom LAYER_HEIGHT (bottomTree idx) idx.toNat
  let answer ← layerSchedule pp cb .top (bottomTree idx) (packBytes both.1)
  return answer.map (fun top => (both.2, top))

def packSignature (idx : LeafIndex) (rho : Randomizer) (ys : Vector Digest V)
    (result : Vector Digest LAYER_HEIGHT × LayerSignature) : Signature :=
  ⟨idx, ⟨rho, ys, result.1⟩, result.2⟩

/-- Only a successful two-layer reply directly reads the bottom chain signature. -/
noncomputable def releasedSchedule (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (idx : LeafIndex) (msg : Message) : OracleComp SharedSpec (Except XmssError Signature) := do
  let e := UInt32.ofNat idx.toNat
  let bytes := packBytes msg
  let base ← randomizerBase pp cb .bottom e bytes
  let some (rho, x) ←
      Xmss.Internal.findCodeword hash pp .bottom e bytes base 0 MAX_RANDOMIZER_TRIALS
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  let lift := selection pp .bottom
  simulateQ lift.liftQuery (beforeValues pp .bottom e x)
  match ← finishTree pp cb idx with
  | .error err => return .error err
  | .ok b =>
    let ys ← simulateQ lift.liftQuery (revealValues e x)
    return .ok (packSignature idx rho ys b)

attribute [local irreducible] Xmss.Internal.findCodeword beforeValues revealValues
  layerSchedule builtPathSchedule

/-- The actual signer and its success-only chain disclosures have the same full shared eager law. -/
theorem signDerived_released (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (pairs : ∀ l, Pairs pp l cb) (idx : LeafIndex) (msg : Message) :
    simulateQ (graph pp).eagerImpl (Xmss.signDerived hash cb pp idx msg) =
      simulateQ (graph pp).eagerImpl (releasedSchedule pp cb idx msg) := by
  rw [signDerived_schedule pp cb pairs]
  unfold singleBuildSchedule releasedSchedule signSchedule
  simp only [simulateQ_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro base
  apply bind_congr
  rintro (_ | ⟨rho, x⟩)
  · rfl
  · let e := UInt32.ofNat idx.toNat
    let lift := selection pp .bottom
    let mark := simulateQ lift.liftQuery (beforeValues pp .bottom e x)
    let read := simulateQ lift.liftQuery (revealValues e x)
    have same := delay pp mark read (finishTree pp cb idx) (packSignature idx rho)
      (stable_values pp .bottom e x)
    simp only [simulateQ_bind] at same
    simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
    refine Eq.trans ?_ (same.trans ?_)
    · simp only [mark, read, lift, e]
      apply bind_congr
      intro _
      apply bind_congr
      intro ys
      simp only [finishTree, simulateQ_bind, bind_assoc, pure_bind, simulateQ_pure]
      apply bind_congr
      intro both
      apply bind_congr
      intro ans
      cases ans <;> rfl
    · apply bind_congr
      intro _
      apply bind_congr
      intro reply
      cases reply <;> rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
