module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LocalReleaseTrace
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ResidualClient

/-!
# Direct reads in an adaptive signing transcript

A disclosed cell belongs to a successful request in the actual returned log.

Both codewords come from the two finder runs of that request.

The raw signing log and the graph query log are concatenated in request order.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleSpec OracleComp

/-- Positions authorized by the returned signatures and their actual finder results. -/
@[expose] def releasedCells (pp : PublicParam) (last : SharedState) (raw : RawLog) : Set Cell :=
  {c | ∃ (req : SignRequest) (sig : Signature), (req, .ok sig) ∈ raw ∧
    sig.leafIndex = req.leafIndex ∧
    ∃ (root : Digest) (x y : Vector (Fin CHAIN_LENGTH) V),
      last.2 (.inr (.inl (.bottom, LayerGraph.treeRole LAYER_HEIGHT (bottomTree req.leafIndex)))) =
        some (ChainGraph.digestEquiv root) ∧
      Trial pp .bottom (UInt32.ofNat req.leafIndex.toNat) (packBytes req.message)
        sig.bottom.randomizer x last ∧
      Trial pp .top (UInt32.ofNat (bottomTree req.leafIndex)) (packBytes root)
        sig.top.randomizer y last ∧
      c ∈ positions .bottom (UInt32.ofNat req.leafIndex.toNat) x ∪
        positions .top (UInt32.ofNat (bottomTree req.leafIndex)) y}

private theorem released_mono {pp : PublicParam} {s t : SharedState} {xs ys : RawLog}
    (later : s ≤ t)
    (records : ∀ a ∈ xs, a ∈ ys) : releasedCells pp s xs ⊆ releasedCells pp t ys := by
  rintro c ⟨r, sig, mem, same, root, x, y, stored, lower, upper, selected⟩
  exact ⟨r, sig, records _ mem, same, root, x, y, later.2 stored, lower.mono later,
    upper.mono later, selected⟩

theorem logged_signer_cells (pp : PublicParam) (req : SignRequest)
    (r : ResidualCache pp) {s a out log t}
    (ran : Logged pp ((localReleased pp (graphPrf pp) req.leafIndex req.message).run r) s
      (a, out) log t) :
    LogWithin (releasedCells pp t.1 [(req, a)]) log := by
  have h := local_signature_release pp r req.leafIndex req.message ran
  cases a with
  | error err => exact h.mono (Set.empty_subset _)
  | ok sig =>
    obtain ⟨same, root, x, y, stored, low, high, reads⟩ := h
    exact reads.mono fun _ c => ⟨req, sig, List.mem_singleton_self _, same,
      root, x, y, stored, low, high, c⟩

private theorem map_inverse {α β : Type} {pp : PublicParam} {p : OracleComp SharedSpec α}
    {f : α → β}
    {s b log t} (ran : Logged pp (f <$> p) s b log t) :
    ∃ a, Logged pp p s a log t ∧ f a = b := by
  unfold Logged at ran ⊢
  simp only [simulateQ_map, WriterT.run_map', StateT.run_map, support_map] at ran
  obtain ⟨⟨⟨a, pre⟩, state⟩, h, eq⟩ := ran
  cases eq
  exact ⟨a, h, rfl⟩

/-- Compose the actual single-step log property for an adaptive caller with private state. -/
theorem adaptive_log {α R : Type} (pp : PublicParam)
    (impl : QueryImpl (World + SigningSpec) (WriterT RawLog (WithLocal R))) (invariant : R → Prop)
    (step : ∀ q initial s ans out xs t, invariant initial →
      Logged pp ((impl q).run.run initial) s (ans, out) xs t →
        invariant out ∧ LogWithin (releasedCells pp t.1 ans.2) xs)
    (p : OracleComp (World + SigningSpec) α) (initial : R) (ok : invariant initial) {s ans out xs t}
    (ran : Logged pp ((simulateQ impl p).run.run initial) s (ans, out) xs t) :
    invariant out ∧ LogWithin (releasedCells pp t.1 ans.2) xs := by
  induction p using OracleComp.inductionOn generalizing initial s ans out xs t with
  | pure a =>
    simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure] at ran
    obtain ⟨eq, rfl, _⟩ := ran.pure_result
    cases eq
    exact ⟨ok, fun _ e => (List.not_mem_nil e).elim⟩
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind',
      StateT.run_bind, StateT.run_map] at ran
    obtain ⟨⟨⟨reply, left⟩, next⟩, prelog, mid, postlog, ha, hb, rfl⟩ := ran.bind
    obtain ⟨⟨⟨result, right⟩, final⟩, tail, eq⟩ := map_inverse hb
    cases eq
    obtain ⟨good, pre⟩ := step q initial s _ next _ _ ok ha
    obtain ⟨finish, post⟩ := ih reply next good tail
    exact ⟨finish,
      (pre.mono (released_mono tail.grows (fun _ h => List.mem_append_left _ h))).append
      (post.mono (released_mono le_rfl (fun _ h => List.mem_append_right _ h)))⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
