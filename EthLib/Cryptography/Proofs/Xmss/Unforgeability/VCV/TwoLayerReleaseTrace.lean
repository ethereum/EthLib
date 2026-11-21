module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerDelayed
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Direct chain reads in a realized signing trace

The leanXMSS draft, section "The scheme", releases one WOTS+C value per chain of each signed layer.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants HashSig OracleComp LayerGraph.Hidden

/-- Extract a direct read of a private start or a low WOTS+C chain row. -/
def directChain : SharedSpec.Domain → Option Cell
  | .inl (.inr x) => some (.inl x)
  | .inr (.inr (.inl (l, .chain e i j))) => some (.inr (.inl (l, .chain e i j)))
  | _ => none

/-- Reads of non-chain rows, touches, public queries and ordinary coins are unrestricted. -/
def Within (cells : Set Cell) (q : SharedSpec.Domain) : Prop :=
  ∀ c, directChain q = some c → c ∈ cells

/-- The positions encoded by one actual codeword, with the epoch and layer included. -/
def positions (l : Layer) (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V) : Set Cell :=
  {c | ∃ i : Fin V, c = inLayer l (LayerGraph.position e i x[i].val)}

private theorem touch_within (pp : PublicParam) (l : Layer) (c : Option LayerGraph.Cell)
    (cells : Set Cell) : AllQueriesSatisfy
      (simulateQ (selection pp l).liftQuery (touchCell c)) (Within cells) := by
  cases c with
  | none => exact allQueriesSatisfy_pure _ _
  | some c =>
    change AllQueriesSatisfy (touchCell (pub := ChainGraph.Public) (R := ChainGraph.Word)
      (some (inLayer l c))) _
    exact (allQueriesSatisfy_query_iff _ _).2 (by intro _; simp [directChain])

private theorem read_within (pp : PublicParam) (l : Layer) (c : LayerGraph.Cell) (cells : Set Cell)
    (allowed : ∀ q : SharedSpec.Domain, directChain q = some (inLayer l c) →
      inLayer l c ∈ cells) :
    AllQueriesSatisfy (simulateQ (selection pp l).liftQuery (readCell (some c)))
      (Within cells) := by
  rcases c with x | k
  · apply (allQueriesSatisfy_query_iff _ _).2
    intro d eq
    cases eq
    exact allowed (.inl (.inr (l, x))) rfl
  · rcases k with k | k
    · cases k <;> apply (allQueriesSatisfy_query_iff _ _).2
      · rename_i e i j
        intro d eq
        cases eq
        exact allowed (.inr (.inr (.inl (l, .chain e i j)))) rfl
      all_goals intro d eq; cases eq
    · apply (allQueriesSatisfy_query_iff _ _).2
      intro d eq
      cases eq

private theorem mark_within (pp : PublicParam) (l : Layer) (cells : Set Cell)
    {p : OracleComp LayerGraph.Spec Unit}
    (structural : ∀ P : OracleComp LayerGraph.Spec Unit → Prop, P (pure ()) →
      (∀ a b, P a → P b → P (a >>= fun _ => b)) →
      (∀ c, P (touchCell c)) → P p) :
    AllQueriesSatisfy (simulateQ (selection pp l).liftQuery p) (Within cells) := by
  apply structural
  · exact allQueriesSatisfy_pure _ _
  · intro a b ha hb
    rw [simulateQ_bind]
    exact allQueriesSatisfy_bind ha fun _ => hb
  · exact fun c => touch_within pp l c cells

/-- Both halves of every physical input in the internal signing traversal are touches. -/
theorem beforeValues_within (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) (cells : Set Cell) : AllQueriesSatisfy
      (simulateQ (selection pp l).liftQuery (beforeValues pp l e x)) (Within cells) :=
  mark_within pp l cells fun P ret seq touch =>
    beforeValues_pred P ret seq (fun c => touch (some c)) pp l e x

/-- The full honest tree traversal has no direct chain read. -/
theorem beforeNode_within (pp : PublicParam) (l : Layer) (h j : Nat) (cells : Set Cell) :
    AllQueriesSatisfy (simulateQ (selection pp l).liftQuery (beforeNode pp l h j)) (Within cells) :=
  mark_within pp l cells fun P ret seq touch =>
    beforeNode_pred P ret seq (fun c => touch (some c)) pp l h j

private theorem collect_within {α ι : Type} (spec : OracleSpec ι) (P : spec.Domain → Prop) :
    ∀ n (f : Fin n → OracleComp spec α), (∀ i, AllQueriesSatisfy (f i) P) →
      AllQueriesSatisfy (ofFnInOrder n f) P
  | 0, _, _ => allQueriesSatisfy_pure _ _
  | n + 1, f, h => allQueriesSatisfy_bind (h 0) fun _ =>
      allQueriesSatisfy_bind (collect_within spec P n (fun i => f i.succ) fun i => h i.succ)
        fun _ =>
        allQueriesSatisfy_pure _ _

private theorem map_within {α β : Type} {op : OracleComp SharedSpec α}
    {p : SharedSpec.Domain → Prop}
    (f : α → β) (safe : AllQueriesSatisfy op p) : AllQueriesSatisfy (f <$> op) p := by
  rw [← bind_pure_comp]
  exact allQueriesSatisfy_bind safe fun _ => allQueriesSatisfy_pure _ _

/-- Each actual chain disclosure reads only the cell picked out by its decoded digit. -/
theorem revealValues_within (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) : AllQueriesSatisfy
      (simulateQ (selection pp l).liftQuery (revealValues e x)) (Within (positions l e x)) := by
  unfold revealValues
  rw [HashSig.ofFnInOrder_map_monad (fun {_} p => simulateQ (selection pp l).liftQuery p)
    (simulateQ_pure _) (simulateQ_bind _)]
  apply collect_within
  intro i
  rw [simulateQ_map]
  exact map_within _ (read_within pp l _ _ (fun _ _ => ⟨i, rfl⟩))

private theorem treeRead_within (pp : PublicParam) (l : Layer) (h j : Nat) (cells : Set Cell) :
    AllQueriesSatisfy (simulateQ (selection pp l).liftQuery
      (readCell (some (.inr (.inl (LayerGraph.treeRole h j)))))) (Within cells) := by
  unfold LayerGraph.treeRole LayerGraph.atDepth
  split <;> apply (allQueriesSatisfy_query_iff _ _).2 <;> intro c eq <;> cases eq

private theorem output_within (pp : PublicParam) (l : Layer) (h j : Nat) (cells : Set Cell) :
    AllQueriesSatisfy (simulateQ (selection pp l).liftQuery
      (LayerGraph.readOutput (LayerGraph.treeRole h j))) (Within cells) := by
  unfold LayerGraph.readOutput
  simp only [simulateQ_bind, simulateQ_pure]
  exact allQueriesSatisfy_bind (treeRead_within pp l h j cells) fun _ =>
    allQueriesSatisfy_bind (touch_within pp l _ cells) fun _ => allQueriesSatisfy_pure _ _

/-- Reading the root and the low/high tree rows never reads a private or public chain cell. -/
theorem root_within (pp : PublicParam) (l : Layer) (h j : Nat) (cells : Set Cell) :
    AllQueriesSatisfy (simulateQ (selection pp l).liftQuery
      (beforeNode pp l h j >>= fun _ => LayerGraph.readOutput (LayerGraph.treeRole h j)))
      (Within cells) := by
  rw [simulateQ_bind]
  exact allQueriesSatisfy_bind (beforeNode_within pp l h j cells) fun _ =>
    output_within pp l h j cells

/-- Sibling paths in a generated tree contain only Merkle and OTS-leaf rows. -/
theorem revealPath_within (pp : PublicParam) (l : Layer) (h e : Nat) (cells : Set Cell) :
    AllQueriesSatisfy (simulateQ (selection pp l).liftQuery (revealPath h e)) (Within cells) := by
  unfold revealPath
  rw [HashSig.ofFnInOrder_map_monad (fun {_} p => simulateQ (selection pp l).liftQuery p)
    (simulateQ_pure _) (simulateQ_bind _)]
  apply collect_within
  intro i
  rw [simulateQ_map]
  exact map_within _ (treeRead_within pp l _ _ cells)

/-- Computing the top path from its sibling subtrees is also outside the chain release set. -/
theorem path_within (pp : PublicParam) (l : Layer) (e : Nat) (cells : Set Cell) :
    AllQueriesSatisfy (pathSchedule pp l e) (Within cells) :=
  collect_within SharedSpec _ _ _ fun _ => root_within pp l _ _ cells

private theorem search_within {κ β : Type} (trial : Nat → κ)
    (test : κ → OracleComp SharedSpec (Option β)) (cells : Set Cell)
    (allowed : ∀ k, AllQueriesSatisfy (test k) (Within cells)) :
    ∀ c fuel, AllQueriesSatisfy (Wots.findFirst trial test c fuel) (Within cells)
  | _, 0 => allQueriesSatisfy_pure _ _
  | c, fuel + 1 => allQueriesSatisfy_bind (allowed _) fun
    | none => search_within trial test cells allowed (c + 1) fuel
    | some _ => allQueriesSatisfy_pure _ _

/-- An honest digest trial makes only ordinary public calls, including warm repeated trials. -/
theorem finder_within (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (cells : Set Cell) (c fuel : Nat) :
    AllQueriesSatisfy (Xmss.Internal.findCodeword hash pp l e msg base c fuel) (Within cells) := by
  apply search_within
  intro _
  apply map_within
  apply allQueriesSatisfy_bind
  · unfold hash
    apply allQueriesSatisfy_bind
    · apply (allQueriesSatisfy_query_iff _ _).2
      intro _ eq
      cases eq
    · intro _
      apply allQueriesSatisfy_bind
      · apply (allQueriesSatisfy_query_iff _ _).2
        intro _ eq
        cases eq
      · exact fun _ => allQueriesSatisfy_pure _ _
  · exact fun _ => allQueriesSatisfy_pure _ _

/-- Every cached-seed callback used for a randomizer must avoid direct chain reads. -/
def ResidualReads (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec)) : Prop :=
  ∀ l e msg, AllQueriesSatisfy (cb pp (addrRnd l e) msg) (Within ∅)

theorem randomizer_within (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (residual : ResidualReads pp cb) (l : Layer) (e : UInt32) (msg : ByteArray) :
    AllQueriesSatisfy (randomizerBase pp cb l e msg) (Within ∅) :=
  allQueriesSatisfy_bind (residual l e msg) fun _ => allQueriesSatisfy_pure _ _

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
