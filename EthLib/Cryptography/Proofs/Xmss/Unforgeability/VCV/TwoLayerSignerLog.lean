module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerReleaseTrace
public import VCVio.OracleComp.QueryTracking.RandomOracle.ReadSet

/-!
# The chronologically logged result of the actual two-layer signer

The deferred graph returns each reply alongside the requests that produced it.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants HashSig OracleSpec OracleComp LayerGraph.Hidden

abbrev DeferredState := SharedState × List Cell

/-- Execute the ordinary VCVio logger through the shared deferred graph. -/
def Logged {α : Type} (pp : PublicParam) (op : OracleComp SharedSpec α)
    (s : DeferredState) (a : α) (log : SharedSpec.QueryLog) (t : DeferredState) : Prop :=
  ((a, log), t) ∈ support
    ((simulateQ (graph pp).deferredImpl (simulateQ loggingOracle op).run).run s)

/-- Each step of the log whose query directly reads a chain must belong to the release set. -/
def LogWithin (cells : Set Cell) (log : SharedSpec.QueryLog) : Prop :=
  ∀ entry ∈ log, Within cells entry.1

namespace Logged

theorem raw {α : Type} {pp : PublicParam} {p : OracleComp SharedSpec α} {s a log t}
    (ran : Logged pp p s a log t) :
    (a, t) ∈ support ((simulateQ (graph pp).deferredImpl p).run s) := by
  rw [← loggingOracle.fst_map_run_simulateQ p, simulateQ_map, StateT.run_map, support_map]
  exact ⟨((a, log), t), ran, rfl⟩

theorem grows {α : Type} {pp : PublicParam} {p : OracleComp SharedSpec α} {s a log t}
    (ran : Logged pp p s a log t) : s.1 ≤ t.1 :=
  (graph pp).le_of_mem_support_simulateQ_deferredImpl p ran.raw

theorem within {α : Type} {pp : PublicParam} {p : OracleComp SharedSpec α} {s a log t}
    (ran : Logged pp p s a log t) (cells : Set Cell) (safe : AllQueriesSatisfy p (Within cells)) :
    LogWithin cells log := by
  have free : (a, log) ∈ support ((simulateQ loggingOracle p).run) :=
    mem_support_of_mem_support_simulateQ_run (graph pp).deferredImpl _ s ran
  exact holds_of_mem_log_of_mem_support_run_simulateQ safe free

theorem bind {α β : Type} {pp : PublicParam} {p : OracleComp SharedSpec α}
    {k : α → OracleComp SharedSpec β} {s b log t} (ran : Logged pp (p >>= k) s b log t) :
    ∃ a pre middle post, Logged pp p s a pre middle ∧ Logged pp (k a) middle b post t ∧
      log = pre ++ post := by
  unfold Logged at ran
  simp only [simulateQ_bind, WriterT.run_bind', StateT.run_bind, simulateQ_map, StateT.run_map,
    mem_support_bind_iff, support_map] at ran
  obtain ⟨⟨⟨a, pre⟩, middle⟩, ha, ⟨⟨c, post⟩, last⟩, hc, same⟩ := ran
  cases same
  exact ⟨a, pre, middle, post, ha, hc, rfl⟩

theorem pure_result {α : Type} {pp : PublicParam} {a b : α} {s log t}
    (ran : Logged pp (pure a) s b log t) : b = a ∧ log = [] ∧ t = s := by
  change ((b, log), t) ∈ support (pure ((a, []), s) : ProbComp _) at ran
  rw [mem_support_pure_iff] at ran
  cases ran
  exact ⟨rfl, rfl, rfl⟩

end Logged

theorem LogWithin.mono {a b : Set Cell} {log : SharedSpec.QueryLog}
    (h : LogWithin a log) (le : a ⊆ b) : LogWithin b log :=
  fun entry member c eq => le (h entry member c eq)

theorem LogWithin.append {a : Set Cell} {xs ys : SharedSpec.QueryLog}
    (x : LogWithin a xs) (y : LogWithin a ys) : LogWithin a (xs ++ ys) := by
  intro entry member
  rcases List.mem_append.mp member with hx | hy
  · exact x entry hx
  · exact y entry hy

/-- The named digits came from a supported execution of the original finder in this shared graph. -/
def Trial (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer)
    (x : Vector (Fin CHAIN_LENGTH) V) (final : SharedState) : Prop :=
  ∃ (base : Randomizer) (s t : DeferredState), (some (rho, x), t) ∈ support
    ((simulateQ (graph pp).deferredImpl
      (Xmss.Internal.findCodeword hash pp l e msg base 0 MAX_RANDOMIZER_TRIALS)).run s) ∧
    t.1 ≤ final

theorem Trial.mono {pp l e msg rho x s t} (trial : Trial pp l e msg rho x s) (later : s ≤ t) :
    Trial pp l e msg rho x t := by
  obtain ⟨base, initial, last, ran, cut⟩ := trial
  exact ⟨base, initial, last, ran, cut.trans later⟩

/-- The returned randomizer names the actual finder run that selected each read position. -/
def OtsRelease (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (ans : Option (Randomizer × Vector Digest V)) (log : SharedSpec.QueryLog)
    (last : SharedState) : Prop :=
  match ans with
  | none => LogWithin ∅ log
  | some (rho, _) => ∃ x, Trial pp l e msg rho x last ∧ LogWithin (positions l e x) log

attribute [local irreducible] Xmss.Internal.findCodeword beforeValues revealValues

theorem ots_logged (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec))
    (residual : ResidualReads pp cb) (e : UInt32) (msg : ByteArray) {s ans log t}
    (ran : Logged pp (signSchedule pp l cb e msg) s ans log t) :
    OtsRelease pp l e msg ans log t.1 := by
  unfold signSchedule at ran
  obtain ⟨base, l₀, s₁, rest, seed, work, rfl⟩ := ran.bind
  have seedSafe := seed.within ∅ (randomizer_within pp cb residual l e msg)
  obtain ⟨found, l₁, s₂, suffix, find, tail, rfl⟩ := work.bind
  have findSafe := find.within ∅ (finder_within pp l e msg base ∅ 0 MAX_RANDOMIZER_TRIALS)
  cases found with
  | none =>
    obtain ⟨rfl, rfl, _⟩ := tail.pure_result
    simpa only [OtsRelease, List.append_nil] using seedSafe.append findSafe
  | some pair =>
    obtain ⟨rho, x⟩ := pair
    obtain ⟨values, valueLog, s₃, pureLog, exposure, pureRun, rfl⟩ := tail.bind
    obtain ⟨rfl, rfl, rfl⟩ := pureRun.pure_result
    rw [simulateQ_bind] at exposure
    obtain ⟨_, marks, s₄, reads, marked, read, rfl⟩ := exposure.bind
    let targets := positions l e x
    have h₀ := seedSafe.mono (Set.empty_subset targets)
    have h₁ := findSafe.mono (Set.empty_subset targets)
    have hm := marked.within targets (beforeValues_within pp l e x targets)
    have hr := read.within targets (revealValues_within pp l e x)
    refine ⟨x, ⟨base, s₁, s₂, find.raw, marked.grows.trans read.grows⟩, ?_⟩
    simpa only [List.append_nil] using h₀.append (h₁.append (hm.append hr))

/-- On failure the layer returns no chain reads; on success its actual randomizer selected them. -/
def LayerRelease (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (ans : Except XmssError LayerSignature) (log : SharedSpec.QueryLog)
    (last : SharedState) : Prop :=
  match ans with
  | .error _ => LogWithin ∅ log
  | .ok sig => ∃ x, Trial pp l (UInt32.ofNat e) msg sig.randomizer x last ∧
      LogWithin (positions l (UInt32.ofNat e) x) log

theorem layer_logged (pp : PublicParam) (l : Layer) (cb : SeedPrf (OracleComp SharedSpec))
    (residual : ResidualReads pp cb) (e : Nat) (msg : ByteArray) {s ans log t}
    (ran : Logged pp (layerSchedule pp cb l e msg) s ans log t) :
    LayerRelease pp l e msg ans log t.1 := by
  unfold layerSchedule at ran
  obtain ⟨decision, otsLog, middle, suffix, ots, tail, rfl⟩ := ran.bind
  have checked := ots_logged pp l cb residual (UInt32.ofNat e) msg ots
  cases decision with
  | none =>
    obtain ⟨rfl, rfl, _⟩ := tail.pure_result
    simpa only [LayerRelease, OtsRelease, List.append_nil] using checked
  | some pair =>
    obtain ⟨rho, ys⟩ := pair
    obtain ⟨x, found, allowed⟩ := checked
    obtain ⟨path, pathLog, _, pureLog, route, pureRun, rfl⟩ := tail.bind
    obtain ⟨rfl, rfl, rfl⟩ := pureRun.pure_result
    refine ⟨x, found.mono route.grows, ?_⟩
    simpa only [List.append_nil] using allowed.append (route.within _ (path_within pp l e _))

/-- A root read directly identifies the low row shared by all signatures from its bottom tree. -/
theorem logged_root_value (pp : PublicParam) (l : Layer) (h j : Nat) {s root log t}
    (ran : Logged pp (simulateQ (selection pp l).liftQuery
      (beforeNode pp l h j >>= fun _ => LayerGraph.readOutput (LayerGraph.treeRole h j)))
      s root log t) :
    t.1.2 (.inr (.inl (l, LayerGraph.treeRole h j))) = some (ChainGraph.digestEquiv root) := by
  rw [simulateQ_bind] at ran
  obtain ⟨_, _, _, _, _, result, _⟩ := ran.bind
  simp only [LayerGraph.readOutput, simulateQ_bind, simulateQ_pure] at result
  obtain ⟨word, _, mid, _, low, rest, _⟩ := result.bind
  obtain ⟨_, _, _, _, high, pureRun, _⟩ := rest.bind
  obtain ⟨rfl, _, rfl⟩ := pureRun.pure_result
  have lookup : mid.1.2 (.inr (.inl (l, LayerGraph.treeRole h j))) = some word :=
    (graph pp).cell_eq_of_mem_support_simulateQ_deferredImpl_readCell (z := (word, mid)) low.raw
  rw [Equiv.apply_symm_apply]
  exact high.grows.2 lookup

/-- The returned top signature authenticates the exact bottom-root row read before its finder. -/
def TreeRelease (pp : PublicParam) (idx : LeafIndex)
    (ans : Except XmssError (Vector Digest LAYER_HEIGHT × LayerSignature))
    (log : SharedSpec.QueryLog) (last : SharedState) : Prop :=
  match ans with
  | .error _ => LogWithin ∅ log
  | .ok (_, top) => ∃ root x,
      last.2 (.inr (.inl (.bottom, LayerGraph.treeRole LAYER_HEIGHT (bottomTree idx)))) =
        some (ChainGraph.digestEquiv root) ∧
      Trial pp .top (UInt32.ofNat (bottomTree idx)) (packBytes root) top.randomizer x last ∧
      LogWithin (positions .top (UInt32.ofNat (bottomTree idx)) x) log

attribute [local irreducible] beforeNode LayerGraph.readOutput revealPath layerSchedule

theorem tree_logged (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (residual : ResidualReads pp cb) (idx : LeafIndex) {s ans log t}
    (ran : Logged pp (releasedTree pp cb idx) s ans log t) : TreeRelease pp idx ans log t.1 := by
  unfold releasedTree at ran
  obtain ⟨root, treeLog, middle, rest, tree, finish, rfl⟩ := ran.bind
  have rootSeen := logged_root_value pp .bottom LAYER_HEIGHT (bottomTree idx) tree
  obtain ⟨decision, topLog, mid, suffix, checked, tail, rfl⟩ := finish.bind
  have top := layer_logged pp .top cb residual (bottomTree idx) (packBytes root) checked
  cases decision with
  | error err =>
    obtain ⟨rfl, rfl, _⟩ := tail.pure_result
    have cold := tree.within ∅ (root_within pp .bottom LAYER_HEIGHT (bottomTree idx) ∅)
    simpa only [TreeRelease, List.append_nil] using cold.append top
  | ok sig =>
    obtain ⟨x, found, allowed⟩ := top
    obtain ⟨path, pathLog, _, pureLog, route, pureRun, rfl⟩ := tail.bind
    obtain ⟨rfl, rfl, rfl⟩ := pureRun.pure_result
    let targets := positions .top (UInt32.ofNat (bottomTree idx)) x
    have h₀ := tree.within targets (root_within pp .bottom LAYER_HEIGHT (bottomTree idx) targets)
    have hr := route.within targets (revealPath_within pp .bottom LAYER_HEIGHT idx.toNat targets)
    refine ⟨root, x, (checked.grows.trans route.grows).2 rootSeen, found.mono route.grows, ?_⟩
    simpa only [List.append_nil] using h₀.append (allowed.append hr)

/-- A signing error releases no chain cells.

A successful reply identifies its two actual finder results and the shared bottom root. -/
def SignatureRelease (pp : PublicParam) (idx : LeafIndex) (msg : Message)
    (ans : Except XmssError Signature) (log : SharedSpec.QueryLog) (last : SharedState) : Prop :=
  match ans with
  | .error _ => LogWithin ∅ log
  | .ok sig => sig.leafIndex = idx ∧ ∃ (root : Digest) (x y : Vector (Fin CHAIN_LENGTH) V),
      last.2 (.inr (.inl (.bottom, LayerGraph.treeRole LAYER_HEIGHT (bottomTree idx)))) =
        some (ChainGraph.digestEquiv root) ∧
      Trial pp .bottom (UInt32.ofNat idx.toNat) (packBytes msg) sig.bottom.randomizer x last ∧
      Trial pp .top (UInt32.ofNat (bottomTree idx)) (packBytes root) sig.top.randomizer y last ∧
      LogWithin (positions .bottom (UInt32.ofNat idx.toNat) x ∪
        positions .top (UInt32.ofNat (bottomTree idx)) y) log

/-- The actual graph logger records direct chain reads only at the two returned codewords.

The private randomizer callback is required to keep its seed operations off direct chain rows. -/
theorem releasedSchedule_logged (pp : PublicParam) (cb : SeedPrf (OracleComp SharedSpec))
    (residual : ResidualReads pp cb) (idx : LeafIndex) (msg : Message) {s ans log t}
    (ran : Logged pp (releasedSchedule pp cb idx msg) s ans log t) :
    SignatureRelease pp idx msg ans log t.1 := by
  let e := UInt32.ofNat idx.toNat
  let bytes := packBytes msg
  unfold releasedSchedule at ran
  obtain ⟨base, seedLog, s₁, rest, seed, grinding, rfl⟩ := ran.bind
  have seedSafe := seed.within ∅ (randomizer_within pp cb residual .bottom e bytes)
  obtain ⟨result, trials, s₂, suffix, find, signer, rfl⟩ := grinding.bind
  have findSafe := find.within ∅
    (finder_within pp .bottom e bytes base ∅ 0 MAX_RANDOMIZER_TRIALS)
  cases result with
  | none =>
    obtain ⟨rfl, rfl, _⟩ := signer.pure_result
    simpa only [SignatureRelease, List.append_nil] using seedSafe.append findSafe
  | some code =>
    obtain ⟨rho, x⟩ := code
    obtain ⟨_, markLog, s₃, rest, mark, top, rfl⟩ := signer.bind
    obtain ⟨decision, topLog, s₄, afterTop, finish, tail, rfl⟩ := top.bind
    have checked := tree_logged pp cb residual idx finish
    cases decision with
    | error err =>
      obtain ⟨rfl, rfl, _⟩ := tail.pure_result
      have markSafe := mark.within ∅ (beforeValues_within pp .bottom e x ∅)
      simpa only [SignatureRelease, List.append_nil] using
        seedSafe.append (findSafe.append (markSafe.append checked))
    | ok sig =>
      obtain ⟨path, upper⟩ := sig
      obtain ⟨root, y, stored, upperTrial, served⟩ := checked
      obtain ⟨ys, readLog, _, pureLog, read, doneRun, rfl⟩ := tail.bind
      obtain ⟨rfl, rfl, rfl⟩ := doneRun.pure_result
      let bottom := positions .bottom e x
      let topCells := positions .top (UInt32.ofNat (bottomTree idx)) y
      let targets := bottom ∪ topCells
      have pre := seedSafe.mono (Set.empty_subset targets)
      have tries := findSafe.mono (Set.empty_subset targets)
      have marks := mark.within targets (beforeValues_within pp .bottom e x targets)
      have topReads := served.mono (Set.subset_union_right (s := bottom) (t := topCells))
      have reads := read.within bottom (revealValues_within pp .bottom e x)
      have lowReads := reads.mono (Set.subset_union_left (s := bottom) (t := topCells))
      refine ⟨rfl, root, x, y, read.grows.2 stored, ?_, upperTrial.mono read.grows, ?_⟩
      · exact ⟨base, s₁, s₂, find.raw, mark.grows.trans (finish.grows.trans read.grows)⟩
      · simpa only [List.append_nil] using
          pre.append (tries.append (marks.append (topReads.append lowReads)))

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
