module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.FixedParam
public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead
public import VCVio.OracleComp.SimSemantics.StateT.EqDistTriple.Simulate

/-!
# Proofs: honest and lab steps in the eager game

The eager game adds two label operations to the relabelled game of the graph of `P`.

A touch draws a cell and discards it, and a read draws a cell and returns it.

A lab program reads each node's label where the scheme hashes the node's children.

It touches the values it never reveals, so a later game can defer their draws.

This file relates honest steps to lab steps.

Two related programs, run from one state, give one law of the output and the final state.

- A tweakable hash at a node whose children are held in their cells draws the node's label.
- A chain walk draws each step, and the lab chain to a position reads only that position.
- A key's leaf, with its chain ends held in their cells, is one draw of the leaf's label.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open OracleSpec OracleComp

/-- A node's address is not one of the message digest's. -/
theorem Node.notDigestAddress (k : Node) : NotDigestAddress k.address := by
  obtain ⟨step, layer, tree, hi, lo, hk⟩ := k.exists_address_eq
  rw [hk]
  exact Unforgeability.notDigestAddress (by cases k <;> simp only [Node.type] <;> decide)
    step layer tree hi lo

/-- In the game that skips the thrown-away halves, a tweakable hash's input asks half 0 only. -/
theorem skipHalves_inl_of_isThBytes {a : List UInt8} (h : IsThBytes a) :
    skipHalves (.inl (.inr a)) = (do
      let u ← HalvedWorld.query (.inl (.inr (a, 0)))
      return hashHalves.symm (u, default)) := by
  simp [QueryImpl.apply_compose, ghostHalves, skipGhost, h]

/-- So a tweakable hash asks half 0 of its input, and returns it. -/
theorem simulateQ_skipHalves_th (pp : PublicParam) {A : Address} (hA : NotDigestAddress A)
    (payload : ByteArray) :
    simulateQ skipHalves (th (liftH DerivationInput) pp A payload) =
      HalvedWorld.query (.inl (.inr ((thInput pp A payload).data.toList, 0))) := by
  change simulateQ _ (liftH DerivationInput (thInput pp A payload) >>= fun x =>
    pure (halfOf 0 x)) = _
  simp only [simulateQ_bind, liftH_eq, simulateQ_map, simulateQ_spec_query,
    skipHalves_inl_of_isThBytes (isThBytes_thInput pp hA payload), map_bind, map_pure,
    bind_assoc, pure_bind, simulateQ_pure]
  refine (bind_congr fun x => ?_).trans (bind_pure _)
  exact congrArg pure (halfOf_zero_hashHalves_symm x default)

/-- The same, for the hash of that game. -/
theorem th_skipH (pp : PublicParam) {A : Address} (hA : NotDigestAddress A)
    (payload : ByteArray) :
    th skipH pp A payload =
      HalvedWorld.query (.inl (.inr ((thInput pp A payload).data.toList, 0))) := by
  rw [← simulateQ_skipHalves_th pp hA payload, th_map_monad (simulateQ skipHalves)
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f)]
  rfl

/-! ## The lab world -/

/-- Programs with the public points and derivations asked half by half, and the label operations
on the cells of the graph. -/
abbrev LabWorld :=
  (List UInt8 × Fin 2 →ₒ Digest).withLabels (DerivationInput × Fin 2) Node Digest

/-- The state of the eager game: the public cache, and the cells drawn. -/
abbrev LabState :=
  RelabelState (List UInt8 × Fin 2 →ₒ Digest) (DerivationInput × Fin 2) Node Digest

/-- The hash of the game that skips the thrown-away halves, in the lab world. -/
noncomputable def labH (x : ByteArray) : OracleComp LabWorld (Vector UInt8 32) :=
  liftComp (skipH x) LabWorld

/-- In the lab world, a tweakable hash at a node's address asks half 0 of its input. -/
theorem th_labH (pp : PublicParam) {A : Address} (hA : NotDigestAddress A)
    (payload : ByteArray) :
    th labH pp A payload =
      LabWorld.query (.inl (.inl (.inr ((thInput pp A payload).data.toList, 0)))) := by
  change th (fun x => liftComp (skipH x) LabWorld) pp A payload = _
  rw [← th_map_monad (fun oa => liftComp oa LabWorld) (fun b => liftComp_pure _ b)
    (fun x f => liftComp_bind _ x f), th_skipH pp hA payload]
  simp
  rfl

/-- Two programs of the lab world related in the eager game of the graph of `P`.

Their runs from a state meeting `pre` have one law of the output and the final state.

Each outcome of the second program meets `post`, and no run shrinks the state. -/
abbrev LabTriple (P : PublicParam) {α : Type} (pre : LabState → Prop)
    (oa ob : OracleComp LabWorld α) (post : α → LabState → Prop) : Prop :=
  (graph P).eagerImpl.EqDistTriple (· ≤ ·) pre oa ob post

/-- The lab read of a node: its label. -/
noncomputable def readNode (k : Node) : OracleComp LabWorld Digest :=
  readCell (some (.inr k))

/-- **The node step.**

From a state whose cells of the children of `k` hold `vs`, the honest tweakable hash at `k`'s
point and the lab read of `k` are one draw of `k`'s label.

The cell of `k` then holds the result. -/
theorem th_labTriple (P : PublicParam) (k : Node) (vs : List Digest) :
    LabTriple P (fun st => List.Forall₂ (fun c v => st.2 c = some v) (k.children P) vs)
      (th labH P k.address (digestsBytes vs ++ k.suffix)) (readNode k)
      fun y st => st.2 (.inr k) = some y := by
  intro st hst
  have hch : (graph P).childVals st k = some vs := (graph P).childVals_eq_some_iff.2 hst
  have hlab : (simulateQ (graph P).eagerImpl (readNode k)).run st =
      (RelabelState.drawCell (.inr k)).run st :=
    (graph P).eagerImpl_readCell_run _ st
  have hhon : (simulateQ (graph P).eagerImpl
      (th labH P k.address (digestsBytes vs ++ k.suffix))).run st =
        (RelabelState.drawCell (.inr k)).run st := by
    rw [th_labH P k.notDigestAddress]
    simp only [simulateQ_spec_query]
    refine ((graph P).relabelImpl_run_pt hch).trans ?_
    exact id_map _
  refine ⟨fun {_} => by rw [hhon, hlab], fun z hz => ?_⟩
  rw [hlab] at hz
  exact RelabelState.le_and_cell_eq_of_mem_support_drawCell hz

/-! ## Chains -/

/-- The cell, if any, holds `y`. -/
def Holds (st : LabState) (c : Option Cell) (y : Digest) : Prop :=
  ∃ c', c = some c' ∧ st.2 c' = some y

/-- A held cell stays held as the state grows. -/
theorem Holds.mono {st st' : LabState} (hle : st ≤ st') {c : Option Cell} {y : Digest}
    (h : Holds st c y) : Holds st' c y :=
  h.imp fun _ h' => ⟨h'.1, hle.2 h'.2⟩

/-- The cells of chain `i` of a key: cell 0 holds its start, cell `mu + 1` the value after step
`mu`, and there is no cell past the end. -/
def chainCell (P : PublicParam) (key : GraphKey) (i : Fin V) : Nat → Option Cell
  | 0 => some (.inl (startCell P key i))
  | n + 1 => if h : n < CHAIN_LENGTH - 1 then some (.inr (.chain key i ⟨n, h⟩)) else none

/-- Chain cell `n + 1` is step `n`'s node. -/
theorem chainCell_succ (P : PublicParam) (key : GraphKey) (i : Fin V) {n : Nat}
    (h : n < CHAIN_LENGTH - 1) : chainCell P key i (n + 1) = some (.inr (.chain key i ⟨n, h⟩)) :=
  dite_eq_left_of_eq_true (eq_true h)

/-- **A chain step.**

From a state in which chain cell `mu` holds `x`, the honest step `mu` and the lab read of its
node are one draw, which chain cell `mu + 1` then holds. -/
theorem chainStep_labTriple (P : PublicParam) (key : GraphKey) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (x : Digest) :
    LabTriple P (fun st => Holds st (chainCell P key i mu) x)
      (chainStep labH P key.toOtsKey i mu x) (readNode (.chain key i mu))
      fun y st => Holds st (chainCell P key i (mu + 1)) y := by
  have e : chainStep labH P key.toOtsKey i mu x =
      th labH P (Node.chain key i mu).address
        (digestsBytes [x] ++ (Node.chain key i mu).suffix) := by
    simp only [chainStep, Node.address, Node.suffix, digestsBytes_singleton,
      ByteArray.append_empty]
  rw [e]
  refine (th_labTriple P _ [x]).mono (fun st ⟨c, hc, hx⟩ => ?_)
    fun y st h => ⟨_, chainCell_succ P key i mu.isLt, h⟩
  obtain ⟨_ | n, hn⟩ := mu
  · simp only [chainCell, Option.some.injEq] at hc
    subst hc
    simpa [Node.children] using hx
  · rw [chainCell_succ P key i (by omega), Option.some.injEq] at hc
    subst hc
    simpa [Node.children] using hx

/-- **Chain walks.**

From a state in which chain cell `start` holds `x`, the honest walk of `s` steps and the walk
that reads each step's node are related.

Chain cell `start + s` then holds the result. -/
theorem chain_labTriple (P : PublicParam) (key : GraphKey) (i : Fin V) (x : Digest)
    (start : Nat) : ∀ s (h : start + s ≤ CHAIN_LENGTH - 1),
      LabTriple P (fun st => Holds st (chainCell P key i start) x)
        (Wots.chain (chainStep labH P key.toOtsKey i) start s h x)
        (Wots.chain (fun mu _ => readNode (.chain key i mu)) start s h x)
        fun y st => Holds st (chainCell P key i (start + s)) y
  | 0, _ => QueryImpl.EqDistTriple.pure x fun _ h => h
  | s + 1, h => by
    rw [Wots.chain_succ, Wots.chain_succ]
    exact (chain_labTriple P key i x start s (by omega)).bind fun y =>
      chainStep_labTriple P key i ⟨start + s, by omega⟩ y

/-- The lab chain to position `s`: touch the start and the steps below `s`, then read cell `s`.

Only the value at position `s` is read, so the lower values can stay hidden. -/
noncomputable def labChain (P : PublicParam) (key : GraphKey) (i : Fin V) (s : Nat) :
    OracleComp LabWorld Digest :=
  touchRead (chainCell P key i) s

/-- In the eager game, the lab chain reads the start, then reads each step's node. -/
theorem simulateQ_eagerImpl_labChain (P : PublicParam) (key : GraphKey) (i : Fin V) :
    ∀ s (h : s ≤ CHAIN_LENGTH - 1), simulateQ (graph P).eagerImpl (labChain P key i s) =
      simulateQ (graph P).eagerImpl (do
        let x ← readCell (chainCell P key i 0)
        Wots.chain (fun mu _ => readNode (.chain key i mu)) 0 s (by omega) x)
  | 0, _ => by
    simp only [labChain, touchRead, touchUpTo, pure_bind, Wots.chain_zero, bind_pure]
  | s + 1, h => by
    rw [labChain, (graph P).simulateQ_eagerImpl_touchRead_succ, ← labChain,
      simulateQ_eagerImpl_labChain P key i s (by omega)]
    simp only [Wots.chain_succ, simulateQ_bind, bind_assoc, Nat.zero_add]
    rw [chainCell_succ P key i (by omega)]
    rfl

/-- A read of a cell that holds `x` returns `x` and changes nothing. -/
theorem readCell_labTriple (P : PublicParam) (c : Option Cell) (x : Digest) :
    LabTriple P (fun st => Holds st c x) (pure x) (readCell c)
      fun y st => y = x ∧ Holds st c x := by
  rintro st ⟨c', rfl, hx⟩
  have hrun : (simulateQ (graph P).eagerImpl (readCell (some c'))).run st = pure (x, st) := by
    rw [(graph P).eagerImpl_readCell_run, RelabelState.drawCell_run_of_cell_eq_some hx]
  refine ⟨fun {_} => by rw [hrun, simulateQ_pure, StateT.run_pure], fun z hz => ?_⟩
  rw [hrun, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨le_rfl, rfl, c', rfl, hx⟩

/-- **A chain from its start.**

From a state in which chain cell 0 holds `x`, the honest walk of `s` steps from `x` and the lab
chain to position `s` are related.

Chain cell `s` then holds the result. -/
theorem labChain_labTriple (P : PublicParam) (key : GraphKey) (i : Fin V) (x : Digest) {s : Nat}
    (h : s ≤ CHAIN_LENGTH - 1) :
    LabTriple P (fun st => Holds st (chainCell P key i 0) x)
      (Wots.chain (chainStep labH P key.toOtsKey i) 0 s (by omega) x) (labChain P key i s)
      fun y st => Holds st (chainCell P key i s) y := by
  refine QueryImpl.EqDistTriple.of_simulateQ_eq_right ?_
    (simulateQ_eagerImpl_labChain P key i s h).symm
  rw [← pure_bind x fun x => Wots.chain (chainStep labH P key.toOtsKey i) 0 s (by omega) x]
  refine (readCell_labTriple P _ x).bind fun y => ?_
  refine (chain_labTriple P key i y 0 s (by omega)).mono (fun st h => ?_) fun _ _ h => ?_
  · obtain ⟨rfl, h⟩ := h
    exact h
  · rwa [Nat.zero_add] at h

/-! ## One-time leaves -/

/-- **A key's leaf.**

From a state in which the last cell of each chain of `key` holds its end, the honest hash of the
ends and the lab read of the key's leaf are one draw.

The leaf's cell then holds the result. -/
theorem otsLeafHash_labTriple (P : PublicParam) (key : GraphKey) (ends : Vector Digest V) :
    LabTriple P (fun st => ∀ i, Holds st (chainCell P key i (CHAIN_LENGTH - 1)) ends[i])
      (otsLeafHash labH P key.toOtsKey ends) (readNode (.otsLeaf key))
      fun y st => st.2 (.inr (.otsLeaf key)) = some y := by
  have e : otsLeafHash labH P key.toOtsKey ends =
      th labH P (Node.otsLeaf key).address
        (digestsBytes ends.toList ++ (Node.otsLeaf key).suffix) := by
    simp only [otsLeafHash, Node.address, Node.suffix, digestsBytes_toList,
      ByteArray.append_empty]
  rw [e]
  refine (th_labTriple P _ ends.toList).mono (fun st h => ?_) fun _ _ h => h
  simp only [Node.children]
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun n h₁ h₂ => ?_⟩
  obtain ⟨c, hc, hx⟩ := h ⟨n, by simpa using h₂⟩
  rw [show CHAIN_LENGTH - 1 = CHAIN_LENGTH - 2 + 1 by decide,
    chainCell_succ P key _ (by decide), Option.some.injEq] at hc
  subst hc
  simp only [List.get_eq_getElem, Vector.getElem_toList]
  rw [List.getElem_ofFn]
  exact hx

end EthLib.Cryptography.Sphincs.Unforgeability
