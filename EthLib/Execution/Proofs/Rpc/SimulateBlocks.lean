module

public import EthLib.Execution.Rpc.Simulate.Blocks
public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Blocks.Codes
public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Rpc.Simulate
public import EthLib.Execution.Proofs.Transactions.Overrides
public import EthLib.Execution.Proofs.Transactions.Process
public import EthLib.Execution.Proofs.Transactions.Unsigned

/-!
# Proofs: the blocks of `eth_simulateV1`

A simulated block follows the last block of its chain, and has the number that it is given.

Its parent hash is the hash of the header of that block, and its hash is the hash of its own header.

The blocks of a simulation, gap blocks included, have consecutive numbers after the base block.

When the view holds the hash of each header, the first has the hash of the base block as parent.

Each other has the hash of the block before it.

Without validation, a block whose base fee is not overridden has a base fee of 0.

That holds whatever the base fee of the block before it.

With validation and no overrides, a simulated block agrees with the state transition.

Its calls must then be signed and the block must pass its checks.

Its transition may still fail at a sender with code.
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions

/-- A simulated block unfolded into its parent, its header, its hash and the chain after it. -/
private theorem simulateBlock_spec {chain chain' : BlockChain} {base : RecentBlock} {fork : Fork}
    {number time budget budget' : Nat} {request : BlockStateCall} {validation : Bool}
    {b : SimulatedBlock}
    (h : simulateBlock chain base fork number time request validation budget =
      .ok (chain', budget', b)) :
    ∃ parent parentHash, chain.recent.getLast? = some parent ∧
      parent.header.hash = .ok parentHash ∧
      ∃ (result : BodyResult fork) (txs : List Transaction)
        (ws : Since .shapella fork (List Withdrawal)) (hash : Hash32)
        (c : BlockChain) (senders : List Address),
        (fillHeader (simulatedHeader chain.config fork base parent parentHash number time
          request.blockOverrides validation) result.output result.roots).hash = .ok hash ∧
        b = ⟨{ fork := fork
               block := ⟨fillHeader (simulatedHeader chain.config fork base parent parentHash
                 number time request.blockOverrides validation) result.output result.roots,
                 txs, [], ws⟩
               hash := hash
               state := result.post
               receipts := result.output.receipts
               logs := result.output.logs }, senders⟩ ∧
        chain' = c.addBlock (⟨fillHeader (simulatedHeader chain.config fork base parent parentHash
          number time request.blockOverrides validation) result.output result.roots, txs, [], ws⟩ :
          Block fork Transaction) result.post := by
  simp only [simulateBlock] at h
  split at h
  · rename_i parent hP
    simp only [bind_ok_iff, mapError_ok_iff] at h
    obtain ⟨ph, hph, -, -, -, -, -, -, calls, -, res, -, hash, hh, hEq⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hEq
    obtain ⟨rfl, -, rfl⟩ := hEq
    exact ⟨parent, ph, hP, hph, res, _, _, hash, _, _, hh, rfl, rfl⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A simulated block follows the last block of its chain, at the number that it is given.

Its parent hash is the hash of the header of that block.

Its hash is the hash of its own header, and the chain after it ends with it. -/
theorem simulateBlock_links {chain chain' : BlockChain} {base : RecentBlock} {fork : Fork}
    {number time budget budget' : Nat} {request : BlockStateCall} {validation : Bool}
    {b : SimulatedBlock}
    (h : simulateBlock chain base fork number time request validation budget =
      .ok (chain', budget', b)) :
    (∃ parent, chain.recent.getLast? = some parent ∧
      parent.header.hash = .ok b.record.block.header.parentHash) ∧
    b.record.block.header.number = number ∧
    b.record.block.header.hash = .ok b.record.hash ∧
    chain'.recent.getLast? = some b.record.recent := by
  obtain ⟨parent, ph, hP, hph, res, txs, ws, hash, c, senders, hh, rfl, rfl⟩ :=
    simulateBlock_spec h
  refine ⟨⟨parent, hP, hph⟩, rfl, hh, ?_⟩
  simp [BlockChain.addBlock, List.getLast?_drop, BlockRecord.recent]
  omega

/-- Without validation, a simulated block whose base fee is not overridden has a base fee of 0. -/
theorem simulateBlock_baseFee {chain chain' : BlockChain} {base : RecentBlock} {fork : Fork}
    {number time budget budget' : Nat} {request : BlockStateCall} {b : SimulatedBlock}
    (h : simulateBlock chain base fork number time request false budget =
      .ok (chain', budget', b))
    (hNone : request.blockOverrides.baseFeePerGas = none) (hLondon : .london ≤ b.record.fork) :
    b.record.block.header.baseFeePerGas hLondon = 0 := by
  obtain ⟨parent, ph, hP, hph, res, txs, ws, hash, c, senders, hh, rfl, rfl⟩ :=
    simulateBlock_spec h
  simp [fillHeader, simulatedHeader, hNone]

/-- Without validation, BASEFEE reads 0 in a simulated block whose base fee is not overridden.

Its body runs in the environment of its header, whose base fee BASEFEE reads. -/
theorem simulateBlock_environment_baseFee {chain chain' : BlockChain} {base : RecentBlock}
    {fork : Fork} {number time budget budget' : Nat} {request : BlockStateCall}
    {b : SimulatedBlock}
    (h : simulateBlock chain base fork number time request false budget =
      .ok (chain', budget', b))
    (hNone : request.blockOverrides.baseFeePerGas = none) (hLondon : .london ≤ b.record.fork)
    (config : ChainConfig) (hashes : List Hash32) (blobGasPrice : Option Nat) :
    (blockEnvironment config hashes b.record.block.header blobGasPrice).baseFeePerGas hLondon =
      0 :=
  simulateBlock_baseFee h hNone hLondon

/-- A plan holds the planned blocks of the request after its base block.

They pass the order check. -/
private theorem planSimulate_spec {v : ChainView} {payload : SimulatePayload} {p : BlockParam}
    {choices : SimulateChoices} {plan : SimulatePlan}
    (h : v.planSimulate payload p choices = .ok plan) :
    plan.blocks.map Prod.fst = planBlocks choices.blockTime plan.base.block.header.number
      plan.base.block.header.timestamp.toNat payload.blockStateCalls ∧
    checkOrder choices.blockTime plan.base.block.header.number
      plan.base.block.header.timestamp.toNat (planBlocks choices.blockTime
        plan.base.block.header.number plan.base.block.header.timestamp.toNat
        payload.blockStateCalls) = .ok () := by
  simp only [ChainView.planSimulate] at h
  obtain ⟨r, -, h⟩ := bind_ok_iff.mp h
  split at h
  · rename_i base
    obtain ⟨-, h⟩ := bind_unit_ok_iff.mp h
    obtain ⟨hOrder, h⟩ := bind_unit_ok_iff.mp h
    obtain ⟨blocks, hBlocks, h⟩ := bind_ok_iff.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨map_of_mapM_ok (fun x y hxy => ?_) hBlocks |>.trans (List.map_id' _), hOrder⟩
    split at hxy
    · obtain ⟨-, hxy⟩ := bind_unit_ok_iff.mp hxy
      obtain ⟨-, hxy⟩ := bind_unit_ok_iff.mp hxy
      simp only [pure, Except.pure, Except.ok.injEq] at hxy
      subst hxy
      rfl
    · simp [throw, throwThe, MonadExceptOf.throw] at hxy
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A property that each gap block keeps holds after the gap blocks.

The number grows by the gap. -/
private theorem gaps_invariant {config : ChainConfig} {base : RecentBlock} {validation : Bool}
    (Q : SimulateStep → Prop)
    (gapStep : ∀ (t : SimulateStep) fork n time chain budget blk, Q t → n = t.number + 1 →
      simulateBlock t.chain base fork n time {} validation t.budget = .ok (chain, budget, blk) →
      Q ⟨chain, budget, n, time, t.blocks ++ [blk]⟩)
    (N : Nat) (T : Nat → Nat) :
    ∀ (g : Nat) (s s' : SimulateStep), Q s → s.number = N →
      ((List.range g).map fun k => (N + 1 + k, T k)).foldlM (init := s)
        (fun (s : SimulateStep) (number, time) => do
          let some fork := config.activeFork number time
            | throw (callInternalError "no fork for the block")
          let (chain, budget, block) ←
            simulateBlock s.chain base fork number time {} validation s.budget
          return ({ chain, budget, number, time, blocks := s.blocks ++ [block] } :
            SimulateStep)) = .ok s' →
      Q s' ∧ s'.number = N + g := by
  intro g
  induction g with
  | zero =>
    intro s s' hs hN h
    simp only [List.range_zero, List.map_nil, List.foldlM_nil, pure, Except.pure,
      Except.ok.injEq] at h
    subst h
    exact ⟨hs, hN⟩
  | succ g ih =>
    intro s s' hs hN h
    rw [List.range_succ, List.map_append, List.foldlM_append] at h
    obtain ⟨mid, hMid, h⟩ := bind_ok_iff.mp h
    obtain ⟨hQ, hNum⟩ := ih s mid hs hN hMid
    simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind_pure] at h
    split at h
    · obtain ⟨x, hBlk, h⟩ := bind_ok_iff.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨gapStep mid _ _ _ x.1 x.2.1 x.2.2 hQ (by omega) hBlk, by simp only; omega⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A property that each gap block and the planned block keep holds after the next step. -/
private theorem next_invariant {config : ChainConfig} {base : RecentBlock} {validation : Bool}
    {blockTime : Nat} (Q : SimulateStep → Prop) {s s' : SimulateStep} {b : PlannedBlock}
    {fork : Fork}
    (gapStep : ∀ (t : SimulateStep) fork n time chain budget blk, Q t → n = t.number + 1 →
      simulateBlock t.chain base fork n time {} validation t.budget = .ok (chain, budget, blk) →
      Q ⟨chain, budget, n, time, t.blocks ++ [blk]⟩)
    (plannedStep : ∀ (t : SimulateStep) chain budget blk, Q t → t.number = s.number + b.gap →
      simulateBlock t.chain base fork b.number b.time b.request validation t.budget =
        .ok (chain, budget, blk) →
      Q ⟨chain, budget, b.number, b.time, t.blocks ++ [blk]⟩)
    (hs : Q s) (h : SimulateStep.next config base validation blockTime s (b, fork) = .ok s') :
    Q s' := by
  simp only [SimulateStep.next] at h
  obtain ⟨t, hGaps, h⟩ := bind_ok_iff.mp h
  obtain ⟨hQ, hNum⟩ := gaps_invariant Q gapStep s.number _ b.gap s t hs rfl hGaps
  obtain ⟨x, hBlk, h⟩ := bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact plannedStep t x.1 x.2.1 x.2.2 hQ hNum hBlk

/-- After the next step, the last block has the number of the planned block. -/
private theorem next_number {config : ChainConfig} {base : RecentBlock} {validation : Bool}
    {blockTime : Nat} {s s' : SimulateStep} {b : PlannedBlock} {fork : Fork}
    (h : SimulateStep.next config base validation blockTime s (b, fork) = .ok s') :
    s'.number = b.number := by
  simp only [SimulateStep.next] at h
  obtain ⟨t, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨x, -, h⟩ := bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rfl

/-- The links of the blocks so far after a base block, kept when one more block is simulated. -/
private theorem links_snoc {N0 : Nat} {H0 : Hash32} {t : SimulateStep} {base : RecentBlock}
    {fork : Fork} {n time : Nat} {request : BlockStateCall} {validation : Bool}
    {chain : BlockChain} {budget : Nat} {blk : SimulatedBlock}
    (hQ : t.number = N0 + t.blocks.length ∧
      (∀ i (hi : i < t.blocks.length), t.blocks[i].record.block.header.number = N0 + i + 1) ∧
      (∀ b ∈ t.blocks.head?, b.record.block.header.parentHash = H0) ∧
      (∀ i (hi : i + 1 < t.blocks.length),
        t.blocks[i + 1].record.block.header.parentHash = t.blocks[i].record.hash) ∧
      (∀ b ∈ t.blocks, b.record.block.header.hash = .ok b.record.hash) ∧
      (∃ r, t.chain.recent.getLast? = some r ∧
        r.header.hash = .ok ((t.blocks.getLast?.map (·.record.hash)).getD H0)))
    (hn : n = t.number + 1)
    (hBlk : simulateBlock t.chain base fork n time request validation t.budget =
      .ok (chain, budget, blk)) :
    let u : SimulateStep := ⟨chain, budget, n, time, t.blocks ++ [blk]⟩
    u.number = N0 + u.blocks.length ∧
      (∀ i (hi : i < u.blocks.length), u.blocks[i].record.block.header.number = N0 + i + 1) ∧
      (∀ b ∈ u.blocks.head?, b.record.block.header.parentHash = H0) ∧
      (∀ i (hi : i + 1 < u.blocks.length),
        u.blocks[i + 1].record.block.header.parentHash = u.blocks[i].record.hash) ∧
      (∀ b ∈ u.blocks, b.record.block.header.hash = .ok b.record.hash) ∧
      (∃ r, u.chain.recent.getLast? = some r ∧
        r.header.hash = .ok ((u.blocks.getLast?.map (·.record.hash)).getD H0)) := by
  obtain ⟨hNum, hNums, hHead, hLinks, hHashes, r, hr, hrHash⟩ := hQ
  obtain ⟨⟨parent, hParent, hParentHash⟩, hBlkNum, hBlkHash, hLast⟩ := simulateBlock_links hBlk
  rw [hr, Option.some.injEq] at hParent
  subst hParent
  rw [hrHash, Except.ok.injEq] at hParentHash
  intro u
  refine ⟨by simp [u]; omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [u, List.length_append, List.length_singleton] at hi ⊢
    by_cases hlt : i < t.blocks.length
    · rw [List.getElem_append_left hlt]
      exact hNums i hlt
    · obtain rfl : i = t.blocks.length := by omega
      rw [List.getElem_concat_length rfl, hBlkNum]
      omega
  · intro b hb
    simp only [u] at hb
    cases hB : t.blocks with
    | nil =>
      rw [hB] at hb
      simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      simp [hB] at hParentHash
      exact hParentHash.symm
    | cons c cs =>
      rw [hB] at hb hHead
      simp only [List.cons_append, List.head?_cons] at hb hHead
      exact hHead b hb
  · intro i hi
    simp only [u, List.length_append, List.length_singleton] at hi ⊢
    by_cases hlt : i + 1 < t.blocks.length
    · rw [List.getElem_append_left hlt, List.getElem_append_left (by omega)]
      exact hLinks i hlt
    · have hi' : i + 1 = t.blocks.length := by omega
      have hget : t.blocks.getLast? = some t.blocks[i] := by
        rw [List.getLast?_eq_getElem?]
        simp [← hi']
      rw [hget] at hParentHash
      simp only [Option.map_some, Option.getD_some] at hParentHash
      rw [List.getElem_append_left (show i < t.blocks.length by omega)]
      rw [List.getElem_concat_length hi']
      exact hParentHash.symm
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hHashes b hb
    · rw [List.mem_singleton] at hb
      exact hb ▸ hBlkHash
  · refine ⟨blk.record.recent, hLast, ?_⟩
    simp only [u, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some,
      Option.getD_some]
    exact hBlkHash

/-- The simulated blocks, gap blocks included, follow the base block of the plan one by one.

There is one block for each planned block and each gap block before it.

The block at index `i`, from 0, has the number of the base block plus `i + 1`.

The first has the hash of the base block as parent hash, and each other the hash of the one before.

The hash of each block is the hash of its header.

The view must hold the hash of the header of each canonical block, as a valid view does. -/
theorem simulateBlocks_links {v : ChainView}
    (hHash : ∀ r ∈ v.canonical, r.block.header.hash = .ok r.hash) {payload : SimulatePayload}
    {p : BlockParam} {choices : SimulateChoices}
    {plan : SimulatePlan} {blocks : List SimulatedBlock}
    (hPlan : v.planSimulate payload p choices = .ok plan)
    (h : v.simulateBlocks payload p choices = .ok blocks) :
    blocks.length = PlannedBlock.count (plan.blocks.map Prod.fst) ∧
    (∀ i (hi : i < blocks.length),
      blocks[i].record.block.header.number = plan.base.block.header.number + i + 1) ∧
    (∀ b ∈ blocks.head?, b.record.block.header.parentHash = plan.base.hash) ∧
    (∀ i (hi : i + 1 < blocks.length),
      blocks[i + 1].record.block.header.parentHash = blocks[i].record.hash) ∧
    (∀ b ∈ blocks, b.record.block.header.hash = .ok b.record.hash) := by
  simp only [ChainView.simulateBlocks] at h
  obtain ⟨plan', hPlan', h⟩ := bind_ok_iff.mp h
  rw [hPlan, Except.ok.injEq] at hPlan'
  subst hPlan'
  split at h
  · rename_i i hi
    obtain ⟨s, hFold, h⟩ := bind_ok_iff.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    let N0 := plan.base.block.header.number
    let H0 := plan.base.hash
    let Q : SimulateStep → Prop := fun t =>
      t.number = N0 + t.blocks.length ∧
      (∀ i (hi : i < t.blocks.length), t.blocks[i].record.block.header.number = N0 + i + 1) ∧
      (∀ b ∈ t.blocks.head?, b.record.block.header.parentHash = H0) ∧
      (∀ i (hi : i + 1 < t.blocks.length),
        t.blocks[i + 1].record.block.header.parentHash = t.blocks[i].record.hash) ∧
      (∀ b ∈ t.blocks, b.record.block.header.hash = .ok b.record.hash) ∧
      (∃ r, t.chain.recent.getLast? = some r ∧
        r.header.hash = .ok ((t.blocks.getLast?.map (·.record.hash)).getD H0))
    suffices hAll : ∀ (L : List (PlannedBlock × Fork)) (num time : Nat)
        (cs : List BlockStateCall) (t t' : SimulateStep),
        L.map Prod.fst = planBlocks choices.blockTime num time cs →
        checkOrder choices.blockTime num time (planBlocks choices.blockTime num time cs) =
          .ok () →
        Q t → t.number = num →
        L.foldlM (SimulateStep.next v.config plan.base.recent payload.validation
          choices.blockTime) t = .ok t' →
        Q t' ∧ t'.number = num + PlannedBlock.count (L.map Prod.fst) by
      have hBase : v.canonical[i].hash = plan.base.hash := by
        have := (List.findFinIdx?_eq_some_iff.mp hi).1
        simpa using this
      have hStart : Q ⟨v.chainAt i i.2, choices.gasCap, plan.base.block.header.number,
          plan.base.block.header.timestamp.toNat, []⟩ := by
        refine ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ hb => by simp at hb,
          fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ hb => absurd hb List.not_mem_nil,
          v.canonical[i].recent, ?_, ?_⟩
        · show (v.history ++ (v.canonical.take (i + 1)).map BlockRecord.recent).getLast? = _
          rw [List.take_succ_eq_append_getElem i.2, List.map_append, List.map_singleton,
            ← List.append_assoc, List.getLast?_concat]
          rfl
        · show v.canonical[i].block.header.hash = .ok plan.base.hash
          rw [← hBase]
          exact hHash v.canonical[i] (List.getElem_mem _)
      obtain ⟨⟨hLen, hNums, hHead, hLinks, hHashes, -⟩, hCount⟩ := hAll plan.blocks _ _ _ _ s
        (planSimulate_spec hPlan).1 (planSimulate_spec hPlan).2 hStart rfl hFold
      exact ⟨by omega, hNums, hHead, hLinks, hHashes⟩
    intro L
    induction L with
    | nil =>
      intro num time cs t t' _ _ ht hNum hL
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hL
      subst hL
      exact ⟨ht, by simp [PlannedBlock.count, hNum]⟩
    | cons x L ih =>
      intro num time cs t t' hMap hOrder ht hNum hL
      cases cs with
      | nil => simp [planBlocks] at hMap
      | cons c cs =>
        simp only [planBlocks, List.map_cons, List.cons.injEq] at hMap hOrder
        obtain ⟨hx, hMap⟩ := hMap
        rw [checkOrder] at hOrder
        obtain ⟨h1, hOrder⟩ := bind_unit_ok_iff.mp hOrder
        obtain ⟨-, hOrder⟩ := bind_unit_ok_iff.mp hOrder
        rw [ensure_ok_iff] at h1
        rw [List.foldlM_cons] at hL
        obtain ⟨mid, hMid, hRest⟩ := bind_ok_iff.mp hL
        obtain ⟨b, fork⟩ := x
        simp only at hx
        subst hx
        have hQmid : Q mid := next_invariant Q
          (fun u _ _ _ _ _ _ hu hn hBlk => links_snoc hu hn hBlk)
          (fun u _ _ _ hu hu' hBlk => links_snoc hu (by simp only at hu' h1 ⊢; omega) hBlk)
          ht hMid
        obtain ⟨hQ', hNum'⟩ := ih _ _ cs mid t' hMap hOrder hQmid (next_number hMid) hRest
        refine ⟨hQ', ?_⟩
        simp only [PlannedBlock.count, List.map_cons, List.sum_cons] at hNum' ⊢
        simp only at h1
        omega
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- With validation off, every block whose base fee is not overridden has a base fee of 0.

A block at the number of a planned block takes the overrides of its request.

For a gap block, the caller shows that no planned block has its number.

That holds whatever the base fee of the block before it. -/
theorem simulateBlocks_baseFee {v : ChainView} {payload : SimulatePayload} {p : BlockParam}
    {choices : SimulateChoices} {plan : SimulatePlan} {blocks : List SimulatedBlock}
    (hPlan : v.planSimulate payload p choices = .ok plan)
    (h : v.simulateBlocks payload p choices = .ok blocks) (hOff : payload.validation = false) :
    ∀ b ∈ blocks,
      (∀ x ∈ plan.blocks, x.1.number = b.record.block.header.number →
        x.1.request.blockOverrides.baseFeePerGas = none) →
      ∀ hLondon : .london ≤ b.record.fork, b.record.block.header.baseFeePerGas hLondon = 0 := by
  simp only [ChainView.simulateBlocks] at h
  obtain ⟨plan', hPlan', h⟩ := bind_ok_iff.mp h
  rw [hPlan, Except.ok.injEq] at hPlan'
  subst hPlan'
  split at h
  · rename_i i _
    obtain ⟨s, hFold, h⟩ := bind_ok_iff.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    let Q : SimulateStep → Prop := fun s =>
      ∀ b ∈ s.blocks,
        (∀ x ∈ plan.blocks, x.1.number = b.record.block.header.number →
          x.1.request.blockOverrides.baseFeePerGas = none) →
        ∀ hLondon : .london ≤ b.record.fork, b.record.block.header.baseFeePerGas hLondon = 0
    suffices ∀ (L : List (PlannedBlock × Fork)) (t t' : SimulateStep),
        (∀ x ∈ L, x ∈ plan.blocks) → Q t →
        L.foldlM (SimulateStep.next v.config plan.base.recent payload.validation
          choices.blockTime) t = .ok t' → Q t' from
      this plan.blocks _ s (fun _ hx => hx) (fun _ hb => absurd hb List.not_mem_nil) hFold
    intro L
    induction L with
    | nil =>
      intro t t' _ ht hL
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hL
      exact hL ▸ ht
    | cons x L ih =>
      intro t t' hx ht hL
      rw [List.foldlM_cons] at hL
      obtain ⟨mid, hMid, hRest⟩ := bind_ok_iff.mp hL
      refine ih mid t' (fun y hy => hx y (List.mem_cons_of_mem _ hy)) ?_ hRest
      obtain ⟨b, fork⟩ := x
      refine next_invariant Q ?_ ?_ ht hMid
      · intro u fork n time chain budget blk hu _ hBlk c hc hNone hLondon
        rcases List.mem_append.mp hc with hc | hc
        · exact hu c hc hNone hLondon
        · rw [List.mem_singleton] at hc
          subst hc
          rw [hOff] at hBlk
          exact simulateBlock_baseFee hBlk rfl hLondon
      · intro u chain budget blk hu _ hBlk c hc hNone hLondon
        rcases List.mem_append.mp hc with hc | hc
        · exact hu c hc hNone hLondon
        · rw [List.mem_singleton] at hc
          subst hc
          have hNum := (simulateBlock_links hBlk).2.1
          rw [hOff] at hBlk
          exact simulateBlock_baseFee hBlk
            (hNone _ (hx _ List.mem_cons_self) hNum.symm) hLondon
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Agreement with the state transition -/

/-- A recovered sender passes the checks of a given sender, then the rule on its code. -/
private theorem checkSender_signed {fork : Fork} {state : State.TransactionState}
    {sender : Address} {tx : Transaction} {skip : Bool} :
    checkSender fork state sender tx true skip = (do
      checkSender fork state sender tx false skip
      let code ← (state.getCode (state.getAccount sender).codeHash).mapError fun _ =>
        InclusionError.missingCode (state.getAccount sender).codeHash
      failIf ((state.getAccount sender).codeHash ≠ State.EMPTY_CODE_HASH ∧
        !(fork ≥ .pectra ∧ Evm.isValidDelegation code)) .senderNotEoa) := by
  cases skip <;> simp [checkSender, bind_assoc]

/-- A check that recovers the sender is the check with that sender given, then the code rule. -/
private theorem checkInclusion_none_eq {fork : Fork} {chainId : UInt64}
    {env : Evm.BlockEnvironment fork} {used : BlockGas} {state : State.TransactionState}
    {tx : Transaction} {sender : Address} {lifted : LiftedRules}
    (hChain : checkChainId fork chainId tx = .ok ())
    (hSender : recoverSender fork tx = .ok sender) :
    checkInclusion chainId env used state tx none lifted = (do
      let inc ← checkInclusion chainId env used state tx (some sender) lifted
      let code ← (state.getCode (state.getAccount sender).codeHash).mapError fun _ =>
        InclusionError.missingCode (state.getAccount sender).codeHash
      failIf ((state.getAccount sender).codeHash ≠ State.EMPTY_CODE_HASH ∧
        !(fork ≥ .pectra ∧ Evm.isValidDelegation code)) .senderNotEoa
      pure inc) := by
  have hOk : (Except.ok () : Except InclusionError Unit) = pure () := rfl
  have hOkSender : (Except.ok sender : Except InclusionError Address) = pure sender := rfl
  unfold checkInclusion
  by_cases hg : fork ≥ .glamsterdam <;>
    simp [hg, hChain, hSender, Except.mapError, checkSender_signed, bind_assoc] <;>
    simp only [hOk, hOkSender, pure_bind, ite_self]

/-- When the check with the sender given passes, the real check agrees, or the code rule fails. -/
private theorem checkInclusion_none_of_some {fork : Fork} {chainId : UInt64}
    {env : Evm.BlockEnvironment fork} {used : BlockGas} {state : State.TransactionState}
    {tx : Transaction} {sender : Address} {lifted : LiftedRules} {inc : Included}
    (hChain : checkChainId fork chainId tx = .ok ()) (hSender : recoverSender fork tx = .ok sender)
    (h : checkInclusion chainId env used state tx (some sender) lifted = .ok inc) :
    checkInclusion chainId env used state tx none lifted = .ok inc ∨
      ∃ e, checkInclusion chainId env used state tx none lifted = .error e ∧
        (e = .senderNotEoa ∨ ∃ codeHash, e = .missingCode codeHash) := by
  rw [checkInclusion_none_eq hChain hSender, h]
  cases hc : state.getCode (state.getAccount sender).codeHash with
  | error _ =>
    exact Or.inr ⟨.missingCode (state.getAccount sender).codeHash,
      by simp [Except.mapError, bind, Except.bind], Or.inr ⟨_, rfl⟩⟩
  | ok code =>
    simp only [Except.mapError, bind, Except.bind, pure, Except.pure, failIf]
    by_cases hr : decide ((state.getAccount sender).codeHash ≠ State.EMPTY_CODE_HASH ∧
        (!decide (fork ≥ Fork.pectra ∧ Evm.isValidDelegation code = true)) = true) = true
    · simp only [hr, ↓reduceIte]
      exact Or.inr ⟨_, rfl, Or.inl rfl⟩
    · simp only [hr]
      exact Or.inl rfl

/-- A transaction that enters a simulated body enters a real one alike, or fails the rule on code.

The simulation gives the sender of its signature, keeps each precompile and lifts the gas cap. -/
private theorem applyTransaction_signed {fork : Fork} {env : Evm.BlockEnvironment fork}
    {index : Nat} {before after : BodyOutput fork} {tx : Transaction} {sender : Address}
    {overrides : BodyOverrides} (hs : overrides.senders index = some sender)
    (hp : overrides.precompiles = some) (hl : overrides.lifted = { totalGasCap := true })
    (hChain : checkChainId fork env.chainId tx = .ok ())
    (hSender : recoverSender fork tx = .ok sender)
    (hGas : tx.gas.toNat ≤ Evm.GasCosts.TX_MAX_TOTAL_GAS_LIMIT)
    (h : applyTransaction env index before tx.unsigned overrides = .ok after) :
    applyTransaction env index before tx = .ok after ∨
      ∃ e, applyTransaction env index before tx = .error (.invalidTransaction index e) ∧
        (e = .senderNotEoa ∨ ∃ codeHash, e = .missingCode codeHash) := by
  unfold applyTransaction at h ⊢
  rw [hs, hl, hp, checkInclusion_unsigned, checkInclusion_totalGasCap hGas] at h
  simp only [processTransaction_totalGasCap, processTransaction_unsigned,
    Transaction.type_unsigned] at h
  dsimp only
  cases hc : checkInclusion env.chainId env before.gas (.ofBlock before.block) tx (some sender) with
  | error e => simp [hc, Except.mapError, bind, Except.bind] at h
  | ok inc =>
    rw [hc] at h
    rcases checkInclusion_none_of_some hChain hSender hc with hEq | ⟨e, hEq, hP⟩
    · rw [hEq]
      exact Or.inl h
    · rw [hEq]
      exact Or.inr ⟨e, rfl, hP⟩

/-- Transactions that enter a simulated body enter a real one alike, or one fails the rule on code.

Each transaction must agree so, with indices counted from `n`. -/
private theorem foldlM_signed {fork : Fork} {env : Evm.BlockEnvironment fork}
    {overrides : BodyOverrides} :
    ∀ (txs : List Transaction) (n : Nat) (init out : BodyOutput fork),
    (∀ tx index, (tx, index) ∈ txs.zipIdx n → ∀ before after,
      applyTransaction env index before tx.unsigned overrides = .ok after →
      applyTransaction env index before tx = .ok after ∨
        ∃ e, applyTransaction env index before tx = .error (.invalidTransaction index e) ∧
          (e = .senderNotEoa ∨ ∃ codeHash, e = .missingCode codeHash)) →
    ((txs.map Transaction.unsigned).zipIdx n).foldlM
      (fun before (tx, index) => applyTransaction env index before tx overrides) init = .ok out →
    (txs.zipIdx n).foldlM (fun before (tx, index) => applyTransaction env index before tx) init =
        .ok out ∨
      ∃ i e, (txs.zipIdx n).foldlM
          (fun before (tx, index) => applyTransaction env index before tx) init =
          .error (.invalidTransaction i e) ∧
        (e = .senderNotEoa ∨ ∃ codeHash, e = .missingCode codeHash)
  | [], _, _, _, _, h => Or.inl h
  | tx :: txs, n, init, out, hStep, h => by
    simp only [List.map_cons, List.zipIdx_cons, List.foldlM_cons] at h ⊢
    obtain ⟨mid, hMid, h⟩ := bind_ok_iff.mp h
    rcases hStep tx n List.mem_cons_self init mid hMid with hEq | ⟨e, hEq, hP⟩
    · rw [hEq]
      exact foldlM_signed txs (n + 1) mid out
        (fun tx index hm => hStep tx index (List.mem_cons_of_mem _ hm)) h
    · rw [hEq]
      exact Or.inr ⟨n, e, rfl, hP⟩

/-- A simulated body whose transactions agree with the real ones agrees with the real body. -/
private theorem applyBody_signed {fork : Fork} {config : ChainConfig}
    {env : Evm.BlockEnvironment fork} {header : Header fork} {txs : List Transaction}
    {ws : Since .shapella fork (List Withdrawal)} {start : State.BlockState}
    {overrides : BodyOverrides} {output : BlockOutput fork}
    (hT : ∀ body out, applyTransactions env body (txs.map Transaction.unsigned) overrides =
      .ok out → applyTransactions env body txs = .ok out ∨
        ∃ i e, applyTransactions env body txs = .error (.invalidTransaction i e) ∧
          (e = .senderNotEoa ∨ ∃ codeHash, e = .missingCode codeHash))
    (h : applyBody config env ⟨header, txs.map Transaction.unsigned, [], ws⟩ start overrides =
      .ok output) :
    applyBody config env ⟨header, txs, [], ws⟩ start = .ok output ∨
      ∃ i e, applyBody config env ⟨header, txs, [], ws⟩ start = .error (.invalidTransaction i e) ∧
        (e = .senderNotEoa ∨ ∃ codeHash, e = .missingCode codeHash) := by
  unfold applyBody at h ⊢
  obtain ⟨state, hState, h⟩ := bind_ok_iff.mp h
  obtain ⟨body, hBody, h⟩ := bind_ok_iff.mp h
  obtain ⟨out, hOut, h⟩ := bind_ok_iff.mp h
  rw [List.length_map] at h
  rcases hT body out hOut with hEq | ⟨i, e, hEq, hP⟩
  · left
    simp only [hState, hBody, hEq, bind, Except.bind]
    exact h
  · right
    refine ⟨i, e, ?_, hP⟩
    simp only [hState, hBody, hEq, bind, Except.bind]

/-- With validation and no overrides, a simulated block runs its filled calls as a real body.

The body gives each call its sender, keeps every precompile, and lifts only the cap on gas. -/
private theorem simulateBlock_valid_spec {chain chain' : BlockChain} {base : RecentBlock}
    {fork : Fork} {number time budget budget' : Nat} {calls : List GenericTransaction}
    {b : SimulatedBlock}
    (h : simulateBlock chain base fork number time { calls } true budget =
      .ok (chain', budget', b)) :
    ∃ (header : Header fork) (filled : List (Transaction × Address)) (result : BodyResult fork)
      (hash : Hash32),
      runBody chain ⟨header, filled.map (·.1), [], fun _ => []⟩
        { senders := ((filled.map (·.2))[·]?), precompiles := some,
          lifted := { totalGasCap := true } } = .ok result ∧
      b = ⟨{ fork := fork
             block := ⟨fillHeader header result.output result.roots, filled.map (·.1), [],
               fun _ => []⟩
             hash := hash
             state := result.post
             receipts := result.output.receipts
             logs := result.output.logs }, filled.map (·.2)⟩ := by
  have hState : overrideState fork chain.state [] = chain.state := by
    simp [overrideState, applyOverrides]
  have hMoves : movedPrecompiles (precompileMoves []) = some := by
    funext a
    rfl
  simp only [simulateBlock] at h
  split at h
  · rename_i parent hP
    simp only [bind_ok_iff, mapError_ok_iff] at h
    obtain ⟨_, -, _, -, _, -, _, -, filled, -, result, hResult, hash, -, hEq⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hEq
    obtain ⟨-, -, rfl⟩ := hEq
    rw [hState, hMoves] at hResult
    exact ⟨_, filled.1, result, hash, hResult, rfl⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The blob gas of transactions that run is the sum of the blob gas of each, from the index `n`. -/
private theorem foldlM_blob {fork : Fork} {env : Evm.BlockEnvironment fork} :
    ∀ (txs : List Transaction) (n : Nat) (init out : BodyOutput fork),
    (txs.zipIdx n).foldlM (fun before (tx, index) => applyTransaction env index before tx) init =
      .ok out →
    out.gas.blob = init.gas.blob + (txs.map Fees.BlobBaseFee.calculateTotalBlobGas).sum
  | [], _, _, _, h => by
    cases h
    simp
  | tx :: txs, n, init, out, h => by
    simp only [List.zipIdx_cons, List.foldlM_cons] at h
    obtain ⟨mid, hMid, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, run, -, hRun, hGas, -⟩ := applyTransaction_eq_ok hMid
    rw [foldlM_blob txs (n + 1) mid out h, hGas, BlockGas.add,
      processTransaction_blockGas_blob hRun]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Other transactions with the root `root` give the roots of an output with that root. -/
private theorem outputRoots_of_transactionsRoot {fork : Fork} {txs txs' : List Transaction}
    {ws : Since .shapella fork (List Withdrawal)} {output : BlockOutput fork}
    {post : State.State} {roots : OutputRoots} {root : Hash32}
    (h : outputRoots txs' ws output post = .ok roots) (hRoot : transactionsRoot txs = .ok root) :
    outputRoots txs ws output post = .ok { roots with transactions := root } := by
  have hTx : (transactionsRoot txs).mapError BlockError.trie = .ok root := by
    rw [hRoot]
    rfl
  unfold outputRoots at h ⊢
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨postRoot, hPost, h⟩ := bind_ok_iff.mp h
  obtain ⟨receiptRoot, hReceipt, h⟩ := bind_ok_iff.mp h
  obtain ⟨withdrawalRoot, hWithdrawal, h⟩ := bind_ok_iff.mp h
  cases h
  simp only [hTx, hPost, hReceipt, hWithdrawal, bind, Except.bind, pure, Except.pure]

/-- When a block passes its checks and its body fails, its transition fails with that error. -/
private theorem stateTransition_of_runBody_error {fork : Fork} {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {e : BlockError}
    (hFork : ¬.hegota ≤ fork)
    (hActive :
      chain.config.activeFork block.header.number block.header.timestamp.toNat = some fork)
    (hCheck : checkBlock chain.config checkSeal chain.recent block = .ok ())
    (hBody : runBody chain block = .error e) :
    stateTransition chain block checkSeal = .error e := by
  simp only [stateTransition, hFork, hActive, ↓reduceIte, hCheck, hBody, bind, Except.bind]

/-- A simulated block agrees with the state transition, or a sender has code or lacks it.

The hypotheses are those of the theorem below, without the codes of the state. -/
private theorem stateTransition_of_simulateBlock_or {chain chain' : BlockChain} {base : RecentBlock}
    {fork : Fork} {number time budget budget' : Nat} {calls : List GenericTransaction}
    {b : SimulatedBlock} {txs : List Transaction} {root : Hash32}
    (h : simulateBlock chain base fork number time { calls } true budget =
      .ok (chain', budget', b))
    (hFork : chain.config.activeFork b.record.block.header.number
      b.record.block.header.timestamp.toNat = some b.record.fork)
    (hHegota : b.record.fork < .hegota)
    (hUnsigned : txs.map Transaction.unsigned = b.record.block.transactions)
    (hSenders : ∀ p ∈ txs.zip b.senders, recoverSender b.record.fork p.1 = .ok p.2 ∧
      checkChainId b.record.fork chain.config.chainId p.1 = .ok ())
    (hGas : ∀ tx ∈ txs, tx.gas.toNat ≤ Evm.GasCosts.TX_MAX_TOTAL_GAS_LIMIT)
    (hBlob : (txs.map Fees.BlobBaseFee.calculateTotalBlobGas).sum < 2 ^ 64)
    (hRoot : transactionsRoot txs = .ok root)
    (hCheck : checkBlock chain.config false chain.recent (b.withTransactions txs root) = .ok ()) :
    stateTransition chain (b.withTransactions txs root) false = .ok b.record.state ∨
      ∃ i e, stateTransition chain (b.withTransactions txs root) false =
          .error (.invalidTransaction i e) ∧
        (e = .senderNotEoa ∨ ∃ codeHash, e = .missingCode codeHash) := by
  obtain ⟨header, filled, result, hash, hRun, rfl⟩ := simulateBlock_valid_spec h
  dsimp only at hFork hHegota hUnsigned hSenders hCheck ⊢
  have hLen : (filled.map (·.2)).length = txs.length := by
    have := congrArg List.length hUnsigned
    simp only [List.length_map] at this ⊢
    omega
  rw [← hUnsigned] at hRun
  unfold runBody at hRun
  obtain ⟨hashes, hHashes, hRun⟩ := bind_ok_iff.mp hRun
  obtain ⟨output, hOutput, hRun⟩ := bind_ok_iff.mp hRun
  obtain ⟨roots, hRoots, hRun⟩ := bind_ok_iff.mp hRun
  cases hRun
  dsimp only at hOutput hRoots
  have hNot : ¬.hegota ≤ fork := Nat.not_le_of_lt hHegota
  have hTxs : ∀ body out, applyTransactions (blockEnvironment chain.config hashes header) body
      (txs.map Transaction.unsigned)
      { senders := ((filled.map (·.2))[·]?), lifted := { totalGasCap := true } } = .ok out →
      applyTransactions (blockEnvironment chain.config hashes header) body txs = .ok out ∨
        ∃ i e, applyTransactions (blockEnvironment chain.config hashes header) body txs =
            .error (.invalidTransaction i e) ∧
          (e = .senderNotEoa ∨ ∃ codeHash, e = .missingCode codeHash) := by
    intro body out hT
    refine foldlM_signed txs 0 _ out (fun tx index hm before after hA => ?_) hT
    obtain ⟨hi, hx⟩ := List.mem_zipIdx' hm
    rw [hx] at hA ⊢
    have hi' : index < (filled.map (·.2)).length := hLen ▸ hi
    have hp : (txs[index], (filled.map (·.2))[index]) ∈ txs.zip (filled.map (·.2)) := by
      have := List.getElem_mem (l := txs.zip (filled.map (·.2))) (n := index)
        (by simp only [List.length_zip, List.length_map] at hi' ⊢; omega)
      simpa only [List.getElem_zip] using this
    obtain ⟨hS, hC⟩ := hSenders _ hp
    exact applyTransaction_signed (List.getElem?_eq_getElem hi') rfl rfl hC hS
      (hGas _ (List.getElem_mem hi)) hA
  rcases applyBody_signed hTxs hOutput with hReal | ⟨i, e, hErr, hP⟩
  · left
    have hBody : runBody chain (⟨header, txs, [], fun _ => []⟩ : Block fork Transaction) =
        .ok ⟨output, { roots with transactions := root }⟩ := by
      unfold runBody
      simp only [hHashes, hReal, outputRoots_of_transactionsRoot hRoots hRoot, bind, Except.bind,
        pure, Except.pure]
    obtain ⟨_, _, txsOut, _, _, _, _, hApply, _, _, _, _, _, _, hGasEq, _⟩ :=
      applyBody_eq_ok hReal
    unfold applyTransactions at hApply
    have hb : output.gas.blob < 2 ^ 64 := by
      rw [hGasEq, foldlM_blob txs 0 _ txsOut hApply]
      simpa [BlockGas.zero] using hBlob
    have hw : .shapella ≤ fork → roots.withdrawals.isSome := fun hs => by
      obtain ⟨r, -, hr⟩ := outputRoots_withdrawals hs hRoots
      simp [hr]
    have ha : .glamsterdam ≤ fork → output.accessListHash.isSome := fun hg => by
      obtain ⟨v, hv, -⟩ := applyBody_accessListHash hReal hg
      simp [hv]
    exact stateTransition_of_runBody (result := ⟨output, { roots with transactions := root }⟩)
      hNot hFork hCheck (Eq.trans rfl hBody)
      (outputChecks_fillHeader (header := header) (roots := { roots with transactions := root })
        hb hw ha)
  · right
    refine ⟨i, e, ?_, hP⟩
    have hBody : runBody chain (⟨header, txs, [], fun _ => []⟩ : Block fork Transaction) =
        .error (.invalidTransaction i e) := by
      unfold runBody
      simp only [hHashes, hErr, bind, Except.bind]
    exact stateTransition_of_runBody_error hNot hFork hCheck (Eq.trans rfl hBody)

/-- With validation and no overrides, a simulated block agrees with the state transition.

The fork must be the active fork at the number and time of the block, and come before Hegotá.

The calls must be the transactions `txs` without their signatures.

Each signature must give the sender of its call and name the chain.

Each gas limit must be at most `2^32 - 1`, the cap from Glamsterdam that a simulation lifts.

The blob gas must fit the 64 bits of the header, which a large blob schedule of a chain allows.

The block with `txs` and their root `root` must pass the checks of a block, its parent included.

That block has the gas used, the other roots and the logs Bloom of the simulated block.

The state must hold the code of each of its accounts.

Then its transition gives the state after the simulated block.

Otherwise it fails at a sender with code, by [EIP-3607][eip-3607], which the simulation skips.

[eip-3607]: https://eips.ethereum.org/EIPS/eip-3607#specification -/
theorem stateTransition_of_simulateBlock {chain chain' : BlockChain} {base : RecentBlock}
    {fork : Fork} {number time budget budget' : Nat} {calls : List GenericTransaction}
    {b : SimulatedBlock} {txs : List Transaction} {root : Hash32}
    (h : simulateBlock chain base fork number time { calls } true budget =
      .ok (chain', budget', b))
    (hFork : chain.config.activeFork b.record.block.header.number
      b.record.block.header.timestamp.toNat = some b.record.fork)
    (hHegota : b.record.fork < .hegota)
    (hUnsigned : txs.map Transaction.unsigned = b.record.block.transactions)
    (hSenders : ∀ p ∈ txs.zip b.senders, recoverSender b.record.fork p.1 = .ok p.2 ∧
      checkChainId b.record.fork chain.config.chainId p.1 = .ok ())
    (hGas : ∀ tx ∈ txs, tx.gas.toNat ≤ Evm.GasCosts.TX_MAX_TOTAL_GAS_LIMIT)
    (hBlob : (txs.map Fees.BlobBaseFee.calculateTotalBlobGas).sum < 2 ^ 64)
    (hRoot : transactionsRoot txs = .ok root)
    (hCheck : checkBlock chain.config false chain.recent (b.withTransactions txs root) = .ok ())
    (available : chain.state.HasCodes) :
    stateTransition chain (b.withTransactions txs root) false = .ok b.record.state ∨
      ∃ i, stateTransition chain (b.withTransactions txs root) false =
        .error (.invalidTransaction i .senderNotEoa) := by
  rcases stateTransition_of_simulateBlock_or h hFork hHegota hUnsigned hSenders hGas hBlob hRoot
    hCheck with ok | ⟨i, e, he, hE⟩
  · exact .inl ok
  · rcases hE with rfl | ⟨c, rfl⟩
    · exact .inr ⟨i, he⟩
    · exact absurd he (stateTransition_ne_invalidTransaction_missingCode _ _ _ available i c)

end EthLib.Execution.Rpc
