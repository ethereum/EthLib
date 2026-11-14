module

public import EthLib.Execution.Rpc.Simulate.Blocks
public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Rpc.Simulate

/-!
# Proofs: the blocks of `eth_simulateV1`

A simulated block follows the last block of its chain, and has the number that it is given.

Its parent hash is the hash of the header of that block, and its hash is the hash of its own header.

The blocks of a simulation, gap blocks included, have consecutive numbers after the base block.

When the view holds the hash of each header, the first has the hash of the base block as parent.

Each other has the hash of the block before it.

Without validation, a block whose base fee is not overridden has a base fee of 0.

That holds whatever the base fee of the block before it.
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

end EthLib.Execution.Rpc
