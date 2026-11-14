module

public import EthLib.Engine.BuildPayload
public import EthLib.Engine.Proofs.NewPayload
public import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the payload that the execution layer builds

A built block passes the state transition of its chain, with the state that the build gives.

So `engine_newPayload` answers valid for a built block whose parameters pass its checks.

The built block carries the timestamp, RANDAO mix, withdrawals, beacon root, slot and choices.

From Pectra, its header commits to the requests that the build gives.

Its value sums the priority fee of each of its transactions, at the gas that its run uses.

A build on a chain from the attributes of a forkchoice update is such a build, at their fork.

Each refusal of a build happens when its check fails and every earlier check passes.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Evm (BlockEnvironment)
open EthLib.Execution.Transactions (Transaction TransactionOutput checkInclusion
  processTransaction priorityFeeOf baseFeeOf)

variable {fork : Fork} {chain : BlockChain} {attributes : PayloadAttributes fork}
  {choices : BuildChoices} {transactions : List Transaction} {built : BuiltPayload fork}

/-- From Hegotá a build is aborted, since the rules of that fork are not specified here yet. -/
theorem buildPayload_eq_error_of_hegota_le (h : .hegota ≤ fork) :
    buildPayload chain attributes choices transactions =
      .error (.aborted (.forkNotYetSpecified fork)) := by
  simp [buildPayload, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A build that succeeds went through each of its steps.

The parent is the last recent block, and the fork is the active fork after it at the timestamp.

The body ran on the header before it was filled, and the block holds the filled header. -/
private theorem buildPayload_spec
    (h : buildPayload chain attributes choices transactions = .ok built) :
    ¬ .hegota ≤ fork ∧ ∃ parent parentHash result,
      chain.recent.getLast? = some parent ∧
      chain.config.activeFork (parent.header.number + 1) attributes.timestamp.toNat = some fork ∧
      parent.header.hash = .ok parentHash ∧
      runBody chain ⟨buildHeader chain.config parent parentHash attributes choices, transactions,
        [], attributes.withdrawals⟩ = .ok result ∧
      checkBlock chain.config false chain.recent built.block = .ok () ∧
      firstFailure (outputChecks built.block.header result.output result.roots) = .ok () ∧
      built.block = ⟨fillHeader (buildHeader chain.config parent parentHash attributes choices)
        result.output result.roots, transactions, [], attributes.withdrawals⟩ ∧
      built.state = result.post ∧ built.requests = result.output.requests ∧
      built.blockValue = priorityFees
        (if h : .london ≤ fork then
          (buildHeader chain.config parent parentHash attributes choices).baseFeePerGas h
        else 0) transactions result.output.receipts := by
  have hH : ¬ .hegota ≤ fork := fun hc => by simp [buildPayload_eq_error_of_hegota_le hc] at h
  simp only [buildPayload, hH, reduceIte] at h
  split at h
  next parent hP =>
    split at h
    next hA =>
      simp only [bind_ok_iff] at h
      obtain ⟨parentHash, hHash, result, hR, u, hC, v, hF, hEq⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq] at hEq
      subst hEq
      have hHash' : parent.header.hash = .ok parentHash := by
        cases hp : parent.header.hash <;> simp_all [Except.mapError]
      exact ⟨hH, parent, parentHash, result, hP, hA, hHash', hR, hC, hF, rfl, rfl, rfl, rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A built block passes the state transition of its chain, without the proof of work.

The state after it is the state that the build gives. -/
theorem stateTransition_of_buildPayload
    (h : buildPayload chain attributes choices transactions = .ok built) :
    stateTransition chain built.block false = .ok built.state := by
  obtain ⟨hH, parent, parentHash, result, -, hA, -, hR, hC, hF, hBlock, hState, -⟩ :=
    buildPayload_spec h
  rw [hState]
  rw [hBlock] at hC hF ⊢
  refine stateTransition_of_runBody hH ?_ hC (by rw [runBody_fillHeader]; exact hR) hF
  rw [show (fillHeader (buildHeader chain.config parent parentHash attributes choices)
      result.output result.roots).timestamp.toNat = attributes.timestamp.toNat from
    toNat_ofNat_timestamp attributes.timestamp]
  exact hA

/-- A built block carries these fields of the attributes and of the builder's choices.

It holds the timestamp, the RANDAO mix, the withdrawals, the parent beacon block root and the slot.

It holds the fee recipient, the extra data and the transactions that the builder chose.

Its parent is the last recent block, and its gas limit moves from the parent's toward the target.
-/
theorem buildPayload_fields
    (h : buildPayload chain attributes choices transactions = .ok built) :
    built.block.header.timestamp.toNat = attributes.timestamp.toNat ∧
      built.block.header.prevRandao = attributes.prevRandao ∧
      built.block.withdrawals = attributes.withdrawals ∧
      built.block.header.parentBeaconBlockRoot = attributes.parentBeaconBlockRoot ∧
      built.block.header.slotNumber = attributes.slotNumber ∧
      built.block.header.coinbase = choices.feeRecipient ∧
      built.block.header.extraData = choices.extraData ∧
      built.block.transactions = transactions ∧
      ∃ parent, chain.recent.getLast? = some parent ∧
        parent.header.hash = .ok built.block.header.parentHash ∧
        built.block.header.number = parent.header.number + 1 ∧
        built.block.header.gasLimit = gasLimitToward
          (Execution.Fees.GasLimit.parentGasLimitForCheck parent.fork fork parent.header.gasLimit)
          (gasTarget attributes choices) := by
  obtain ⟨-, parent, parentHash, _, hP, -, hHash, -, -, -, hBlock, -, -⟩ := buildPayload_spec h
  rw [hBlock]
  exact ⟨toNat_ofNat_timestamp attributes.timestamp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, parent,
    hP, hHash, rfl, rfl⟩

/-- From Pectra, the header of a built block commits to the requests that the build gives. -/
theorem requestsHash_of_buildPayload
    (h : buildPayload chain attributes choices transactions = .ok built)
    (hPectra : .pectra ≤ fork) :
    built.block.header.requestsHash hPectra = requestsHash built.requests := by
  obtain ⟨-, _, _, _, -, -, -, -, -, -, hBlock, -, hRequests, -⟩ := buildPayload_spec h
  rw [hBlock, hRequests]
  rfl

/-! ## The value of a built block -/

/-- Differences of a list after a start value, with one value appended.

The new difference is that value minus the last of the list, or minus the start when it is empty. -/
private theorem zipWith_sub_append (c : List Nat) (start x : Nat) :
    List.zipWith (· - ·) (c ++ [x]) (start :: (c ++ [x])) =
      List.zipWith (· - ·) c (start :: c) ++ [x - (c.getLast?.getD start)] := by
  induction c generalizing start with
  | nil => rfl
  | cons a c ih =>
    simp only [List.cons_append, List.zipWith_cons_cons, ih a, List.cons.injEq, true_and]
    cases c <;> rfl

/-- A run of transactions with one more is the run of the others, then that one at its index. -/
private theorem applyTransactions_append {env : BlockEnvironment fork} {body : BodyState}
    {l : List Transaction} {tx : Transaction} :
    applyTransactions env body (l ++ [tx]) =
      applyTransactions env body l >>= fun before => applyTransaction env l.length before tx := by
  simp [applyTransactions, List.zipIdx_append, List.foldlM_append]

/-- A property of every list follows from the empty list and from adding one value at the end. -/
private theorem appendInduction {α : Type} {motive : List α → Prop} (nil : motive [])
    (append_singleton : ∀ l a, motive l → motive (l ++ [a])) (l : List α) : motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons a r ih =>
    rw [List.reverse_cons]
    exact append_singleton _ _ ih

/-- A run of transactions adds one receipt each, the last with the cumulative gas of the run.

Its priority fees sum those of the output of each transaction, at the gas that output used.

The run of each transaction follows the run of those before it. -/
private theorem applyTransactions_priorityFees {env : BlockEnvironment fork} {body : BodyState}
    (baseFee : Nat) {l : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body l = .ok output) :
    output.receipts.length = l.length ∧
      (output.receipts.map (·.2.cumulativeGasUsed)).getLast?.getD 0 = output.cumulativeGasUsed ∧
      ∃ outs : List TransactionOutput, outs.length = l.length ∧
        priorityFees baseFee l output.receipts =
          (List.zipWith (fun tx out => priorityFeeOf baseFee out.gasUsed tx) l outs).sum ∧
        ∀ i (hi : i < l.length), ∃ before included out, outs[i]? = some out ∧
          applyTransactions env body (l.take i) = .ok before ∧
          checkInclusion env.chainId env before.gas (.ofBlock before.block) l[i] = .ok included ∧
          processTransaction env before.block included l[i] = .ok out := by
  induction l using appendInduction generalizing output with
  | nil =>
    simp only [applyTransactions, List.zipIdx_nil, List.foldlM_nil, pure, Except.pure,
      Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, [], rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | append_singleton l tx ih =>
    rw [applyTransactions_append] at h
    obtain ⟨before, hBefore, hStep⟩ := bind_ok_iff.mp h
    obtain ⟨hLen, hLast, outs, hOuts, hSum, hRuns⟩ := ih hBefore
    obtain ⟨included, out, hInc, hProc, -, hCum, -⟩ := applyTransaction_eq_ok hStep
    obtain ⟨outcome, logs, hReceipts⟩ := applyTransaction_receipts hStep
    refine ⟨by simp [hReceipts, hLen], by simp [hReceipts, makeReceipt], outs ++ [out],
      by simp [hOuts], ?_, ?_⟩
    · have hUsed : (List.zipWith (· - ·) (before.receipts.map (·.2.cumulativeGasUsed))
          (0 :: before.receipts.map (·.2.cumulativeGasUsed))).length = l.length := by
        simp [hLen]
      simp only [priorityFees, hReceipts, List.map_append, List.map_cons, List.map_nil]
      rw [zipWith_sub_append, List.zipWith_append hUsed.symm,
        List.zipWith_append hOuts.symm, List.sum_append, List.sum_append]
      simp only [priorityFees] at hSum
      rw [hSum]
      simp only [makeReceipt, hLast, hCum, Nat.add_sub_cancel_left, List.zipWith_cons_cons,
        List.zipWith_nil_left, List.sum_cons, List.sum_nil]
    · intro i hi
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      rcases Nat.lt_or_ge i l.length with hlt | hge
      · obtain ⟨b, inc, o, ho, hb, hinc, hproc⟩ := hRuns i hlt
        refine ⟨b, inc, o, by rw [List.getElem?_append_left (by omega)]; exact ho, ?_, ?_, ?_⟩
        · rw [List.take_append_of_le_length (by omega)]
          exact hb
        · rw [List.getElem_append_left hlt]
          exact hinc
        · rw [List.getElem_append_left hlt]
          exact hproc
      · have hi' : i = l.length := by omega
        subst hi'
        refine ⟨before, included, out, by simp [hOuts], by simpa using hBefore, ?_, ?_⟩
        · simpa using hInc
        · simpa using hProc

/-- The value of a built block sums the priority fee of each transaction, at the gas its run uses.

The body runs in the environment of the block, after the DAO transfer and the system calls.

Each transaction runs after those before it.

The priority fee is the gas used times the price above the base fee. -/
theorem blockValue_of_buildPayload
    (h : buildPayload chain attributes choices transactions = .ok built) :
    ∃ hashes state body outs,
      recentHashes chain.recent = .ok hashes ∧
      daoTransfer chain.config fork built.block.header.number ⟨chain.state, ∅, ∅, ∅, ∅⟩ =
        .ok state ∧
      startSystemCalls (blockEnvironment chain.config hashes built.block.header)
        built.block.header.parentHash (.init state) = .ok body ∧
      outs.length = transactions.length ∧
      built.blockValue = (List.zipWith (fun tx (out : TransactionOutput) =>
        priorityFeeOf (baseFeeOf (blockEnvironment chain.config hashes built.block.header))
          out.gasUsed tx) transactions outs).sum ∧
      ∀ i (hi : i < transactions.length), ∃ before included out, outs[i]? = some out ∧
        applyTransactions (blockEnvironment chain.config hashes built.block.header) body
          (transactions.take i) = .ok before ∧
        checkInclusion chain.config.chainId
          (blockEnvironment chain.config hashes built.block.header) before.gas
          (.ofBlock before.block) transactions[i] = .ok included ∧
        processTransaction (blockEnvironment chain.config hashes built.block.header)
          before.block included transactions[i] = .ok out := by
  obtain ⟨-, parent, parentHash, result, -, -, -, hR, -, -, hBlock, -, -, hValue⟩ :=
    buildPayload_spec h
  obtain ⟨hashes, hHashes, hApply, -⟩ := runBody_eq_ok.mp hR
  obtain ⟨state, body, txs, hDao, hStart, hTxs, hReceipts⟩ := applyBody_receipts hApply
  rw [hBlock]
  obtain ⟨-, -, outs, hOuts, hSum, hRuns⟩ :=
    applyTransactions_priorityFees (baseFeeOf (blockEnvironment chain.config hashes
      (buildHeader chain.config parent parentHash attributes choices))) hTxs
  refine ⟨hashes, state, body, outs, hHashes, hDao, hStart, hOuts, ?_, fun i hi => ?_⟩
  · rw [hValue, hReceipts]
    exact hSum
  · exact hRuns i hi

/-- `engine_newPayload` answers that a built block is valid, on the chain that it was built on.

The payload must pass the checks of the method before execution, with the built block.

The last block of the chain must pass the terminal block check, as one from Paris on always does.

The latest valid hash is the block's own hash, and the state after it is the state of the build.
-/
theorem newPayloadOnChain_of_buildPayload {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {version : Nat} {params : Lean.Json}
    {checked : CheckedBlock version} {attributes : PayloadAttributes checked.fork}
    {built : BuiltPayload checked.fork}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (h : buildPayload chain attributes choices transactions = .ok built)
    (hBlock : built.block = checked.block)
    (hTerminal : ∀ parent, chain.recent.getLast? = some parent →
      passesTerminalCheck transition totalDifficulty parent = true) :
    newPayloadOnChain transition totalDifficulty chain version params =
      .ok (⟨.valid, checked.block.header.hash.toOption⟩, none,
        some (⟨checked.fork, checked.block.header, []⟩, built.state)) := by
  obtain ⟨-, -, -, -, -, -, -, -, parent, hP, hHash, -⟩ := buildPayload_fields h
  rw [hBlock] at hHash
  exact newPayloadOnChain_of_stateTransition_ok hCheck hP hHash (hTerminal parent hP)
    (hBlock ▸ stateTransition_of_buildPayload h)

/-- A build on a chain from decoded attributes is a build of a payload, at the fork it gives.

The parent is the last recent block, and the attributes pass the checks of the update against it.

The transactions are those that decode from the payload form, at that fork.

So every theorem on that build holds for the payload that it returns. -/
theorem buildPayload_of_buildPayloadOnChain {version : Nat}
    {decoded : Σ f, PayloadAttributes f} {encoded : List ByteArray} {built : BuiltPayload fork}
    (h : buildPayloadOnChain chain version decoded choices encoded = .ok ⟨fork, built⟩) :
    ∃ parent attributes transactions,
      chain.recent.getLast? = some parent ∧
      checkAttributes chain.config version
        ⟨parent.header.parentHash, true, UInt64.ofNat parent.header.number,
          UInt64.ofNat parent.header.timestamp.toNat, none⟩ decoded = .ok ⟨fork, attributes⟩ ∧
      decodeTransactions fork 0 encoded = .ok transactions ∧
      buildPayload chain attributes choices transactions = .ok built := by
  unfold buildPayloadOnChain at h
  split at h
  · rename_i parent hParent
    obtain ⟨⟨f, a⟩, hA, h⟩ := bind_ok_iff.mp h
    obtain ⟨txs, hT, h⟩ := bind_ok_iff.mp h
    obtain ⟨b, hB, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨parent, a, txs, hParent, mapError_ok_iff.mp hA, mapError_ok_iff.mp hT,
      mapError_ok_iff.mp hB⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Each refusal of a build -/

/-- A build on a chain with no recent block fails for a missing parent. -/
theorem buildPayload_eq_error_of_getLast?_eq_none (hh : ¬ .hegota ≤ fork)
    (hp : chain.recent.getLast? = none) :
    buildPayload chain attributes choices transactions = .error .noParent := by
  simp [buildPayload, hh, hp, throw, throwThe, MonadExceptOf.throw]

/-- A build whose timestamp and parent do not give its own fork fails for the wrong fork. -/
theorem buildPayload_eq_error_of_activeFork_ne {parent : RecentBlock} (hh : ¬ .hegota ≤ fork)
    (hp : chain.recent.getLast? = some parent)
    (ha : chain.config.activeFork (parent.header.number + 1) attributes.timestamp.toNat
      ≠ some fork) :
    buildPayload chain attributes choices transactions = .error .wrongFork := by
  simp [buildPayload, hh, hp, ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A build whose parent header does not encode fails with the error of that encoding. -/
theorem buildPayload_eq_error_of_hash_eq_error {parent : RecentBlock}
    {error : Serialization.Rlp.RlpError}
    (hh : ¬ .hegota ≤ fork) (hp : chain.recent.getLast? = some parent)
    (ha : chain.config.activeFork (parent.header.number + 1) attributes.timestamp.toNat
      = some fork)
    (hx : parent.header.hash = .error error) :
    buildPayload chain attributes choices transactions = .error (.encoding error) := by
  simp [buildPayload, hh, hp, ha, hx, bind, Except.bind, Except.mapError]

/-- A build whose body does not run fails with the error of that run. -/
theorem buildPayload_eq_error_of_runBody_eq_error {parent : RecentBlock} {parentHash : Hash32}
    {error : BlockError} (hh : ¬ .hegota ≤ fork) (hp : chain.recent.getLast? = some parent)
    (ha : chain.config.activeFork (parent.header.number + 1) attributes.timestamp.toNat
      = some fork)
    (hx : parent.header.hash = .ok parentHash)
    (hr : runBody chain ⟨buildHeader chain.config parent parentHash attributes choices,
      transactions, [], attributes.withdrawals⟩ = .error error) :
    buildPayload chain attributes choices transactions = .error error := by
  simp [buildPayload, hh, hp, ha, hx, hr, bind, Except.bind, Except.mapError]

/-- A build whose block fails the checks of its chain fails with the error of those checks. -/
theorem buildPayload_eq_error_of_checkBlock_eq_error {parent : RecentBlock} {parentHash : Hash32}
    {result : BodyResult fork} {error : BlockError} (hh : ¬ .hegota ≤ fork)
    (hp : chain.recent.getLast? = some parent)
    (ha : chain.config.activeFork (parent.header.number + 1) attributes.timestamp.toNat
      = some fork)
    (hx : parent.header.hash = .ok parentHash)
    (hr : runBody chain ⟨buildHeader chain.config parent parentHash attributes choices,
      transactions, [], attributes.withdrawals⟩ = .ok result)
    (hc : checkBlock chain.config false chain.recent
      ⟨fillHeader (buildHeader chain.config parent parentHash attributes choices) result.output
        result.roots, transactions, [], attributes.withdrawals⟩ = .error error) :
    buildPayload chain attributes choices transactions = .error error := by
  simp [buildPayload, hh, hp, ha, hx, hr, hc, bind, Except.bind, Except.mapError]

/-- A build whose filled header disagrees with what its body gave fails with the first such error.

After a body that runs, only blob gas of 2^64 or more makes the filled header disagree. -/
theorem buildPayload_eq_error_of_outputChecks_eq_error {parent : RecentBlock} {parentHash : Hash32}
    {result : BodyResult fork} {error : BlockError} (hh : ¬ .hegota ≤ fork)
    (hp : chain.recent.getLast? = some parent)
    (ha : chain.config.activeFork (parent.header.number + 1) attributes.timestamp.toNat
      = some fork)
    (hx : parent.header.hash = .ok parentHash)
    (hr : runBody chain ⟨buildHeader chain.config parent parentHash attributes choices,
      transactions, [], attributes.withdrawals⟩ = .ok result)
    (hc : checkBlock chain.config false chain.recent
      ⟨fillHeader (buildHeader chain.config parent parentHash attributes choices) result.output
        result.roots, transactions, [], attributes.withdrawals⟩ = .ok ())
    (hf : firstFailure (outputChecks
      (fillHeader (buildHeader chain.config parent parentHash attributes choices) result.output
        result.roots) result.output result.roots) = .error error) :
    buildPayload chain attributes choices transactions = .error error := by
  simp [buildPayload, hh, hp, ha, hx, hr, hc, hf, bind, Except.bind, Except.mapError]

/-- A build on a chain with no recent block fails for a missing parent, with no head to apply. -/
theorem buildPayloadOnChain_eq_error_of_getLast?_eq_none {version : Nat}
    {decoded : Σ f, PayloadAttributes f} {encoded : List ByteArray}
    (hp : chain.recent.getLast? = none) :
    buildPayloadOnChain chain version decoded choices encoded = .error (.block .noParent) := by
  simp [buildPayloadOnChain, hp, throw, throwThe, MonadExceptOf.throw]

/-- Attributes that fail the checks of the update fail a build on a chain, with that error. -/
theorem buildPayloadOnChain_eq_error_of_checkAttributes_eq_error {version : Nat}
    {decoded : Σ f, PayloadAttributes f} {encoded : List ByteArray} {parent : RecentBlock}
    {error : EngineError} (hp : chain.recent.getLast? = some parent)
    (ha : checkAttributes chain.config version
      ⟨parent.header.parentHash, true, UInt64.ofNat parent.header.number,
        UInt64.ofNat parent.header.timestamp.toNat, none⟩ decoded = .error error) :
    buildPayloadOnChain chain version decoded choices encoded = .error (.attributes error) := by
  simp [buildPayloadOnChain, hp, ha, bind, Except.bind, Except.mapError]

/-- A transaction that does not decode at the fork of the attributes fails with that error. -/
theorem buildPayloadOnChain_eq_error_of_decodeTransactions_eq_error {version : Nat}
    {decoded : Σ f, PayloadAttributes f} {encoded : List ByteArray} {parent : RecentBlock}
    {error : PayloadError} (hp : chain.recent.getLast? = some parent)
    (ha : checkAttributes chain.config version
      ⟨parent.header.parentHash, true, UInt64.ofNat parent.header.number,
        UInt64.ofNat parent.header.timestamp.toNat, none⟩ decoded = .ok ⟨fork, attributes⟩)
    (ht : decodeTransactions fork 0 encoded = .error error) :
    buildPayloadOnChain chain version decoded choices encoded = .error (.transaction error) := by
  simp [buildPayloadOnChain, hp, ha, ht, bind, Except.bind, Except.mapError]

/-- A build on a chain whose own build fails gives the error of that build. -/
theorem buildPayloadOnChain_eq_error_of_buildPayload_eq_error {version : Nat}
    {decoded : Σ f, PayloadAttributes f} {encoded : List ByteArray} {parent : RecentBlock}
    {error : BlockError} (hp : chain.recent.getLast? = some parent)
    (ha : checkAttributes chain.config version
      ⟨parent.header.parentHash, true, UInt64.ofNat parent.header.number,
        UInt64.ofNat parent.header.timestamp.toNat, none⟩ decoded = .ok ⟨fork, attributes⟩)
    (ht : decodeTransactions fork 0 encoded = .ok transactions)
    (hb : buildPayload chain attributes choices transactions = .error error) :
    buildPayloadOnChain chain version decoded choices encoded = .error (.block error) := by
  simp [buildPayloadOnChain, hp, ha, ht, hb, bind, Except.bind, Except.mapError]

end EthLib.Engine
