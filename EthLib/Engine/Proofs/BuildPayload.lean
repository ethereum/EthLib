module

public import EthLib.Engine.BuildPayload
public import EthLib.Engine.Proofs.NewPayload
public import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the payload that the execution layer builds

A built block passes the state transition of its chain, with the state that the build gives.

So `engine_newPayload` answers valid for a built block whose parameters pass its checks.

A header filled from a body passes every check against what that body gave.

The built block carries the timestamp, RANDAO mix, withdrawals, beacon root, slot and choices.

From Pectra, its header commits to the requests that the build gives.

A build on a chain from the attributes of a forkchoice update is such a build, at their fork.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions (Transaction)

variable {fork : Fork} {chain : BlockChain} {attributes : PayloadAttributes fork}
  {choices : BuildChoices} {transactions : List Transaction} {built : BuiltPayload fork}

/-- A header filled from a body passes every check against what that body gave.

The blob gas used must fit 64 bits.

From Shapella the withdrawals root must exist, and from Glamsterdam the access list hash. -/
theorem outputChecks_fillHeader {header : Header fork} {output : BlockOutput fork}
    {roots : OutputRoots} (hb : output.gas.blob < 2 ^ 64)
    (hw : .shapella ≤ fork → roots.withdrawals.isSome)
    (ha : .glamsterdam ≤ fork → output.accessListHash.isSome) :
    firstFailure (outputChecks (fillHeader header output roots) output roots) = .ok () := by
  rw [firstFailure_eq_ok_iff]
  intro c hc
  simp only [outputChecks, fillHeader, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with ((((hc | hc | hc | hc | hc) | hc) | hc) | hc) | hc <;>
    (try subst hc) <;> (try simp only [decide_true])
  · split at hc
    · next h =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hw h)
      simp [hr]
    · simp at hc
  · split at hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp [Nat.mod_eq_of_lt hb]
    · simp at hc
  · split at hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp
    · simp at hc
  · split at hc
    · next h =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (ha h)
      simp [hr]
    · simp at hc

/-- The body of a block runs alike before and after its header is filled.

The body reads none of the fields that the fill sets. -/
theorem runBody_fillHeader {header : Header fork} {output : BlockOutput fork}
    {roots : OutputRoots} {withdrawals : Since .shapella fork (List Execution.Blocks.Withdrawal)} :
    runBody chain ⟨fillHeader header output roots, transactions, [], withdrawals⟩ =
      runBody chain ⟨header, transactions, [], withdrawals⟩ :=
  rfl

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
      built.state = result.post ∧ built.requests = result.output.requests := by
  have hH : ¬ .hegota ≤ fork := by
    intro hc; simp [buildPayload, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
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
      exact ⟨hH, parent, parentHash, result, hP, hA, hHash', hR, hC, hF, rfl, rfl, rfl⟩
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
  obtain ⟨-, _, _, _, -, -, -, -, -, -, hBlock, -, hRequests⟩ := buildPayload_spec h
  rw [hBlock, hRequests]
  rfl

/-- `engine_newPayload` answers that a built block is valid, on the chain that it was built on.

The payload must pass the checks of the method before execution, with the built block.

The latest valid hash is the block's own hash, and the state after it is the state of the build.
-/
theorem newPayloadOnChain_of_buildPayload {version : Nat} {params : Lean.Json}
    {checked : CheckedBlock version} {attributes : PayloadAttributes checked.fork}
    {built : BuiltPayload checked.fork}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (h : buildPayload chain attributes choices transactions = .ok built)
    (hBlock : built.block = checked.block) :
    newPayloadOnChain chain version params =
      .ok (⟨.valid, checked.block.header.hash.toOption⟩, none,
        some (⟨checked.fork, checked.block.header, []⟩, built.state)) := by
  obtain ⟨-, -, -, -, -, -, -, -, parent, hP, hHash, -⟩ := buildPayload_fields h
  rw [hBlock] at hHash
  exact newPayloadOnChain_of_stateTransition_ok hCheck hP hHash
    (hBlock ▸ stateTransition_of_buildPayload h)

/-- A build on a chain from decoded attributes is a build of a payload, at the fork it gives.

So every theorem on that build holds for the payload that it returns. -/
theorem buildPayload_of_buildPayloadOnChain {version : Nat}
    {decoded : Σ f, PayloadAttributes f} {encoded : List ByteArray} {built : BuiltPayload fork}
    (h : buildPayloadOnChain chain version decoded choices encoded = .ok ⟨fork, built⟩) :
    ∃ (attributes : PayloadAttributes fork) (transactions : List Transaction),
      buildPayload chain attributes choices transactions = .ok built := by
  unfold buildPayloadOnChain at h
  split at h
  · obtain ⟨⟨f, a⟩, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨txs, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨b, hB, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨a, txs, mapError_ok_iff.mp hB⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end EthLib.Engine
