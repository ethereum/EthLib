module

public import EthLib.Engine.BuildPayload
public import EthLib.Engine.Proofs.NewPayload
public import EthLib.Base.Except

/-!
# Proofs: the block that the execution layer builds

A built block passes the state transition of its chain, with the state that the build gives.

So `engine_newPayload` answers that the payload of a built block is valid.

The built block carries each field of the attributes and of the builder's choices.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions (Transaction)

variable {fork : Fork} {chain : BlockChain} {attributes : PayloadAttributes fork}
  {choices : BuildChoices} {transactions : List Transaction} {block : Block fork Transaction}
  {post : Execution.State.State}

private theorem toNat_ofNat_timestamp (t : UInt64) :
    (BitVec.ofNat 256 t.toNat).toNat = t.toNat := by
  have := t.toNat_lt
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- The gas limit toward a target passes the check against a parent of at least 5000 gas. -/
theorem checkGasLimit_gasLimitToward {parentGasLimit : Nat} (target : Nat)
    (h : Execution.Fees.GasLimit.LIMIT_MINIMUM ≤ parentGasLimit) :
    Execution.Fees.GasLimit.checkGasLimit (gasLimitToward parentGasLimit target)
      parentGasLimit = true := by
  simp only [gasLimitToward, Execution.Fees.GasLimit.checkGasLimit,
    Execution.Fees.GasLimit.LIMIT_ADJUSTMENT_FACTOR, Execution.Fees.GasLimit.LIMIT_MINIMUM] at *
  by_cases hc : parentGasLimit < max target 5000 <;>
    simp only [hc, reduceIte, Bool.and_eq_true, decide_eq_true_eq] <;> omega

/-- A target that the check allows is the gas limit itself, so the builder can reach any of them.
-/
theorem gasLimitToward_of_checkGasLimit {parentGasLimit target : Nat}
    (h : Execution.Fees.GasLimit.checkGasLimit target parentGasLimit = true) :
    gasLimitToward parentGasLimit target = target := by
  simp only [Execution.Fees.GasLimit.checkGasLimit, Bool.and_eq_true, decide_eq_true_eq] at h
  dsimp only [gasLimitToward]
  by_cases hc : parentGasLimit < max target Execution.Fees.GasLimit.LIMIT_MINIMUM
  · simp only [hc, reduceIte]
    simp only [Execution.Fees.GasLimit.LIMIT_ADJUSTMENT_FACTOR,
      Execution.Fees.GasLimit.LIMIT_MINIMUM] at *
    omega
  · simp only [hc, reduceIte]
    simp only [Execution.Fees.GasLimit.LIMIT_ADJUSTMENT_FACTOR,
      Execution.Fees.GasLimit.LIMIT_MINIMUM] at *
    omega

/-- A build that succeeds went through each of its steps.

The parent is the last recent block, and the fork is the active fork after it at the timestamp.

The block is the header filled from its body, with the transactions and the withdrawals. -/
private theorem buildBlock_spec
    (h : buildBlock chain attributes choices transactions = .ok (block, post)) :
    ¬ .hegota ≤ fork ∧ ∃ parent parentHash hashes output roots,
      chain.recent.getLast? = some parent ∧
      chain.config.activeFork (parent.header.number + 1) attributes.timestamp.toNat = some fork ∧
      parent.header.hash = .ok parentHash ∧ recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config
        (blockEnvironment chain.config hashes
          (buildHeader chain.config parent parentHash attributes choices))
        ⟨buildHeader chain.config parent parentHash attributes choices, transactions, [],
          attributes.withdrawals⟩ ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      outputRoots transactions attributes.withdrawals output output.block.applyChanges =
        .ok roots ∧
      checkBlock chain.config false chain.recent block = .ok () ∧
      firstFailure (outputChecks block.header output roots) = .ok () ∧
      block = ⟨fillHeader (buildHeader chain.config parent parentHash attributes choices) output
        roots, transactions, [], attributes.withdrawals⟩ ∧
      post = output.block.applyChanges := by
  have hH : ¬ .hegota ≤ fork := by
    intro hc; simp [buildBlock, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [buildBlock, hH, reduceIte] at h
  split at h
  next parent hP =>
    split at h
    next hA =>
      simp only [bind_ok_iff] at h
      obtain ⟨parentHash, hHash, hashes, hR, output, hB, roots, hO, u, hC, v, hF, hEq⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      have hHash' : parent.header.hash = .ok parentHash := by
        cases hp : parent.header.hash <;> simp_all [Except.mapError]
      exact ⟨hH, parent, parentHash, hashes, output, roots, hP, hA, hHash', hR, hB, hO, hC, hF,
        rfl, rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A built block passes the state transition of its chain, without the proof of work.

The state after it is the state that the build gives. -/
theorem stateTransition_of_buildBlock
    (h : buildBlock chain attributes choices transactions = .ok (block, post)) :
    stateTransition chain block false = .ok post := by
  obtain ⟨hH, parent, parentHash, hashes, output, roots, -, hA, -, hR, hB, hO, hC, hF, rfl, rfl⟩ :=
    buildBlock_spec h
  have hB' : applyBody chain.config (blockEnvironment chain.config hashes
      (fillHeader (buildHeader chain.config parent parentHash attributes choices) output roots))
      ⟨fillHeader (buildHeader chain.config parent parentHash attributes choices) output roots,
        transactions, [], attributes.withdrawals⟩ ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output :=
    hB
  simp only [stateTransition, hH, reduceIte, bind, Except.bind, pure, Except.pure]
  have hNum : (fillHeader (buildHeader chain.config parent parentHash attributes choices)
      output roots).number = parent.header.number + 1 := rfl
  have hTs : (fillHeader (buildHeader chain.config parent parentHash attributes choices)
      output roots).timestamp.toNat = attributes.timestamp.toNat :=
    toNat_ofNat_timestamp attributes.timestamp
  rw [hNum, hTs]
  simp only [hA, reduceIte, hC, hR, hB', hO, hF]

/-- A built block carries the fields of the attributes and of the builder's choices.

It holds the timestamp, the RANDAO mix, the withdrawals, the parent beacon block root and the slot.

It holds the fee recipient, the extra data and the transactions that the builder chose.

Its parent is the last recent block, and its gas limit moves from the parent's toward the target.
-/
theorem buildBlock_fields
    (h : buildBlock chain attributes choices transactions = .ok (block, post)) :
    block.header.timestamp.toNat = attributes.timestamp.toNat ∧
      block.header.prevRandao = attributes.prevRandao ∧
      block.withdrawals = attributes.withdrawals ∧
      block.header.parentBeaconBlockRoot = attributes.parentBeaconBlockRoot ∧
      block.header.slotNumber = attributes.slotNumber ∧
      block.header.coinbase = choices.feeRecipient ∧
      block.header.extraData = choices.extraData ∧
      block.transactions = transactions ∧
      ∃ parent, chain.recent.getLast? = some parent ∧
        parent.header.hash = .ok block.header.parentHash ∧
        block.header.number = parent.header.number + 1 ∧
        block.header.gasLimit = gasLimitToward
          (Execution.Fees.GasLimit.parentGasLimitForCheck parent.fork fork parent.header.gasLimit)
          (gasTarget attributes choices) := by
  obtain ⟨-, parent, parentHash, -, -, -, hP, -, hHash, -, -, -, -, -, rfl, rfl⟩ :=
    buildBlock_spec h
  exact ⟨toNat_ofNat_timestamp attributes.timestamp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, parent,
    hP, hHash, rfl, rfl⟩

/-- `engine_newPayload` answers that a built block is valid, on the chain that it was built on.

The payload must pass the checks of the method before execution, with the built block.

The latest valid hash is the block's own hash, and the state after it is the state of the build.
-/
theorem newPayloadOnChain_of_buildBlock {version : Nat} {params : Lean.Json}
    {checked : CheckedBlock version} {attributes : PayloadAttributes checked.fork}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (h : buildBlock chain attributes choices transactions = .ok (checked.block, post)) :
    newPayloadOnChain chain version params =
      .ok (⟨.valid, checked.block.header.hash.toOption⟩, none,
        some (⟨checked.fork, checked.block.header, []⟩, post)) := by
  obtain ⟨-, -, -, -, -, -, -, -, parent, hP, hHash, -⟩ := buildBlock_fields h
  exact newPayloadOnChain_of_stateTransition_ok hCheck hP hHash (stateTransition_of_buildBlock h)

end EthLib.Engine
