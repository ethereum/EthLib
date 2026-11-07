module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Transactions.Settlement
public import EthLib.Execution.Transactions.Process

/-!
# Proofs: the start of a transaction, and its gas used

From Berlin, a transaction starts with these addresses accessed:

- every precompile of its fork;
- its sender, and its recipient or the address it creates;
- each address of its access list;
- from Shapella, the beneficiary of its block.

Before Berlin, it starts with no access.

A first frame that fails to start halts the message with the state from before it.

The sender then keeps its higher nonce and its fee, and gets back the whole reservoir.

Up to BPO5, a transaction runs with one counter of the gas left.

At Glamsterdam, it runs with the meter of EIP-8037.

From Hegotá, a run fails as not yet specified, so no caller gets the rules of Glamsterdam there.

From Pectra to BPO5, a run uses its gas limit minus the gas that its message leaves, less a refund.

The refund is the refund counter of the message, at most a fifth of the gas used before it.

The gas used is never below the call data floor.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm

variable {fork : Fork} {coinbase sender target : Address} {tx : Transaction}

/-- An address of the sender, the target or the precompiles is in the start set. -/
theorem mem_startAccessedAddresses_of_mem {address : Address} (h : .berlin ≤ fork)
    (mem : address ∈ (((∅ : Std.ExtTreeSet Address).insert sender).insert target).insertMany
      (precompileAddresses fork)) :
    address ∈ startAccessedAddresses fork coinbase sender target tx := by
  simp only [startAccessedAddresses, h, ↓reduceIte]
  split <;> simp only [Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.mem_insertMany_list] <;>
    simp_all

/-- From Berlin, a transaction starts with its sender accessed. -/
theorem sender_mem_startAccessedAddresses (h : .berlin ≤ fork) :
    sender ∈ startAccessedAddresses fork coinbase sender target tx :=
  mem_startAccessedAddresses_of_mem h (by simp)

/-- From Berlin, a transaction starts with its recipient, or the address it creates, accessed. -/
theorem target_mem_startAccessedAddresses (h : .berlin ≤ fork) :
    target ∈ startAccessedAddresses fork coinbase sender target tx :=
  mem_startAccessedAddresses_of_mem h (by simp)

/-- An address that some fork adds a precompile at is among the addresses of the table. -/
theorem mem_ADDRESSES_of_addedAt {address : Nat} {added : Fork}
    (h : Precompiles.addedAt address = some added) : address ∈ Precompiles.ADDRESSES := by
  unfold Precompiles.addedAt at h
  split at h <;> simp_all [Precompiles.ADDRESSES]

/-- Each precompile address is among the addresses of the table. -/
theorem mem_ADDRESSES_of_isPrecompile {address : Nat}
    (h : Precompiles.isPrecompile fork address) : address ∈ Precompiles.ADDRESSES := by
  unfold Precompiles.isPrecompile at h
  split at h
  · exact mem_ADDRESSES_of_addedAt (by assumption)
  · simp at h

/-- From Berlin, a transaction starts with every precompile of its fork accessed. -/
theorem precompile_mem_startAccessedAddresses {address : Nat} (h : .berlin ≤ fork)
    (precompile : Precompiles.isPrecompile fork address) :
    toAddressMasked (BitVec.ofNat 256 address) ∈
      startAccessedAddresses fork coinbase sender target tx := by
  refine mem_startAccessedAddresses_of_mem h ?_
  simp only [Std.ExtTreeSet.mem_insertMany_list, List.contains_iff_mem]
  exact .inr (List.mem_map_of_mem
    (List.mem_filter.mpr ⟨mem_ADDRESSES_of_isPrecompile precompile, precompile⟩))

/-- From Berlin, a transaction starts with each address of its access list accessed. -/
theorem access_mem_startAccessedAddresses {access : Access} (h : .berlin ≤ fork)
    (mem : access ∈ tx.accesses) :
    access.account ∈ startAccessedAddresses fork coinbase sender target tx := by
  simp only [startAccessedAddresses, h, ↓reduceIte]
  have : access.account ∈ tx.accesses.map (·.account) := List.mem_map_of_mem mem
  split <;> simp only [Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.mem_insertMany_list,
    List.contains_iff_mem] <;> simp_all

/-- From Shapella, a transaction starts with the beneficiary of its block accessed.

[EIP-3651](https://eips.ethereum.org/EIPS/eip-3651#specification) adds it. -/
theorem coinbase_mem_startAccessedAddresses (h : .shapella ≤ fork) :
    coinbase ∈ startAccessedAddresses fork coinbase sender target tx := by
  have berlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) h
  simp only [startAccessedAddresses, berlin, h, ↓reduceIte]
  exact Std.ExtTreeSet.mem_insert_self

/-- Before Berlin, a transaction starts with no access, since no access counts. -/
theorem startAccessedAddresses_of_lt_berlin (h : fork < .berlin) :
    startAccessedAddresses fork coinbase sender target tx = ∅ := by
  have berlin : ¬Fork.berlin ≤ fork := Nat.not_le_of_lt h
  simp only [startAccessedAddresses, berlin, ↓reduceIte]

/-- From Hegotá, a transaction fails to run, since the rules of that fork are not here yet. -/
theorem processTransaction_of_hegota_le {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} (h : .hegota ≤ fork) :
    processTransaction env block included tx = .error (.forkNotYetSpecified fork) := by
  simp only [processTransaction, h, ↓reduceIte]

/-- At Glamsterdam, a transaction runs with the meter of EIP-8037. -/
theorem processTransaction_of_glamsterdam {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} (h : .glamsterdam ≤ fork)
    (hlt : fork < .hegota) :
    processTransaction env block included tx =
      runTransaction StateGasMeter env block included tx := by
  have hpre : ¬Fork.hegota ≤ fork := Nat.not_le_of_lt hlt
  simp only [processTransaction, hpre, h, ↓reduceIte, GE.ge]

/-! ## The first frame -/

variable {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {chainId : Nat}
  {message : Message fork} {state : State.TransactionState} {substate : Substate}
  {auths : List Authorization} {paid : Std.ExtTreeSet Address}

/-- A message whose first frame fails to start halts with the state from before it.

So a transaction keeps the nonce and the fee of its sender, which come before its message.

The halt keeps only the reads of the preparation, from the state `read`.

No execution gas is left, the reservoir comes back whole, and no state gas is used. -/
theorem processMessageCall_of_halt {e : EvmError} {read : State.TransactionState}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .error (e, read))
    (halts : e.aborts = false) :
    processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok (.ofHalt (state.withReadsOf read) message.reservoir e) := by
  simp only [processMessageCall, h, halts, Bool.false_eq_true, ↓reduceIte]

/-- A halt before the first frame leaves no execution gas, the whole reservoir and no state gas. -/
theorem ofHalt_gas (state : State.TransactionState) (reservoir : Nat) (e : EvmError) :
    (CallOutput.ofHalt state reservoir e).gasLeft = 0 ∧
      (CallOutput.ofHalt state reservoir e).reservoir = reservoir ∧
      (CallOutput.ofHalt state reservoir e).stateGasUsed = 0 ∧
      (CallOutput.ofHalt state reservoir e).state = state :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Up to BPO5, a transaction runs with one counter of the gas left. -/
theorem processTransaction_of_lt_glamsterdam {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} (h : fork < .glamsterdam) :
    processTransaction env block included tx = runTransaction Nat env block included tx := by
  have hpre : ¬Fork.glamsterdam ≤ fork := Nat.not_le_of_lt h
  have hlate : ¬Fork.hegota ≤ fork := fun hh => hpre (Nat.le_trans (by decide) hh)
  simp only [processTransaction, hlate, hpre, ↓reduceIte, GE.ge]

/-! ## The gas used -/

/-- With one counter of gas, a message given no reservoir hands back none. -/
private theorem processMessageCall_reservoir {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (h : processMessageCall (Meter := Nat) chainId { message with reservoir := 0 } state substate
      auths paid = .ok output) :
    output.reservoir = 0 := by
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      rfl
  · split at h
    · obtain ⟨⟨evm, _⟩, -, h⟩ := Base.bind_ok_iff.mp h
      cases h
      unfold CallOutput.ofFrame
      split <;> rfl
    · obtain ⟨⟨evm, _⟩, -, h⟩ := Base.bind_ok_iff.mp h
      cases h
      unfold CallOutput.ofFrame
      split <;> rfl

/-- Up to BPO5, a transaction that runs takes each step of the run, in order.

The sender buys the gas, and the message gets the gas limit minus the intrinsic gas.

The message hands back no reservoir.

The gas is then settled on the state that the message leaves, and the accounts are deleted. -/
private theorem processTransaction_eq_ok_of_lt {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {out : TransactionOutput}
    (hlt : fork < .glamsterdam) (h : processTransaction env block included tx = .ok out) :
    ∃ target bought message output settled,
      messageTarget included.sender
          ((State.TransactionState.ofBlock block).getAccount included.sender).nonce tx =
        .ok target ∧
      buyGas env (State.TransactionState.ofBlock block) included.sender tx = .ok bought ∧
      transactionMessage env ⟨included.sender, included.gasPrice, fun _ => tx.blobHashes⟩ bought
          included.sender target (tx.gas.toNat - included.intrinsicGas) tx = .ok message ∧
      processMessageCall (Meter := Nat) env.chainId.toNat { message with reservoir := 0 } bought
          (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
          (paidWrites included.sender target tx) = .ok output ∧
      settleGas env output.state included.sender tx output.gasLeft output.refund =
        .ok (settled, out.gasUsed) ∧
      deleteAccounts fork settled output = .ok out.state := by
  rw [processTransaction_of_lt_glamsterdam hlt] at h
  unfold runTransaction at h
  simp only [allocateGas_of_lt hlt] at h
  obtain ⟨target, hTarget, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨bought, hBought, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨message, hMessage, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨output, hOutput, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨settled, used⟩, hSettle, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨deleted, hDeleted, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rw [processMessageCall_reservoir hOutput, Nat.add_zero] at hSettle
  exact ⟨target, bought, message, output, settled, hTarget, Base.mapError_ok_iff.mp hBought,
    hMessage, hOutput, Base.mapError_ok_iff.mp hSettle, Base.mapError_ok_iff.mp hDeleted⟩

/-- From Pectra to BPO5, the gas used of a transaction that runs follows from its message.

The message goes to the recipient, or to the address that the creation makes.

It runs on the state after the sender buys the gas, with the gas limit minus the intrinsic gas.

The gas used is the gas limit minus the gas left and the refund.

It is the call data floor instead, when that floor is larger, by EIP-7623 from Pectra.

The refund is the refund counter of the message, at most a fifth of the gas used before it.

That fifth holds from London, by EIP-3529. -/
theorem processTransaction_gasUsed {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {out : TransactionOutput} (hPectra : .pectra ≤ fork)
    (hlt : fork < .glamsterdam) (h : processTransaction env block included tx = .ok out) :
    ∃ target bought message output,
      messageTarget included.sender
          ((State.TransactionState.ofBlock block).getAccount included.sender).nonce tx =
        .ok target ∧
      buyGas env (State.TransactionState.ofBlock block) included.sender tx = .ok bought ∧
      transactionMessage env ⟨included.sender, included.gasPrice, fun _ => tx.blobHashes⟩ bought
          included.sender target (tx.gas.toNat - included.intrinsicGas) tx = .ok message ∧
      processMessageCall (Meter := Nat) env.chainId.toNat { message with reservoir := 0 } bought
          (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
          (paidWrites included.sender target tx) = .ok output ∧
      out.gasUsed = max (tx.gas.toNat - output.gasLeft -
          min ((tx.gas.toNat - output.gasLeft) / 5) output.refund)
        (calldataFloor fork included.sender tx) := by
  obtain ⟨target, bought, message, output, _, hTarget, hBought, hMessage, hOutput, hSettle, -⟩ :=
    processTransaction_eq_ok_of_lt hlt h
  refine ⟨target, bought, message, output, hTarget, hBought, hMessage, hOutput, ?_⟩
  have hLondon : fork ≥ .london := Nat.le_trans (by decide) hPectra
  simp only [settleGas_gasUsed hSettle, gasUsed, gasRefund, maxRefundQuotient, hLondon, hPectra,
    ↓reduceIte]

end EthLib.Execution.Transactions
