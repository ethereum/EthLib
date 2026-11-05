module

public import EthLib.Execution.Transactions.Process

/-!
# Proofs: the start of a transaction

From Berlin, a transaction starts with these addresses accessed:

- every precompile of its fork;
- its sender, and its recipient or the address it creates;
- each address of its access list;
- from Shapella, the beneficiary of its block.

Before Berlin, it starts with no access.

A first frame that fails to start halts the message with the state from before it.

The sender then keeps its higher nonce and its fee, and gets back the whole reservoir.

Up to BPO5, a transaction runs with one counter of the gas left.

From Glamsterdam, a run fails as not yet specified, so no caller gets the rules of BPO5 there.
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

/-- From Glamsterdam, a transaction fails to run, since the rules of that fork are not here yet. -/
theorem processTransaction_of_glamsterdam_le {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} (h : .glamsterdam ≤ fork) :
    processTransaction env block included tx = .error (.forkNotYetSpecified fork) := by
  simp only [processTransaction, h, ↓reduceIte]
  rfl

/-! ## The first frame -/

variable {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {chainId : Nat}
  {message : Message fork} {state : State.TransactionState} {substate : Substate}
  {auths : List Authorization} {paid : Std.ExtTreeSet Address}

/-- A message whose first frame fails to start halts with the state from before it.

So a transaction keeps the nonce and the fee of its sender, which come before its message.

No execution gas is left, the reservoir comes back whole, and no state gas is used. -/
theorem processMessageCall_of_halt {e : EvmError}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid = .error e)
    (halts : e.aborts = false) :
    processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok (.ofHalt state message.reservoir e) := by
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
  simp only [processTransaction, hpre, ↓reduceIte, GE.ge]

end EthLib.Execution.Transactions
