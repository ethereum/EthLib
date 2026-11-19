module

public import EthLib.Execution.Proofs.Blocks.AccessListComplete
public import EthLib.Execution.Proofs.Blocks.CallsAgree
public import EthLib.Execution.Proofs.Transactions.NoninterferenceRun

/-!
# Proofs: each transaction and call of a block depends only on what its access list names

From Glamsterdam, a block that passes the transition commits to a block access list.

Run one of its transactions on another block state instead.

That state must agree with the one the transaction ran on, at what the list names.

It must also agree on the code and, for each named account with nonce 0 and no code, the storage.

The list names neither the code nor that storage.

The other state must also hold the code of every account.

Then the transaction is accepted alike, and gives the same gas used, block gas, logs and error.

The states it leaves agree on what the list names, with the same tracker.

The same holds for the calls of the body that are not transactions.

These are the two system calls at its start, the withdrawals and the calls to the request contracts.

None of them needs the other state to hold the code of every account.

Source: [EIP-7928, Scope and Inclusion][bal].

[bal]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState EMPTY_CODE_HASH TransactionState)
open EthLib.Execution.Transactions

/-- The named accounts that have nonce 0 and no code in the block state.

A creation at such an account reads its whole storage, by [EIP-7610][eip7610].

The list names no key of that storage.

[eip7610]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7610.md#specification -/
def BlockAccessList.NamesCandidate (bal : BlockAccessList) (block : BlockState)
    (address : Address) : Prop :=
  bal.NamesAccount address ∧ ((TransactionState.ofBlock block).getAccount address).nonce = 0 ∧
    ((TransactionState.ofBlock block).getAccount address).codeHash = EMPTY_CODE_HASH

/-- The code hashes in the block state of the accounts that the list names. -/
def BlockAccessList.NamesCode (bal : BlockAccessList) (block : BlockState)
    (codeHash : Hash32) : Prop :=
  ∃ address, bal.NamesAccount address ∧
    ((TransactionState.ofBlock block).getAccount address).codeHash = codeHash

/-- Two block states agree on what a list names.

They agree on each named account and named storage key.

They agree on the whole storage of each named account with nonce 0 and no code in the first.

They agree on the code under the code hash, in the first block state, of each named account. -/
abbrev _root_.EthLib.Execution.State.BlockState.AgreesOnList (bal : BlockAccessList)
    (block other : BlockState) : Prop :=
  BlockState.AgreesOn bal.NamesAccount (bal.NamesCandidate block) bal.NamesKey
    (bal.NamesCode block) block other

/-- Two transaction states agree on what a list names, for runs from the block state `block`.

They agree on each named account and named storage key, with the same tracker.

They agree on the whole storage of each named account with nonce 0 and no code in `block`.

They agree on the code under the code hash, in `block`, of each named account. -/
abbrev _root_.EthLib.Execution.State.TransactionState.AgreesOnList (bal : BlockAccessList)
    (block : BlockState) (tx other : TransactionState) : Prop :=
  TransactionState.AgreesOn bal.NamesAccount (bal.NamesCandidate block) bal.NamesKey
    (bal.NamesCode block) tx other

/-- A list that covers a transaction state names everything that the state read. -/
private theorem BlockAccessList.Covers.readsIn {bal : BlockAccessList} {tx : TransactionState}
    (h : bal.Covers tx) : ReadsIn bal.NamesAccount bal.NamesKey tx := by
  refine ⟨h.accountRead, fun address key hkey => ?_⟩
  cases hkeys : tx.storageReads[address]? with
  | none => simp [Std.ExtTreeMap.getD_eq_getD_getElem?, hkeys] at hkey
  | some keys =>
    exact h.keyRead address keys key hkeys
      (by simpa [Std.ExtTreeMap.getD_eq_getD_getElem?, hkeys] using hkey)

/-- A transaction accepted on one state is accepted alike on a state with the same sender.

That state must hold the same account at the sender, and the same code under its code hash. -/
private theorem checkInclusion_of_sender {fork : Fork} {chainId : UInt64}
    {env : BlockEnvironment fork} {used : BlockGas} {state other : TransactionState}
    {tx : Transaction} {included : Included}
    (h : checkInclusion chainId env used state tx = .ok included)
    (hAccount : other.getAccount included.sender = state.getAccount included.sender)
    (hCode : other.getCode (state.getAccount included.sender).codeHash =
      state.getCode (state.getAccount included.sender).codeHash) :
    checkInclusion chainId env used other tx = .ok included := by
  have hSender : ∀ sender signed, sender = included.sender →
      checkSender fork other sender tx signed = checkSender fork state sender tx signed := by
    rintro _ _ rfl
    unfold checkSender
    dsimp only
    rw [hAccount, hCode]
  unfold checkInclusion at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hg
    rw [ite_eq_left_of_eq_true _ _ (eq_true hg)]
    obtain ⟨_, h1, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h5, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h6, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h7, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h8, h⟩ := bind_ok_iff.mp h
    cases h
    rw [← hSender _ _ rfl] at h8
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, bind, Except.bind]
    rfl
  · rename_i hg
    rw [ite_eq_right_of_eq_false _ _ (eq_false hg)]
    obtain ⟨_, h1, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h5, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h6, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h7, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h8, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, h9, h⟩ := bind_ok_iff.mp h
    cases h
    rw [← hSender _ _ rfl] at h9
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, bind, Except.bind]
    rfl

/-- From Glamsterdam, each transaction of a block that passes depends only on what its list names.

The list is the one whose hash the header commits to.

The transaction at index `i`, from 0, runs after the system calls and the transactions before it.

Take another block state that agrees with the state before it on what the list names.

The transaction is accepted alike there.

It gives the same gas, logs and error, and a state that agrees on what the list names.

The other block state must hold the code of every account.

From Hegotá the transition is not yet specified, so this holds from Glamsterdam up to Hegotá. -/
theorem stateTransition_transaction_agrees {fork : Fork} {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State.State}
    (hFork : .glamsterdam ≤ fork) (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes env output body,
      recentHashes chain.recent = .ok hashes ∧
      env = blockEnvironment chain.config hashes block.header ∧
      applyBody chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      BlockAccessList.hash output.body.builder.build =
        .ok (block.header.blockAccessListHash hFork) ∧
      startSystemCalls env block.header.parentHash (.init ⟨chain.state, ∅, ∅, ∅, ∅⟩) = .ok body ∧
      ∀ i (hi : i < block.transactions.length), ∃ before included out,
        applyTransactions env body (block.transactions.take i) = .ok before ∧
        checkInclusion env.chainId env before.gas (.ofBlock before.block)
          block.transactions[i] = .ok included ∧
        processTransaction env before.block included block.transactions[i] = .ok out ∧
        ∀ other, BlockState.AgreesOnList output.body.builder.build before.block other →
          Transactions.HasCodes (.ofBlock other) →
          checkInclusion env.chainId env before.gas (.ofBlock other) block.transactions[i] =
            .ok included ∧
          ∃ out', processTransaction env other included block.transactions[i] = .ok out' ∧
            out' = { out with state := out'.state } ∧
            TransactionState.AgreesOnList output.body.builder.build before.block
              out.state out'.state := by
  obtain ⟨hashes, env, output, body, -, -, hHashes, hEnv, hOutput, hBal, -, hStart, -, hTx, -, -⟩ :=
    stateTransition_accessList_covers hFork h
  refine ⟨hashes, env, output, body, hHashes, hEnv, hOutput, hBal, hStart, fun i hi => ?_⟩
  obtain ⟨before, included, out, hBefore, hIncluded, hRun, hCovers⟩ := hTx i hi
  refine ⟨before, included, out, hBefore, hIncluded, hRun, fun other hagree hcodes => ?_⟩
  have hParis : Fork.paris ≤ fork := Nat.le_trans (by decide) hFork
  have hSender := hCovers.accountRead _ (sender_mem_processTransaction hParis hRun)
  have hFresh := TransactionState.AgreesOn.ofBlock hagree
  refine ⟨checkInclusion_of_sender hIncluded (hFresh.getAccount_eq (.inr hSender))
    (hFresh.getCode_eq (.inr (.inr ⟨_, hSender, rfl⟩))), ?_⟩
  exact processTransaction_agrees hParis
    ⟨fun address h => ⟨address, h, rfl⟩, fun _ h hnonce hcode => ⟨h, hnonce, hcode⟩⟩
    hagree hcodes hRun hCovers.readsIn

/-- From Glamsterdam, the calls of a block that passes depend only on what its list names.

The list is the one whose hash the header commits to.

They are the two system calls at the start, the withdrawals and each call to a request contract.

Run one of them on another block state that agrees with its own on what the list names.

A system call gives the same output there, and a state that agrees on what the list names.

The withdrawals give a state that agrees on what the list names.

From Hegotá the transition is not yet specified, so this holds from Glamsterdam up to Hegotá. -/
theorem stateTransition_calls_agree {fork : Fork} {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State.State}
    (hFork : .glamsterdam ≤ fork) (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes env output body txOutput withdrawn,
      recentHashes chain.recent = .ok hashes ∧
      env = blockEnvironment chain.config hashes block.header ∧
      applyBody chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      BlockAccessList.hash output.body.builder.build =
        .ok (block.header.blockAccessListHash hFork) ∧
      (∃ out mid out',
        systemCall env ⟨chain.state, ∅, ∅, ∅, ∅⟩ BEACON_ROOTS_ADDRESS
          ⟨(block.header.parentBeaconBlockRoot (Nat.le_trans (by decide) hFork)).toArray⟩ =
          .ok out ∧
        (BodyState.init ⟨chain.state, ∅, ∅, ∅, ∅⟩).join out.state = .ok mid ∧
        systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨block.header.parentHash.toArray⟩ =
          .ok out' ∧
        (∀ other,
          BlockState.AgreesOnList output.body.builder.build ⟨chain.state, ∅, ∅, ∅, ∅⟩ other →
          ∃ o, systemCall env other BEACON_ROOTS_ADDRESS
              ⟨(block.header.parentBeaconBlockRoot (Nat.le_trans (by decide) hFork)).toArray⟩ =
              .ok o ∧ o = { out with state := o.state } ∧
            TransactionState.AgreesOnList output.body.builder.build ⟨chain.state, ∅, ∅, ∅, ∅⟩
              out.state o.state) ∧
        ∀ other, BlockState.AgreesOnList output.body.builder.build mid.block other →
          ∃ o, systemCall env other HISTORY_STORAGE_ADDRESS ⟨block.header.parentHash.toArray⟩ =
              .ok o ∧ o = { out' with state := o.state } ∧
            TransactionState.AgreesOnList output.body.builder.build mid.block out'.state o.state) ∧
      startSystemCalls env block.header.parentHash (.init ⟨chain.state, ∅, ∅, ∅, ∅⟩) = .ok body ∧
      applyTransactions env body block.transactions = .ok txOutput ∧
      (∃ tx,
        withdrawalState fork txOutput.body.block
          (block.withdrawals (Nat.le_trans (by decide) hFork)) = .ok tx ∧
        (txOutput.body.beginIndex (block.transactions.length + 1)).join tx = .ok withdrawn ∧
        ∀ other, BlockState.AgreesOnList output.body.builder.build txOutput.body.block other →
          ∃ tx', withdrawalState fork other
              (block.withdrawals (Nat.le_trans (by decide) hFork)) = .ok tx' ∧
            TransactionState.AgreesOnList output.body.builder.build txOutput.body.block tx tx') ∧
      ∀ j (hj : j < (requestContracts fork).length), ∃ mid out,
        ((requestContracts fork).take j).foldlM (readRequest env) (withdrawn, []) = .ok mid ∧
        checkedSystemCall env mid.1.block (requestContracts fork)[j].2 .empty = .ok out ∧
        ∀ other, BlockState.AgreesOnList output.body.builder.build mid.1.block other →
          ∃ o, checkedSystemCall env other (requestContracts fork)[j].2 .empty = .ok o ∧
            o = { out with state := o.state } ∧
            TransactionState.AgreesOnList output.body.builder.build mid.1.block
              out.state o.state := by
  obtain ⟨hashes, env, output, body, txOutput, withdrawn, hHashes, hEnv, hOutput, hBal,
    ⟨out, mid, out', hOut, hMid, hOut', hCovers, hCovers'⟩, hStart, hTx, -,
    ⟨tx, hWithdrawn, hJoin, hCoversTx⟩, hRequests⟩ := stateTransition_accessList_covers hFork h
  have covers (b : BlockState) : CoversBlock b output.body.builder.build.NamesAccount
      (output.body.builder.build.NamesCandidate b) (output.body.builder.build.NamesCode b) :=
    ⟨fun address h => ⟨address, h, rfl⟩, fun _ h hnonce hcode => ⟨h, hnonce, hcode⟩⟩
  refine ⟨hashes, env, output, body, txOutput, withdrawn, hHashes, hEnv, hOutput, hBal,
    ⟨out, mid, out', hOut, hMid, hOut',
      fun _ hagree => systemCall_agrees (covers _) hagree hOut hCovers.readsIn,
      fun _ hagree => systemCall_agrees (covers _) hagree hOut' hCovers'.readsIn⟩,
    hStart, hTx,
    ⟨tx, hWithdrawn, hJoin, fun _ hagree => withdrawalState_agrees hagree hWithdrawn
      hCoversTx.readsIn⟩, fun j hj => ?_⟩
  obtain ⟨mid, out, hMid, hCall, hCoversCall⟩ := hRequests j hj
  exact ⟨mid, out, hMid, hCall,
    fun _ hagree => checkedSystemCall_agrees (covers _) hagree hCall hCoversCall.readsIn⟩

end EthLib.Execution.Blocks
