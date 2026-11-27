module

public import EthLib.Execution.Proofs.Blocks.Reaches
public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Transactions.StorageInvariant

/-!
# Proofs: an invariant of the storage of a contract holds in every state that a chain reaches

Take an account with a nonce of at least 1 that holds a given code, and an invariant of its storage.

From Cancun, if each call that runs that code there keeps the invariant, every block keeps it.

So the invariant holds in every state that a chain reaches through such blocks.

From Hegotá no block runs, so the theorems say nothing there.

The proof assumes that no other code has the Keccak-256 hash of the given code.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Transactions

variable {fork : Fork} {address : Address} {code : ByteArray} {Inv : (Bytes32 → U256) → Prop}

/-! ## The steps of a block outside its messages -/

/-- A state that joins its block keeps the account and the invariant at `address`. -/
theorem liveAt_incorporate {tx : TransactionState} (h : LiveAt address code Inv tx) :
    LiveAt address code Inv (.ofBlock tx.incorporateTxIntoBlock.parent) := by
  have hacc : (TransactionState.ofBlock tx.incorporateTxIntoBlock.parent).getAccount address =
      tx.getAccount address := by
    simp only [getAccount]
    exact congrArg (fun o => Option.getD o State.EMPTY_ACCOUNT)
      (getAccountOptional_incorporateTxIntoBlock tx address)
  obtain ⟨⟨⟨hhash, hcode⟩, hinv⟩, hnonce⟩ := h
  refine ⟨⟨⟨by rw [hacc]; exact hhash, (getCode_incorporateTxIntoBlock tx _).trans hcode⟩, ?_⟩,
    by rw [hacc]; exact hnonce⟩
  rw [show (TransactionState.ofBlock tx.incorporateTxIntoBlock.parent).getStorage address =
    tx.getStorage address from funext (getStorage_incorporateTxIntoBlock tx address)]
  exact hinv

/-- A state that joins a body keeps the account and the invariant at `address`. -/
theorem liveAt_join {body body' : BodyState} {tx : TransactionState}
    (h : LiveAt address code Inv tx) (hj : body.join tx = .ok body') :
    LiveAt address code Inv (.ofBlock body'.block) := by
  unfold BodyState.join at hj
  obtain ⟨builder, -, hj⟩ := bind_ok_iff.mp hj
  cases hj
  exact liveAt_incorporate h

/-- A step on a block, run as a transaction of its own, keeps the account at `address`.

The step must keep the account that holds `code`, and lower no nonce. -/
theorem liveAt_onBlock {block block' : BlockState}
    {step : TransactionState → Except State.StateError TransactionState}
    (keeps : ∀ tx tx', step tx = .ok tx' → KeepsAt address code tx tx' ∧ NonceLe tx tx')
    (h : onBlock block step = .ok block') (live : LiveAt address code Inv (.ofBlock block)) :
    LiveAt address code Inv (.ofBlock block') := by
  obtain ⟨tx, htx, rfl⟩ := onBlock_eq_ok h
  obtain ⟨k, n⟩ := keeps _ _ htx
  exact liveAt_incorporate (live.of_keepsAt k n)

/-- New ether at each of a list of addresses keeps the account that holds `code`. -/
theorem keepsAt_foldlM_createEther (hyp : CodeHyp code) {β : Type} (f : β → Address)
    (g : β → U256) : ∀ {l : List β} {tx tx' : TransactionState},
      l.foldlM (fun tx b => tx.createEther fork (f b) (g b)) tx = .ok tx' →
      KeepsAt address code tx tx' ∧ NonceLe tx tx'
  | [], _, _, h => by
    cases h
    exact ⟨.refl _, .refl _⟩
  | _ :: _, _, _, h => by
    obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
    obtain ⟨k, n⟩ := keepsAt_foldlM_createEther hyp f g h
    exact ⟨(keepsAt_createEther hyp hmid).trans k, (nonceLe_createEther hmid).trans n⟩

/-- The rewards of a block keep the account that holds `code`. -/
theorem keepsAt_payRewards (hyp : CodeHyp code) {tx tx' : TransactionState} {coinbase : Address}
    {number : Nat} {ommers : List (Address × Nat)}
    (h : payRewards fork tx coinbase number ommers = .ok tx') :
    KeepsAt address code tx tx' ∧ NonceLe tx tx' := by
  unfold payRewards at h
  split at h
  · cases h
    exact ⟨.refl _, .refl _⟩
  · obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
    obtain ⟨k, n⟩ := keepsAt_foldlM_createEther hyp _ _ h
    exact ⟨(keepsAt_createEther hyp hmid).trans k, (nonceLe_createEther hmid).trans n⟩

/-- The DAO transfer keeps the account that holds `code`. -/
theorem keepsAt_applyDaoFork (hyp : CodeHyp code) {tx tx' : TransactionState}
    (h : applyDaoFork fork tx = .ok tx') : KeepsAt address code tx tx' ∧ NonceLe tx tx' := by
  unfold applyDaoFork at h
  exact foldlM_ok_invariant (fun s => KeepsAt address code tx s ∧ NonceLe tx s)
    (fun _ _ _ hs hstep => ⟨hs.1.trans (keepsAt_moveEther hyp hstep),
      hs.2.trans (nonceLe_moveEther hstep)⟩) ⟨.refl _, .refl _⟩ h

/-! ## The messages of a block -/

/-- A system call keeps the invariant and the account at `address`.

Each call that runs `code` at `address` must keep them, with the gas meter of the fork. -/
theorem liveAt_systemCall (hyp : CodeHyp code)
    (frames : fork < .glamsterdam → FramesKeepCode address code fork Nat Inv)
    (framesState : .glamsterdam ≤ fork → FramesKeepCode address code fork StateGasMeter Inv)
    {env : BlockEnvironment fork} {block : BlockState} {target : Address} {data : ByteArray}
    {out : SystemCallOutput} (h : systemCall env block target data = .ok out)
    (live : LiveAt address code Inv (.ofBlock block)) : LiveAt address code Inv out.state := by
  -- The message of the call runs at its target.
  have recipient : ∀ to, (systemMessage env target data).target = some to →
      to = (systemMessage env target data).currentTarget := fun _ hto => (Option.some.inj hto).symm
  -- A system call starts from the block, where no account is created yet.
  have fresh : address ∉ (TransactionState.ofBlock block).createdAccounts := by
    simp [TransactionState.ofBlock]
  unfold systemCall at h
  dsimp only at h
  split at h
  · rename_i hglam
    obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    exact (liveAt_processMessageCall hyp (framesState hglam) recipient hcall live fresh).1
  · rename_i hglam
    obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    exact (liveAt_processMessageCall hyp (frames (Nat.lt_of_not_le hglam)) recipient hcall live
      fresh).1

/-! ## A block -/

section Block

variable (hyp : CodeHyp code) (hfork : .dencun ≤ fork)
  (frames : fork < .glamsterdam → FramesKeepCode address code fork Nat Inv)
  (framesState : .glamsterdam ≤ fork → FramesKeepCode address code fork StateGasMeter Inv)
include hyp hfork frames framesState

/-- From Cancun, the body of a block keeps the invariant and the account at `address`.

Each call that runs `code` at `address` must keep them, with the gas meter of the fork. -/
theorem liveAt_applyBody {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output)
    (live : LiveAt address code Inv (.ofBlock start)) :
    LiveAt address code Inv (.ofBlock output.block) := by
  let P : BlockState → Prop := fun b => LiveAt address code Inv (.ofBlock b)
  have call : ∀ {b : BlockState} {target : Address} {data : ByteArray} {out : SystemCallOutput},
      P b → systemCall env b target data = .ok out → LiveAt address code Inv out.state :=
    fun hb hout => liveAt_systemCall hyp frames framesState hout hb
  obtain ⟨state, body, txs, withdrawn, requested, hState, hBody, hTxs, hW, hNotW, hRequests,
    hRewards, -⟩ := applyBody_eq_ok h
  -- The DAO transfer.
  have h₀ : P state := by
    unfold daoTransfer at hState
    split at hState
    · exact liveAt_onBlock (fun _ _ => keepsAt_applyDaoFork hyp) hState live
    · cases hState
      exact live
  -- The system calls at the start.
  have h₁ : P body.block := by
    obtain ⟨mid, hFirst, hNoFirst, hSecond, hNoSecond⟩ := startSystemCalls_eq_ok hBody
    have hmid : P mid.block := by
      by_cases hDencun : .dencun ≤ fork
      · obtain ⟨out, hOut, hJoin⟩ := hFirst hDencun
        exact liveAt_join (call h₀ hOut) hJoin
      · rw [hNoFirst hDencun]
        exact h₀
    by_cases hPectra : .pectra ≤ fork
    · obtain ⟨out, hOut, hJoin⟩ := hSecond hPectra
      exact liveAt_join (call hmid hOut) hJoin
    · rw [hNoSecond hPectra]
      exact hmid
  -- The transactions.
  have h₂ : P txs.body.block := by
    unfold applyTransactions at hTxs
    refine foldlM_ok_invariant (fun before : BodyOutput fork => P before.body.block)
      (fun before _ after hb hstep => ?_) h₁ hTxs
    obtain ⟨included, out, -, hRun, -, -, hJoin⟩ := applyTransaction_eq_ok hstep
    exact liveAt_join (liveAt_processTransaction hyp hfork frames framesState hRun hb) hJoin
  -- The withdrawals.
  have h₃ : P withdrawn.block := by
    by_cases hShapella : .shapella ≤ fork
    · obtain ⟨tx, hTx, hJoin⟩ := hW hShapella
      obtain ⟨k, n⟩ := keepsAt_foldlM_createEther hyp _ _ hTx
      exact liveAt_join (h₂.of_keepsAt k n) hJoin
    · rw [hNotW hShapella]
      exact h₂
  -- The requests.
  have h₄ : P requested.block := by
    obtain ⟨hNoPectra, hPectra⟩ := blockRequests_eq_ok hRequests
    by_cases hp : .pectra ≤ fork
    · obtain ⟨_, read, -, hRead, hResult⟩ := hPectra hp
      obtain ⟨rfl, -⟩ := Prod.mk.inj hResult
      refine foldlM_ok_invariant (fun s : BodyState × List ByteArray => P s.1.block)
        (fun s _ s' hs hstep => ?_) h₃ hRead
      obtain ⟨out, hOut, hJoin, -⟩ := readRequest_eq_ok hstep
      exact liveAt_join (call hs (checkedSystemCall_ok hOut).2.1) hJoin
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (hNoPectra hp)
      exact h₃
  -- The rewards.
  exact liveAt_onBlock (fun _ _ => keepsAt_payRewards hyp) hRewards h₄

/-- From Cancun, a block that passes its transition keeps the invariant and the account.

Each call that runs `code` at `address` must keep them, with the gas meter of the fork. -/
theorem liveAt_stateTransition {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post)
    (live : LiveAt address code Inv (.ofBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩)) :
    LiveAt address code Inv (.ofBlock ⟨post, ∅, ∅, ∅, ∅⟩) := by
  obtain ⟨-, -, -, _, output, _, -, hbody, -, -, rfl⟩ := stateTransition_eq_ok h
  obtain ⟨⟨⟨hhash, hcode⟩, hinv⟩, hnonce⟩ :=
    liveAt_applyBody hyp hfork frames framesState hbody live
  have hacc := State.BlockState.getAccount_applyChanges output.block address
  refine ⟨⟨⟨by rw [hacc]; exact hhash, ?_⟩, ?_⟩, by rw [hacc]; exact hnonce⟩
  · have e : (TransactionState.ofBlock ⟨output.block.applyChanges, ∅, ∅, ∅, ∅⟩).getCode
        (Cryptography.Hash.Keccak.keccak256 code) =
          output.block.applyChanges.getCode (Cryptography.Hash.Keccak.keccak256 code) := by
      simp only [TransactionState.getCode, TransactionState.ofBlock]
      split
      · rename_i empty
        simp [State.getCode, empty]
      · rfl
    rw [e]
    exact (State.BlockState.getCode_applyChanges _ _).trans hcode
  · have hs : (TransactionState.ofBlock ⟨output.block.applyChanges, ∅, ∅, ∅, ∅⟩).getStorage
        address = (TransactionState.ofBlock output.block).getStorage address := by
      funext key
      refine Eq.trans ?_ (State.BlockState.getStorage_applyChanges _ _ _)
      simp [TransactionState.getStorage, TransactionState.ofBlock, State.StorageMap.slot]
    rw [hs]
    exact hinv

end Block

/-! ## Every state that a chain reaches -/

/-- An invariant of the storage of a contract holds in every state that a chain reaches.

The blocks must run at forks from Cancun on.

At each of these forks, each call that runs `code` at `address` must keep the invariant.

The account must hold `code` and a nonce of at least 1, and meet the invariant, where they start. -/
theorem BlockChain.Reaches.liveAt (hyp : CodeHyp code) {forks : Fork → Prop}
    (hforks : ∀ fork, forks fork → .dencun ≤ fork)
    (frames : ∀ fork, forks fork → fork < .glamsterdam →
      FramesKeepCode address code fork Nat Inv)
    (framesState : ∀ fork, forks fork → .glamsterdam ≤ fork →
      FramesKeepCode address code fork StateGasMeter Inv)
    {chain chain' : BlockChain} (reaches : chain.Reaches forks chain')
    (start : LiveAt address code Inv (.ofBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩)) :
    LiveAt address code Inv (.ofBlock ⟨chain'.state, ∅, ∅, ∅, ∅⟩) :=
  reaches.invariant (P := fun state => LiveAt address code Inv (.ofBlock ⟨state, ∅, ∅, ∅, ∅⟩))
    (fun hfork transition live => liveAt_stateTransition hyp (hforks _ hfork) (frames _ hfork)
      (framesState _ hfork) transition live) start

end EthLib.Execution.Blocks
