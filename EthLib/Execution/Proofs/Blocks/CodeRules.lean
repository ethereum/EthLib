module

public import EthLib.Execution.Proofs.Blocks.BodyGas
public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Transactions.CodeOrigin
public import EthLib.Execution.Proofs.Transactions.CodeRules

/-!
# Proofs: every code that a block changes meets the rules of its fork

A block writes code only through the messages of its transactions and of its system calls.

From Pectra, the authorizations of its transactions also write delegation indicators.

So each account whose code changes in a block gets the empty code, or a code that the block wrote.

Codes from the genesis or from an earlier block are out of scope, as they may break the rules.

Sources: [EIP-170][eip170], [EIP-3541][eip3541], [EIP-7702][eip7702], [EIP-7954][eip7954].

[eip170]: https://eips.ethereum.org/EIPS/eip-170#specification
[eip3541]: https://eips.ethereum.org/EIPS/eip-3541#specification
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#specification
[eip7954]: https://eips.ethereum.org/EIPS/eip-7954#specification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base (Address ChainConfig Fork Hash32 U256)
open EthLib.Execution.Evm
open EthLib.Execution.State (Account BlockState EMPTY_ACCOUNT EMPTY_CODE_HASH State
  TransactionState)
open EthLib.Execution.Transactions (Transaction TxCodeRules)

variable {fork : Fork}

/-! ## A step of a transaction state -/

/-- The second state keeps the origin of the code hashes of the first, and the rules of its codes.

Each code that it writes meets the rules of the fork, or is a delegation indicator from Pectra. -/
private def Keeps (fork : Fork) (tx tx' : TransactionState) : Prop :=
  KeepsCodeOrigin tx tx' ∧ KeepsCodeRules (TxCodeRules fork) tx tx'

/-- A state keeps itself. -/
private theorem Keeps.refl (tx : TransactionState) : Keeps fork tx tx :=
  ⟨.refl tx, .refl tx⟩

/-- Two steps in a row keep the origin and the rules together. -/
private theorem Keeps.trans {a b c : TransactionState} (hab : Keeps fork a b)
    (hbc : Keeps fork b c) : Keeps fork a c :=
  ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

/-- A change of one account that keeps its code hash keeps the origin and the rules. -/
private theorem keeps_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except State.StateError Account}
    (hf : ∀ account updated, f account = .ok updated → updated.codeHash = account.codeHash)
    (h : tx.modifyState fork address f = .ok tx') : Keeps fork tx tx' :=
  ⟨.modifyState_of_keeps hf h, .of_codeWrites (codeWrites_modifyState h)⟩

/-- A creation of ether keeps the origin and the rules. -/
private theorem keeps_createEther {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.createEther fork address amount = .ok tx') : Keeps fork tx tx' :=
  keeps_modifyState (fun _ _ hf => codeHash_credit hf) h

/-- A move of ether keeps the origin and the rules. -/
private theorem keeps_moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    Keeps fork tx tx' :=
  ⟨.moveEther h, .of_codeWrites (codeWrites_moveEther h)⟩

/-- A deletion of an account keeps the origin of the code hashes.

The empty account has no code. -/
private theorem keepsCodeOrigin_destroyAccount (tx : TransactionState) (address : Address) :
    KeepsCodeOrigin tx (tx.destroyAccount address) := by
  refine ⟨rfl, fun _ h => h, fun x => ?_⟩
  rw [TransactionState.getAccount_destroyAccount]
  split
  · exact .inl rfl
  · exact .inr (.inr rfl)

/-! ## The message and the transaction -/

/-- A message keeps the origin of the code hashes. -/
private theorem keepsCodeOrigin_processMessageCall {Meter : Type} [GasMeter Meter]
    [LawfulGasMeter Meter] {chainId : Nat} {message : Message fork} {state : TransactionState}
    {substate : Substate} {auths : List Transactions.Authorization}
    {paid : Std.ExtTreeSet Address} {output : Transactions.CallOutput}
    (h : Transactions.processMessageCall (Meter := Meter) chainId message state substate auths
      paid = .ok output) :
    KeepsCodeOrigin state output.state := by
  rw [Transactions.processMessageCall_unfold] at h
  rcases hprep : Transactions.prepareFirstFrame (Meter := Meter) chainId message state substate
    auths paid with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
    · cases h
      -- A halt before the first frame keeps the writes, with new reads.
      exact ⟨rfl, fun _ h => h, fun _ => .inr (.inr rfl)⟩
  · rw [hprep] at h
    dsimp only at h
    have vfirst := Transactions.keepsCodeOrigin_prepareFirstFrame hprep
    have hframe : ∀ {evm : Evm fork Meter} {r : Nat} {t : Std.ExtTreeSet Address},
        (Transactions.CallOutput.ofFrame evm r t).state = evm.state := by
      intro evm r t
      unfold Transactions.CallOutput.ofFrame
      dsimp only
      split <;> rfl
    split at h
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      rw [hframe]
      exact vfirst.trans (keepsCodeOrigin_processCreateMessage hrun)
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      rw [hframe]
      exact vfirst.trans (keepsCodeOrigin_processMessage hrun)

/-- A message keeps the origin of the code hashes and the rules of its codes.

Its authorizations need Pectra, unless there is none. -/
private theorem keeps_processMessageCall {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Transactions.Authorization} {paid : Std.ExtTreeSet Address}
    {output : Transactions.CallOutput} (hauth : auths = [] ∨ .pectra ≤ fork)
    (h : Transactions.processMessageCall (Meter := Meter) chainId message state substate auths
      paid = .ok output) :
    Keeps fork state output.state :=
  ⟨keepsCodeOrigin_processMessageCall h, Transactions.keepsCodeRules_processMessageCall hauth h⟩

/-- Buying gas keeps the origin of the code hashes, since it raises a nonce and takes a fee. -/
private theorem keepsCodeOrigin_buyGas {env : BlockEnvironment fork}
    {state state' : TransactionState} {sender : Address} {tx : Transaction}
    {lifted : Transactions.LiftedRules}
    (h : Transactions.buyGas env state sender tx lifted = .ok state') :
    KeepsCodeOrigin state state' := by
  unfold Transactions.buyGas at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  refine (KeepsCodeOrigin.incrementNonce h1).trans ?_
  refine KeepsCodeOrigin.modifyState_of_keeps (fun account updated hupd => ?_) h2
  split at hupd
  · cases hupd
    rfl
  · cases hupd

/-- A credit of ether keeps the origin of the code hashes. -/
private theorem keepsCodeOrigin_creditEther {tx tx' : TransactionState} {address : Address}
    {amount : Nat} (h : Transactions.creditEther fork tx address amount = .ok tx') :
    KeepsCodeOrigin tx tx' := by
  unfold Transactions.creditEther at h
  split at h
  · exact (keeps_createEther h).1
  · cases h

/-- Settling gas keeps the origin of the code hashes. -/
private theorem keepsCodeOrigin_settleGas {env : BlockEnvironment fork}
    {state state' : TransactionState} {sender : Address} {tx : Transaction}
    {gasLeft refundCounter used : Nat} {lifted : Transactions.LiftedRules}
    (h : Transactions.settleGas env state sender tx gasLeft refundCounter lifted =
      .ok (state', used)) :
    KeepsCodeOrigin state state' := by
  unfold Transactions.settleGas at h
  obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨paid, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  refine (keepsCodeOrigin_creditEther h1).trans ?_
  unfold Transactions.payBeneficiary at h2
  split at h2
  · cases h2
    split
    · exact keepsCodeOrigin_destroyAccount _ _
    · exact .refl _
  · exact keepsCodeOrigin_creditEther h2

/-- The deletions at the end of a transaction keep the origin of the code hashes.

From Glamsterdam, a deletion clears the code of an account and keeps its balance. -/
private theorem keepsCodeOrigin_deleteAccounts {state state' : TransactionState}
    {output : Transactions.CallOutput}
    (h : Transactions.deleteAccounts fork state output = .ok state') :
    KeepsCodeOrigin state state' := by
  have touched : ∀ (l : List Address) (tx : TransactionState),
      KeepsCodeOrigin tx (l.foldl (fun tx address =>
        if tx.accountExistsAndIsEmpty address then tx.destroyAccount address else tx) tx) := by
    intro l
    induction l with
    | nil => exact fun tx => .refl tx
    | cons address rest ih =>
      intro tx
      refine KeepsCodeOrigin.trans ?_ (ih _)
      dsimp only
      split
      · exact keepsCodeOrigin_destroyAccount _ _
      · exact .refl _
  have fold : ∀ (l : List Address) (init final : TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      KeepsCodeOrigin init final := by
    intro l
    induction l with
    | nil =>
      intro init final h
      cases h
      exact .refl _
    | cons address rest ih =>
      intro init final h
      obtain ⟨mid, hmid, h⟩ := Base.bind_ok_iff.mp h
      refine KeepsCodeOrigin.trans ?_ (ih mid final h)
      split at hmid
      · -- The wipe of the storage keeps every account, and the clear empties the code.
        have hwipe : KeepsCodeOrigin init (init.destroyStorage address) :=
          ⟨rfl, fun _ h => h, fun _ => .inr (.inr rfl)⟩
        exact hwipe.trans (.modifyState (fun _ hupd => by cases hupd; exact .inl rfl) hmid)
      · cases hmid
        exact keepsCodeOrigin_destroyAccount _ _
  unfold Transactions.deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  refine (fold _ _ _ hdeleted).trans ?_
  unfold TransactionState.destroyTouchedEmptyAccounts
  split
  · exact .refl _
  · exact touched _ _

/-- A run of a transaction keeps the origin of the code hashes of its block. -/
private theorem keepsCodeOrigin_runTransaction {Meter : Type} [GasMeter Meter]
    [LawfulGasMeter Meter] {env : BlockEnvironment fork} {block : BlockState}
    {included : Transactions.Included} {tx : Transaction}
    {precompiles : Address → Option Address} {lifted : Transactions.LiftedRules}
    {output : Transactions.TransactionOutput}
    (h : Transactions.runTransaction Meter env block included tx precompiles lifted =
      .ok output) :
    KeepsCodeOrigin (TransactionState.ofBlock block) output.state := by
  rw [Transactions.runTransaction_unfold] at h
  obtain ⟨target, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨bought, hBought, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨message, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨out, hOutput, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨settled, used⟩, hSettle, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨deleted, hDeleted, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (keepsCodeOrigin_buyGas (Base.mapError_ok_iff.mp hBought)).trans
    ((keepsCodeOrigin_processMessageCall hOutput).trans
      ((keepsCodeOrigin_settleGas (Base.mapError_ok_iff.mp hSettle)).trans
        (keepsCodeOrigin_deleteAccounts (Base.mapError_ok_iff.mp hDeleted))))

/-- A transaction keeps the origin of the code hashes of its block and the rules of its codes.

The type of the transaction must exist at the fork. -/
private theorem keeps_processTransaction {env : BlockEnvironment fork} {block : BlockState}
    {included : Transactions.Included} {tx : Transaction}
    {output : Transactions.TransactionOutput} (hfork : tx.fork ≤ fork)
    (h : Transactions.processTransaction env block included tx = .ok output) :
    Keeps fork (TransactionState.ofBlock block) output.state := by
  refine ⟨?_, fun codeHash code hc =>
    .inr (Transactions.codeRules_processTransaction hfork h codeHash code hc)⟩
  rw [Transactions.processTransaction_unfold] at h
  split at h
  · cases h
  split at h
  · exact keepsCodeOrigin_runTransaction h
  · exact keepsCodeOrigin_runTransaction h

/-- A system call keeps the origin of the code hashes of its block and the rules of its codes. -/
private theorem keeps_systemCall {env : BlockEnvironment fork} {block : BlockState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput}
    (h : systemCall env block target data = .ok out) :
    Keeps fork (TransactionState.ofBlock block) out.state := by
  simp only [systemCall] at h
  split at h <;>
  · obtain ⟨call, hcall, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact keeps_processMessageCall (.inl rfl) hcall

/-! ## The block state -/

/-- What a block state keeps of the codes, from the state `pre` before the block.

Each code that it wrote meets the rules of the fork, or is a delegation indicator from Pectra.

Each account has no code, a written code, or the code hash it had in `pre`. -/
private def Carried (pre : State) (fork : Fork) (block : BlockState) : Prop :=
  (∀ (codeHash : Hash32) (code : ByteArray), block.codeWrites[codeHash]? = some code →
    TxCodeRules fork code) ∧
    ∀ address, ((TransactionState.ofBlock block).getAccount address).codeHash = EMPTY_CODE_HASH ∨
      ((TransactionState.ofBlock block).getAccount address).codeHash ∈ block.codeWrites ∨
      ((TransactionState.ofBlock block).getAccount address).codeHash =
        ((pre.getAccountOptional address).getD EMPTY_ACCOUNT).codeHash

/-- The block state before any write carries the codes. -/
private theorem carried_start (pre : State) : Carried pre fork ⟨pre, ∅, ∅, ∅, ∅⟩ := by
  refine ⟨fun _ _ h => by simp at h, fun address => .inr (.inr ?_)⟩
  simp [TransactionState.getAccount, TransactionState.getAccountOptional,
    TransactionState.ofBlock]

/-- The block that a transaction joins reads each written code from the transaction first. -/
private theorem codeWrites_incorporateTxIntoBlock (tx : TransactionState) (codeHash : Hash32) :
    tx.incorporateTxIntoBlock.parent.codeWrites[codeHash]? =
      tx.codeWrites[codeHash]?.or tx.parent.codeWrites[codeHash]? := by
  simp only [TransactionState.incorporateTxIntoBlock, TransactionState.ofBlock]
  rw [State.getElem?_foldl_of_step (F := fun _ code _ => some code)]
  · cases tx.codeWrites[codeHash]? <;> rfl
  · intro acc k v k'
    by_cases hk : k = k' <;> simp_all [Std.ExtTreeMap.getElem?_insert]

/-- A transaction state that keeps the origin and the rules carries the codes once it joins. -/
private theorem Carried.incorporate {pre : State} {block : BlockState} {tx : TransactionState}
    (carried : Carried pre fork block) (keeps : Keeps fork (.ofBlock block) tx) :
    Carried pre fork tx.incorporateTxIntoBlock.parent := by
  have hparent : tx.parent = block := keeps.1.1
  have hw : ∀ codeHash, tx.incorporateTxIntoBlock.parent.codeWrites[codeHash]? =
      tx.codeWrites[codeHash]?.or block.codeWrites[codeHash]? := fun codeHash => by
    rw [codeWrites_incorporateTxIntoBlock, hparent]
  -- A code written in the transaction or in the block is written in the block after.
  have mem : ∀ codeHash, codeHash ∈ tx.codeWrites ∨ codeHash ∈ block.codeWrites →
      codeHash ∈ tx.incorporateTxIntoBlock.parent.codeWrites := by
    intro codeHash hh
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hw]
    rcases hh with hh | hh <;> rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hh
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hh
      rw [hc]
      rfl
    · cases tx.codeWrites[codeHash]?
      · exact hh
      · rfl
  refine ⟨fun codeHash code hc => ?_, fun address => ?_⟩
  · rw [hw] at hc
    cases htx : tx.codeWrites[codeHash]? with
    | some written =>
      rw [htx, Option.some_or] at hc
      cases hc
      rcases keeps.2 codeHash _ htx with hb | hr
      · simp [TransactionState.ofBlock] at hb
      · exact hr
    | none =>
      rw [htx] at hc
      exact carried.1 codeHash code hc
  · rw [TransactionState.getAccount_ofBlock_incorporateTxIntoBlock]
    rcases keeps.1.2.2 address with he | hw' | heq
    · exact .inl he
    · exact .inr (.inl (mem _ (.inl hw')))
    · rw [heq]
      rcases carried.2 address with he | hb | hpre
      · exact .inl he
      · exact .inr (.inl (mem _ (.inr hb)))
      · exact .inr (.inr hpre)

/-- A call that keeps the origin and the rules carries the codes once it joins the body. -/
private theorem Carried.join {pre : State} {body body' : BodyState} {tx : TransactionState}
    (carried : Carried pre fork body.block) (keeps : Keeps fork (.ofBlock body.block) tx)
    (h : body.join tx = .ok body') : Carried pre fork body'.block := by
  obtain ⟨_, -, rfl⟩ := BodyState.join_eq_ok h
  exact carried.incorporate keeps

/-- A step that keeps the origin and the rules on a block state carries the codes. -/
private theorem Carried.onBlock {pre : State} {block block' : BlockState}
    {step : TransactionState → Except State.StateError TransactionState}
    (carried : Carried pre fork block)
    (keeps : ∀ tx, step (.ofBlock block) = .ok tx → Keeps fork (.ofBlock block) tx)
    (h : onBlock block step = .ok block') : Carried pre fork block' := by
  obtain ⟨tx, htx, rfl⟩ := onBlock_eq_ok h
  exact carried.incorporate (keeps tx htx)

/-- A system call that joins the body carries the codes. -/
private theorem Carried.systemCall {pre : State} {env : BlockEnvironment fork}
    {body body' : BodyState} {target : Address} {data : ByteArray} {out : SystemCallOutput}
    (carried : Carried pre fork body.block)
    (hcall : systemCall env body.block target data = .ok out)
    (hjoin : body.join out.state = .ok body') : Carried pre fork body'.block :=
  carried.join (keeps_systemCall hcall) hjoin

/-- A fold of creations of ether keeps the origin and the rules. -/
private theorem keeps_foldlM_createEther {α : Type} {f : α → Address} {g : α → U256}
    {xs : List α} {start tx : TransactionState}
    (h : xs.foldlM (fun tx x => tx.createEther fork (f x) (g x)) start = .ok tx) :
    Keeps fork start tx :=
  Base.foldlM_ok_invariant (fun tx => Keeps fork start tx)
    (fun _ _ _ fit step => fit.trans (keeps_createEther step)) (.refl start) h

/-- The DAO transfer carries the codes. -/
private theorem Carried.daoTransfer {pre : State} {config : ChainConfig} {number : Nat}
    {start state : BlockState} (carried : Carried pre fork start)
    (h : daoTransfer config fork number start = .ok state) : Carried pre fork state := by
  unfold Blocks.daoTransfer at h
  split at h
  · refine carried.onBlock (fun tx hdao => ?_) h
    exact Base.foldlM_ok_invariant (fun tx' => Keeps fork (.ofBlock start) tx')
      (fun _ _ _ fit step => fit.trans (keeps_moveEther step)) (.refl _) hdao
  · cases h
    exact carried

/-- The system calls at the start of a block carry the codes. -/
private theorem Carried.startSystemCalls {pre : State} {env : BlockEnvironment fork}
    {parentHash : Hash32} {body body' : BodyState} (carried : Carried pre fork body.block)
    (h : startSystemCalls env parentHash body = .ok body') : Carried pre fork body'.block := by
  obtain ⟨mid, hFirst, hNoFirst, hSecond, hNoSecond⟩ := startSystemCalls_eq_ok h
  have first : Carried pre fork mid.block := by
    by_cases hd : .dencun ≤ fork
    · obtain ⟨out, hout, hjoin⟩ := hFirst hd
      exact carried.systemCall hout hjoin
    · rw [hNoFirst hd]
      exact carried
  by_cases hp : .pectra ≤ fork
  · obtain ⟨out, hout, hjoin⟩ := hSecond hp
    exact first.systemCall hout hjoin
  · rw [hNoSecond hp]
    exact first

/-- A transaction that enters the body carries the codes. -/
private theorem Carried.applyTransaction {pre : State} {env : BlockEnvironment fork}
    {index : Nat} {before after : BodyOutput fork} {tx : Transaction}
    (carried : Carried pre fork before.block)
    (h : applyTransaction env index before tx = .ok after) : Carried pre fork after.block := by
  obtain ⟨included, out, hincluded, hout, -, -, hjoin⟩ := applyTransaction_eq_ok h
  exact Carried.join (body := before.body.beginIndex (index + 1)) carried
    (keeps_processTransaction (Transactions.checkInclusion_fork_le hincluded) hout) hjoin

/-- The transactions of a block carry the codes. -/
private theorem Carried.applyTransactions {pre : State} {env : BlockEnvironment fork}
    {body : BodyState} {transactions : List Transaction} {output : BodyOutput fork}
    (carried : Carried pre fork body.block)
    (h : applyTransactions env body transactions = .ok output) :
    Carried pre fork output.block :=
  (applyTransactions_steps
    (fun a b : BodyOutput fork => Carried pre fork a.block → Carried pre fork b.block)
    (fun _ => id) (fun hab hbc fit => hbc (hab fit))
    (fun h fit => fit.applyTransaction h) h).1 carried

/-- The requests of a block carry the codes. -/
private theorem Carried.blockRequests {pre : State} {depositContract : Address}
    {env : BlockEnvironment fork} {body : BodyState} {logs : List Log}
    {result : BodyState × List ByteArray} (carried : Carried pre fork body.block)
    (h : blockRequests depositContract env body logs = .ok result) :
    Carried pre fork result.1.block := by
  obtain ⟨hNoPectra, hPectra⟩ := blockRequests_eq_ok h
  by_cases hp : .pectra ≤ fork
  · obtain ⟨_, read, -, hread, rfl⟩ := hPectra hp
    exact Base.foldlM_ok_invariant
      (fun st : BodyState × List ByteArray => Carried pre fork st.1.block)
      (fun _ _ _ fit hstep => by
        obtain ⟨out, hout, hjoin, -⟩ := readRequest_eq_ok hstep
        exact fit.systemCall (checkedSystemCall_ok hout).2.1 hjoin)
      (b' := read) carried hread
  · rw [hNoPectra hp]
    exact carried

/-- The rewards keep the origin and the rules. -/
private theorem keeps_payRewards {tx tx' : TransactionState} {coinbase : Address}
    {number : Nat} {ommers : List (Address × Nat)}
    (h : payRewards fork tx coinbase number ommers = .ok tx') : Keeps fork tx tx' := by
  unfold payRewards at h
  split at h
  · cases h
    exact .refl _
  · obtain ⟨mid, hmid, h⟩ := Base.bind_ok_iff.mp h
    exact (keeps_createEther hmid).trans (keeps_foldlM_createEther h)

/-- The body of a block carries the codes.

Its other steps change balances, nonces and accounts, and write no code. -/
private theorem Carried.applyBody {pre : State} {config : ChainConfig}
    {env : BlockEnvironment fork} {block : Block fork Transaction} {start : BlockState}
    {output : BlockOutput fork} (carried : Carried pre fork start)
    (h : applyBody config env block start = .ok output) : Carried pre fork output.block := by
  obtain ⟨_, body, txs, withdrawn, requested, hdao, hsys, htxs, hWithdrawn, hStays, hreq, hrew,
    -⟩ := applyBody_eq_ok h
  have afterTxs : Carried pre fork txs.block :=
    ((carried.daoTransfer hdao).startSystemCalls (body := .init _) hsys).applyTransactions htxs
  have afterWithdrawn : Carried pre fork withdrawn.block := by
    by_cases hShapella : .shapella ≤ fork
    · obtain ⟨_, htx, hj⟩ := hWithdrawn hShapella
      exact Carried.join (body := txs.body.beginIndex _) afterTxs
        (keeps_foldlM_createEther htx) hj
    · rw [hStays hShapella]
      exact afterTxs
  exact (afterWithdrawn.blockRequests (result := (requested, _)) hreq).onBlock
    (fun _ hp => keeps_payRewards hp) hrew

/-! ## The block -/

/-- Each code that a block changes meets the rules of its fork.

From Pectra, it may also be a delegation indicator.

An account changes its code when it is new, or when its code hash differs from the one before. -/
theorem stateTransition_codeRules {chain : BlockChain} {fork : Fork}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (h : stateTransition chain block checkSeal = .ok post) {address : Address} {account : Account}
    (hpost : post.getAccountOptional address = some account)
    (changed : ∀ before, chain.state.getAccountOptional address = some before →
      before.codeHash ≠ account.codeHash)
    {code : ByteArray} (hcode : post.getCode account.codeHash = .ok code) :
    TxCodeRules fork code := by
  obtain ⟨-, -, -, _, output, _, -, hbody, -, -, rfl⟩ := stateTransition_eq_ok h
  have carried := (carried_start chain.state).applyBody hbody
  rw [State.BlockState.getAccountOptional_applyChanges] at hpost
  rw [State.BlockState.getCode_applyChanges] at hcode
  have hacc : (TransactionState.ofBlock output.block).getAccount address = account := by
    simp [TransactionState.getAccount, hpost]
  -- The empty code meets the rules: it has no byte.
  have empty : account.codeHash = EMPTY_CODE_HASH → TxCodeRules fork code := by
    intro he
    simp only [TransactionState.getCode, he, ↓reduceIte, Except.ok.injEq] at hcode
    subst hcode
    exact .inl ⟨fun _ _ => by simp, fun _ => by simp⟩
  rcases carried.2 address with he | hw | hpre <;> rw [hacc] at *
  · exact empty he
  · by_cases he : account.codeHash = EMPTY_CODE_HASH
    · exact empty he
    -- A code that the block wrote is read first.
    obtain ⟨written, hwritten⟩ := Option.isSome_iff_exists.mp
      (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hw)
    simp only [TransactionState.getCode, he, ↓reduceIte, TransactionState.ofBlock,
      Std.ExtTreeMap.getElem?_empty, hwritten, Except.ok.injEq] at hcode
    subst hcode
    exact carried.1 _ _ hwritten
  · -- The code hash before the block is excluded, so the account is new with no code.
    cases hbefore : chain.state.getAccountOptional address with
    | none =>
      rw [hbefore] at hpre
      exact empty hpre
    | some before =>
      rw [hbefore] at hpre
      exact absurd hpre.symm (changed before hbefore)

end EthLib.Execution.Blocks
