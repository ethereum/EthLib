module

public import EthLib.Base.Proofs.List
public import EthLib.Execution.Proofs.Blocks.DaoFork
public import EthLib.Execution.Proofs.Blocks.Rewards
public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Transactions.Replay
public import EthLib.Execution.Proofs.Transactions.Signature

/-!
# Proofs: no transaction runs twice in a chain

A signed transaction is public, so anyone can put it in a block again.

The nonce check stops the second copy.

It asks that the nonce of the transaction equals the nonce of its sender.

After the first copy runs, the nonce of its sender is above the nonce of the copy.

That nonce never drops again, through the rest of the block and through every later block.

The other transactions never lower a nonce that is above 0.

Before Cancun, that needs an account without code, and the sender keeps none.

The system calls run code, but only from Cancun, where no nonce above 0 drops.

The withdrawals, the rewards and the DAO transfer change only balances.

So two transactions of one sender in a chain have distinct nonces, the later one higher.

Two positions of a chain then never hold one transaction.

The fork of a block is never below the fork of its parent.

So the blocks before a block that comes before Cancun also come before Cancun.

Replay across chains is out of scope: EIP-155 binds a transaction to its chain.

Section 6 of the [Yellow Paper][yp], Shanghai version, gives the nonce check.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (Account BlockState EMPTY_CODE_HASH State TransactionState)
open EthLib.Execution.Transactions

variable {fork : Fork}

/-! ## An account above a nonce -/

/-- At `fork`, an account has a nonce above `n`, and before Cancun it has no code. -/
def NonceAbove (fork : Fork) (n : Nat) (account : Account) : Prop :=
  n < account.nonce ∧ (fork < .dencun → account.codeHash = EMPTY_CODE_HASH)

/-- An account above a nonce at a fork is above it at every later fork. -/
theorem NonceAbove.mono {fork fork' : Fork} {n : Nat} {account : Account} (h : fork ≤ fork')
    (above : NonceAbove fork n account) : NonceAbove fork' n account :=
  ⟨above.1, fun h' => above.2 (Nat.lt_of_le_of_lt h h')⟩

/-- At `fork`, every account above a nonce in the first block state is above it in the second. -/
def KeepsNonces (fork : Fork) (block block' : BlockState) : Prop :=
  ∀ address n, NonceAbove fork n ((TransactionState.ofBlock block).getAccount address) →
    NonceAbove fork n ((TransactionState.ofBlock block').getAccount address)

/-- A block state keeps its own nonces. -/
theorem KeepsNonces.refl (fork : Fork) (block : BlockState) : KeepsNonces fork block block :=
  fun _ _ above => above

/-- Two steps that each keep the nonces keep them together. -/
theorem KeepsNonces.trans {a b c : BlockState} (hab : KeepsNonces fork a b)
    (hbc : KeepsNonces fork b c) : KeepsNonces fork a c :=
  fun address n above => hbc address n (hab address n above)

/-! ## A transaction -/

/-- A transaction that runs keeps every account above a nonce.

Its type must exist at the fork of the block. -/
theorem processTransaction_nonceAbove {env : BlockEnvironment fork} {block : BlockState}
    {tx : Transaction} {included : Included} {out : TransactionOutput} {address : Address}
    {n : Nat} (hfork : tx.fork ≤ fork) (h : processTransaction env block included tx = .ok out)
    (above : NonceAbove fork n ((TransactionState.ofBlock block).getAccount address)) :
    NonceAbove fork n (out.state.getAccount address) :=
  ⟨Nat.lt_of_lt_of_le above.1 (processTransaction_nonce_le hfork h above.2),
    fun hd => processTransaction_codeHash_of_lt_dencun hd hfork h (.inl (by have := above.1; omega))
      (above.2 hd)⟩

/-- A transaction that runs leaves its sender above the nonce of the transaction.

The transaction passes the inclusion check on the state of the block it runs on. -/
theorem processTransaction_sender_nonceAbove {env : BlockEnvironment fork} {block : BlockState}
    {chainId : UInt64} {used : BlockGas} {tx : Transaction} {included : Included}
    {out : TransactionOutput}
    (hcheck : checkInclusion chainId env used (.ofBlock block) tx = .ok included)
    (h : processTransaction env block included tx = .ok out) :
    NonceAbove fork tx.nonce.toNat (out.state.getAccount included.sender) := by
  refine ⟨processTransaction_nonce_lt hcheck h, fun hd => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, code, -, hcode⟩ :=
    checkInclusion_eq_ok_iff.mp hcheck
  refine processTransaction_codeHash_of_lt_dencun hd (checkInclusion_fork_le hcheck) h
    (.inr rfl) ?_
  rcases hcode with hempty | ⟨hp, -⟩
  · exact hempty
  · exact absurd hp (Nat.not_le.mpr (Nat.lt_of_lt_of_le hd (by decide)))

/-- A transaction that enters the body keeps every account above a nonce. -/
theorem applyTransaction_keepsNonces {env : BlockEnvironment fork} {index : Nat}
    {before after : BodyOutput fork} {tx : Transaction}
    (h : applyTransaction env index before tx = .ok after) :
    KeepsNonces fork before.block after.block := by
  obtain ⟨included, out, hcheck, hout, -, -, hjoin⟩ := applyTransaction_eq_ok h
  intro address n above
  show NonceAbove fork n ((TransactionState.ofBlock after.body.block).getAccount address)
  rw [BodyState.getAccount_join hjoin]
  exact processTransaction_nonceAbove (checkInclusion_fork_le hcheck) hout above

/-! ## The transactions of a block -/

/-- The transactions of a block keep every account above a nonce, each step and all together. -/
private theorem applyTransactions_keepsNonces_steps {env : BlockEnvironment fork}
    {body : BodyState} {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    KeepsNonces fork body.block output.block ∧ ∀ i (hi : i < transactions.length), ∃ before next,
      applyTransactions env body (transactions.take i) = .ok before ∧
      applyTransaction env i before transactions[i] = .ok next ∧
      KeepsNonces fork next.block output.block :=
  applyTransactions_steps (fun a b : BodyOutput fork => KeepsNonces fork a.block b.block)
    (fun _ => KeepsNonces.refl _ _) (fun h h' => h.trans h') applyTransaction_keepsNonces h

/-- The transactions of a block keep every account above a nonce. -/
theorem applyTransactions_keepsNonces {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    KeepsNonces fork body.block output.block :=
  (applyTransactions_keepsNonces_steps h).1

/-- Each transaction of a block from an account above `n` at the start has a nonce above `n`. -/
theorem applyTransactions_nonce_gt {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork} {sender : Address} {n : Nat}
    (h : applyTransactions env body transactions = .ok output)
    (above : NonceAbove fork n ((TransactionState.ofBlock body.block).getAccount sender))
    {tx : Transaction} (mem : tx ∈ transactions) (hs : recoverSender fork tx = .ok sender) :
    n < tx.nonce.toNat := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp mem
  obtain ⟨before, next, hBefore, hNext, -⟩ := (applyTransactions_keepsNonces_steps h).2 i hi
  obtain ⟨included, -, hcheck, -⟩ := applyTransaction_eq_ok hNext
  obtain ⟨hs', -, -, -, -, -, -, -, hnonce, -⟩ := checkInclusion_ok hcheck
  rw [hnonce, show included.sender = sender from Except.ok.inj (hs'.symm.trans hs)]
  exact (applyTransactions_keepsNonces hBefore sender n above).1

/-- After the transactions of a block, the sender of each is above the nonce of that one. -/
theorem applyTransactions_sender_nonceAbove {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork} {sender : Address}
    (h : applyTransactions env body transactions = .ok output) {i : Nat}
    (hi : i < transactions.length) (hs : recoverSender fork transactions[i] = .ok sender) :
    NonceAbove fork transactions[i].nonce.toNat
      ((TransactionState.ofBlock output.block).getAccount sender) := by
  obtain ⟨before, next, -, hNext, hEnd⟩ := (applyTransactions_keepsNonces_steps h).2 i hi
  obtain ⟨included, out, hcheck, hout, -, -, hjoin⟩ := applyTransaction_eq_ok hNext
  obtain rfl : sender = included.sender :=
    Except.ok.inj (hs.symm.trans (checkInclusion_ok hcheck).1)
  apply hEnd
  show NonceAbove fork _ ((TransactionState.ofBlock next.body.block).getAccount _)
  rw [BodyState.getAccount_join hjoin]
  exact processTransaction_sender_nonceAbove hcheck hout

/-- Of two transactions of one sender in a block, the later one has the higher nonce. -/
theorem applyTransactions_nonce_lt {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork} {sender : Address}
    (h : applyTransactions env body transactions = .ok output) {i i' : Nat} (lt : i < i')
    (hi' : i' < transactions.length)
    (hs : recoverSender fork (transactions[i]'(Nat.lt_trans lt hi')) = .ok sender)
    (hs' : recoverSender fork transactions[i'] = .ok sender) :
    (transactions[i]'(Nat.lt_trans lt hi')).nonce.toNat < transactions[i'].nonce.toNat := by
  obtain ⟨before, next, hBefore, hNext, -⟩ := (applyTransactions_keepsNonces_steps h).2 i' hi'
  obtain ⟨included, -, hcheck, -⟩ := applyTransaction_eq_ok hNext
  obtain ⟨hs'', -, -, -, -, -, -, -, hnonce, -⟩ := checkInclusion_ok hcheck
  rw [show included.sender = sender from Except.ok.inj (hs''.symm.trans hs')] at hnonce
  have hlen : i < (transactions.take i').length := by simp [lt, Nat.lt_trans lt hi']
  have above := applyTransactions_sender_nonceAbove hBefore hlen
    (by rw [List.getElem_take]; exact hs)
  rw [List.getElem_take] at above
  rw [hnonce]
  exact above.1

/-! ## The other steps of a block -/

/-- From Cancun, a system call keeps every account above a nonce. -/
theorem systemCall_nonceAbove {env : BlockEnvironment fork} {block : BlockState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput} {address : Address} {n : Nat}
    (hd : .dencun ≤ fork) (h : systemCall env block target data = .ok out)
    (above : NonceAbove fork n ((TransactionState.ofBlock block).getAccount address)) :
    NonceAbove fork n (out.state.getAccount address) := by
  have before : fork < .dencun → False := fun hlt => absurd hd (Nat.not_le.mpr hlt)
  -- The call runs one message, with either gas meter.
  have keeps : ∀ {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {call : CallOutput},
      processMessageCall (Meter := Meter) env.chainId.toNat (systemMessage env target data)
        (.ofBlock block) Substate.empty = .ok call →
      NonceAbove fork n (call.state.getAccount address) := by
    intro Meter _ _ call hcall
    have := processMessageCall_keeps (address := address) hcall
      (fun t ht => Option.some.inj ht) (by have := above.1; omega)
      (by simp [TransactionState.ofBlock]) (by simp [Substate.empty])
      (fun hlt => (before hlt).elim)
    exact ⟨Nat.lt_of_lt_of_le above.1 this.1, fun hlt => (before hlt).elim⟩
  simp only [systemCall] at h
  split at h <;>
  · obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    exact keeps hcall

/-- From Cancun, a system call that joins the body keeps every account above a nonce. -/
private theorem join_systemCall_keepsNonces {env : BlockEnvironment fork} {body body' : BodyState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput} (hd : .dencun ≤ fork)
    (hcall : systemCall env body.block target data = .ok out)
    (hjoin : body.join out.state = .ok body') : KeepsNonces fork body.block body'.block := by
  intro address n above
  rw [BodyState.getAccount_join hjoin]
  exact systemCall_nonceAbove hd hcall above

/-- From Pectra, the request contracts keep every account above a nonce. -/
private theorem readRequests_keepsNonces {env : BlockEnvironment fork} {body : BodyState}
    {result : BodyState × List ByteArray} (h : readRequests env body = .ok result) :
    KeepsNonces fork body.block result.1.block := by
  by_cases hp : .pectra ≤ fork
  · rw [readRequests_of_pectra hp] at h
    refine foldlM_ok_invariant (fun st : BodyState × List ByteArray =>
      KeepsNonces fork body.block st.1.block) ?_ (KeepsNonces.refl _ _) h
    intro st c st' keeps hstep
    obtain ⟨out, hout, hjoin, -⟩ := readRequest_eq_ok hstep
    exact keeps.trans (join_systemCall_keepsNonces (Nat.le_trans (by decide) hp)
      (checkedSystemCall_ok hout).2.1 hjoin)
  · rw [readRequests_of_lt_pectra (Nat.lt_of_not_le hp)] at h
    cases h
    exact KeepsNonces.refl _ _

/-- The system calls at the start of a block keep every account above a nonce. -/
theorem startSystemCalls_keepsNonces {env : BlockEnvironment fork} {parentHash : Hash32}
    {body body' : BodyState} (h : startSystemCalls env parentHash body = .ok body') :
    KeepsNonces fork body.block body'.block := by
  obtain ⟨mid, hFirst, hNoFirst, hSecond, hNoSecond⟩ := startSystemCalls_eq_ok h
  have first : KeepsNonces fork body.block mid.block := by
    by_cases hd : .dencun ≤ fork
    · obtain ⟨out, hout, hjoin⟩ := hFirst hd
      exact join_systemCall_keepsNonces hd hout hjoin
    · rw [hNoFirst hd]
      exact KeepsNonces.refl _ _
  by_cases hp : .pectra ≤ fork
  · obtain ⟨out, hout, hjoin⟩ := hSecond hp
    exact first.trans (join_systemCall_keepsNonces (Nat.le_trans (by decide) hp) hout hjoin)
  · rw [hNoSecond hp]
    exact first

/-- The requests of a block keep every account above a nonce. -/
theorem blockRequests_keepsNonces {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} {logs : List Log} {result : BodyState × List ByteArray}
    (h : blockRequests depositContract env body logs = .ok result) :
    KeepsNonces fork body.block result.1.block := by
  obtain ⟨hNoPectra, hPectra⟩ := blockRequests_eq_ok h
  by_cases hp : .pectra ≤ fork
  · obtain ⟨_, read, -, hread, rfl⟩ := hPectra hp
    exact readRequests_keepsNonces (result := read) ((readRequests_of_pectra hp).trans hread)
  · rw [hNoPectra hp]
    exact KeepsNonces.refl _ _

/-- A step that keeps every nonce and every code hash keeps every account above a nonce. -/
private theorem onBlock_keepsNonces {block block' : BlockState}
    {step : TransactionState → Except State.StateError TransactionState}
    (keeps : ∀ tx, step (.ofBlock block) = .ok tx → ∀ address,
      (tx.getAccount address).nonce = ((TransactionState.ofBlock block).getAccount address).nonce ∧
      (tx.getAccount address).codeHash =
        ((TransactionState.ofBlock block).getAccount address).codeHash)
    (h : onBlock block step = .ok block') : KeepsNonces fork block block' := by
  unfold onBlock at h
  obtain ⟨tx, htx, h⟩ := bind_ok_iff.mp h
  cases h
  intro address n above
  obtain ⟨hn, hc⟩ := keeps tx (mapError_ok_iff.mp htx) address
  rw [TransactionState.getAccount_ofBlock_incorporateTxIntoBlock]
  exact ⟨hn ▸ above.1, fun hd => hc.trans (above.2 hd)⟩

/-- The DAO transfer keeps every account above a nonce. -/
theorem daoTransfer_keepsNonces {config : ChainConfig} {number : Nat}
    {start state : BlockState} (h : daoTransfer config fork number start = .ok state) :
    KeepsNonces fork start state := by
  unfold daoTransfer at h
  split at h
  · exact onBlock_keepsNonces (fun _ hdao => applyDaoFork_nonce_codeHash hdao) h
  · cases h
    exact KeepsNonces.refl _ _

/-- The rewards of a block keep every account above a nonce. -/
theorem onBlock_payRewards_keepsNonces {block block' : BlockState} {coinbase : Address}
    {number : Nat} {ommers : List (Address × Nat)}
    (h : onBlock block (fun tx => payRewards fork tx coinbase number ommers) = .ok block') :
    KeepsNonces fork block block' :=
  onBlock_keepsNonces (fun _ hp address => payRewards_nonce_codeHash hp address) h

/-! ## The body of a block -/

/-- The body of a block runs its transactions between steps that keep the nonces. -/
private theorem applyBody_split {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) :
    ∃ body txs, KeepsNonces fork start body.block ∧
      applyTransactions env body block.transactions = .ok txs ∧
      KeepsNonces fork txs.block output.block := by
  obtain ⟨_, body, txs, withdrawn, requested, hdao, hsys, htxs, hWithdrawn, hStays, hreq, hrew,
    -⟩ := applyBody_eq_ok h
  refine ⟨body, txs, (daoTransfer_keepsNonces hdao).trans (startSystemCalls_keepsNonces hsys),
    htxs, ?_⟩
  -- The withdrawals change only balances.
  have withdrawals : KeepsNonces fork txs.block withdrawn.block := by
    by_cases hShapella : .shapella ≤ fork
    · obtain ⟨_, htx, hj⟩ := hWithdrawn hShapella
      intro address n above
      rw [BodyState.getAccount_join hj]
      obtain ⟨-, hn, hc⟩ := TransactionState.getAccount_foldlM_createEther _ _ _ htx address
      exact ⟨hn ▸ above.1, fun hd => hc.trans (above.2 hd)⟩
    · rw [hStays hShapella]
      exact KeepsNonces.refl _ _
  exact withdrawals.trans ((blockRequests_keepsNonces (result := (requested, _)) hreq).trans
    (onBlock_payRewards_keepsNonces hrew))

/-- The body of a block keeps every account above a nonce. -/
theorem applyBody_keepsNonces {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) :
    KeepsNonces fork start output.block := by
  obtain ⟨_, _, before, htxs, after⟩ := applyBody_split h
  exact before.trans ((applyTransactions_keepsNonces htxs).trans after)

/-- Each transaction of a body from an account above `n` at the start has a nonce above `n`. -/
theorem applyBody_nonce_gt {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    {sender : Address} {n : Nat} (h : applyBody config env block start = .ok output)
    (above : NonceAbove fork n ((TransactionState.ofBlock start).getAccount sender))
    {tx : Transaction} (mem : tx ∈ block.transactions) (hs : recoverSender fork tx = .ok sender) :
    n < tx.nonce.toNat := by
  obtain ⟨_, _, before, htxs, -⟩ := applyBody_split h
  exact applyTransactions_nonce_gt htxs (before sender n above) mem hs

/-- After the body of a block, the sender of each transaction is above the nonce of that one. -/
theorem applyBody_sender_nonceAbove {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    {sender : Address} (h : applyBody config env block start = .ok output) {i : Nat}
    (hi : i < block.transactions.length)
    (hs : recoverSender fork block.transactions[i] = .ok sender) :
    NonceAbove fork block.transactions[i].nonce.toNat
      ((TransactionState.ofBlock output.block).getAccount sender) := by
  obtain ⟨_, _, -, htxs, after⟩ := applyBody_split h
  exact after sender _ (applyTransactions_sender_nonceAbove htxs hi hs)

/-- Of two transactions of one sender in a body, the later one has the higher nonce. -/
theorem applyBody_nonce_lt {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    {sender : Address} (h : applyBody config env block start = .ok output) {i i' : Nat}
    (lt : i < i') (hi' : i' < block.transactions.length)
    (hs : recoverSender fork (block.transactions[i]'(Nat.lt_trans lt hi')) = .ok sender)
    (hs' : recoverSender fork block.transactions[i'] = .ok sender) :
    (block.transactions[i]'(Nat.lt_trans lt hi')).nonce.toNat <
      block.transactions[i'].nonce.toNat := by
  obtain ⟨_, _, -, htxs, -⟩ := applyBody_split h
  exact applyTransactions_nonce_lt htxs lt hi' hs hs'

/-- Each transaction of a block that enters its body has a sender that its signature names. -/
theorem applyBody_exists_recoverSender {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) {tx : Transaction}
    (mem : tx ∈ block.transactions) : ∃ sender, recoverSender fork tx = .ok sender := by
  obtain ⟨_, _, -, htxs, -⟩ := applyBody_split h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp mem
  obtain ⟨_, _, -, hNext, -⟩ := (applyTransactions_keepsNonces_steps htxs).2 i hi
  obtain ⟨included, -, hcheck, -⟩ := applyTransaction_eq_ok hNext
  exact ⟨included.sender, (checkInclusion_ok hcheck).1⟩

/-! ## A chain of blocks -/

/-- The account at `address` in the state of a chain. -/
def BlockChain.account (chain : BlockChain) (address : Address) : Account :=
  (TransactionState.ofBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩).getAccount address

/-- A block that passes its transition runs its body on the state of its chain.

The state after it reads each account as the body leaves it. -/
theorem stateTransition_body {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post) :
    ∃ env output, applyBody chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      ∀ address, (TransactionState.ofBlock ⟨post, ∅, ∅, ∅, ∅⟩).getAccount address =
        (TransactionState.ofBlock output.block).getAccount address := by
  obtain ⟨-, -, -, _, output, _, -, hbody, -, -, rfl⟩ := stateTransition_eq_ok h
  exact ⟨_, output, hbody, State.BlockState.getAccount_applyChanges output.block⟩

/-- A run of blocks from a chain.

Each block passes its transition on the chain after the blocks before it.

That next chain holds the state after the block, and the block as its last recent block.

Its configuration and its older recent blocks are free, since no claim reads them. -/
inductive ChainRun : BlockChain → List ((fork : Fork) × Block fork Transaction) → Prop
  /-- No block. -/
  | nil (chain : BlockChain) : ChainRun chain []
  /-- A block that passes its transition, then a run from the chain after it. -/
  | cons {chain next : BlockChain} {fork : Fork} {block : Block fork Transaction}
      {post : State} {rest : List ((fork : Fork) × Block fork Transaction)} (checkSeal : Bool)
      (transition : stateTransition chain block checkSeal = .ok post)
      (state : next.state = post)
      (last : next.recent.getLast? = some ⟨fork, block.header, block.ommers⟩)
      (tail : ChainRun next rest) :
      ChainRun chain (⟨fork, block⟩ :: rest)

/-- The transaction at position `j` of the block at position `i`, with the fork of its block. -/
def transactionAt (blocks : List ((fork : Fork) × Block fork Transaction)) (i j : Nat) :
    Option (Fork × Transaction) := do
  let ⟨f, block⟩ ← blocks[i]?
  let tx ← block.transactions[j]?
  return (f, tx)

/-- The transactions of the first block of a run are those of that block, at its fork. -/
private theorem transactionAt_zero {block : Block fork Transaction}
    {rest : List ((fork : Fork) × Block fork Transaction)} {j : Nat} {f : Fork}
    {tx : Transaction} (h : transactionAt (⟨fork, block⟩ :: rest) 0 j = some (f, tx)) :
    f = fork ∧ ∃ hj : j < block.transactions.length, block.transactions[j] = tx := by
  simp only [transactionAt, bind, pure, List.getElem?_cons_zero, Option.bind_some] at h
  cases hj : block.transactions[j]? with
  | none => simp [hj] at h
  | some a =>
    simp only [hj, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hj
    exact ⟨rfl, hlt, heq⟩

/-- The transactions of a later block of a run are those of the rest of the run. -/
private theorem transactionAt_succ {b : (fork : Fork) × Block fork Transaction}
    {rest : List ((fork : Fork) × Block fork Transaction)} {i j : Nat} :
    transactionAt (b :: rest) (i + 1) j = transactionAt rest i j :=
  rfl

/-- An account above `n` at the fork of the last block sends later only nonces above `n`. -/
private theorem ChainRun.nonce_gt {chain : BlockChain}
    {blocks : List ((fork : Fork) × Block fork Transaction)} (run : ChainRun chain blocks)
    {parent : RecentBlock} (hlast : chain.recent.getLast? = some parent) {sender : Address}
    {n : Nat} (above : NonceAbove parent.fork n (chain.account sender)) {i j : Nat} {f : Fork}
    {tx : Transaction} (at₁ : transactionAt blocks i j = some (f, tx))
    (hs : recoverSender f tx = .ok sender) : n < tx.nonce.toNat := by
  induction run generalizing parent i with
  | nil => simp [transactionAt] at at₁
  | cons checkSeal transition state last tail ih =>
    obtain ⟨p, hp, hle⟩ := stateTransition_parent transition
    obtain rfl : p = parent := Option.some.inj (hp.symm.trans hlast)
    have above' := above.mono hle
    obtain ⟨env, output, hbody, hread⟩ := stateTransition_body transition
    cases i with
    | zero =>
      obtain ⟨rfl, hj, rfl⟩ := transactionAt_zero at₁
      exact applyBody_nonce_gt hbody above' (List.getElem_mem hj) hs
    | succ i =>
      refine ih last ?_ at₁
      unfold BlockChain.account
      rw [state, hread]
      exact applyBody_keepsNonces hbody sender n above'

/-- Each transaction of a run of blocks has a sender that its signature names. -/
private theorem ChainRun.exists_recoverSender {chain : BlockChain}
    {blocks : List ((fork : Fork) × Block fork Transaction)} (run : ChainRun chain blocks)
    {i j : Nat} {f : Fork} {tx : Transaction} (at₁ : transactionAt blocks i j = some (f, tx)) :
    ∃ sender, recoverSender f tx = .ok sender := by
  induction run generalizing i with
  | nil => simp [transactionAt] at at₁
  | cons checkSeal transition state last tail ih =>
    cases i with
    | zero =>
      obtain ⟨rfl, hj, rfl⟩ := transactionAt_zero at₁
      obtain ⟨env, output, hbody, -⟩ := stateTransition_body transition
      exact applyBody_exists_recoverSender hbody (List.getElem_mem hj)
    | succ i => exact ih at₁

/-- Of two transactions of one sender in a run of blocks, the later one has the higher nonce.

The position `(i, j)` is the transaction `j` of the block `i`, and it comes before `(i', j')`. -/
theorem ChainRun.nonce_lt {chain : BlockChain}
    {blocks : List ((fork : Fork) × Block fork Transaction)} (run : ChainRun chain blocks)
    {i j i' j' : Nat} {f f' : Fork} {tx tx' : Transaction} {sender : Address}
    (at₁ : transactionAt blocks i j = some (f, tx))
    (at₂ : transactionAt blocks i' j' = some (f', tx'))
    (hs : recoverSender f tx = .ok sender) (hs' : recoverSender f' tx' = .ok sender)
    (before : i < i' ∨ (i = i' ∧ j < j')) : tx.nonce.toNat < tx'.nonce.toNat := by
  induction run generalizing i i' with
  | nil => simp [transactionAt] at at₁
  | cons checkSeal transition state last tail ih =>
    obtain ⟨env, output, hbody, hread⟩ := stateTransition_body transition
    cases i with
    | zero =>
      obtain ⟨rfl, hj, rfl⟩ := transactionAt_zero at₁
      cases i' with
      | zero =>
        obtain ⟨rfl, hj', rfl⟩ := transactionAt_zero at₂
        have lt : j < j' := by omega
        exact applyBody_nonce_lt hbody lt hj' hs hs'
      | succ i' =>
        refine ChainRun.nonce_gt tail last ?_ at₂ hs'
        unfold BlockChain.account
        rw [state, hread]
        exact applyBody_sender_nonceAbove hbody hj hs
    | succ i =>
      cases i' with
      | zero => omega
      | succ i' => exact ih at₁ at₂ (by omega)

/-- Two positions of a run that hold transactions of one sender with one nonce are one position. -/
theorem ChainRun.eq_of_nonce_eq {chain : BlockChain}
    {blocks : List ((fork : Fork) × Block fork Transaction)} (run : ChainRun chain blocks)
    {i j i' j' : Nat} {f f' : Fork} {tx tx' : Transaction} {sender : Address}
    (at₁ : transactionAt blocks i j = some (f, tx))
    (at₂ : transactionAt blocks i' j' = some (f', tx'))
    (hs : recoverSender f tx = .ok sender) (hs' : recoverSender f' tx' = .ok sender)
    (nonce : tx.nonce = tx'.nonce) : i = i' ∧ j = j' := by
  have same : tx.nonce.toNat = tx'.nonce.toNat := by rw [nonce]
  rcases Nat.lt_trichotomy i i' with lt | rfl | lt
  · exact absurd (run.nonce_lt at₁ at₂ hs hs' (.inl lt)) (by omega)
  · rcases Nat.lt_trichotomy j j' with lt | rfl | lt
    · exact absurd (run.nonce_lt at₁ at₂ hs hs' (.inr ⟨rfl, lt⟩)) (by omega)
    · exact ⟨rfl, rfl⟩
    · exact absurd (run.nonce_lt at₂ at₁ hs' hs (.inr ⟨rfl, lt⟩)) (by omega)
  · exact absurd (run.nonce_lt at₂ at₁ hs' hs (.inl lt)) (by omega)

/-- Two positions of a run of blocks that hold one transaction are one position. -/
theorem ChainRun.eq_of_transactionAt {chain : BlockChain}
    {blocks : List ((fork : Fork) × Block fork Transaction)} (run : ChainRun chain blocks)
    {i j i' j' : Nat} {f f' : Fork} {tx : Transaction}
    (at₁ : transactionAt blocks i j = some (f, tx))
    (at₂ : transactionAt blocks i' j' = some (f', tx)) : i = i' ∧ j = j' := by
  obtain ⟨sender, hs⟩ := run.exists_recoverSender at₁
  obtain ⟨sender', hs'⟩ := run.exists_recoverSender at₂
  obtain rfl := recoverSender_eq_of_ok hs hs'
  exact run.eq_of_nonce_eq at₁ at₂ hs hs' rfl

end EthLib.Execution.Blocks
