module

public import EthLib.Execution.Proofs.Evm.Call.Supply
public import EthLib.Execution.Proofs.Transactions.Deletion

/-!
# Proofs: a transaction creates no ether, and burns its base fee and its blob fee

The supply of a state is the sum of its balances, and a transaction changes it in four steps.

The sender buys the gas: it pays the gas limit at the price per gas, and the fee of its blobs.

The message then keeps or lowers the supply, since only SELFDESTRUCT can burn ether in it.

The settlement gives back the gas left to the sender, and the priority fee to the beneficiary.

Before Glamsterdam, the deletions at the end remove the balance of each account marked to delete.

So the supply drops by at least the burned fees.

Those are the base fee of each unit of gas used, and the fee of the blobs.

[EIP-1559][e1559] burns the base fee, and [EIP-4844][e4844] burns the fee of the blobs.

Before London the base fee is 0, and before Cancun there are no blobs.

From Glamsterdam the supply drops by exactly the burned fees.

There, SELFDESTRUCT and the deletion keep the balance of the account, by [EIP-8246][e8246].

From Cancun, it drops by exactly the burned fees when the transaction ends with no created account.

There, only an account created in the transaction can be burned or deleted, by [EIP-6780][e6780].

Before Cancun, SELFDESTRUCT and the deletions can burn any balance, beyond the burned fees.

[e1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
[e4844]: https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
[e6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
[e8246]: https://eips.ethereum.org/EIPS/eip-8246#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.Fees.BlobBaseFee (calculateTotalBlobGas)
open State.TransactionState (supply balanceOf)

variable {fork : Fork} {tx : Transaction}

/-! ## The burned fees -/

/-- The wei that a transaction burns for its gas and its blobs, at `fork`, from its gas used.

It is the base fee per gas times the gas used, plus the base fee per blob gas times the blob gas. -/
def burnedFees (env : BlockEnvironment fork) (tx : Transaction) (gasUsed : Nat) : Nat :=
  gasUsed * baseFeeOf env + calculateTotalBlobGas tx * blobGasPriceOf env

/-! ## The authorizations and the first frame -/

section Meter

variable {Meter : Type} [GasMeter Meter]

/-- An authorization keeps the supply: it only sets a code and raises a nonce. -/
theorem supply_applyAuthorization {chainId : Nat} {done done' : Delegations Meter}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok done') :
    done'.state.supply = done.state.supply := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · rfl
  · exact State.TransactionState.supply_recordAccountRead _ _
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    obtain ⟨coded, hcode, hdelegate⟩ := bind_ok_iff.mp hdelegate
    obtain ⟨bumped, hnonce, hdelegate⟩ := bind_ok_iff.mp hdelegate
    cases hdelegate
    have e1 := State.TransactionState.supply_setCode hcode
    simp only [State.TransactionState.supply_recordAccountRead] at e1
    exact (State.TransactionState.supply_incrementNonce hnonce).trans e1

/-- Authorizations that succeed keep the supply. -/
theorem supply_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      done.state.supply = start.state.supply
  | [], _, _, h => by
    cases h
    rfl
  | _ :: _, _, _, h => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    exact (supply_foldlM_applyAuthorization h).trans (supply_applyAuthorization hnext)

/-- The first frame of a transaction starts with the supply of the state before it. -/
theorem supply_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    first.state.supply = state.supply := by
  have read : ∀ (s : State.TransactionState) (address : Address),
      (s.recordAccountRead address).supply = s.supply :=
    State.TransactionState.supply_recordAccountRead
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact read _ _
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact read _ _
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target _
    dsimp only at h
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have hauth : done.state.supply = state.supply := supply_foldlM_applyAuthorization hdone
    -- After the authorizations, the first frame only records reads.
    generalize hread : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = read0 at h
    have base : read0.supply = state.supply := by
      subst hread
      split
      · exact (read _ _).trans hauth
      · exact hauth
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact (read _ _).trans base
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact (read _ _).trans ((read _ _).trans base)

/-- The message of a transaction keeps or lowers the supply, at every fork.

It keeps it from Glamsterdam, and from Cancun when the end state has no created account. -/
theorem supplyLe_processMessageCall [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    SupplyLe fork state output.state := by
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      exact SupplyLe.of_eq rfl rfl
  rename_i first hfirst
  have start : SupplyLe fork state first.state :=
    SupplyLe.of_eq (supply_prepareFirstFrame hfirst) (createdAccounts_prepareFirstFrame hfirst)
  split at h
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    rw [state_ofFrame]
    exact start.trans (supplyLe_processCreateMessage hrun)
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    rw [state_ofFrame]
    exact start.trans (supplyLe_processMessage hrun)

end Meter

/-! ## The purchase and the settlement of gas -/

/-- Buying the gas lowers the supply by the gas limit times the price per gas, plus the blob fee. -/
theorem supply_buyGas {env : BlockEnvironment fork} {state state' : State.TransactionState}
    {sender : Address} (h : buyGas env state sender tx = .ok state') :
    state'.supply + (tx.gas.toNat * effectiveGasPrice (baseFeeOf env) tx +
        calculateTotalBlobGas tx * blobGasPriceOf env) = state.supply ∧
      state'.createdAccounts = state.createdAccounts := by
  have hsender := buyGas_sender rfl h
  unfold buyGas at h
  obtain ⟨mid, hnonce, hfee⟩ := bind_ok_iff.mp h
  have hmid := State.TransactionState.supply_incrementNonce hnonce
  obtain ⟨account, hf, hsum⟩ := State.TransactionState.supply_modifyState hfee
  obtain ⟨hself, -⟩ := State.TransactionState.getAccount_incrementNonce hnonce
  obtain ⟨-, hread, -⟩ := State.TransactionState.modifyState_eq_ok hfee
  refine ⟨?_, (State.TransactionState.createdAccounts_modifyState hfee).trans
    (State.TransactionState.createdAccounts_modifyState hnonce)⟩
  have hacc : account.balance.toNat = (state'.getAccount sender).balance.toNat := by
    obtain ⟨account', hf', hread', -⟩ := State.TransactionState.modifyState_eq_ok hfee
    rw [hf, Except.ok.injEq] at hf'
    rw [hf', hread']
  have hbal : mid.balanceOf sender = (state.getAccount sender).balance.toNat := by
    unfold balanceOf
    rw [hself]
  rw [hacc, hsender.2.1, hbal] at hsum
  have := hsender.1
  omega

/-- A credit of `amount` wei adds it to the supply. -/
theorem supply_creditEther {state state' : State.TransactionState} {address : Address}
    {amount : Nat} (h : creditEther fork state address amount = .ok state') :
    state'.supply = state.supply + amount ∧ state'.createdAccounts = state.createdAccounts := by
  unfold creditEther at h
  split at h
  · rename_i hlt
    refine ⟨?_, State.TransactionState.createdAccounts_modifyState h⟩
    rw [State.TransactionState.supply_createEther h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · cases h

/-- The payment of the priority fee adds the fee to the supply. -/
theorem supply_payBeneficiary {state state' : State.TransactionState} {coinbase : Address}
    {fee : Nat} (h : payBeneficiary fork state coinbase fee = .ok state') :
    state'.supply = state.supply + fee ∧ state'.createdAccounts = state.createdAccounts := by
  unfold payBeneficiary at h
  split at h
  · -- A fee of 0 to an empty beneficiary deletes it, and its balance is 0.
    rename_i hzero
    cases h
    have hfee : fee = 0 := by omega
    subst hfee
    split
    · rename_i hempty
      have := State.TransactionState.supply_destroyAccount state coinbase
      have hbal : state.balanceOf coinbase = 0 := by
        unfold balanceOf
        rw [State.TransactionState.eq_empty_of_accountExistsAndIsEmpty hempty]
        rfl
      exact ⟨by omega, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact supply_creditEther h

/-- Settling the gas adds the refund of the sender and the priority fee to the supply. -/
theorem supply_settleGas {env : BlockEnvironment fork} {state state' : State.TransactionState}
    {sender : Address} {gasLeft refund used : Nat}
    (h : settleGas env state sender tx gasLeft refund = .ok (state', used)) :
    let s := settlement fork (baseFeeOf env) sender tx gasLeft refund
    state'.supply = state.supply + s.senderRefund + s.priorityFee := by
  unfold settleGas at h
  obtain ⟨refunded, hrefund, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, hpay, h⟩ := bind_ok_iff.mp h
  cases h
  obtain ⟨h1, -⟩ := supply_creditEther hrefund
  obtain ⟨h2, -⟩ := supply_payBeneficiary hpay
  rw [h2, h1]

/-! ## The deletions -/

/-- The deletions at the end of a transaction keep or lower the supply, and keep created accounts.

They keep the supply from Glamsterdam, or when no account is to be deleted. -/
theorem supply_deleteAccounts {state state' : State.TransactionState} {output : CallOutput}
    (h : deleteAccounts fork state output = .ok state') :
    state'.supply ≤ state.supply ∧ state'.createdAccounts = state.createdAccounts ∧
      (.glamsterdam ≤ fork ∨ (∀ address, address ∉ output.accountsToDelete) →
        state'.supply = state.supply) := by
  have fold : ∀ (l : List Address) (init final : State.TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      final.supply ≤ init.supply ∧ final.createdAccounts = init.createdAccounts ∧
        (.glamsterdam ≤ fork ∨ l = [] → final.supply = init.supply) := by
    intro l
    induction l with
    | nil =>
      intro init final h
      cases h
      exact ⟨Nat.le_refl _, rfl, fun _ => rfl⟩
    | cons address rest ih =>
      intro init final h
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      obtain ⟨hle, hc, heq⟩ := ih mid final h
      split at hmid
      · rename_i hglam
        have hs := State.TransactionState.supply_clearAccountPreservingBalance hmid
        have hcm : mid.createdAccounts = init.createdAccounts := by
          dsimp only at hmid
          unfold State.TransactionState.clearAccountPreservingBalance at hmid
          rw [State.TransactionState.createdAccounts_modifyState hmid]; rfl
        exact ⟨by omega, hc.trans hcm, fun _ => (heq (.inl hglam)).trans hs⟩
      · cases hmid
        have := State.TransactionState.supply_destroyAccount init address
        refine ⟨by omega, hc, fun hcase => ?_⟩
        rcases hcase with hglam | hnil
        · exact absurd hglam ‹_›
        · cases hnil
  unfold deleteAccounts at h
  obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hmid
  obtain ⟨hle, hc, heq⟩ := fold _ _ _ hmid
  have hcreated : ∀ (touched : List Address) (s : State.TransactionState),
      (s.destroyTouchedEmptyAccounts fork touched).createdAccounts = s.createdAccounts := by
    intro touched s
    unfold State.TransactionState.destroyTouchedEmptyAccounts
    split
    · rfl
    · induction touched generalizing s with
      | nil => rfl
      | cons address rest ih =>
        rw [List.foldl_cons, ih]
        split <;> rfl
  rw [State.TransactionState.supply_destroyTouchedEmptyAccounts, hcreated]
  refine ⟨hle, hc, fun hcase => heq ?_⟩
  rcases hcase with hglam | hnone
  · exact .inl hglam
  · exact .inr (List.eq_nil_iff_forall_not_mem.mpr fun address hmem =>
      hnone address (Std.ExtTreeSet.mem_toList.mp hmem))

/-! ## The transaction -/

/-- A transaction that runs with any gas meter lowers the supply by at least its burned fees.

It lowers it by exactly those fees from Glamsterdam, and from Cancun when it creates no account.

Its gas limit must cover the least gas, and its price must cover the base fee. -/
theorem runTransaction_supply {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : State.BlockState} {included : Included}
    {out : TransactionOutput}
    (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : runTransaction Meter env block included tx = .ok out) :
    out.state.supply + burnedFees env tx out.gasUsed ≤
        (State.TransactionState.ofBlock block).supply ∧
      (BurnsNone fork out.state →
        out.state.supply + burnedFees env tx out.gasUsed =
          (State.TransactionState.ofBlock block).supply) := by
  obtain ⟨target, bought, message, output, settled, -, hbought, -, houtput, -, hs, hd⟩ :=
    runTransaction_eq_ok h
  obtain ⟨hbuy, -⟩ := supply_buyGas hbought
  have hmsg := supplyLe_processMessageCall houtput
  have hset := supply_settleGas hs
  have cset := createdAccounts_settleGas hs
  obtain ⟨hdel, cdel, hdelEq⟩ := supply_deleteAccounts hd
  have hused := settleGas_gasUsed hs
  have conserve := settlement_conserves hMin hPrice (output.gasLeft + output.reservoir)
    output.refund
  dsimp only at hset conserve
  simp only [settlement] at hset conserve
  simp only [burnedFees]
  rw [hused]
  generalize gasUsed fork included.sender tx (output.gasLeft + output.reservoir) output.refund =
    g at hset conserve ⊢
  refine ⟨by have := hmsg.1; omega, fun burns => ?_⟩
  -- The message burns nothing, and neither do the deletions.
  have burnsOut : BurnsNone fork output.state := by
    unfold BurnsNone at burns ⊢
    rwa [cdel, cset] at burns
  have hmsgEq := hmsg.2.2 burnsOut
  have hdelSame : out.state.supply = settled.supply := by
    refine hdelEq ?_
    rcases burnsOut with hglam | ⟨hdencun, hnone⟩
    · exact .inl hglam
    · exact .inr fun address hmem => hnone address
        (accountsToDelete_processMessageCall hdencun houtput (by simp) address hmem)
  omega

/-- A transaction that runs lowers the supply by at least its burned fees, at every fork.

It lowers it by exactly those fees from Glamsterdam, and from Cancun when it creates no account.

The gas limit must cover the least gas, and the price must cover the base fee.

The checks of the block ensure both. -/
theorem processTransaction_supply {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {out : TransactionOutput}
    (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : processTransaction env block included tx = .ok out) :
    out.state.supply + burnedFees env tx out.gasUsed ≤
        (State.TransactionState.ofBlock block).supply ∧
      (BurnsNone fork out.state →
        out.state.supply + burnedFees env tx out.gasUsed =
          (State.TransactionState.ofBlock block).supply) := by
  unfold processTransaction at h
  split at h
  · cases h
  split at h
  · exact runTransaction_supply hMin hPrice h
  · exact runTransaction_supply hMin hPrice h

/-- A transaction that runs lowers the supply by at least its burned fees, at every fork.

The burned fees are the base fee per gas times the gas used.

From Cancun, they add the base fee per blob gas times the blob gas.

The gas limit must cover the least gas, and the price must cover the base fee.

The checks of the block ensure both. -/
theorem processTransaction_supply_le {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {out : TransactionOutput}
    (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : processTransaction env block included tx = .ok out) :
    out.state.supply + burnedFees env tx out.gasUsed ≤
      (State.TransactionState.ofBlock block).supply :=
  (processTransaction_supply hMin hPrice h).1

/-- From Glamsterdam, a transaction that runs lowers the supply by exactly its burned fees.

The gas limit must cover the least gas, and the price must cover the base fee.

The checks of the block ensure both. -/
theorem processTransaction_supply_of_glamsterdam {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {out : TransactionOutput}
    (hfork : .glamsterdam ≤ fork) (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : processTransaction env block included tx = .ok out) :
    out.state.supply + burnedFees env tx out.gasUsed =
      (State.TransactionState.ofBlock block).supply :=
  (processTransaction_supply hMin hPrice h).2 (.inl hfork)

/-- From Cancun, a transaction that ends with no created account lowers the supply by its fees.

It lowers it by exactly its burned fees.

No creation of it may have passed its preparation, not even one that then reverted.

The gas limit must cover the least gas, and the price must cover the base fee.

The checks of the block ensure both. -/
theorem processTransaction_supply_of_dencun {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {out : TransactionOutput}
    (hfork : .dencun ≤ fork) (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : processTransaction env block included tx = .ok out)
    (created : ∀ address, address ∉ out.state.createdAccounts) :
    out.state.supply + burnedFees env tx out.gasUsed =
      (State.TransactionState.ofBlock block).supply :=
  (processTransaction_supply hMin hPrice h).2 (.inr ⟨hfork, created⟩)

end EthLib.Execution.Transactions
