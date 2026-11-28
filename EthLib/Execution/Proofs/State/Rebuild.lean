module

public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: a property of states under which a block state can be rebuilt

A block state can be rebuilt when its code matches its hash and no plain account holds storage.

A plain account has nonce 0 and no code, and a missing account counts as one.

Only such an account loses its storage to a creation, and a block access list cannot record that.

Adding ether cannot make a nonempty account empty.
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- Returned code matches its hash, and an account with nonce 0 and no code has only zero storage.

[EIP-8253][eip8253], a draft, would restore this invariant, which 28 accounts of mainnet break.

A creation at such an account wipes its storage, which a block access list does not record.

[eip8253]: https://github.com/ethereum/EIPs/blob/d2be3735b2f894e1e35f54de408159b5c7e14a94/EIPS/eip-8253.md#motivation -/
structure RebuildInvariant (tx : TransactionState) : Prop where
  /-- Each returned code has the hash under which it is read. -/
  code : ∀ hash code, tx.getCode hash = .ok code → keccak256 code = hash
  /-- Accounts with nonce 0 and no code, missing ones too, hold no nonzero storage word. -/
  storage : ∀ address, (tx.getAccount address).nonce = 0 →
    (tx.getAccount address).codeHash = EMPTY_CODE_HASH → ∀ key, tx.getStorage address key = 0

/-- A block state can be rebuilt when, with no write on top, the property above holds. -/
def Rebuildable (block : BlockState) : Prop :=
  RebuildInvariant (TransactionState.ofBlock block)

/-- Adding ether cannot make a nonempty account empty. -/
theorem getAccount_eq_empty_of_createEther {fork : Fork}
    {tx tx' : TransactionState} {target : Address} {amount : U256}
    (h : tx.createEther fork target amount = .ok tx') (address : Address)
    (empty : tx'.getAccount address = EMPTY_ACCOUNT) : tx.getAccount address = EMPTY_ACCOUNT := by
  obtain ⟨balance, nonce, code⟩ := TransactionState.getAccount_createEther h address
  cases old : tx.getAccount address with
  | mk n b c =>
    simp only [old, empty, EMPTY_ACCOUNT] at balance nonce code ⊢
    change 0 = b.toNat + _ at balance
    have zero : b = 0 := by
      apply BitVec.eq_of_toNat_eq
      change b.toNat = 0
      omega
    subst n
    subst c
    subst b
    rfl

end EthLib.Execution.State
