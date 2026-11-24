module

public import EthLib.Execution.Proofs.Blocks.Codes
public import EthLib.Execution.Proofs.Blocks.Funded
public import EthLib.Execution.Proofs.Blocks.Halts
public import EthLib.Execution.Proofs.Blocks.NoAccount
public import EthLib.Execution.Proofs.Blocks.Overflow
public import EthLib.Execution.Proofs.Blocks.StateAborts

/-!
# Proofs: the transition of a block never aborts on a state that holds what it needs

The transition fails in three ways: the block is invalid, the run aborts, or the state fails.

An error of the state is a missing account, a missing code, a short balance or an overflow.

Five hypotheses exclude every abort and every error of the state.

One of them bounds every nonce by `2^64 - 1`, as [EIP-2681][e2681] does.

[e2681]: https://eips.ethereum.org/EIPS/eip-2681#specification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.Transactions (Transaction)

variable {fork : Fork}

/-- Before Hegotá, the transition of a block fails only with an error that makes it invalid.

A root or a parent with a field of `2^64` bytes or more also counts as an invalid block. -/
theorem stateTransition_eq_error_invalid {chain : BlockChain} {block : Block fork Transaction}
    -- The fork is before Hegotá, whose rules are not yet specified.
    {checkSeal : Bool} {e : BlockError} (before : fork < .hegota)
    -- Every nonce of the state is at most `2^64 - 1`, by EIP-2681.
    --
    -- The state holds the code of every account.
    (hfit : chain.state.NoncesFit) (available : chain.state.HasCodes)
    -- The supply plus the ether that the block creates leaves room for every credit.
    (room : SupplyRoom fork (chain.state.supply + createdWei block))
    -- The numbers of the header that an instruction pushes as words are below `2^256`.
    (hwords : ∀ hashes, (blockEnvironment chain.config hashes block.header).WordsFit)
    (h : stateTransition chain block checkSeal = .error e) :
    -- The transition neither aborts nor fails with an error of the state.
    (∀ error, e ≠ .aborted error) ∧ (∀ error, e ≠ .state error) ∧
      -- A system call that must succeed fails only with an error that does not abort, on any state.
      (∀ address error, e = .systemCallFailed address error → error.aborts = false) ∧
      -- The state holds the code of every sender, so no transaction is invalid for a missing code.
      ∀ index codeHash, e ≠ .invalidTransaction index (.missingCode codeHash) := by
  -- No error of the state occurs, as an abort or as an error of the block.
  have noState : ∀ error : State.StateError,
      e ≠ .aborted (.state error) ∧ e ≠ .state error := by
    intro error
    cases error with
    | noAccount a =>
      exact stateTransition_ne_noAccount chain block checkSeal a |>.imp (· ∘ (· ▸ h))
        (· ∘ (· ▸ h))
    | missingCode c =>
      exact stateTransition_ne_missingCode chain block checkSeal available c |>.imp
        (· ∘ (· ▸ h)) (· ∘ (· ▸ h))
    | insufficientBalance a =>
      exact stateTransition_ne_insufficientBalance chain block checkSeal a |>.imp
        (· ∘ (· ▸ h)) (· ∘ (· ▸ h))
    | balanceOverflow a =>
      exact stateTransition_ne_balanceOverflow chain block checkSeal room a |>.imp
        (· ∘ (· ▸ h)) (· ∘ (· ▸ h))
  refine ⟨fun error he => ?_, fun error he => (noState error).2 he, fun address error he => ?_,
    fun index codeHash he => ?_⟩
  -- Under the hypotheses, an abort can only be an error of the state, which cannot occur.
  · subst he
    obtain ⟨s, rfl⟩ := stateTransition_aborted before hfit hwords h
    exact (noState s).1 rfl
  · subst he
    exact stateTransition_systemCallFailed h
  · subst he
    exact stateTransition_ne_invalidTransaction_missingCode chain block checkSeal available index
      codeHash h

end EthLib.Execution.Blocks
