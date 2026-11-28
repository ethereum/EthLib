module

public import EthLib.Execution.Proofs.Blocks.Supply
public import EthLib.Execution.Proofs.Blocks.Validate
public import EthLib.Execution.Proofs.Fees.BaseFee

/-!
# Proofs: the supply of ether bounds the base fee that a block passes on

A block burns its base fee for each unit of gas it uses, out of the supply before it.

The base fee rises only after a block above its target, so it is at most what that supply pays.

So the base fee that a block passes on stays below `2^64` when its own does.

That needs the supply over the target below `2^63`.

Source: [EIP-1559][eip1559], the base fee and its burn.

[eip1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Fees.BaseFee
open EthLib.Execution.State (State)
open EthLib.Execution.Transactions (Transaction)

/-- A block burns its gas used at its base fee out of the supply before it and what it creates.

It also uses at most its gas limit.

The block passes the transition, from London to before Glamsterdam. -/
private theorem paid_of_stateTransition {chain : BlockChain} {fork : Fork}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (hLondon : .london ≤ fork) (hFork : fork < .glamsterdam)
    (h : stateTransition chain block checkSeal = .ok post) :
    block.header.gasUsed ≤ block.header.gasLimit ∧
      block.header.baseFeePerGas hLondon * block.header.gasUsed ≤
        chain.state.supply + createdWei block := by
  obtain ⟨hashes, -, hle⟩ := stateTransition_supply_le_of_lt_glamsterdam hFork h
  -- The burn of the header counts the gas used at the base fee of the block.
  have burn : block.header.gasUsed * block.header.baseFeePerGas hLondon ≤
      headerBurnedWei (blockEnvironment chain.config hashes block.header) block.header := by
    simp only [headerBurnedWei, Transactions.baseFeeOf, hLondon, ↓reduceDIte, blockEnvironment]
    exact Nat.le_add_right _ _
  -- A block that passes its checks uses at most its gas limit.
  obtain ⟨parent, -, hParent, hhead⟩ := checkBlock_checkHeader (stateTransition_eq_ok h).2.2.1
  obtain ⟨-, -, -, used, -⟩ := checkHeader_eq_ok_iff.mp hhead
  refine ⟨used, ?_⟩
  rw [Nat.mul_comm]
  omega

/-- The base fee that a block passes on is at most its own, or what the supply before it pays.

What the supply pays is the fee after a full block at `S / (t + 1)`.

Here `S` is the supply before the block plus the ether it creates, and `t` is its target.

The block passes the transition, from London to before Glamsterdam. -/
theorem stateTransition_expectedBaseFee_le {chain : BlockChain} {fork : Fork}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (hLondon : .london ≤ fork) (hFork : fork < .glamsterdam)
    (h : stateTransition chain block checkSeal = .ok post) :
    expectedBaseFee hLondon block.header ≤
      max (block.header.baseFeePerGas hLondon)
        (calculateBaseFeePerGas block.header.gasLimit block.header.gasLimit
          ((chain.state.supply + createdWei block) /
            (block.header.gasLimit / ELASTICITY_MULTIPLIER + 1))) :=
  let ⟨used, paid⟩ := paid_of_stateTransition hLondon hFork h
  calculateBaseFeePerGas_le_of_mul_le used paid

/-- The base fee that a block passes on is below `2^64` while the supply over the target is small.

The block's own base fee is below `2^64`.

The supply before it plus the ether it creates, over its target plus one, is below `2^63`.

The block passes the transition, from London to before Glamsterdam. -/
theorem stateTransition_expectedBaseFee_lt_two_pow_64 {chain : BlockChain} {fork : Fork}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (hLondon : .london ≤ fork) (hFork : fork < .glamsterdam)
    (h : stateTransition chain block checkSeal = .ok post)
    (fee : block.header.baseFeePerGas hLondon < 2 ^ 64)
    (small : (chain.state.supply + createdWei block) /
      (block.header.gasLimit / ELASTICITY_MULTIPLIER + 1) < 2 ^ 63) :
    expectedBaseFee hLondon block.header < 2 ^ 64 :=
  let ⟨used, paid⟩ := paid_of_stateTransition hLondon hFork h
  calculateBaseFeePerGas_lt_two_pow_64 used paid fee small

end EthLib.Execution.Blocks
