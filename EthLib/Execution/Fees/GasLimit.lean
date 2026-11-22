module

public import EthLib.Base.Fork
public import EthLib.Execution.Fees.BaseFee

/-!
# `Fees.GasLimit`

The rule that bounds the gas limit of a block by the gas limit of its parent.

A producer can raise or lower the gas limit only slowly, block after block.

Section 4.4.4 of the Yellow Paper, Shanghai version, states the rule: [`Paper.tex`][yp].

Each relation of the rule is marked on its line, with the parent's gas limit `P(H)_H_l'` it reads.

[EIP-1559][eip-1559] doubles the parent's gas limit at the fork block in the same way.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip-1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
-/

@[expose] public section

namespace EthLib.Execution.Fees.GasLimit

/-- The gas limit moves by less than the parent's gas limit over this. -/
def LIMIT_ADJUSTMENT_FACTOR : Nat := 1024

/-- The smallest gas limit of a block. -/
def LIMIT_MINIMUM : Nat := 5000

/-- Whether a gas limit may follow the gas limit of the parent. -/
def checkGasLimit (gasLimit parentGasLimit : Nat) : Bool :=
  -- The parent's gas limit here is already `P(H)_H_l'`.
  --
  -- `floor(P(H)_H_l' / 1024)`, computed once for the two bounds.
  let maxAdjustmentDelta := parentGasLimit / LIMIT_ADJUSTMENT_FACTOR
  -- `H_l < P(H)_H_l' + floor(P(H)_H_l' / 1024)`.
  decide (gasLimit < parentGasLimit + maxAdjustmentDelta) &&
    -- `H_l > P(H)_H_l' - floor(P(H)_H_l' / 1024)`.
    --
    -- The subtraction never stops at 0, since a 1024th of a gas limit is at most the gas limit.
    decide (parentGasLimit - maxAdjustmentDelta < gasLimit) &&
    -- `H_l >= 5000`.
    decide (LIMIT_MINIMUM ≤ gasLimit)

open EthLib.Base in
/-- The gas limit `P(H)_H_l'` that the rule reads, for a parent at `parentFork`.

The child is at `fork`.

At the first London block, the parent's gas limit is doubled.

So the gas target after London can match the gas limit before it. -/
def parentGasLimitForCheck (parentFork fork : Fork) (parentGasLimit : Nat) : Nat :=
  -- `P(H)_H_l' = P(H)_H_l * rho` if `H_i = F_London`, with `rho = 2`.
  --
  -- The first London block is the one whose parent is before London.
  if parentFork < .london ∧ .london ≤ fork then
    parentGasLimit * BaseFee.ELASTICITY_MULTIPLIER
  -- `P(H)_H_l' = P(H)_H_l` if `H_i > F_London`.
  --
  -- The paper defines `P(H)_H_l'` only from London on.
  --
  -- Before London, the rule reads `P(H)_H_l` itself.
  else
    parentGasLimit

open EthLib.Base in
/-- Whether a gas limit at `fork` may follow the gas limit of a parent at `parentFork`.

The header checks from Paris on have a parent from London on, so they use the plain rule. -/
def checkGasLimitAcross (parentFork fork : Fork) (gasLimit parentGasLimit : Nat) : Bool :=
  -- The three relations on `H_l`, against `P(H)_H_l'`.
  checkGasLimit gasLimit (parentGasLimitForCheck parentFork fork parentGasLimit)

end EthLib.Execution.Fees.GasLimit
