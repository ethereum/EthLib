module

public import EthLib.Execution.Blocks.Header
public import EthLib.Execution.Evm.Gas.Prices
public import EthLib.Execution.State.Tracker

/-!
# `Blocks.Rewards`

The mining rewards of a block before Paris.

The beneficiary of a block gains the block reward, and a 32nd of it for each ommer.

The beneficiary of each ommer gains the block reward, less an 8th of it per block of its age.

The block reward is 5 ether before Byzantium, 3 ether from Byzantium, and 2 from Constantinople.

From Paris on, no block pays a reward.

Section 11.3 of the Yellow Paper, Berlin version, defines the rewards: [`Paper.tex`][yp].

[EIP-649][eip-649] and [EIP-1234][eip-1234] lower the block reward.

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[eip-649]: https://eips.ethereum.org/EIPS/eip-649#specification
[eip-1234]: https://eips.ethereum.org/EIPS/eip-1234#specification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State

/-- The block reward at a fork before Paris: `R_block` of the Yellow Paper, 11.3, in wei. -/
def blockReward (fork : Fork) : Nat :=
  (Evm.gasSchedule fork).BLOCK_REWARD

/-- The reward of the beneficiary of a block with `ommers` ommers: `(1 + n / 32) · R_block`.

The 32nd of the block reward is rounded down, which leaves it exact for every fork. -/
def minerReward (fork : Fork) (ommers : Nat) : Nat :=
  -- §11.3: `(1 + ||B_U|| / 32) R_block`, as `R_block + ||B_U|| × (R_block / 32)`.
  --
  -- That is exact, since 32 divides each `R_block`.
  blockReward fork + ommers * (blockReward fork / 32)

/-- The reward of the beneficiary of an ommer `age` blocks older than the block.

It is `(1 + (U_i - H_i) / 8) · R_block = (8 - age) · R_block / 8` of the Yellow Paper, 11.3. -/
def ommerReward (fork : Fork) (age : Nat) : Nat :=
  -- §11.3: `R = (1 + (U_i - H_i) / 8) R_block`, and `U_i - H_i = -age`.
  --
  -- EIP-649 writes `(8 - k) R_block / 8`, exact since 8 divides `R_block`.
  (8 - age) * blockReward fork / 8

/-- Pay the rewards of a block at `number`: its beneficiary first, then each ommer's.

Each ommer is given by its beneficiary and its number.

From Paris on there is no reward, and the state is unchanged. -/
def payRewards (fork : Fork) (tx : TransactionState) (coinbase : Address) (number : Nat)
    (ommers : List (Address × Nat)) : Except StateError TransactionState :=
  -- From Paris, EIP-3675 ends the rewards.
  if .paris ≤ fork then .ok tx
  else do
    -- §11.3, `Omega`: `sigma'[B_H_c]_b = sigma[B_H_c]_b + (1 + ||B_U|| / 32) R_block`.
    let tx ← tx.createEther fork coinbase (BitVec.ofNat 256 (minerReward fork ommers.length))
    -- Then `sigma'[U_c]_b = sigma[U_c]_b + R` for each ommer `U`, summed for a shared address.
    ommers.foldlM
      (fun tx (beneficiary, ommerNumber) => tx.createEther fork beneficiary
        (BitVec.ofNat 256 (ommerReward fork (number - ommerNumber))))
      tx

end EthLib.Execution.Blocks
