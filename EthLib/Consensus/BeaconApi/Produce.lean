module

public import EthLib.Base.Denominations
public import EthLib.Consensus.BeaconApi.Rewards

/-!
# `Consensus.BeaconApi.Produce`

The answers of the Beacon API that produce a block for a validator.

A response of the [v3] and [v4] block production endpoints carries the value of the block.

Its [consensus block value] is what the proposer earns from the block, in Wei.

The source sums the proposer rewards "from attestations, sync committees and slashings".

So it is the total of the block rewards of the block, at 10^9 Wei per Gwei.

[v3]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/validator/block.v3.yaml
[v4]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/validator/block.v4.yaml
[consensus block value]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/beacon-node-oapi.yaml#L615-L624
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork}

/-- What the proposer of a block earns from it, in Wei, from the state of the slot of the block.

It is the total of the block rewards, at 10^9 Wei per Gwei. -/
def consensusBlockValue (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError Nat := do
  return (← blockRewards config checks engine state block).total.toNat * GWEI_TO_WEI

end EthLib.Consensus.BeaconApi
