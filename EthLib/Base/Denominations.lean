module

/-!
# `Base.Denominations`

The units of ether that both layers use.
-/

@[expose] public section

namespace EthLib.Base

/-- The Wei in one Gwei.

The execution layer counts balances in Wei, and the consensus layer counts them in Gwei.

The withdrawals of [EIP-4895] convert their amounts by this factor.

[EIP-4895]: https://eips.ethereum.org/EIPS/eip-4895#specification -/
def GWEI_TO_WEI : Nat := 10 ^ 9

end EthLib.Base
