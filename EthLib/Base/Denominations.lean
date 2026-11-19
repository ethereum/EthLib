module

/-!
# `Base.Denominations`

The units of ether that both layers use.

The execution layer counts balances in Wei, and the consensus layer counts them in Gwei.

One Gwei is 10^9 Wei, as the withdrawals of [EIP-4895] convert their amounts.

[EIP-4895]: https://eips.ethereum.org/EIPS/eip-4895#specification
-/

@[expose] public section

namespace EthLib.Base

/-- The Wei in one Gwei. -/
def GWEI_TO_WEI : Nat := 10 ^ 9

end EthLib.Base
