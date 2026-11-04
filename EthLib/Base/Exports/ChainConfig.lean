module

public import EthLib.Base.ChainConfig

/-!
# Exports: the active fork of mainnet

The C export of the active fork of mainnet, for the Python bindings.

A block number and a timestamp cross the boundary as 64-bit integers, as EIP-6122 reads them.

A fork crosses it as its name in UTF-8, such as `bellatrix`.
-/

public section

namespace EthLib.Base.ChainConfig.Exports

/-- The name of the active fork of mainnet at a block, or no bytes when no fork is active. -/
@[export eth_mainnet_active_fork]
def mainnetActiveForkExport (number timestamp : UInt64) : ByteArray :=
  match mainnet.activeFork number.toNat timestamp.toNat with
  | some fork => fork.name.toUTF8
  | none => .empty

end EthLib.Base.ChainConfig.Exports
