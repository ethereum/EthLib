module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Execution.Evm.Precompiles.Table

/-!
# `Exports.Precompiles`

C-ABI exports that run any precompile, and give its price, at a fork named by the caller.

A fork with no precompile at the address gives an error with code 0.

Glamsterdam keeps the precompiles of BPO2, and Hegotá is not yet specified.
-/

public section

namespace EthLib.Execution.Evm.Precompiles.Exports

open EthLib.Exports (Result PyValue forkUpTo pyExport)

open EthLib.Execution.Evm.Precompiles

/-- Run the precompile at the address on the call data, with the gas given, at the fork named.

The code of a failed call names the precompile, and the message is its error, as Lean prints it.

An unknown fork, or an address with no precompile at the fork, has code 0.

No error of a precompile has that code. -/
@[export eth_precompile_run]
def runExport (fork : ByteArray) (address : UInt64) (data : ByteArray) (gas : UInt64) :
    Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  match run fork address.toNat data gas.toNat with
  | some result => result.mapError fun e => (e.code, reprStr e)
  | none => throw (0, s!"no precompile at address {address} at fork {fork.name}")

/-- The price of the precompile at the address on the call data, at the fork named.

The arguments are the name of the fork, the address and the call data.

An unknown fork, or an address with no precompile at the fork, has code 0. -/
def priceOf (args : String × Nat × ByteArray) : Result Nat := do
  let (fork, address, data) := args
  let fork ← forkUpTo .glamsterdam fork.toUTF8
  match price fork address data with
  | some cost => return cost
  | none => throw (0, s!"no precompile at address {address} at fork {fork.name}")

/-- The price of the precompile at the address on the call data, at the fork named.

The arguments are the name of the fork, the address and the call data.

An unknown fork, or an address with no precompile at the fork, has code 0. -/
@[export eth_precompile_price]
def priceExport (args : PyValue) : Result PyValue :=
  pyExport priceOf args

end EthLib.Execution.Evm.Precompiles.Exports
