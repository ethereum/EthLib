module

public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.AccountData`

The instructions that read the balance, the code or the code hash of an account.

An address with no account reads as the empty account: balance 0 and no code.

From Berlin, the first access to an address in a transaction is cold and costs more.

That access adds the address to the accessed addresses, so later accesses are warm.

Before Berlin, the price does not depend on earlier accesses.

From Pectra, the code of a delegated account is its delegation indicator, and these read it.

Each records its read of the account once it has paid, for the block access list of EIP-7928.

Appendix H.2 of the Yellow Paper, Shanghai version, defines these instructions.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

The EIPs that add or change an instruction define it:

- [EIP-1052][eip1052], EXTCODEHASH
- [EIP-1884][eip1884], SELFBALANCE
- [EIP-2929][eip2929], the cold and warm accesses
- [EIP-7702][eip7702], the delegation indicator as code

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip1052]: https://eips.ethereum.org/EIPS/eip-1052#specification
[eip1884]: https://eips.ethereum.org/EIPS/eip-1884#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#delegation-indicator
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256 toAddressMasked)
open EthLib.Execution.State (EMPTY_ACCOUNT)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Whether an access to an address is cold, and the frame after the access.

From Berlin, the access is cold when the transaction has not yet accessed the address.

It then adds the address to the accessed addresses.

Before Berlin, no access is cold, and the frame stays as it is. -/
def accessAddress (evm : Evm fork Meter) (address : Address) : Bool × Evm fork Meter :=
  if fork ≥ .berlin then
    let accessed := evm.substate.accessedAddresses
    (address ∉ accessed,
      { evm with substate := { evm.substate with accessedAddresses := accessed.insert address } })
  else (false, evm)

/-- The code of the account at an address, or empty for an address with no account. -/
def accountCode (evm : Evm fork Meter) (address : Address) : Except EvmError ByteArray :=
  (evm.state.getCode (evm.state.getAccount address).codeHash).mapError .state

/-- BALANCE: replace an address with the balance of its account. -/
def balanceStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (word, evm) ← popWord evm
  let address := toAddressMasked word
  let (cold, evm) := accessAddress evm address
  let evm ← chargeGas evm (balanceCost fork cold)
  let evm := recordAccountRead evm address
  let evm ← pushWord evm (evm.state.getAccount address).balance
  return advance evm

/-- EXTCODESIZE: replace an address with the size of the code of its account. -/
def extcodesizeStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (word, evm) ← popWord evm
  let address := toAddressMasked word
  let (cold, evm) := accessAddress evm address
  let evm ← chargeGas evm (externalBaseCost fork cold)
  let evm := recordAccountRead evm address
  let code ← accountCode evm address
  let evm ← pushWord evm (BitVec.ofNat 256 code.size)
  return advance evm

/-- EXTCODECOPY: copy `size` bytes of the code of an account from `offset` to memory at `start`.

The code reads as zeros past its end. -/
def extcodecopyStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (word, evm) ← popWord evm
  let (start, evm) ← popWord evm
  let (offset, evm) ← popWord evm
  let (size, evm) ← popWord evm
  let address := toAddressMasked word
  let (cold, evm) := accessAddress evm address
  let cost := externalBaseCost fork cold + OPCODE_COPY_PER_WORD * wordCount size.toNat
  let evm ← chargeGasAndMemory evm cost [(start, size)]
  let evm := recordAccountRead evm address
  let code ← accountCode evm address
  let value : ByteArray := ⟨(bufferRead code offset.toNat size.toNat).toArray⟩
  return advance { evm with memory := memoryWrite evm.memory start.toNat value }

/-- The code hash of an account as a word, or 0 for the empty account. -/
def codeHashWord (account : State.Account) : U256 :=
  if account = EMPTY_ACCOUNT then 0 else U256.fromBeBytes account.codeHash

/-- EXTCODEHASH: replace an address with the code hash of its account.

An address with no account, or with the empty account, gives 0. -/
def extcodehashStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (word, evm) ← popWord evm
  let address := toAddressMasked word
  let (cold, evm) := accessAddress evm address
  let evm ← chargeGas evm (extcodehashCost fork cold)
  let evm := recordAccountRead evm address
  let evm ← pushWord evm (codeHashWord (evm.state.getAccount address))
  return advance evm

/-- The instruction of an opcode that reads another account, at fork `fork`.

Other opcodes give none, and so does an opcode before the fork that adds it. -/
def accountStep (fork : Fork) : Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .balance => some balanceStep
  | .selfbalance =>
    if .istanbul ≤ fork then
      some fun evm => readFrame OPCODE_SELFBALANCE
        (fun evm => (evm.state.getAccount evm.message.currentTarget).balance)
        (recordAccountRead evm evm.message.currentTarget)
    else none
  | .extcodesize => some extcodesizeStep
  | .extcodecopy => some extcodecopyStep
  | .extcodehash => if .constantinople ≤ fork then some extcodehashStep else none
  | _ => none

end EthLib.Execution.Evm
