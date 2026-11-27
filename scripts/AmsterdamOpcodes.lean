import EthLib.Execution.Rpc.Trace

open EthLib.Execution.Evm (Op)
open EthLib.Execution.Rpc (opMnemonic)

/-- Print the byte and trace mnemonic of each opcode defined at Amsterdam. -/
def main : IO Unit := do
  for byte in List.range 256 do
    if let some op := Op.ofByte .glamsterdam (UInt8.ofNat byte) then
      IO.println s!"{byte}\t{opMnemonic .glamsterdam op}"
