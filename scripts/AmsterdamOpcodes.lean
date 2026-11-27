import EthLib.Execution.Rpc.Trace

/-!
# Opcodes defined at Amsterdam

Lists each opcode that the specification defines at Amsterdam, with its trace mnemonic.

`bindings/python/tests/parity/opcode_coverage.py` runs it and reads one opcode per line.
-/

open EthLib.Execution.Evm (Op)
open EthLib.Execution.Rpc (opMnemonic)

/-- Print each opcode defined at Amsterdam as its decimal byte, a tab and its trace mnemonic. -/
def main : IO Unit := do
  for byte in List.range 256 do
    if let some op := Op.ofByte .glamsterdam (UInt8.ofNat byte) then
      IO.println s!"{byte}\t{opMnemonic .glamsterdam op}"
