import EthLib.Execution.Evm.Precompiles.Identity

/-!
An ordinary consumer of the IDENTITY precompile.

It imports the library module alone, without any proof.
It evaluates the definitions in the Lean interpreter, not in the kernel.
`bindings/python/tests/identity` tests the native code that Python calls.

The expected values are written by hand.
The prices are `15 + 3 * ceil(len / 32)`, worked out for each length.
The expected output of a successful call is the call data, as `identity` in execution-specs sets `evm.output = data`.
The two cases with 32 bytes of `0xff` are `identity_4_exact_gas` and `identity_4_insufficient_gas` of `tests/frontier/identity_precompile/test_identity.py` in execution-specs.

`scripts/test_module_system.sh` checks the `#guard` lines with warnings as errors, then runs `main`.
-/

namespace ConsumerTest.IdentityOrdinary

open EthLib.Execution.Evm.Precompiles.Identity

/-- One call and the outcome it must have. -/
structure Case where
  /-- What the case pins. -/
  name : String
  /-- The call data. -/
  data : ByteArray
  /-- The gas given. -/
  gas : Nat
  /-- The output or the error. -/
  expected : Except IdentityError ByteArray

/-- Whether two outcomes agree, byte for byte on success. -/
def sameOutcome : Except IdentityError ByteArray → Except IdentityError ByteArray → Bool
  | .ok a, .ok b => a.data == b.data
  | .error a, .error b => a == b
  | _, _ => false

/-- `n` bytes `0x00, 0x01, ...`, written out by `List.range` rather than by any helper of the code under test. -/
def counting (n : Nat) : ByteArray := ⟨((List.range n).map UInt8.ofNat).toArray⟩

/-- Thirty-two bytes `0xff`, the call data of the execution-specs cases. -/
def ones32 : ByteArray := ⟨Array.replicate 32 0xff⟩

/-- Each call data at exactly its price, at one gas less, and with surplus gas. -/
def cases : List Case := [
  ⟨"empty, exact price 15", .empty, 15, .ok .empty⟩,
  ⟨"empty, 14", .empty, 14, .error (.outOfGas 15 14)⟩,
  ⟨"empty, 0 gas", .empty, 0, .error (.outOfGas 15 0)⟩,
  ⟨"empty, surplus gas", .empty, 1000000, .ok .empty⟩,
  ⟨"1 byte, exact price 18", ⟨#[0xab]⟩, 18, .ok ⟨#[0xab]⟩⟩,
  ⟨"1 byte, 17", ⟨#[0xab]⟩, 17, .error (.outOfGas 18 17)⟩,
  ⟨"32 x 0xff, exact price 18 (identity_4_exact_gas)", ones32, 18, .ok ⟨Array.replicate 32 0xff⟩⟩,
  ⟨"32 x 0xff, 17 (identity_4_insufficient_gas)", ones32, 17, .error (.outOfGas 18 17)⟩,
  ⟨"31 bytes, exact price 18", counting 31, 18, .ok (counting 31)⟩,
  ⟨"33 bytes, exact price 21", counting 33, 21, .ok (counting 33)⟩,
  ⟨"33 bytes, 20", counting 33, 20, .error (.outOfGas 21 20)⟩,
  ⟨"64 bytes, exact price 21", counting 64, 21, .ok (counting 64)⟩,
  ⟨"65 bytes, exact price 24", counting 65, 24, .ok (counting 65)⟩,
  ⟨"65 bytes, 23", counting 65, 23, .error (.outOfGas 24 23)⟩,
  ⟨"256 bytes, surplus gas", counting 256, 2 ^ 64 - 1, .ok (counting 256)⟩ ]

/-- The price of each length at the EVM word boundaries, worked out by hand. -/
def gasTable : List (Nat × Nat) :=
  [(0, 15), (1, 18), (31, 18), (32, 18), (33, 21), (64, 21), (65, 24), (1024, 111), (1025, 114)]

#guard (counting 33).size == 33 && (counting 33).data[32]! == 32 && ones32.size == 32
#guard cases.all fun c => sameOutcome (identity c.data c.gas) c.expected
#guard gasTable.all fun (size, price) => gasCost size == price
#guard cases.all fun c => match identity c.data c.gas with
  | .ok out => out.size == c.data.size
  | .error _ => true

end ConsumerTest.IdentityOrdinary

open ConsumerTest.IdentityOrdinary in
/-- Run every case in the Lean interpreter, print one line each, and fail on any mismatch. -/
def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let ok := sameOutcome (EthLib.Execution.Evm.Precompiles.Identity.identity c.data c.gas) c.expected
    IO.println s!"{if ok then "ok" else "FAIL"}: identity {c.name}"
    unless ok do failures := failures + 1
  for (size, price) in gasTable do
    let ok := EthLib.Execution.Evm.Precompiles.Identity.gasCost size == price
    IO.println s!"{if ok then "ok" else "FAIL"}: gasCost {size} = {price}"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length + gasTable.length - failures} passed, {failures} failed"
  return if failures == 0 then 0 else 1
