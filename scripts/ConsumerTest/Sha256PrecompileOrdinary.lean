import EthLib.Execution.Evm.Precompiles.Sha256

/-!
An ordinary consumer of the SHA-256 precompile.

It imports the library module alone, without any proof.
It evaluates the definitions in the Lean interpreter, not in the kernel.
The native code that Python calls is tested separately, in `bindings/python/tests/sha256_precompile`.

The expected values are written by hand.
The digests are NIST CAVP vectors from `bindings/python/tests/sha256/cavp/SHA256ShortMsg.rsp` (Len 0, 256, 264 and 512) and the FIPS 180-4 example "abc".
The prices are `60 + 12 * ceil(len / 32)`, worked out for each length.

`scripts/test_module_system.sh` checks the `#guard` lines with warnings as errors, then runs `main`.
-/

namespace ConsumerTest.Sha256PrecompileOrdinary

open EthLib.Execution.Evm.Precompiles.Sha256

/-- The bytes a hex string spells, read here rather than with any helper of the code under test. -/
def hex (s : String) : ByteArray :=
  let digit (c : Char) : Nat :=
    if c.toNat < 58 then c.toNat - 48 else if c.toNat < 71 then c.toNat - 55 else c.toNat - 87
  let rec go : List Char → List UInt8
    | hi :: lo :: rest => UInt8.ofNat (16 * digit hi + digit lo) :: go rest
    | _ => []
  ⟨(go s.toList).toArray⟩

/-- One call and the outcome it must have. -/
structure Case where
  /-- What the case pins. -/
  name : String
  /-- The call data. -/
  data : ByteArray
  /-- The gas given. -/
  gas : Nat
  /-- The output or the error. -/
  expected : Except Sha256Error ByteArray

/-- Whether two outcomes agree, byte for byte on success. -/
def sameOutcome : Except Sha256Error ByteArray → Except Sha256Error ByteArray → Bool
  | .ok a, .ok b => a.data == b.data
  | .error a, .error b => a == b
  | _, _ => false

/-- The FIPS 180-4 example message. -/
def abc : ByteArray := ⟨#[0x61, 0x62, 0x63]⟩

/-- `Len = 256`: one whole word. -/
def message32 : ByteArray := hex "09fc1accc230a205e4a208e64a8f204291f581a12756392da4b8c0cf5ef02b95"

/-- `Len = 264`: one byte into the second word. -/
def message33 : ByteArray := hex "0546f7b8682b5b95fd32385faf25854cb3f7b40cc8fa229fbd52b16934aab388a7"

/-- `Len = 512`: two words, and two blocks once padded. -/
def message64 : ByteArray := hex ("5a86b737eaea8ee976a0a24da63e7ed7eefad18a101c1211e2b3650c5187c2a8" ++
  "a650547208251f6d4237e661c7bf4c77f335390394c37fa1a9f9be836ac28509")

/-- The digest of the empty message, `Len = 0`. -/
def digestEmpty := hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
/-- The digest of "abc". -/
def digestAbc := hex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
/-- The digest of `message32`. -/
def digest32 := hex "4f44c1c7fbebb6f9601829f3897bfd650c56fa07844be76489076356ac1886a4"
/-- The digest of `message33`. -/
def digest33 := hex "b31ad3cd02b10db282b3576c059b746fb24ca6f09fef69402dc90ece7421cbb7"
/-- The digest of `message64`. -/
def digest64 := hex "42e61e174fbb3897d6dd6cef3dd2802fe67b331953b06114a65c772859dfc1aa"

/-- Each message at exactly its price, and at one gas less. -/
def cases : List Case := [
  ⟨"empty, exact price 60", .empty, 60, .ok digestEmpty⟩,
  ⟨"empty, 59", .empty, 59, .error (.outOfGas 60 59)⟩,
  ⟨"empty, 0 gas", .empty, 0, .error (.outOfGas 60 0)⟩,
  ⟨"empty, surplus gas", .empty, 1000000, .ok digestEmpty⟩,
  ⟨"abc, exact price 72", abc, 72, .ok digestAbc⟩,
  ⟨"abc, 71", abc, 71, .error (.outOfGas 72 71)⟩,
  ⟨"32 bytes, exact price 72", message32, 72, .ok digest32⟩,
  ⟨"32 bytes, 71", message32, 71, .error (.outOfGas 72 71)⟩,
  ⟨"33 bytes, exact price 84", message33, 84, .ok digest33⟩,
  ⟨"33 bytes, 83", message33, 83, .error (.outOfGas 84 83)⟩,
  ⟨"64 bytes, exact price 84", message64, 84, .ok digest64⟩,
  ⟨"64 bytes, 83", message64, 83, .error (.outOfGas 84 83)⟩ ]

/-- The price of each length at the word boundaries, worked out by hand. -/
def gasTable : List (Nat × Nat) :=
  [(0, 60), (1, 72), (31, 72), (32, 72), (33, 84), (64, 84), (65, 96), (1024, 444)]

#guard message32.size == 32 && message33.size == 33 && message64.size == 64
#guard cases.all fun c => sameOutcome (sha256 c.data c.gas) c.expected
#guard gasTable.all fun (size, price) => gasCost size == price
#guard (cases.filterMap fun c => (sha256 c.data c.gas).toOption).all (·.size == OUTPUT_BYTES)

end ConsumerTest.Sha256PrecompileOrdinary

open ConsumerTest.Sha256PrecompileOrdinary in
/-- Run every case in the Lean interpreter, print one line each, and fail on any mismatch. -/
def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let ok := sameOutcome (EthLib.Execution.Evm.Precompiles.Sha256.sha256 c.data c.gas) c.expected
    IO.println s!"{if ok then "ok" else "FAIL"}: sha256 {c.name}"
    unless ok do failures := failures + 1
  for (size, price) in gasTable do
    let ok := EthLib.Execution.Evm.Precompiles.Sha256.gasCost size == price
    IO.println s!"{if ok then "ok" else "FAIL"}: gasCost {size} = {price}"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length + gasTable.length - failures} passed, {failures} failed"
  return if failures == 0 then 0 else 1
