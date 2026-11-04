module

public import EthLib.Cryptography.Hash.Ripemd160
public import EthLib.Execution.Evm.Words

/-!
# `EthLib.Execution.Evm.Precompiles.Ripemd160`

The RIPEMD-160 precompile at address `0x03`: its price and its output.

The hash is RIPEMD-160 of the whole call data.

The output is the 20-byte digest left-padded with twelve zero bytes to 32 bytes.

```text
output:  [ zeros: 12 | RIPEMD-160(data): 20 ]
```

Source: Appendix E of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>.

The price is 600, plus 120 for each 32-byte word of call data, a partial word counting as a whole one.

A call with less gas fails, and it fails in no other case.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Ripemd160

open EthLib.Execution.Evm (wordCount)

/-- The size of the output in bytes. -/
def OUTPUT_BYTES : Nat := 32

/-- The size of the RIPEMD-160 digest in bytes. -/
def DIGEST_BYTES : Nat := 20

/-- The output on the call data: the digest, left-padded with zero bytes to 32 bytes. -/
def ripemd160 (data : ByteArray) : ByteArray :=
  ⟨Array.replicate (OUTPUT_BYTES - DIGEST_BYTES) 0⟩ ++ Cryptography.Hash.ripemd160 data

/-- The price of every call, from Appendix E of the Yellow Paper. -/
def GAS_BASE : Nat := 600

/-- The price of each word of call data, from Appendix E of the Yellow Paper. -/
def GAS_PER_WORD : Nat := 120

/-- The gas a call with `size` bytes of call data is charged. -/
def gasCost (size : Nat) : Nat := GAS_BASE + GAS_PER_WORD * wordCount size

/-- Why a RIPEMD-160 call fails. -/
inductive Ripemd160Error where
  /-- The gas given was below the price, so the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- The call: the output on the call data, once the gas covers the price. -/
def call (data : ByteArray) (gas : Nat) : Except Ripemd160Error ByteArray :=
  let cost := gasCost data.size
  if gas < cost then .error (.outOfGas cost gas) else .ok (ripemd160 data)

end EthLib.Execution.Evm.Precompiles.Ripemd160
