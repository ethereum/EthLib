module

public import EthLib.Cryptography.Secp256k1.Recovery
public import EthLib.Cryptography.Secp256k1.Address
public import EthLib.Execution.Evm.Precompiles.Ecrecover.Errors
public import EthLib.Execution.Evm.Memory

/-!
# `Ecrecover.Core`

The ECRECOVER precompile at address `0x01`, as of the BPO2 fork.

It returns the address that signed a 32-byte hash, so contracts can check signatures.

Source: Appendix E of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>.

The input has this layout:

```text
    [ hash: 32 | v: 32 | r: 32 | s: 32 ]
```

- `v`, `r` and `s` are 32-byte big-endian integers.
- The call data reads as if followed by infinitely many zero bytes, so a short input is padded.
- Data past 128 bytes is ignored.

The output is the address, left-padded with zero bytes to 32 bytes.

Every rejection gives the empty output, and the call still succeeds and pays its gas:

- `v` is neither 27 nor 28.
- `r` or `s` is not in `[1, n - 1]`.
- No key is recovered.

A high `s` is accepted: the low-s rule of EIP-2 is for transactions only.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Ecrecover

open EthLib.Cryptography.Secp256k1
open EthLib.Execution.Evm (byteAt)

/-- The gas of a call, from Appendix E of the Yellow Paper. -/
def GAS_ECRECOVER : Nat := 3000

/-- 32 bytes of the call data from `start`, zero-padded on the right. -/
def word (data : ByteArray) (start : Nat) : Vector UInt8 32 :=
  Vector.ofFn fun i => byteAt data (start + i.val)

/-- The output for a hash and the integers `v`, `r` and `s`. -/
def output (hash : Vector UInt8 32) (v r s : Nat) : ByteArray :=
  -- `v` is 27 or 28, the recovery id plus 27.
  if hv : v = 27 ∨ v = 28 then
    -- The recovery rejects `r` and `s` outside `[1, n - 1]`, as the Yellow Paper does first.
    match Ecdsa.recover hash r s ⟨v - 27, by omega⟩ with
    | .ok (.affine x y) => ⟨(List.replicate 12 0 ++ (address x y).toList).toArray⟩
    | _ => ByteArray.empty
  else ByteArray.empty

/-- The operation of the precompile: read the four words, then compute the output. -/
def compute (data : ByteArray) : ByteArray :=
  output (word data 0) (ofBytesBE (word data 32).toList) (ofBytesBE (word data 64).toList)
    (ofBytesBE (word data 96).toList)

/-- Run the precompile on `data` with `gas` available.

Returns the output, or the lack of gas that ends the call and consumes it all.

The gas is charged first, then the operation runs. -/
def ecrecover (data : ByteArray) (gas : Nat) : Except EcrecoverError ByteArray :=
  if gas < GAS_ECRECOVER then .error (.outOfGas GAS_ECRECOVER gas) else .ok (compute data)

end EthLib.Execution.Evm.Precompiles.Ecrecover
