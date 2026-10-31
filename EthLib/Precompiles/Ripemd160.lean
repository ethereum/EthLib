import EthLib.Cryptography.Hash.Ripemd160

/-!
# `EthLib.Precompiles.Ripemd160`

The RIPEMD-160 precompile at address `0x03`: its output.

The hash is RIPEMD-160 of the whole call data.
The output is the 20-byte digest left-padded with twelve zero bytes to 32 bytes.

```text
output:  [ zeros: 12 | RIPEMD-160(data): 20 ]
```

The executable source is `src/ethereum/forks/frontier/vm/precompiled_contracts/ripemd160.py` in `ethereum/execution-specs`.
It calls `hashlib.new("ripemd160", data).digest()`, then `left_pad_zero_bytes(hash_bytes, 32)`.
The Yellow Paper lists the precompile in Appendix E.

The gas price is not specified here.
The precompile never fails once it has the gas, so its output does not depend on the price.
-/

namespace EthLib.Precompiles.Ripemd160

/-- The size of the output in bytes. -/
def OUTPUT_BYTES : Nat := 32

/-- The size of the RIPEMD-160 digest in bytes. -/
def DIGEST_BYTES : Nat := 20

/-- The output of the precompile on the call data: the digest, left-padded with zero bytes to 32 bytes. -/
def ripemd160 (data : ByteArray) : ByteArray :=
  ⟨Array.replicate (OUTPUT_BYTES - DIGEST_BYTES) 0⟩ ++ Cryptography.Hash.ripemd160 data

end EthLib.Precompiles.Ripemd160
