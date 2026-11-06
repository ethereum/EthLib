# Precompiles

A precompile is a contract at a fixed address whose code is not EVM bytecode.
A call to it runs a function of the protocol on the call data, for a price in gas.
Every client must return the same bytes and charge the same gas, or the chain splits.

Ethereum has 18 precompiles, added by six forks from Frontier to Fusaka.
This directory specifies all of them, and one table runs each by its address.
This page first states how every precompile is written.
A new precompile follows the same rules, and a review checks them.

## Families

A family is a set of precompiles that share one error type and one encoding of the call data.
The 18 precompiles form ten families:

- ECRECOVER at `0x01`, from Frontier.
- SHA256 at `0x02`, from Frontier.
- RIPEMD160 at `0x03`, from Frontier.
- IDENTITY at `0x04`, from Frontier.
- MODEXP at `0x05`, from Byzantium.
- The three alt_bn128 precompiles at `0x06` to `0x08`, from Byzantium.
- BLAKE2F at `0x09`, from Istanbul.
- The point evaluation at `0x0a`, from Dencun.
- The seven BLS12-381 precompiles at `0x0b` to `0x11`, from Pectra.
- P256VERIFY at `0x100`, from Fusaka.

Each family has one namespace, `EthLib.Execution.Evm.Precompiles.<Family>`.

## Files

A family is one file, `<Family>.lean`, in this directory.
It becomes a folder `<Family>/` only when one file would pass about 250 lines.
The folder then has an umbrella `<Family>.lean` beside it, which imports every file of the folder.
The files of a folder take their names from this list, in import order:

- `Constants.lean` holds the numbers of the sources, when several files share them.
- `Errors.lean` holds the error type.
- `Encoding.lean` reads the call data and writes the output.
- `Gas.lean` holds the price, when it depends on the fork.
- `Core.lean` holds the calls, or one file per group of calls, such as `G1.lean` for the G1 calls.

A folder holds Lean files, so no folder holds only a README.

## The call

Each precompile has one call, named after the precompile in lowerCamelCase, such as `ecadd`.
The call takes the fork first, when an EIP changes the precompile after the fork that adds it.
It then takes the call data and the gas:

```lean
def modexp (fork : Fork) (data : ByteArray) (gas : Nat) : Except ModexpError ByteArray
```

The call runs its steps in the order of the source:

1. It checks the call data that the source checks before the charge, such as the length.
2. It fails with `outOfGas` when the gas is below the price.
3. It decodes and checks the rest of the call data.
4. It returns the output.

The doc comment of the call states that order.
A check that a source leaves unordered gets an order in the code, and the doc comment says so.

Every failure of a precompile consumes all the gas given to the call, and returns no data.
So the order decides only which error the specification reports, and no client can observe it.

## Errors

Each family has one error type, `<Family>Error`, which derives `Repr` and `DecidableEq`.
Every error type has the constructor `outOfGas (cost gas : Nat)`.
The other constructors use one name for one cause across families:

- `invalidInputLength (size : Nat)` for call data of a length that the precompile does not accept.
- `invalidFieldElement`, `notOnCurve` and `notInSubgroup` for a point that does not decode.

An input that the source answers with an output is not an error.
For example, ECRECOVER returns empty output for an invalid signature, and the call succeeds.

Every error type has a code for each constructor, from 1, which ignores the arguments.
Its proofs show that the code is injective on constructors, as for every error type of EthLib.
A new constructor takes a new code, so that each code keeps its meaning.

The table wraps the error of each family in one type, which has a code for each family.
The C exports report that code, and the message prints the error of the family.

## The price

The price of a precompile is one declaration, which the call compares with the gas:

- A price that is one number at every fork is a constant, such as `GAS_ECRECOVER`.
- Any other price is a function: `gasCost` in a family of one precompile, `<call>Gas` otherwise.
- A price that changes at a fork takes the fork first, as the call does.

The price lives in the family, even when an EIP changes it at a later fork.
No precompile keeps its price in the gas schedule of the EVM, which is for instructions.

The table gives the price of each address at each fork.
Its proofs show that a call that succeeds had at least that price in gas.

## Proofs

The proofs of a family mirror its files in `EthLib/Execution/Proofs/Evm/Precompiles/`.
A family of one file has one proof file of the same name.
A property that needs more imports, such as the group law of a curve, gets its own file.
That file is named after the property.
The proofs then form a folder, and the properties of the single file go in `Basic.lean`.

Each call has these theorems, named after the call and the error constructor:

- `<call>_outOfGas`: once the checks before the charge pass, gas below the price fails the call.
- `<call>_<error>`: each other error constructor is reached, under its condition.
- `<call>_eq_ok_iff`, or `<call>_ok`: what a successful call returns.
- `<call>_size`: the length of every output.

Each error type has `<Family>Error.code_injective`.

A family proves more where its source asks for more, such as the round trip of an encoding.

## Exports and bindings

Python reaches every precompile through the table, by its address, at a fork:

- `eth_precompile_run` takes the fork name, the address, the call data and the gas.
- `eth_precompile_price` takes the fork name, the address and the call data, and returns the price.

An unknown fork, or a fork with no precompile at the address, gives the error code 0.
No precompile has an export of its own.

In Python, these are `ethlib.precompiles.run` and `ethlib.precompiles.price`.
A failed call raises `PrecompileError`, whose code names the family.
Its message is the error of the family, as Lean prints it.

## Tests

The tests of a family are `bindings/python/tests/precompile/test_<family>.py`.
They run the official vectors of the family through the table, at the prices that the EIPs give.
They run at the fork that adds the family, at each fork that changes it, and at the latest fork.
A test of the price, which costs little, runs at every fork from the fork that adds the family.
Each vector file has its pinned source, as `tests/sources.toml` records it.

## Sources

Each family cites its primary source, with the section:

- The Yellow Paper, Appendix E, for the four precompiles of Frontier.
- The EIP that adds the precompile, and each EIP that changes it later.
- The standard that defines the arithmetic, such as RFC 7693 for BLAKE2b or SEC 1 for ECDSA.

The code does not cite execution-specs.
A doc comment names a function of a source only when the cited EIP or standard defines it.

## This page

Each family has one section on this page, in the order of the addresses.
A family gets its section when its files follow the rules above.
Each section gives the source, the input and the output, the errors and the price.
It then gives the proofs and the test vectors.
A Lean module header says in a few lines what its precompile does, and this page gives the rest.

## ECRECOVER

ECRECOVER at `0x01` returns the address that signed a 32-byte hash.
A contract can check a signature with it for 3000 gas.

### Source

The source is Appendix E of the Yellow Paper, Shanghai version, in
[`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).
The recovery follows SEC 1 v2 §4.1.6, and the address follows Appendix F of the Yellow Paper.
Every fork from Frontier computes the same result at the same price.

### Input and output

```text
input:   [ hash: 32 | v: 32 | r: 32 | s: 32 ]
output:  [ 12 zero bytes | address: 20 ], or empty
```

The call data reads as if followed by zero bytes, so a short input is padded.
Bytes past the first 128 are ignored.
The output is empty when `v` is neither 27 nor 28, when `r` or `s` is outside `[1, n - 1]`, or
when no key is recovered.
A high `s` is accepted, because the low-s rule of EIP-2 applies to transactions only.

### Errors and price

The price is 3000.
The call fails only with `outOfGas`, when the gas is below the price.
An empty output is a successful call, and its gas is paid.

### Proofs

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/Ecrecover.lean`.
A nonempty output is the address of a key that verifies the signature (`output_verify`).
Conversely, when `r + n >= p`, every key that verifies a signature has its address returned for
`v = 27` or `v = 28` (`output_of_verify`).
A signature made with a private key returns that key's address (`output_sign`).
The signatures `(v, r, s)` and `(55 - v, r, n - s)` give the same output (`output_neg_s`).
Each cause of an empty output gives one (`output_of_bad_v`, `output_of_range`,
`output_of_recover_error`).
Only the first 128 bytes count (`compute_congr`), and the output is empty or 32 bytes long
(`compute_size`).
A call fails exactly when the gas is below 3000 (`ecrecover_outOfGas`, `ecrecover_ok`).

One case is outside the converse statement.
When `r < p - n`, the point `R` of a signature may have the x-coordinate `r + n`.
Only the recovery ids 2 and 3 reach such a point, and the precompile accepts only 27 and 28.

### Test vectors

`bindings/python/tests/precompile/test_ecrecover.py` runs the 52 cases of `test_precompiles` in
`tests/frontier/precompiles/test_ecrecover.py` of execution-specs, at the pinned commit.

## SHA256

SHA256 at `0x02` returns the SHA-256 digest of the call data, by FIPS 180-4.

### Source

The source is Appendix E of the Yellow Paper, at the commit above.
Every fork from Frontier computes the same result at the same price.

### Input and output

```text
input:   any call data
output:  [ SHA-256(data): 32 ]
```

### Errors and price

The price is `60 + 12 * ceil(len / 32)`.
The call fails only with `outOfGas`, when the gas is below the price.

### Proofs

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/Sha256.lean`.
A call succeeds exactly when the gas covers the price, and then returns 32 bytes
(`sha256_eq_ok_iff`, `sha256_eq_error_iff`, `sha256_ok_size`).
When the gas is below the price of `2^61` bytes, those bytes are the hash of FIPS 180-4 §6.2
(`sha256_ok_eq_spec_of_gas`).

### Test vectors

`bindings/python/tests/precompile/test_sha256.py` runs the NIST messages of `tests/sha256`.
Each runs at its exact price and one gas below it, and the price is checked at word boundaries.

## RIPEMD160

RIPEMD160 at `0x03` returns the RIPEMD-160 digest of the call data, left-padded to 32 bytes.

### Source

The source is Appendix E of the Yellow Paper, at the commit above.
Every fork from Frontier computes the same result at the same price.

### Input and output

```text
input:   any call data
output:  [ 12 zero bytes | RIPEMD-160(data): 20 ]
```

### Errors and price

The price is `600 + 120 * ceil(len / 32)`.
The call fails only with `outOfGas`, when the gas is below the price.

### Proofs

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/Ripemd160.lean`.
The output has twelve zero bytes, then the digest (`output_size`, `output_leading_zeros`,
`output_digest`).
A call succeeds exactly when the gas covers the price (`ripemd160_eq_ok_iff`,
`ripemd160_eq_error_iff`).

### Test vectors

`bindings/python/tests/precompile/test_ripemd160.py` runs the vectors of Bosselaers' RIPEMD-160
page.
It also runs the lengths at which the padding adds a block.

## IDENTITY

IDENTITY at `0x04` returns its call data, so contracts can copy memory cheaply.

### Source

The source is Appendix E of the Yellow Paper, at the commit above.
Every fork from Frontier computes the same result at the same price.

### Input and output

The output is the call data, unchanged.

### Errors and price

The price is `15 + 3 * ceil(len / 32)`.
The call fails only with `outOfGas`, when the gas is below the price.

### Proofs

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/Identity.lean`.
A call succeeds exactly when the gas covers the price, and then returns its call data
(`identity_eq_ok_iff`, `identity_eq_error_iff`).

### Test vectors

`bindings/python/tests/precompile/test_identity_absence.py` runs the IDENTITY calls of the
execution-specs tests, and the calls of addresses that have no precompile.

## MODEXP

MODEXP at `0x05` computes `BASE ^ EXPONENT mod MODULUS` for integers of up to 1024 bytes each.
RSA verification and other number-theoretic checks use it, because the same work in EVM code would
cost far more gas.
For example, with `BASE = 3`, `EXPONENT = 5` and `MODULUS = 7`, the output is `243 mod 7 = 5`.

### Source

Four EIPs define MODEXP:

- [EIP-198](https://eips.ethereum.org/EIPS/eip-198) defines the input, the output, the arithmetic
  and the first price, from Byzantium.
- [EIP-2565](https://eips.ethereum.org/EIPS/eip-2565) replaces the price from Berlin.
- [EIP-7883](https://eips.ethereum.org/EIPS/eip-7883) replaces it again from Fusaka.
- [EIP-7823](https://eips.ethereum.org/EIPS/eip-7823) bounds each length by 1024 bytes, from Fusaka.

So the call and the price take the fork.
The files follow the README: `Constants.lean`, `Encoding.lean`, `Errors.lean`, `Gas.lean` and
`Core.lean`.

### Input and output

```text
input:   [ len_base: 32 | len_exp: 32 | len_mod: 32 | BASE | EXPONENT | MODULUS ]
output:  BASE ^ EXPONENT mod MODULUS, on len_mod bytes
```

The call data reads as if followed by zero bytes, so a short input is padded, and data past the
last field is ignored.
A zero modulus gives `len_mod` zero bytes, since Appendix E of the Yellow Paper takes `x mod 0` to
be zero.

### Errors and price

From Fusaka, a length above 1024 fails with `lengthTooLarge`, before any gas is charged.
Otherwise the call fails only with `outOfGas`, when the gas is below the price.

The price multiplies a complexity of the longer of the base and the modulus by an iteration count
of the exponent:

- EIP-198 divides that product by 20.
- EIP-2565 squares the 8-byte words of the longer operand, divides by 3, and charges at least 200.
- EIP-7883 doubles the iterations per exponent byte past the first 32, drops the division, and
  charges at least 500.

The pseudocode of EIP-2565 and of EIP-7883, read literally, differs for an exponent longer than
32 bytes.
It reads the low 256 bits of the exponent, and counts one iteration less when they are zero.
The code follows EIP-198, which takes the first 32 bytes of the exponent and counts no iteration
less.
`iterations_long_zero_head` pins the zero case from Fusaka.

### Proofs

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/Modexp/`.
The loop of square-and-multiply equals `b ^ e % m` (`powMod_eq`, in `Proofs/Evm/PowMod.lean`).
So the output is `BASE ^ EXPONENT mod MODULUS`, or 0 for a zero modulus (`compute_eq_pow_mod`), on
exactly `len_mod` bytes (`modexp_ok_size`).
Zero bytes appended to the input change nothing (`modexp_append_zeros`), and neither does data past
the last field (`modexp_append_excess`, `modexp_congr`).
From Fusaka, each oversized length fails the call whatever the gas (`modexp_lengthTooLarge_base`,
`modexp_lengthTooLarge_exponent`, `modexp_lengthTooLarge_modulus`).
With every length in bounds, a call fails exactly when the gas is below the price, at every fork
(`modexp_outOfGas`, `modexp_ok`).

The price of each fork has its theorem (`gasCost_of_lt_berlin`, `gasCost_of_berlin_le`).
From Fusaka, the price is at least 500, does not fall when a length grows, and is at most
528449536 (`min_gas_le_gasCost`, `gasCost_le`, `chargedGas_le`).

No theorem bounds the cost of computing the result, which the price is meant to cover.

### Test vectors

`bindings/python/tests/precompile/test_modexp.py` runs the worked examples of EIP-198 at every fork
from Byzantium.
It checks the prices of the 15 `modexp_nagydani_*` cases from the tables of EIP-2565 and EIP-7883,
at the forks of each.
`test_execution_specs_vectors.py` and `test_modexp_state_tests.py` run the MODEXP vectors of
execution-specs and of the state tests.

## alt_bn128

The three alt_bn128 precompiles let zkSNARK verifiers work on the curve alt_bn128, also called
BN254:

- ECADD at `0x06` adds two points of `G_1`.
- ECMUL at `0x07` multiplies a point of `G_1` by a 32-byte scalar.
- ECPAIRING at `0x08` checks that the product of the pairings of pairs of points is 1.

### Source

[EIP-196](https://eips.ethereum.org/EIPS/eip-196) defines the addition and the multiplication, and
[EIP-197](https://eips.ethereum.org/EIPS/eip-197) the pairing check, from Byzantium.
[EIP-1108](https://eips.ethereum.org/EIPS/eip-1108) lowers the three prices from Istanbul.
Every fork computes the same results, so only the prices depend on the fork.

### Input and output

```text
ECADD input:  [ x1: 32 | y1: 32 | x2: 32 | y2: 32 ]
ECMUL input:  [ x: 32 | y: 32 | scalar: 32 ]
output:       [ x: 32 | y: 32 ]
ECPAIRING:    k pairs of [ G_1 point: 64 | G_2 point: 128 ], and the word 1 or 0
G_2 point:    [ x.c1: 32 | x.c0: 32 | y.c1: 32 | y.c0: 32 ]
```

Each coordinate is a 32-byte big-endian integer, and `(0, 0)` is the point at infinity.
ECADD and ECMUL read their call data as if followed by zero bytes.
The scalar of ECMUL is the full 32-byte integer, not reduced.

### Errors and price

The errors are `outOfGas`, `invalidFieldElement`, `notOnCurve`, `invalidInputLength` and
`notInSubgroup`.
ECPAIRING charges the gas before it checks that the call data is a whole number of 192-byte pairs.

| Fork | ECADD | ECMUL | ECPAIRING on `k` pairs |
| --- | --- | --- | --- |
| Byzantium to Petersburg | 500 | 40000 | `100000 + 80000 * k` |
| From Istanbul | 150 | 6000 | `45000 + 34000 * k` |

### Proofs

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/AltBn128/`.
ECADD and ECMUL fail exactly when the gas is below the price or a point does not decode
(`ecadd_eq_ok_iff`, `ecmul_eq_ok_iff`), and they return 64 bytes (`ecadd_size`, `ecmul_size`).
ECPAIRING succeeds exactly when the gas covers the price and every pair decodes
(`ecpairing_eq_ok_iff`), and it returns the word 0 or 1 (`ecpairing_ok`).
Every decoded point is on the curve (`bytesToG1_isOnCurve`).
The decoder of a point of `G_1` reads back every point on the curve from its 64 bytes
(`bytesToG1_g1ToBytes`).
Each 64 bytes that it accepts encode the point that it returns (`g1ToBytes_of_bytesToG1`).
`Group.lean` shows that ECADD returns the sum of its points in the group of the curve, and ECMUL
the product of its point by its scalar (`ecadd_toPoint`, `ecmul_toPoint`).

### Test vectors

`bindings/python/tests/precompile/test_alt_bn128.py` checks the three precompiles against py_ecc.
`test_alt_bn128_eest.py` runs the cases of the EIP-196 and EIP-197 tests of execution-specs.
Both run on each side of EIP-1108, at the prices of each fork.

## BLAKE2F

BLAKE2F at `0x09` runs F, the compression function of BLAKE2b, for the number of rounds that the
caller asks for.
F processes one 128-byte block, so a contract hashes a long message one block at a time.

### Source

[EIP-152](https://eips.ethereum.org/EIPS/eip-152) defines the input, the errors and the output,
from Istanbul.
[RFC 7693](https://www.rfc-editor.org/rfc/rfc7693) §3.2 defines F.

### Input and output

```text
input:   [ rounds: 4 | h: 64 | m: 128 | t0: 8 | t1: 8 | f: 1 ]
output:  [ h: 64 ]
```

The rounds field is big-endian.
Every 64-bit word of `h`, `m`, `t0` and `t1` is little-endian.
The flag byte `f` is `1` for true and `0` for false.

### Errors and price

The price is one gas per round.
The call checks the length, then charges the gas, then reads the flag byte.
EIP-152 does not order the two checks of the call data, so the code orders them.
The errors are `invalidInputLength`, `outOfGas` and `invalidFlag`.

### Proofs

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/Blake2f.lean` and
`EthLib/Cryptography/Proofs/Hash/Blake2b.lean`.
A call fails exactly on a wrong length, too little gas or a wrong flag byte, in that order
(`blake2f_eq_error_iff`).
Otherwise it returns F on the decoded fields (`blake2f_of_gas`, `output_ok`).
Every field is decoded with its own byte order, and the output words keep the order of the input
(`readRounds_toNat`, `readWord_toNat`, `writeState_word`).
Each word of the initialization vector is the square root of its prime, and each row of the
message schedule is a permutation, as RFC 7693 defines them.

No theorem relates F to another statement of RFC 7693 §3.2.
The code transcribes §3.2 line by line instead.

### Test vectors

`bindings/python/tests/precompile/test_blake2f.py` runs test vectors 0 to 7 of EIP-152.
It runs only the rounds field of vector 8, because `2^32 - 1` rounds take too long.
It also checks BLAKE2b-512 of the bytes `0x00` to `0x7f`, and vector 5 with `t1 = 1`.
`test_blake2b_kat.py` hashes the BLAKE2b known answers with the precompile as F.

## Point evaluation

The point evaluation at `0x0a` checks a KZG proof that the polynomial of a blob takes the value `y`
at the point `z`.
A blob transaction names each blob by the versioned hash of its commitment.

### Source

The section "Point evaluation precompile" of
[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#point-evaluation-precompile), from Dencun.
Every later fork computes the same result at the same price.

### Input and output

```text
input:   [ versioned hash: 32 | z: 32 | y: 32 | commitment: 48 | proof: 48 ]
output:  [ FIELD_ELEMENTS_PER_BLOB: 32 | BLS_MODULUS: 32 ]
```

The versioned hash must be `0x01` followed by bytes 1 to 31 of the SHA-256 of the commitment.
The proof must pass the pairing check of EIP-4844:

```text
e(commitment - [y]_1, -[1]_2) * e(proof, [tau]_2 - [z]_2) = 1
```

### Errors and price

The price is 50000.
The call checks the length, then charges the gas, then checks the hash and the proof.
The errors are `invalidInputLength`, `outOfGas`, `versionedHashMismatch`, `invalidCommitment`,
`invalidFieldElement`, `invalidProof`, `invalidTrustedSetup` and `proofRejected`.

### Proofs

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/PointEvaluation.lean`.
A call succeeds exactly when the call data has 192 bytes, the gas covers 50000, the versioned hash
names the commitment and the proof verifies (`pointEvaluation_eq_ok_iff`).
Every successful call returns the same 64 bytes (`output_eq`).

### Test vectors

`bindings/python/tests/precompile/test_point_evaluation.py` turns each of the 122
`verify_kzg_proof` vectors of `tests/cryptography/kzg` into a call.

## BLS12-381

The seven BLS12-381 precompiles of EIP-2537 work on the curve of the consensus layer's signatures:

- BLS12_G1ADD at `0x0b` and BLS12_G2ADD at `0x0d` add two points.
- BLS12_G1MSM at `0x0c` and BLS12_G2MSM at `0x0e` sum the products of points by 32-byte scalars.
- BLS12_PAIRING_CHECK at `0x0f` checks that the product of the pairings of pairs of points is 1.
- BLS12_MAP_FP_TO_G1 at `0x10` and BLS12_MAP_FP2_TO_G2 at `0x11` map a field element to a point,
  by RFC 9380.

### Source

[EIP-2537](https://eips.ethereum.org/EIPS/eip-2537), from Pectra.
Every later fork accepts the same inputs at the same prices.
The files follow the README: `Errors.lean`, `Encoding.lean`, and one file for each group of calls,
`G1.lean`, `G2.lean` and `Pairing.lean`.

### Input and output

A field element takes 64 bytes: 16 zero bytes, then its 48 bytes, big-endian.
A point takes its coordinates in order, and the point at infinity is all zeros:

```text
G1 point:  [ x: 64 | y: 64 ]
G2 point:  [ x.c0: 64 | x.c1: 64 | y.c0: 64 | y.c1: 64 ]
MSM pair:  [ point | scalar: 32 ]
pairing:   k pairs of [ G1 point: 128 | G2 point: 256 ], and the word 1 or 0
```

The additions accept any points on the curve, and the multiplications and the pairing check require
points in the subgroup of prime order.

### Errors and price

Each call checks the length before it charges the gas.
The errors are `invalidInputLength`, `outOfGas`, `invalidPadding`, `invalidFieldElement`,
`notOnCurve`, `notInSubgroup` and `notASquare`.

The additions cost 375 for G1 and 600 for G2, and the maps 5500 and 23800.
The pairing check costs `32600 * k + 37700` on `k` pairs.
An MSM on `k` pairs costs `k * 12000` for G1, or `k * 22500` for G2, times a discount of EIP-2537,
in thousandths.

### Proofs

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/Bls12381/`.
Each call rejects a wrong length before it charges the gas, then runs out of gas below its price
(`bls12G1Add_invalidInputLength`, `bls12G1Add_outOfGas`, and the same for the other calls).
Every output has the length of a point, or of the word (`bls12G1Add_size`, `bls12Pairing_ok`).
The discount never raises the price of an MSM above that of `k` separate products
(`bls12G1MsmGas_le`, `bls12G2MsmGas_le`).
Decoding undoes encoding for points on the curve, and every decoded point has one encoding
(`bytesToG1_g1ToBytes`, `g1ToBytes_bytesToG1`, and the same for G2).

### Test vectors

`bindings/python/tests/precompile/test_eip2537.py` runs the test vectors of EIP-2537, with the MSM
cases above 8 pairs.
`test_execution_specs_vectors.py` runs the EIP-2537 vectors of execution-specs.

## P256VERIFY

P256VERIFY at `0x100` checks an ECDSA signature over secp256r1, the curve of passkeys and secure
enclaves.

### Source

[EIP-7951](https://eips.ethereum.org/EIPS/eip-7951), from Fusaka.
Its verification algorithm is that of SEC 1 v2 §4.1.4.

### Input and output

```text
input:   [ hash: 32 | r: 32 | s: 32 | qx: 32 | qy: 32 ]
output:  the word 1 for a valid signature, and no bytes otherwise
```

A wrong length, a value out of range, an invalid key or an invalid signature gives empty output.

### Errors and price

The price is 6900.
The call charges the gas first, and fails only with `outOfGas`.

### Proofs

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/P256Verify.lean`.
A call fails exactly when the gas is below 6900 (`p256Verify_eq_error_iff`).
With enough gas, a wrong length gives empty output (`p256Verify_invalidInputLength`), and every
output is the word 1 or empty (`p256Verify_ok`).
A signature with `r` or `s` outside `(0, n)` never verifies (`verify_of_r_out`, `verify_of_s_out`).

### Test vectors

`bindings/python/tests/precompile/test_p256verify.py` runs every test vector of EIP-7951.
