# Changelog

This file lists the changes of each release that a caller of EthLib may need to act on.
The version is the same in `pyproject.toml` and `lakefile.lean`.

## 0.4.0

Not yet released.

### Changes that break callers

- `engine_forkchoiceUpdated` now applies step 2 of its specification ([#1018](https://github.com/ethereum/EthLib/pull/1018)).
  The execution layer may know a finalized block from an earlier update.
  A valid head below that block is answered `VALID`, and the forkchoice state is not checked.
  The Lean function and the C export `eth_engine_forkchoice_updated` take that block as a new argument, between the tree and the request.
  The C export reads it as JSON text: a block hash, or `null` for none.
  In Python, `engine.forkchoice_updated` takes it as the keyword `finalized`, `None` by default, so a call without it gets the same answer as before.

## 0.3.0

Released on 2026-11-06.

0.2.0 had Python bindings for BLS and KZG only.
In 0.3.0, the package `ethlib` has a subpackage for each layer of EthLib:

- `ethlib.cryptography`: `aes`, `bls`, `crc32`, `crc32c`, `ethash`, `hmac`, `kdf`, `keccak`, `kzg`, `secp256k1`, `secp256r1`, `sha256`, `sphincs`, `vrf` and `xmss`
- `ethlib.serialization`: `rlp` and `ssz`
- `ethlib.networking`: `devp2p`, `discv4`, `discv5`, `enr`, `forkid`, `gossip`, `reqresp`, `rlpx`, `snappy` and `varint`
- `ethlib.execution`: `blocks`, `evm`, `fees`, `network`, `pow`, `transactions` and `trie`, with `ethlib.precompiles`, `ethlib.state` and `ethlib.chain`
- `ethlib.consensus` and `ethlib.engine`, for the consensus layer and the Engine API

The sections below list the changes that a caller of 0.2.0, or of master before this release, may need to act on.

### Typed errors in the Python bindings

A failed call into the Python bindings now raises an exception that carries the code and the message of the Lean error ([#310](https://github.com/ethereum/EthLib/pull/310)).
Before, most failures raised a bare `RuntimeError` or `ValueError` with the name of the operation, and the Lean message went to standard error.

The new module `ethlib.errors` defines one exception class for each primitive, such as `KzgError` or `BlsError`.
Each class derives from `EthLibError`, which has two attributes:

- `code`, an integer that names the kind of failure;
- `message`, the text of the Lean error.

Each class also derives from the class that the same failure raised before: `RuntimeError`, `ValueError` or both.
So a caller that catches `RuntimeError` or `ValueError` still catches it.
A caller that parsed the text of an old message must now read `message`.
A message no longer starts with the name of the operation.

The Lean type of each error defines its codes, one for each constructor, from 1.
When one Python class carries several Lean error types, the second type takes its codes from 101, the third from 201, and so on.
A theorem for each error type shows that two errors with one code come from one constructor.

Code 0 means a failure that has no Lean error code.
Examples are an unknown fork name and an input that the export reads before the specification runs.
No Lean error type uses code 0.
Some checks on the type or the length of an argument run in C first, and raise `TypeError` or `ValueError` with no code.

The C signatures of the fallible exports change too.
Each one returns the code and the message of its error, in place of a Lean `IO` error.

### Precompiles

The module `ethlib.precompiles` reaches every precompile by its address, at a fork named by the caller.
`run(fork, address, data, gas)` returns the output, and `price(fork, address, data)` returns the gas that the call charges ([#459](https://github.com/ethereum/EthLib/pull/459)).
A failed call raises `PrecompileError`, whose code names the precompile.

Before the release, master also had the modules `ethlib.precompiles.ecrecover`, `modexp`, `sha256` and `ripemd160`, with the classes `EcrecoverError`, `ModexpError` and `Sha256PrecompileError`.
They are removed, and 0.3.0 does not have them.
A caller of `modexp.modexp(data, gas)` now calls `run(fork, 0x05, data, gas)`, and a caller of `modexp.gas_cost(data)` calls `price(fork, 0x05, data)`.

### Other changes that break callers

- The KZG operations take the trusted setup as an argument and no longer run in `IO` ([#235](https://github.com/ethereum/EthLib/pull/235)), and their byte inputs are typed ([#346](https://github.com/ethereum/EthLib/pull/346)).
- leanXMSS replaced XMSS, with two layers of height 16 ([#134](https://github.com/ethereum/EthLib/pull/134)), and hashes with Keccak-256 in place of BLAKE2s ([#138](https://github.com/ethereum/EthLib/pull/138)).
- The C exports moved into a Lean library of their own, so Lean code that imported them changes its imports ([#119](https://github.com/ethereum/EthLib/pull/119)).
- An integer argument out of its range raises `OverflowError`, as Python's own conversions to a C integer do ([#718](https://github.com/ethereum/EthLib/pull/718)).
  Before, an integer outside [0, 2^64), an EVM opcode above 255 and the range checks of the Python wrappers raised `ValueError`.
  A caller that caught `ValueError` for such an argument now catches `OverflowError`.
- `consensus.verify_data_column_sidecar` takes the signed block before the configuration, in the order of its native export ([#729](https://github.com/ethereum/EthLib/pull/729)).
