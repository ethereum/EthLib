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
- `engine_forkchoiceUpdated` with payload attributes now answers a syncing head, an invalid head and a head below the known finalized block, since no payload build begins there ([#1018](https://github.com/ethereum/EthLib/pull/1018)).
  A request that would select a new head with payload attributes is still refused with code 0, because the build is not specified.
- The shuffle errors of `ConsensusError` now have the codes 201 to 204, in place of 1 to 4 ([#1087](https://github.com/ethereum/EthLib/pull/1087)).
  The custody errors already had the codes 1 to 3 in the same class, so a code did not name one error.
  A caller that tests `code == 1` for an index at or past the count now tests `code == 201`.
  The new code 204 is a count above 2^40.
- `compute_shuffled_index` and `compute_shuffled_permutation` now fail for a count above 2^40, as the consensus specification does ([#1072](https://github.com/ethereum/EthLib/pull/1072) and [#1087](https://github.com/ethereum/EthLib/pull/1087)).
  Before, the index wrapped a bucket number that does not fit in 4 bytes and returned a value.
- The C export `eth_engine_forkchoice_updated` now rejects a tree of known payloads that names one block hash twice, with code 0 ([#1102](https://github.com/ethereum/EthLib/pull/1102)).
  Before, it answered from the first entry of that hash and ignored the second.
- The Ethash exports, the CRC-32 and CRC-32C exports and the precompile price now take and return typed values ([#1516](https://github.com/ethereum/EthLib/pull/1516)).
  A number crosses as a Python `int`, and the proof-of-work function returns its mix digest and its result as a pair.
  The C exports take the tuple of their arguments as one value, as `eth_consensus_fork_choice` does.
  In Python, an argument that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError` before.
  Examples are a `str` given for bytes and a `bool` given for an `int`.
  A negative number raises `ValueError`, where it raised `OverflowError`.
  An address of 2^64 or more has no precompile, so its price raises `PrecompileError`, where it raised `OverflowError`.
- The EVM word and memory exports, the CREATE address, the fee exports and the block difficulty now take and return typed values ([#1524](https://github.com/ethereum/EthLib/pull/1524)).
  `eth_evm_word_op` takes the opcode and a list of at most three operands, each an `int` below 2^256.
  `eth_evm_extend_memory` replaces `eth_evm_extend_memory_cost` and `eth_evm_extend_memory_expand_by`, and returns the price and the growth as a pair.
  Each range is a pair of two words.
  The base fee and the fake exponential now return a result that can fail, as every typed export does.
  The error codes 101 and 102 of `EvmError` are gone, since no export reads the lengths of operands or ranges now.
  In Python, an argument that Lean cannot read raises the error class of the method with code 0.
  Examples are an operand, a range word or an opcode out of range, more than three operands, a `bool` given for an `int` and `bytes` given for a fork name.
  Before, these raised `OverflowError`, `ValueError`, `TypeError` or `AttributeError`.
  A negative number raises `ValueError`, where it raised `OverflowError`.
- The transaction check, the check against a block, the settlement and the run now take and return typed values ([#1529](https://github.com/ethereum/EthLib/pull/1529)).
  The C exports `eth_tx_check`, `eth_tx_check_in_block`, `eth_tx_settle` and `eth_tx_run` take the tuple of their arguments as one value.
  They return tuples where they returned fixed-width bytes or an RLP list.
  In Python, `Run.accounts` holds each nonce, balance and storage value as an `int`, where they were the bytes of RLP scalars.
  Each account and each storage slot is a tuple, where it was a list.
  An argument that Lean cannot read raises `TransactionError` with code 0, where some raised `TypeError` or `OverflowError`.
  Examples are a chain ID of 2^64 or more, a `bool` given for an `int` and `bytes` given for a fork name.
  A negative number raises `ValueError`, where it raised `OverflowError`.
- The header checks, the genesis block, the typed RLP decoder and the hex-prefix encoding now take typed values ([#1542](https://github.com/ethereum/EthLib/pull/1542)).
  The C exports `eth_block_validate_header`, `eth_block_check_header`, `eth_genesis_block`, `eth_rlp_decode_as` and `eth_trie_hex_prefix` take the tuple of their arguments as one value.
  The header checks take the blob schedules as pairs of four integers, and return `None`.
  `eth_genesis_block` takes the fields of the header as one tuple, and `eth_trie_hex_prefix` takes a list of nibbles.
  `eth_rlp_decode_as` returns the value itself, such as an `int`, a `bool` or `None` for a contract creation.
  A new export, `eth_pow_chain_forks`, writes the RLP form of the forks of a chain, which `chain_forks` returns.
  In Python, an argument that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
  Examples are `bytes` given for a fork name or for the kind of `rlp.decode_as`, and an `int` given for the `is_leaf` flag.
  A nibble of 16 or more raises `TrieError` with code 0, where one of 256 or more raised `OverflowError`.
  A negative number raises `ValueError`, where some raised `OverflowError`.
- Every typed export reads a pair, such as a memory range or a blob schedule, from a Python list as from a tuple ([#1542](https://github.com/ethereum/EthLib/pull/1542)).
- The networking exports that returned JSON text, packed records or joined bytes now return typed values ([#1547](https://github.com/ethereum/EthLib/pull/1547)).
  These are the discv5 key derivation, packet, message, WHOAREYOU and handshake exports, the fork identifier, the consensus entries and `eth` entry of a record, the RLPx answer and the req/resp response chunk.
  Their C exports take the tuple of their arguments as one value, and return a typed value where they returned bytes.
  Two new exports, `eth_fork_id_schedule` and `eth_fork_id_encode`, write the RLP schedule and fork identifier that `forkid.schedule` and `forkid.encode` return.
  `forkid.encode` now requires a 4-byte hash and a next fork below 2^64, as the fork identifier types them.
  The discv5 `dict` results keep their keys and values, in the order of the packet rather than sorted.
  In Python, an argument of the right Python type that Lean rejects raises the error class of the method with code 0, where some raised `TypeError`, `OverflowError` or `AttributeError`.
  Examples are a block number of 2^64, `bytes` given for a fork name, and `str` given for bytes.
  A negative number raises `ValueError`, where it raised `OverflowError`, and a value that cannot cross, such as a `bytearray`, still raises `TypeError`.
  `rlpx.SECRETS_SIZE` is now read from Lean.
- The consensus presets, configurations and parameters, and the active fork of a configured chain, now take and return typed values ([#1548](https://github.com/ethereum/EthLib/pull/1548)).
  The C exports `eth_consensus_preset`, `eth_consensus_config`, `eth_consensus_parameters` and `eth_active_fork` take the tuple of their arguments as one value.
  The first three return a `dict`, where they returned JSON text.
  An integer in that `dict` is an `int`, where it was a string of decimal digits.
  `eth_active_fork` takes the chain configuration as a `dict` with the keys of its JSON form, and returns the name of the fork or `None`.
  In Python, an argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
  An example is `bytes` given for a name.
  A timestamp or a block number of 2^64 or more given to `chain.active_fork` raises `ChainError` with code 0, where it raised `OverflowError`.
  A `bool` given there raises `ChainError` with code 0, where it read as 0 or 1.
  A negative number raises `ValueError`, where it raised `OverflowError`.
- A replacement of a 64-bit value of a consensus configuration may now be an `int`, where it had to be a string ([#1548](https://github.com/ethereum/EthLib/pull/1548)).
- The Engine API exports, the block state transition and the check of an `eth_getProof` answer now take typed values in place of JSON text ([#1549](https://github.com/ethereum/EthLib/pull/1549)).
  The C exports `eth_engine_new_payload`, `eth_engine_forkchoice_updated`, `eth_engine_prepare_execution_payload`, `eth_engine_new_payload_on_chain`, `eth_state_transition` and `eth_trie_verify_account_proof` take the tuple of their arguments as one value.
  A configuration, a request or an answer crosses as the Python value of its JSON, and the first three return the value of the JSON of their answer.
  `eth_engine_new_payload_on_chain` returns the status with the header and the accounts in RLP, or `None` twice, where it returned an RLP list.
  `eth_trie_verify_account_proof` returns `None` for an absent account, or one bool for each slot, and Lean reads the patterns of the fields of the answer, where Python read them.
  In Python, `bytes` inside one of these values now crosses as `0x` hex text, where `json.dumps` refused it.
  A `float`, a negative `int` or a `dict` key that is not a `str` raises `TypeError` or `ValueError`, where `json.dumps` wrote it.
  An argument of the right Python type that Lean rejects raises the error class of the method with code 0, where some raised `TypeError`.
  Examples are `str` given for the state, and `1` given for `check_seal`.
  A field of an `eth_getProof` answer that is missing or out of its pattern raises `TrieError` with code 0, where it raised `KeyError` or `ValueError`.
- On a free-threaded build of CPython, such as 3.14t, importing the extension now leaves the GIL disabled ([#1372](https://github.com/ethereum/EthLib/issues/1372)).
  Threads may call the exports at the same time, and a list that another thread changes during a call is read as a snapshot.
- The consensus gossip and req/resp lists, the subscribed subnets and the SSZ root exports now take and return typed values ([#1551](https://github.com/ethereum/EthLib/pull/1551)).
  The C exports `eth_consensus_gossip_topics`, `eth_consensus_reqresp_protocol_ids`, `eth_consensus_reqresp_parse_protocol_id`, `eth_consensus_reqresp_request_bounds`, `eth_consensus_reqresp_response_bounds` and `eth_consensus_compute_subscribed_subnets` take the tuple of their arguments as one value.
  So do `eth_consensus_ssz_static`, `eth_consensus_reqresp_message`, `eth_consensus_merkle_proof` and `eth_pq_keys_ssz`.
  A list comes back as a list, the subscribed subnets as a list of `int`, and a pair as a tuple, where each came back as JSON text.
  The three SSZ exports return the root and the bytes as a pair, where they returned the two joined.
  `eth_consensus_merkle_proof` returns the node and the list of its siblings, and `eth_consensus_compute_subscribed_subnets` takes the node ID as an `int`.
  In Python, a node ID of 2^256 or more, or an epoch or a generalized index of 2^64 or more, raises the error class of the method with code 0, where it raised `OverflowError`.
  A `bool` given for one of them raises the same error, where it read as 0 or 1.
  A negative number raises `ValueError`, where it raised `OverflowError`.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
- The custody exports, the shuffle, the matrix, the shape check of a data column sidecar and the sidecars of a block now take and return typed values ([#1552](https://github.com/ethereum/EthLib/pull/1552)).
  The C exports `eth_consensus_get_custody_groups`, `eth_consensus_compute_columns_for_custody_group`, `eth_consensus_compute_shuffled_permutation`, `eth_consensus_compute_shuffled_index` and `eth_consensus_get_validators_custody_requirement` take the tuple of their arguments as one value.
  So do `eth_consensus_verify_data_column_sidecar`, `eth_consensus_compute_matrix`, `eth_consensus_recover_matrix` and the two exports of the sidecars of a block.
  A list of groups, columns or positions comes back as a list of `int`, where it came back as JSON text.
  A node ID crosses as an `int`, a validator index as an `int`, and a configuration replacement as a `dict`.
  The blobs and the matrix entries cross as a list of bytes, where they crossed joined in one byte string.
  The sidecars come back as a list of bytes, where they came back as the SSZ encoding of a list.
  A row of cells crosses as a pair of lists, and a row with another count than 128 cells and 128 proofs raises `SszError` with code 0.
  In Python, a node ID of 2^256 or more, or a count, group or index of 2^64 or more, raises the error class of the method with code 0.
  A `bool` or a `str` given for one of these numbers raises the same error.
  Before, these cases raised `OverflowError` or `TypeError`, or read a `bool` as 0 or 1, and for a validator index they raised `struct.error`.
  A negative number raises `ValueError`.
  A seed, a blob, a matrix entry, or a cell or proof of a row, of the wrong length, raises the error class of the method with code 0 and the message `expected N bytes, got M`.
  A `bytearray` or a `memoryview` given for bytes raises `TypeError`, where some were read as bytes.
- The consensus transition exports now take typed values ([#1556](https://github.com/ethereum/EthLib/pull/1556)).
  These are the block operations, the epoch steps, the slots and the state transitions of one block or of several blocks.
  They are also the upgrades, the rewards and penalties, the genesis exports and the weak subjectivity exports.
  Their C exports take the tuple of their arguments as one value, in the order they had.
  A configuration replacement crosses as a `dict`, where it crossed as JSON text, and any other value raises the error class of the method with code 0.
  In a replacement, a negative `int` or a `float` raises `ValueError` or `TypeError` from the converter, and `bytes` crosses as `0x` hex.
  The names of the kinds of deltas and of the forks of the blocks cross as `str`.
  The deposits of the genesis cross as a list of bytes, one deposit each, where they crossed joined in one byte string.
  A hash of the Eth1 block of another length than 32 bytes raises `TransitionError` with code 0 and the message `expected 32 bytes, got N`, where the message began with `input rejected`.
  Every argument is read before the names, so an argument that Lean cannot read is reported before an unknown preset.
  In Python, a slot count or an Eth1 timestamp of 2^64 or more, or a negative one, raises an error, where it was read modulo 2^64 without one.
  The times of weak subjectivity of 2^64 or more raise the error class of the method with code 0, where they raised `OverflowError`.
  A negative number raises `ValueError`.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where it raised `TypeError`.
  Examples are `bytes` given for a name and `str` given for a state.
  A `bool` given for a slot count, and `1` or `None` given for `verify`, now raise the same error, where they were read as 0 or 1 or by truthiness.
  The limits of the converter, 2^29 bytes and 1,000,000 values in one call, now apply to the states and the blocks.
- The honest validator exports that take a state, and the optimistic sync exports of the ancestor and the payload verdicts, now take and return typed values ([#1558](https://github.com/ethereum/EthLib/pull/1558)).
  These are the committee, proposer, sync committee and PTC assignments, the sync committee subnets and the upcoming proposal slots.
  They are also the signature of a duty, the construction of an attestation and of a single attestation, the Eth1 vote, the pending deposit count and the new state root.
  The others are the latest verified ancestor and the two payload verdicts.
  Their C exports take the tuple of their arguments as one value, in the order they had, and a configuration replacement as a `dict`, as the transition exports do.
  The committee assignment comes back as a tuple of the committee, its index and its slot, or `None`, where it came back as JSON text.
  The PTC assignment comes back as an `int` or `None`, and the sync committee subnets and the upcoming proposal slots as a list of `int`, where they came back as JSON text.
  The Eth1 chain crosses as a list of pairs of a timestamp and the SSZ bytes of the Eth1 data, where each block crossed as 80 packed bytes.
  Eth1 data of another length than 72 bytes raises `ProposerError` with code 0, after the fork and the state are read, where it raised `ValueError`.
  The optimistic roots cross and come back as a list of 32-byte roots, where they crossed joined in one byte string.
  A root of another length than 32 bytes raises the error class of the method with code 0 and the message `expected 32 bytes, got N`.
  Before, the message was `a root is 32 bytes, not N` or `a list of roots is 32 bytes each, not N`, and it came after the checks of the name and the fork.
  In Python, an epoch, an index or a timestamp of 2^64 or more raises the error class of the method with code 0, where it raised `OverflowError`, or `struct.error` for an Eth1 timestamp.
  A negative number raises `ValueError`, where it raised `OverflowError` or `struct.error`.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
  An example is `bytes` given for a name or a duty.
  A `bool` given for an index, and `1` or `None` given for `verify`, now raise the same error, where they were read as 0 or 1 or by truthiness.
  A `bytearray` or a `memoryview` given for an optimistic root or for the Eth1 data of a block raises `TypeError`, where it was read as bytes.
- The light client exports that take a configuration now take and return typed values ([#1559](https://github.com/ethereum/EthLib/pull/1559)).
  These are the sync, the light client header of a block, the checks of the proofs of an update, the ranking of two updates, the bootstrap, the update and the fork digest.
  Their C exports take the tuple of their arguments as one value, in the order they had, and a configuration replacement as a `dict`, as the transition exports do.
  The steps of a sync cross as tuples, `("update", fork, slot, data)`, `("force", slot)` and `("upgrade", fork)`, where they crossed packed in one byte string.
  The sync returns, for each step, the pair of the finalized and the optimistic header, each a tuple of a slot and two roots, where it returned 144 bytes for each step.
  The light client header of a block comes back as the pair of the root and the bytes, where the two came back joined.
  An unknown finalized block of an update is `None`, where it was empty bytes; in Python, empty bytes still stand for it.
  A root of another length than 32 bytes raises the error class of the method with code 0 and the message `expected 32 bytes, got N`, where it said `a root has 32 bytes`.
  In Python, a step of an unknown kind raises `LightClientError` with code 0, where it raised `ValueError`.
  A slot of a step of 2^64 or more raises `LightClientError` with code 0, and a negative one `ValueError`, where it raised `OverflowError`.
  An epoch of the fork digest of 2^64 or more raises `SszError` with code 0, and a negative one `ValueError`, where both were read modulo 2^64.
  A `bool` given for a slot or an epoch raises the error class of the method with code 0, where it was read as 0 or 1.
  A `bytearray` or a `memoryview` given for the data of an update raises `TypeError`, where it was read as bytes.
  Every argument is read before the names, so a root of the wrong length is reported before an unknown preset or a fork before Altair.
  The limits of the converter, 2^29 bytes and 1,000,000 values in one call, now apply to the states, the blocks and the steps.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
- A chain configuration that the exports read as JSON is now rejected, with code 0, when a fork by block number comes after a fork by timestamp ([#1110](https://github.com/ethereum/EthLib/pull/1110)).
  EIP-6122 requires the forks by timestamp to be scheduled at or after the forks by block.

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
