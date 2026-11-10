# Changelog

This file lists the changes of each release that a caller of EthLib may need to act on.
The version is the same in `pyproject.toml` and `lakefile.lean`.

## 0.4.0

Not yet released.

### Changes that break callers

- `MIN_REQUEST_LIMIT`, the fewest versioned hashes that `engine_getBlobs` must take in one request, is now `MIN_BLOBS_REQUEST_LIMIT`.
  Its value stays 128, and no C export or Python function changes.
- The optimistic store now holds its head as a fork choice node, a root and the status of its payload, in place of the root of the head block ([#1475](https://github.com/ethereum/EthLib/issues/1475)).
  From Gloas, the optimism of the head reads the payload that the status names, so it can fail as a payload chain does, and it returns an `Except`.
  The C export `eth_consensus_is_optimistic_node` takes the code of that status after the head root: 0 empty, 1 full and 2 pending.
  In Python, `consensus.is_optimistic_node` takes it as the keyword `head_payload_status`, 2 by default, so a call before Gloas gets the same answer as before.
  The latest verified ancestor now takes a fork choice node; before Gloas it reads only the root.
  The C export `eth_consensus_latest_verified_ancestor` takes the code of the status after the root, and `consensus.latest_verified_ancestor` takes it as the keyword `payload_status`, 2 by default.
  The latest verified ancestor and the optimistic node now run at Gloas.
  The theorem `latestVerifiedAncestor_of_glamsterdam` now states the Gloas answer, no longer a failure.
  The optimistic node then fails when the head is not optimistic, since its second case is not yet specified.
- `compute_min_epochs_for_block_requests` now takes the fork, and from Gloas it applies a formula derived from the [weak subjectivity period of EIP-8061](https://eips.ethereum.org/EIPS/eip-8061#weak-subjectivity-period).
  Before, every fork got the Phase 0 value: 33024 epochs on mainnet, where Gloas asks for 14299.
  `Config.computeMinEpochsForBlockRequests` takes the fork as a new argument.
  The C export `eth_consensus_compute_min_epochs_for_block_requests` reads the configuration and the fork as a pair, as `eth_consensus_gossip_topics` does.
  In Python, `consensus.compute_min_epochs_for_block_requests` takes the fork first, then the configuration, `mainnet` by default.
- `NoiseError` now gives its own code to each failure of the local identity secret, of signing and of the saved remote message, in the libp2p Noise handshake ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  Before, a failure of the secret or of signing had code 9, the code of an invalid remote identity.
  An identity secret that is 0, or at least the secp256k1 group order, now gives code 11, `identitySecret`.
  A failure of ECDSA signing with that secret gives code 12, `signing`.
  Completion of a state whose saved remote message is missing, or does not match the state, gives code 13, `savedRemote`.
  Before, such a state gave the error of the failed step: code 1, 3, 4, 6, 7, 8 or 9.
  Code 9 now means only a remote identity that fails to authenticate.
- The libp2p Noise handshake gives the identity secret, the chaining key and the handshake hash their own types, apart from the type of the X25519 keys ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  The secp256k1 identity secret of `writeLibp2p` and `makePayload` is a scalar `Secp256k1.Fn`, in place of 32 bytes.
  `Libp2p.publicKey` and `Libp2p.sign` take that scalar too, and the exports read it from 32 big-endian bytes whose value must be below the group order.
  The chaining key and the handshake hash of `SymmetricState` have the types `ChainingKey` and `HandshakeHash`, and `hkdf2` takes a `ChainingKey`.
  The C exports and the Python functions keep their signatures: they take the secret and return the chaining key and the hash as 32 bytes.
  `writeLibp2p` now rejects a zero identity secret before every other check, on every message, message 1 included.
  The C export `eth_noise_libp2p_write`, and `noise_libp2p_write` in Python, give code 11 for a secret of 0 or at least the group order.
  Before, a write at step 0 ignored the secret: message 1 succeeded, and a responder writing out of turn got code 1, `wrongPhase`, or code 10, `firstMessageExtensions`.
- The libp2p Noise state now stores the authenticated remote, in place of the encrypted remote message and the state before it ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  Completion returns that remote with the transport ciphers, and reads no message.
  It returns `Remote × CipherState × CipherState`.
  `Libp2pState.remoteMessage` is now `Libp2pState.remote`, a `Remote` with the static key, the identity point, the signature and the extensions.
  `AuthenticatedRemote`, `RemoteInfo` and `remoteInfo` are removed, and `authenticatePayload` returns a `Remote`.
  `writeLibp2p` no longer runs completion after message 3.
  The Python state of `noise_libp2p_*` holds the remote as `(static_key, public_key, signature, extensions)`, or `None`, in place of the saved message and its state.
  Completion checks that the stored remote has the remote static key of the handshake, and no longer verifies its signature.
  Code 13, `savedRemote`, now means that at completion the state holds no remote, or one whose static key is not the remote static key of the handshake.
  `readLibp2p_authenticates` now concludes that the new state stores the authenticated `Remote`.
  The theorems `complete_authenticates` and `complete_peerId` are replaced by `complete_ok` and the `Produced` theorems, and `authenticatePayload_decode` by `authenticatePayload_ok`.
  The C exports and Python functions that take a libp2p state, to write, read or complete, also give code 13 when the stored public key does not decode.
- `ethlib.networking.noise` now exports short typed wrappers in place of the raw `noise_*` names of the extension ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  `noise_initialize` is now `initialize`, `noise_cipher_encrypt` is `cipher_encrypt`, `noise_libp2p_complete` is `libp2p_complete`, and so on; `libp2p_write` takes `extensions=None` by default.
  The package also exports the type aliases of its states, `CipherState`, `HandshakeState`, `Remote`, `Libp2pState`, `Identity` and `Completion`, which `lake exe gen-bindings` writes from Lean, and `NoiseError`.
  The extension methods keep their names and signatures.
- A chain configuration now holds the address of its deposit contract, and the deposit requests of a block come from that address ([#1486](https://github.com/ethereum/EthLib/issues/1486)).
  Before, every chain read deposits from the mainnet address, so a chain with another deposit contract, such as Sepolia, got no deposit request.
  The configuration that the exports read as JSON, or as a Python `dict`, must give `depositContractAddress`: `0x` and forty hex digits, or 20 bytes in Python.
  A configuration without it is rejected with `config: no depositContractAddress`.
  `depositRequests`, the C export `eth_block_deposit_requests` and `blocks.deposit_requests` in Python take the address first.
- The output of the VRF tree at index `i` now hashes the index before the secret: `keccak256(PQ_VRF_OUTPUT | LE32(i) | s)` ([#1652](https://github.com/ethereum/EthLib/pull/1652)).
  Every output changes, for every root, index and seed.
  Roots and openings are unchanged, so an existing opening still verifies, but returns a different output.
  `verify`, `verifyBytes` and `evaluate` keep their arguments, and `outputHash` takes the index.
  Before, one secret placed at every leaf gave every index the same output, which the holder could choose.
  A new `mixOutput`, the C export `eth_vrf_mix` and `vrf.mix` in Python hash an output with randomness.
  A selection must compare that mixed value, with randomness revealed after the root is registered.
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
  The limits of the converter, 2^29 bytes and 2^22 values in one call, now apply to the states and the blocks.
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
  The limits of the converter, 2^29 bytes and 2^22 values in one call, now apply to the states, the blocks and the steps.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
- The gossip validation export now takes and returns typed values ([#1561](https://github.com/ethereum/EthLib/pull/1561)).
  Its C export takes the tuple of its arguments as one value, in the order it had, and a configuration replacement as a `dict`, as the transition exports do.
  The blocks after the anchor cross as tuples of a kind, a payload status or `None`, the SSZ bytes and an optional envelope, where they crossed packed in one byte string.
  An envelope of `None` means no envelope, as empty bytes still do.
  A payload status of 255 is now a status, where it meant none; only `None` means none.
  The messages cross as tuples of a time, a subnet, the SSZ bytes and an optional topic, where they crossed packed in one byte string.
  A topic of a message may now be longer than 255 bytes in UTF-8, where it raised `ValueError`.
  The finalized checkpoint crosses as a pair of an epoch and a root, or `None`, where it crossed as 40 bytes, and the topic as a `str`.
  Each outcome comes back as a pair of `valid`, `ignore` or `reject` and its reason or `None`, where it came back packed in one byte string.
  In Python, a block or a message of another length than three or four items raises `ForkChoiceError` with code 0.
  Before, a shorter one raised `ValueError`, and a longer one was read without its extra items.
  A time, a subnet or an epoch of 2^64 or more raises `ForkChoiceError` with code 0, and a negative one `ValueError`, where it raised `OverflowError`.
  A kind or a payload status of 256 or more raises `ForkChoiceError` with code 0, where it raised `ValueError`.
  A `bool` given for one of these numbers, and `1` or `None` given for `verify`, raise the same error, where they were read as 0 or 1 or by truthiness.
  A `bytearray` or a `memoryview` given for the bytes of a block, an envelope or a message raises `TypeError`, where it was read as bytes.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError` or `AttributeError`.
  A root of the finalized checkpoint of another length than 32 bytes raises `ForkChoiceError` with code 0 and the message `expected 32 bytes, got N`, where the message was `the finalized checkpoint is not 40 bytes`.
  Every argument is read before the names, and the limits of the converter, 2^29 bytes and 2^22 values in one call, now apply.
- The generic SSZ exports now take and return typed values ([#1563](https://github.com/ethereum/EthLib/pull/1563)).
  The C exports `eth_ssz_serialize`, `eth_ssz_deserialize` and `eth_ssz_hash_tree_root` take the tuple of their arguments as one value.
  A type and a value cross as the Python values of their tagged form, such as `{"uint": 2}` and `{"uint": 258}`, where they crossed as JSON text.
  `eth_ssz_deserialize` returns the value as a `dict`, where it returned JSON text.
  In Python, `bytes` inside a type or a value now crosses as `0x` hex, where `json.dumps` refused it.
  A `float` or a `dict` key that is not a `str` raises `TypeError`, and a negative `int` raises `ValueError`, where each raised `SszError` with code 0.
  Data that is not `bytes` raises `SszError` with code 0, where it raised `TypeError`.
  The converter reads an argument nested at most 64 levels below it, where 256 SSZ levels were read.
  So a value of more than 31 `seq` or `union` levels raises `ValueError`, and so does a type of more than 32 `vector` or `list` levels or more than 21 `container` levels.
  A value that `deserialize` returns past these bounds, or past the converter budget, cannot be given back to `serialize`.
- The active fork of mainnet and of Hoodi, the seal hash, the proof-of-work check, the gossip message ID and the recent blocks of a chain now cross as typed values ([#1571](https://github.com/ethereum/EthLib/pull/1571)).
  The C exports `eth_mainnet_active_fork`, `eth_hoodi_active_fork`, `eth_pow_seal_hash`, `eth_pow_check` and `eth_gossip_message_id` take the tuple of their arguments as one value.
  A fork crosses as its name, a `str`, where it crossed as UTF-8 bytes, and the active fork comes back as a `str` or `None`, where it came back as bytes.
  `eth_state_transition` and `eth_engine_new_payload_on_chain` take the recent blocks as a list of tuples, where they took one RLP list.
  Each tuple is the fork name, the header in RLP form and the list of the RLP forms of its ommers.
  In Python, `mainnet_active_fork` and `hoodi_active_fork` raise `ChainError` with code 0 for a block number or a timestamp of 2^64 or more.
  They raise `ValueError` for a negative one, where both raised `OverflowError`.
  A `bool` given there raises `ChainError` with code 0, where it was read as 0 or 1.
  A recent block whose header or ommer does not decode raises `BlockError` from `state_transition` and `EngineError` from `new_payload_on_chain`, with code 0, where it raised `RlpError`.
  A fork name given as `bytes` to `seal_hash`, `check_proof_of_work` or `message_id` raises the error class of the method with code 0.
- A Python value of a list or a `dict` with many items no longer overflows the stack when an export reads it as JSON or writes JSON as a Python value ([#1563](https://github.com/ethereum/EthLib/pull/1563)).
  Every export that reads a typed value as JSON, or returns JSON as a typed value, reads and writes the items in a loop.
- The converter of typed values now passes up to 2^22 values in one call, where it passed 1,000,000, so that the longest `ssz_generic` vectors of consensus-spec-tests cross ([#1563](https://github.com/ethereum/EthLib/pull/1563)).
- A chain configuration that the exports read as JSON is now rejected, with code 0, when a fork by block number comes after a fork by timestamp ([#1110](https://github.com/ethereum/EthLib/pull/1110)).
  EIP-6122 requires the forks by timestamp to be scheduled at or after the forks by block.
- leanSPHINCS now hashes with the layout of FIPS 205 ([#1555](https://github.com/ethereum/EthLib/pull/1555)).
  For the same seed and message, `key_gen` and `sign` now return a different key and signature.
  `verify` checks the new layout, so keys and signatures made with 0.3.0 must be made again.
  The sizes are unchanged: a 32-byte seed, a 32-byte public key and a 7740-byte signature.
  The public key is now `PK.seed` then the root, 16 bytes each, in place of the root then the public parameter.
  The Python constant `sphincs.PUBLIC_PARAM_LEN` and the C export `eth_sphincs_const_public_param_len` are removed.
- The gossip topics of Heze are now those of Gloas followed by `inclusion_list` ([#1469](https://github.com/ethereum/EthLib/issues/1469)).
  `consensus.gossip_topics` and `consensus.gossip_topic_bound` now answer at `hegota`, where they raised `ConsensusError`.
  The error of code 304 is gone, since every fork now has a list of topics, and no other error takes that code.
  In Lean, `Config.gossipTopics` returns a `List GossipTopic`, where it returned an `Option`.
- The gossip bounds of four topics are now held to the size limits that the networking specification sets on their messages ([#1610](https://github.com/ethereum/EthLib/issues/1610)).
  `consensus.gossip_topic_bound` answers the limit for `beacon_aggregate_and_proof`, `attester_slashing` and `execution_payload_bid` from `glamsterdam`, and for `inclusion_list` at `hegota`, where it answered the payload cap of 10485760 bytes.
  On mainnet the limits are 16829, 2097616, 196932 and 41112 bytes, and that of a bid is 196934 bytes at `hegota`.
  In Lean, `topicBound_eq` now takes a topic without a size limit, and `decodePayload_message` a message within the size limit of its topic.
- Data column sidecars on gossip and in responses, and inclusion lists in responses, are now held to the size limits of the networking specification ([#1618](https://github.com/ethereum/EthLib/issues/1618)).
  From `glamsterdam`, `consensus.gossip_topic_bound` answers 44072 bytes on mainnet and 18920 on minimal for `data_column_sidecar_{subnet_id}`, where it answered the payload cap of 10485760 bytes.
  `consensus.reqresp_response_bounds` answers (56, 44072) on mainnet and (56, 18920) on minimal for `data_column_sidecars_by_range` and `data_column_sidecars_by_root`, and (152, 41112) for `inclusion_lists_by_indices` at `hegota`.
  Their largest length was the payload cap of 10485760 bytes.
  The limit of a sidecar is its size with a cell and a proof for each blob of the largest blob limit.
  In Lean, `GossipTopic.sizeLimit` now takes the configuration, and the gossip `sizeLimit_ne_none_iff` names the data column sidecar topics.
  From `glamsterdam`, `decodePayload_message` at a sidecar topic now needs a message within the size limit of the topic.
  `responseBounds_eq` now takes a protocol without a size limit, and `decodeResponseChunk_response` a value within the size limit of its protocol.
- The rules that a transaction must pass alone now reject a transaction whose type the fork does not have, with `unsupportedType` and the type ([#1779](https://github.com/ethereum/EthLib/issues/1779)).
  Before, only decoding rejected it, so a block built in Lean could run a type-4 transaction before Pectra, or a type-3 transaction before Dencun.
  `validateTransaction` checks the type first, and the inclusion check and `checkTransaction` call it, so they reject such a transaction too.
  The exports decode each transaction at its fork first, so their answers do not change.
  In Lean, `validateTransaction_eq_ok_iff` ends with the new conjunct `tx.fork ≤ fork`, and `checkInclusion_fork_le` derives it from a passing inclusion check.
  `processTransaction_nonce_lt` no longer takes the hypothesis `tx.fork ≤ fork`.

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
