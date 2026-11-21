"""The code and message of the errors that the execution and Engine exports pass to Python."""

from collections.abc import Callable

import pytest

from ethlib import chain, engine, precompiles, state
from ethlib.errors import (
    BlockError,
    ChainError,
    Devp2pError,
    EngineError,
    Era1Error,
    EthLibError,
    EthWireError,
    EvmError,
    FeesError,
    JwtError,
    PrecompileError,
    RpcError,
    SnapError,
    StateError,
    TransactionError,
    TrieError,
)
from ethlib.execution import (
    blocks,
    evm,
    fees,
    history,
    network,
    pow as proof_of_work,
    rpc,
    transactions,
    trie,
)
from ethlib.execution.network import snap
from ethlib.networking import devp2p, forkid
from ethlib.networking.forkid import BLOCK
from ethlib.serialization import rlp
from raising import raises

# An export turns the typed error of an operation into a code and a message.
# Each case pins one way of doing so, with the code and the message that Python sees.

# A Frontier header whose fields are zero, but for a difficulty and a gas limit of 1.
HEADER = [
    bytes(32),
    bytes(32),
    bytes(20),
    bytes(32),
    bytes(32),
    bytes(32),
    bytes(256),
    b"\x01",
    b"",
    b"\x01",
    b"",
    b"",
    b"",
    bytes(32),
    bytes(8),
]
# A chain that starts at Frontier, with a zero genesis hash.
SCHEDULE = forkid.schedule(bytes(32), 0, [("frontier", BLOCK, 0)])
# A chain configuration that activates no fork.
CONFIG = {"chainId": 1, "depositContractAddress": "0x" + "00" * 20, "activations": []}
# A legacy transaction with a gas limit of 1, below the intrinsic gas of 21000.
LOW_GAS_TX = rlp.encode([b"", b"", b"\x01", b"", b"", b"", b"\x1b", b"\x01", b"\x01"])
# The topic of the DepositEvent of the deposit contract, by EIP-6110.
DEPOSIT_TOPIC = bytes.fromhex("649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5")


@pytest.mark.parametrize(
    ("error", "code", "message", "call"),
    [
        # A header is an RLP list, not an empty string.
        pytest.param(
            BlockError,
            10,
            "header rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            lambda: blocks.header_hash("frontier", b"\x80"),
            id="block-rlp",
        ),
        # A block is a list of three fields, not an empty list.
        pytest.param(
            BlockError,
            13,
            "block rejected: EthLib.Serialization.Rlp.RlpError.wrongFieldCount 3 0",
            lambda: blocks.validate_size("frontier", b"\xc0"),
            id="block-size",
        ),
        # A receipt that starts with 0x80 has no known type.
        pytest.param(
            BlockError,
            102,
            "receipt rejected: EthLib.Execution.Blocks.ReceiptError.unsupportedType 128",
            lambda: blocks.receipt_reencode("frontier", b"\x80"),
            id="block-receipt",
        ),
        # The one log is an empty string, not a list.
        pytest.param(
            BlockError,
            10,
            "logs rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            lambda: blocks.deposit_requests(bytes(20), b"\xc1\x80"),
            id="block-deposit",
        ),
        # A block access list is an RLP list, not an empty string.
        pytest.param(
            BlockError,
            10,
            "block access list rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            lambda: blocks.check_block_access_list(b"\x80", 0),
            id="block-access-list",
        ),
        # No fork has the name nofork.
        pytest.param(
            BlockError,
            0,
            "no fork named nofork",
            lambda: blocks.header_hash("nofork", b"\x80"),
            id="block-fork",
        ),
        # A header is an RLP list, not an empty string.
        pytest.param(
            BlockError,
            10,
            "header rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            lambda: proof_of_work.check_proof_of_work("frontier", b"\x80"),
            id="pow",
        ),
        # No fork has the name nofork.
        pytest.param(
            BlockError,
            0,
            "no fork named nofork",
            lambda: proof_of_work.block_difficulty("nofork", 0, 0, 0, 0, 0),
            id="pow-argument",
        ),
        # A sender address is 20 bytes.
        pytest.param(
            EvmError,
            103,
            "the sender must be 20 bytes, not 19",
            lambda: evm.create2_address(bytes(19), bytes(32), b""),
            id="evm-argument",
        ),
        # An operand is a 256-bit word.
        pytest.param(
            EvmError,
            0,
            (
                "expected an int below "
                "115792089237316195423570985008687907853269984665640564039457584007913129639936, "
                "got "
                "115792089237316195423570985008687907853269984665640564039457584007913129639936"
            ),
            lambda: evm.word_op(0x01, 2**256),
            id="evm-word-op",
        ),
        # A fork before Dencun has no blob fee.
        pytest.param(
            FeesError,
            0,
            "a fork before dencun has no blob schedule",
            lambda: fees.calculate_data_fee("shapella", 0, b""),
            id="fees",
        ),
        # A Status message is a list, not an empty string.
        pytest.param(
            EthWireError,
            2,
            "message data is not RLP of the expected shape",
            lambda: network.decode_message(69, 0, b"\x80"),
            id="eth-message",
        ),
        # A header is an RLP list, not an empty string.
        pytest.param(
            EthWireError,
            0,
            ("header does not decode at this fork: EthLib.Serialization.Rlp.RlpError.bytesAsList"),
            lambda: network.check_body("frontier", b"\x80", b"\xc1"),
            id="eth-body",
        ),
        # A request is a list, not an empty string.
        pytest.param(
            EthWireError,
            2,
            "message data is not RLP of the expected shape",
            lambda: network.check_pooled(69, b"\x80", b"\x80"),
            id="eth-pooled",
        ),
        # No snap message has ID 99.
        pytest.param(
            SnapError,
            1,
            "message ID 99 is not used by this snap version",
            lambda: snap.decode_message(1, 99, b"\xc0"),
            id="snap",
        ),
        # The account 0x80 is not an account in slim form.
        pytest.param(
            SnapError,
            3,
            (
                "range answer does not verify: "
                "EthLib.Execution.Network.SnapRangeError.slimAccount (hash := "
                "0x0000000000000000000000000000000000000000000000000000000000000000)"
            ),
            lambda: snap.verify_account_range(bytes(32), bytes(32), [(bytes(32), b"\x80")], []),
            id="snap-range",
        ),
        # A slim account is a list, not an empty string.
        pytest.param(
            SnapError,
            0,
            "account is not in slim form",
            lambda: snap.full_account(b"\x80"),
            id="snap-argument",
        ),
        # An era1 file starts with a version entry.
        pytest.param(
            Era1Error,
            1,
            (
                "era1 file rejected: EthLib.Execution.History.Era1Error.e2store "
                "(EthLib.Serialization.E2store.E2storeError.noVersion none)"
            ),
            lambda: history.decode_era1(b""),
            id="era1",
        ),
        # 0x80 is the type of no transaction.
        pytest.param(
            TransactionError,
            2,
            "unsupportedType (type := 128)",
            lambda: transactions.tx_type("glamsterdam", b"\x80"),
            id="transaction",
        ),
        # No fork has the name nofork.
        pytest.param(
            TransactionError,
            0,
            "no fork named nofork",
            lambda: transactions.tx_type("nofork", b""),
            id="transaction-fork",
        ),
        # 0x80 is the type of no transaction.
        pytest.param(
            TransactionError,
            2,
            "unsupportedType (type := 128)",
            lambda: transactions.network_check("fusaka", b"\x80"),
            id="transaction-network",
        ),
        # An empty range with no proof does not match the zero root.
        pytest.param(
            TrieError,
            207,
            "range does not verify: EthLib.Execution.Trie.RangeError.mismatch",
            lambda: trie.verify_range(bytes(32), bytes(32), [], []),
            id="trie-range",
        ),
        # The answer must be a JSON object, not a list.
        pytest.param(
            TrieError,
            0,
            "answer: not an object",
            lambda: trie.verify_account_proof(bytes(32), []),  # ty: ignore[invalid-argument-type]
            id="trie-account-proof",
        ),
        # A state is an RLP list, not an empty string.
        pytest.param(
            StateError,
            2,
            "state is not an RLP list",
            lambda: state.state_root(b"\x80"),
            id="state-input",
        ),
        # The block is an RLP list, not an empty string.
        pytest.param(
            StateError,
            0,
            "block rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            lambda: state.withdrawals_root("paris", b"\xc0", b"\x80"),
            id="state-block",
        ),
        # MODEXP with no gas, for an input that costs 500.
        pytest.param(
            PrecompileError,
            5,
            (
                "EthLib.Execution.Evm.Precompiles.PrecompileError.modexp "
                "(EthLib.Execution.Evm.Precompiles.Modexp.ModexpError.outOfGas (cost := "
                "500) (gas := 0))"
            ),
            lambda: precompiles.run(
                "fusaka", 0x05, (1).to_bytes(32, "big") * 3 + b"\x02\x03\x05", 0
            ),
            id="precompile",
        ),
        # No precompile is at address 0x12 at Fusaka.
        pytest.param(
            PrecompileError,
            0,
            "no precompile at address 18 at fork fusaka",
            lambda: precompiles.run("fusaka", 0x12, b"", 0),
            id="precompile-address",
        ),
        # A hash is 32 bytes.
        pytest.param(
            RpcError,
            32602,
            "hash32: 1 bytes, not 32",
            lambda: rpc.read_param("hash32", "0x00"),
            id="rpc-param",
        ),
        # A state is an RLP list, not an empty string.
        pytest.param(
            RpcError,
            2,
            "state is not an RLP list",
            lambda: rpc.apply_overrides(b"\x80", {}),
            id="rpc-overrides",
        ),
        # The configuration has no chain ID.
        pytest.param(
            ChainError,
            0,
            "config: no chainId",
            lambda: chain.active_fork({}, 0, 0),
            id="chain",
        ),
        # The configuration has no chain ID.
        pytest.param(
            ChainError,
            0,
            "config: no chainId",
            lambda: chain.execution_blob_schedule({}, {}, 0, 0),
            id="chain-blob-schedule",
        ),
        # The Status announces eth/70 on an eth/69 session.
        pytest.param(
            EthWireError,
            101,
            "Status announces version 70, not the negotiated one",
            lambda: network.check_status(
                69,
                SCHEDULE,
                0,
                0,
                rlp.encode([b"\x46", b"\x01", bytes(32), [bytes(4), b""], b"", b"", bytes(32)]),
            ),
            id="eth-status",
        ),
        # A Status message is a list, not an empty string.
        pytest.param(
            EthWireError,
            2,
            "message data is not RLP of the expected shape",
            lambda: network.check_status(69, SCHEDULE, 0, 0, b"\x80"),
            id="eth-status-decode",
        ),
        # The answer repeats another request ID than the request.
        pytest.param(
            EthWireError,
            206,
            "response is not BlockHeaders with the request ID of the request",
            lambda: network.check_headers(
                69, rlp.encode([b"\x01", [b"\x01", b"\x01", b"", b""]]), rlp.encode([b"\x02", []])
            ),
            id="eth-headers",
        ),
        # The answer repeats another request ID than the request.
        pytest.param(
            EthWireError,
            303,
            "response is not PooledTransactions with the request ID of the request",
            lambda: network.check_pooled(69, rlp.encode([b"\x01", []]), rlp.encode([b"\x02", []])),
            id="eth-pool",
        ),
        # One receipt comes for a block with no transaction.
        pytest.param(
            EthWireError,
            501,
            "1 receipts delivered for 0 transactions",
            lambda: network.check_partial_receipts(rlp.encode([]), 0, rlp.encode([b"\x01"])),
            id="eth-partial-receipts",
        ),
        # A body is a list of its parts, not an empty string.
        pytest.param(
            EthWireError,
            601,
            "body is not the RLP list of its parts: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            lambda: network.check_body("frontier", rlp.encode(HEADER), b"\x80"),
            id="eth-body-refused",
        ),
        # A Status message is a list, not an empty string.
        pytest.param(
            EthWireError,
            2,
            "event 0: message data is not RLP of the expected shape",
            lambda: network.session(69, SCHEDULE, 0, 0, [(False, 0, b"\x80")]),
            id="eth-session-event",
        ),
        # A GetBlockHeaders request comes before the peer's Status.
        pytest.param(
            EthWireError,
            701,
            "event 0: message ID 3 came before the peer's Status",
            lambda: network.session(
                69,
                SCHEDULE,
                0,
                0,
                [(False, 3, rlp.encode([b"\x01", [b"\x01", b"\x01", b"", b""]]))],
            ),
            id="eth-session-refused",
        ),
        # A request is a list, not an empty string.
        pytest.param(
            EthWireError,
            2,
            "message data is not RLP of the expected shape",
            lambda: network.access_lists_answer(71, b"\x80", b"\x80", []),
            id="eth-access-lists",
        ),
        # Our Hello is a list, not an empty string.
        pytest.param(
            Devp2pError,
            0,
            "our Hello: message is not RLP of the expected shape",
            lambda: devp2p.session(b"\x80", []),
            id="devp2p-hello",
        ),
        # A request is a list, not an empty string.
        pytest.param(
            SnapError,
            2,
            "message data is not RLP of the expected shape",
            lambda: snap.codes_answer(1, b"\x80", b"\x80"),
            id="snap-codes",
        ),
        # A start is empty or 32 bytes.
        pytest.param(
            SnapError,
            0,
            "bad start size: 1, expected 0 or 32",
            lambda: snap.verify_storage_ranges([], b"\x01", [], []),
            id="snap-storage-start",
        ),
        # The one node of the proof does not hash to the root.
        pytest.param(
            TrieError,
            102,
            (
                "proof does not verify: EthLib.Execution.Trie.ProofError.hashMismatch (expected := "
                "0x0000000000000000000000000000000000000000000000000000000000000000) (actual := "
                "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421)"
            ),
            lambda: trie.verify_proof(bytes(32), b"", [b"\x80"]),
            id="trie-proof",
        ),
        # A root is 32 bytes.
        pytest.param(
            TrieError,
            0,
            "bad root size: 31, expected 32",
            lambda: trie.verify_proof(bytes(31), b"", []),
            id="trie-root-size",
        ),
        # Withdrawals start at Shapella.
        pytest.param(
            StateError,
            0,
            "the fork is before Shapella",
            lambda: state.withdrawals_root(
                "frontier", rlp.encode([]), rlp.encode([HEADER, [], []])
            ),
            id="state-withdrawals-fork",
        ),
        # The block is an RLP list, not an empty string.
        pytest.param(
            StateError,
            0,
            "block rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            lambda: state.rewards_root([("frontier", 0)], rlp.encode([]), b"\x80"),
            id="state-rewards",
        ),
        # No fork has the name nofork.
        pytest.param(
            StateError,
            0,
            "no fork named nofork",
            lambda: state.rewards_root([("nofork", 0)], rlp.encode([]), b"\x80"),
            id="state-rewards-forks",
        ),
        # The chain activates no fork, so the block is at no active fork.
        pytest.param(
            BlockError,
            225,
            "block invalid: wrongFork (active := none) (fork := EthLib.Base.Fork.frontier)",
            lambda: blocks.state_transition(
                CONFIG, rlp.encode([]), [], "frontier", rlp.encode([HEADER, [], []])
            ),
            id="block-transition",
        ),
        # A block is an RLP list, not an empty string.
        pytest.param(
            BlockError,
            213,
            "block rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            lambda: blocks.state_transition(CONFIG, rlp.encode([]), [], "frontier", b"\x80"),
            id="block-transition-decode",
        ),
        # A state is an RLP list, not an empty string.
        pytest.param(
            BlockError,
            0,
            "state is not an RLP list",
            lambda: blocks.state_transition(CONFIG, b"\x80", [], "frontier", b"\x80"),
            id="block-transition-state",
        ),
        # 0x80 is the type of no transaction.
        pytest.param(
            BlockError,
            0,
            (
                "transaction rejected: "
                "EthLib.Execution.Transactions.TransactionError.unsupportedType (type := 128)"
            ),
            lambda: blocks.transactions_root("frontier", rlp.encode([HEADER, [b"\x80"], []])),
            id="block-transactions-root",
        ),
        # The deposit log has no data.
        pytest.param(
            BlockError,
            301,
            "deposit log rejected: EthLib.Execution.Blocks.DepositError.wrongLength 0",
            lambda: blocks.deposit_requests(
                bytes(20), rlp.encode([[bytes(20), [DEPOSIT_TOPIC], b""]])
            ),
            id="block-deposit-layout",
        ),
        # The same account comes twice.
        pytest.param(
            BlockError,
            401,
            (
                "block access list invalid: "
                "EthLib.Execution.Blocks.BlockAccessList.Error.accountsNotAscending\n  #v[0, 0, 0, "
                "0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]"
            ),
            lambda: blocks.check_block_access_list(
                rlp.encode([[bytes(20), [], [], [], [], []]] * 2), 0
            ),
            id="block-access-list-invalid",
        ),
        # A header of zeros has no valid proof of work.
        pytest.param(
            BlockError,
            222,
            (
                "proof of work invalid: EthLib.Execution.Blocks.PowError.wrongMixDigest (expected "
                ":= 0xc0ff6c7b688611cd37aa7ec907844330d1d891208e8467825dfd44c4f6d02e37) (actual := "
                "0x0000000000000000000000000000000000000000000000000000000000000000)"
            ),
            lambda: proof_of_work.check_proof_of_work("frontier", rlp.encode(HEADER)),
            id="pow-check",
        ),
        # The ommers do not hash to the ommers hash of the header.
        pytest.param(
            BlockError,
            231,
            (
                "ommers invalid: EthLib.Execution.Blocks.OmmerError.wrongOmmersHash (expected := "
                "0x0000000000000000000000000000000000000000000000000000000000000000) (actual := "
                "0x96dcb37b83bd1f5e730a17abd3278a73e48b183f77a7c99b2a04d7d9046297d5)"
            ),
            lambda: proof_of_work.validate_ommers(
                [("frontier", 0)], [], rlp.encode([HEADER, [], [HEADER]])
            ),
            id="pow-ommers",
        ),
        # The recent blocks are an RLP list, not an empty string.
        pytest.param(
            BlockError,
            10,
            "block rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            lambda: proof_of_work.validate_ommers([("frontier", 0)], [b"\x80"], b"\x80"),
            id="pow-ommers-recent",
        ),
        # A signature with r and s zero names no sender.
        pytest.param(
            TransactionError,
            5,
            "invalidSignature",
            lambda: transactions.recover_sender(
                "frontier", rlp.encode([b"", b"", b"\x01", b"", b"", b"", b"\x1b", b"", b""])
            ),
            id="tx-recover-sender",
        ),
        # A gas limit of 1 is below the intrinsic gas.
        pytest.param(
            TransactionError,
            6,
            "insufficientGas (needed := 21000) (gas := 1)",
            lambda: transactions.check_in_block(
                "frontier",
                1,
                LOW_GAS_TX,
                rlp.encode([]),
                gas_limit=0,
                gas_used=0,
                blob_gas_used=0,
                base_fee=0,
                excess_blob_gas=0,
            ),
            id="tx-check-in-block",
        ),
        # A state is an RLP list, not an empty string.
        pytest.param(
            TransactionError,
            2,
            "state is not an RLP list",
            lambda: transactions.check_in_block(
                "frontier",
                1,
                LOW_GAS_TX,
                b"\x80",
                gas_limit=0,
                gas_used=0,
                blob_gas_used=0,
                base_fee=0,
                excess_blob_gas=0,
            ),
            id="tx-check-in-block-state",
        ),
        # A gas limit of 1 is below the intrinsic gas.
        pytest.param(
            TransactionError,
            6,
            "insufficientGas (needed := 21000) (gas := 1)",
            lambda: transactions.admit_to_pool("frontier", 1, LOW_GAS_TX, rlp.encode([])),
            id="tx-admit",
        ),
        # The block is a list of ten items, not an empty string.
        pytest.param(
            TransactionError,
            0,
            "block environment rejected: bytesAsList",
            lambda: transactions.run("frontier", 1, LOW_GAS_TX, rlp.encode([]), b"\x80"),
            id="tx-run-env",
        ),
        # A gas limit of 1 is below the intrinsic gas.
        pytest.param(
            TransactionError,
            6,
            "insufficientGas (needed := 21000) (gas := 1)",
            lambda: transactions.run(
                "frontier",
                1,
                LOW_GAS_TX,
                rlp.encode([]),
                rlp.encode([bytes(20), b"", b"", b"", b"", b"", bytes(32), b"", [], b""]),
            ),
            id="tx-run-inclusion",
        ),
        # The block is a list of ten items, not an empty string.
        pytest.param(
            TransactionError,
            0,
            "block environment rejected: bytesAsList",
            lambda: transactions.trace_eip3155("frontier", 1, LOW_GAS_TX, rlp.encode([]), b"\x80"),
            id="tx-trace-env",
        ),
        # A gas limit of 1 is below the intrinsic gas.
        pytest.param(
            TransactionError,
            6,
            "insufficientGas (needed := 21000) (gas := 1)",
            lambda: transactions.settle("frontier", LOW_GAS_TX, 1, 0, 0),
            id="tx-settle",
        ),
        # A blob transaction in network form has five items, not four.
        pytest.param(
            TransactionError,
            3,
            "decoding: wrongFieldCount 5 4",
            lambda: transactions.network_check("fusaka", b"\x03" + rlp.encode([[], [], [], []])),
            id="tx-network-wrapper",
        ),
        # 0x80 is the type of no transaction.
        pytest.param(
            FeesError,
            0,
            (
                "transaction rejected: "
                "EthLib.Execution.Transactions.TransactionError.unsupportedType (type := 128)"
            ),
            lambda: fees.calculate_data_fee("dencun", 0, b"\x80"),
            id="fees-blob-tx",
        ),
        # A salt is 32 bytes.
        pytest.param(
            EvmError,
            104,
            "the salt must be 32 bytes, not 31",
            lambda: evm.create2_address(bytes(20), bytes(31), b""),
            id="evm-salt",
        ),
        # ADD has no immediate depth.
        pytest.param(
            EvmError,
            0,
            "byte 0 encodes no depth of opcode 1",
            lambda: evm.immediate_depths(0x01, 0),
            id="evm-immediate",
        ),
        # No schema has the name nope.
        pytest.param(
            RpcError,
            0,
            "unknown schema: nope",
            lambda: rpc.read_param("nope", 0),  # ty: ignore[no-matching-overload]
            id="rpc-unknown-schema",
        ),
        # A block access list is a JSON array.
        pytest.param(
            RpcError,
            32602,
            "block access list: not an array",
            lambda: rpc.encode_block_access_list(0),
            id="rpc-bal",
        ),
        # The state overrides are a JSON object.
        pytest.param(
            RpcError,
            32602,
            "stateOverrides: not an object",
            lambda: rpc.apply_overrides(rlp.encode([]), 0),
            id="rpc-overrides-schema",
        ),
        # An era1 file ends with a trailer.
        pytest.param(
            Era1Error,
            2,
            "era1 file rejected: EthLib.Execution.History.Era1Error.noTrailer",
            lambda: history.decode_era1(b"\x65\x32" + bytes(6)),
            id="era1-short",
        ),
        # A chain ID is below 2^64.
        pytest.param(
            EngineError,
            0,
            "config: chainId is not below 2^64",
            lambda: engine.new_payload({"chainId": 2**64}, "engine_newPayloadV1", []),
            id="engine-config",
        ),
        # engine_newPayloadV1 takes one parameter, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: not 1 values"',
            lambda: engine.new_payload(
                {"chainId": 1, "depositContractAddress": "0x" + "00" * 20, "activations": []},
                "engine_newPayloadV1",
                [],
            ),
            id="engine-params",
        ),
        # A JWT secret is 32 bytes.
        pytest.param(
            JwtError,
            1,
            "EthLib.Engine.Jwt.JwtError.secretLength 31",
            lambda: engine.jwt_build(bytes(31), 0),
            id="jwt",
        ),
    ],
)
def test_code_and_message(
    error: type[EthLibError], code: int, message: str, call: Callable[[], object]
) -> None:
    with raises(error, message) as info:
        call()
    assert type(info.value) is error
    assert info.value.code == code
