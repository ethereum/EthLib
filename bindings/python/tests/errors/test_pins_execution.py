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
    ProposerError,
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
# A chain configuration that activates every fork up to Paris at block 0.
PARIS_CONFIG = {
    "chainId": 1,
    "depositContractAddress": "0x" + "00" * 20,
    "activations": [
        [fork, "block", 0]
        for fork in [
            "frontier",
            "homestead",
            "tangerineWhistle",
            "spuriousDragon",
            "byzantium",
            "constantinople",
            "petersburg",
            "istanbul",
            "berlin",
            "london",
            "paris",
        ]
    ],
}
# The root of an empty trie, and the hash of an empty list of ommers.
EMPTY_ROOT = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
EMPTY_OMMERS = bytes.fromhex("1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")
# A Paris genesis header with an empty body, a gas limit of 30000000 and a base fee of 1 gwei.
PARIS_GENESIS = rlp.encode(
    [
        bytes(32),
        EMPTY_OMMERS,
        bytes(20),
        EMPTY_ROOT,
        EMPTY_ROOT,
        EMPTY_ROOT,
        bytes(256),
        b"",
        b"",
        (30_000_000).to_bytes(4, "big"),
        b"",
        b"",
        b"",
        bytes(32),
        bytes(8),
        (10**9).to_bytes(4, "big"),
    ]
)
# The payload attributes of version 1, at time 0.
ATTRIBUTES = {
    "timestamp": "0x0",
    "prevRandao": "0x" + "00" * 32,
    "suggestedFeeRecipient": "0x" + "00" * 20,
}
# An answer of eth_getProof for an empty account, with no proof node and no slot.
ACCOUNT_ANSWER = {
    "address": "0x" + "00" * 20,
    "accountProof": [],
    "balance": "0x0",
    "codeHash": "0x" + "00" * 32,
    "nonce": "0x0",
    "storageHash": "0x" + "00" * 32,
    "storageProof": [],
}


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
        # An activation is a list of a fork, a kind and a number, not a number.
        pytest.param(
            ChainError,
            0,
            "an activation is not [fork, kind, n]",
            lambda: chain.active_fork({**CONFIG, "activations": [5]}, 0, 0),
            id="chain-activation-shape",
        ),
        # An activation is by block or by time, not by slot.
        pytest.param(
            ChainError,
            0,
            "no activation kind slot",
            lambda: chain.active_fork({**CONFIG, "activations": [["frontier", "slot", 0]]}, 0, 0),
            id="chain-activation-kind",
        ),
        # The number of an activation is a number, not text.
        pytest.param(
            ChainError,
            0,
            "an activation has no number",
            lambda: chain.active_fork(
                {**CONFIG, "activations": [["frontier", "block", "x"]]}, 0, 0
            ),
            id="chain-activation-number",
        ),
        # An activation at block 2^64 does not fit in 64 bits.
        pytest.param(
            ChainError,
            0,
            "an activation is not below 2^64",
            lambda: chain.active_fork(
                {**CONFIG, "activations": [["frontier", "block", 2**64]]}, 0, 0
            ),
            id="chain-activation-bound",
        ),
        # A blob schedule is a list, not a number.
        pytest.param(
            ChainError,
            0,
            "a blob schedule is not [fork?, kind, n, target, max, fraction]",
            lambda: chain.active_fork({**CONFIG, "blobSchedules": [5]}, 0, 0),
            id="chain-schedule-shape",
        ),
        # The target of a blob schedule is a number, not text.
        pytest.param(
            ChainError,
            0,
            "a blob schedule has no target",
            lambda: chain.active_fork({**CONFIG, "blobSchedules": [["time", 0, "x", 6, 1]]}, 0, 0),
            id="chain-schedule-target",
        ),
        # The maximum of a blob schedule is a number, not text.
        pytest.param(
            ChainError,
            0,
            "a blob schedule has no maximum",
            lambda: chain.active_fork({**CONFIG, "blobSchedules": [["time", 0, 3, "x", 1]]}, 0, 0),
            id="chain-schedule-maximum",
        ),
        # The update fraction of a blob schedule is a number, not text.
        pytest.param(
            ChainError,
            0,
            "a blob schedule has no fraction",
            lambda: chain.active_fork({**CONFIG, "blobSchedules": [["time", 0, 3, 6, "x"]]}, 0, 0),
            id="chain-schedule-fraction",
        ),
        # A target of 7 is above a maximum of 6.
        pytest.param(
            ChainError,
            0,
            (
                "a blob schedule needs target ≤ max, 0 < max, "
                "0 < update fraction and a blob gas of max below 2^64"
            ),
            lambda: chain.active_fork({**CONFIG, "blobSchedules": [["time", 0, 7, 6, 1]]}, 0, 0),
            id="chain-schedule-bounds",
        ),
        # The blob schedules are a list, not a number.
        pytest.param(
            ChainError,
            0,
            "config: blobSchedules is not an array",
            lambda: chain.active_fork({**CONFIG, "blobSchedules": 5}, 0, 0),
            id="chain-schedules-type",
        ),
        # The configuration names no deposit contract.
        pytest.param(
            ChainError,
            0,
            "config: no depositContractAddress",
            lambda: chain.active_fork({"chainId": 1, "activations": []}, 0, 0),
            id="chain-deposit-missing",
        ),
        # The deposit contract is an address, not a number.
        pytest.param(
            ChainError,
            0,
            "config: depositContractAddress is not text",
            lambda: chain.active_fork({**CONFIG, "depositContractAddress": 5}, 0, 0),
            id="chain-deposit-text",
        ),
        # The address 00 has no 0x in front.
        pytest.param(
            ChainError,
            0,
            "config: depositContractAddress does not start with 0x",
            lambda: chain.active_fork({**CONFIG, "depositContractAddress": "00"}, 0, 0),
            id="chain-deposit-prefix",
        ),
        # The address 0x00 has 2 hex digits, not 40.
        pytest.param(
            ChainError,
            0,
            "config: depositContractAddress is not forty hex digits",
            lambda: chain.active_fork({**CONFIG, "depositContractAddress": "0x00"}, 0, 0),
            id="chain-deposit-digits",
        ),
        # The digit z is not hex.
        pytest.param(
            ChainError,
            0,
            "config: depositContractAddress is not hex",
            lambda: chain.active_fork({**CONFIG, "depositContractAddress": "0x" + "zz" * 20}, 0, 0),
            id="chain-deposit-hex",
        ),
        # A chain ID of 2^64 does not fit in 64 bits.
        pytest.param(
            ChainError,
            0,
            "config: chainId is not below 2^64",
            lambda: chain.active_fork({**CONFIG, "chainId": 2**64}, 0, 0),
            id="chain-id-bound",
        ),
        # The configuration has no activations.
        pytest.param(
            ChainError,
            0,
            "config: no activations",
            lambda: chain.active_fork({"chainId": 1, "depositContractAddress": bytes(20)}, 0, 0),
            id="chain-activations-missing",
        ),
        # A configuration file is an object, not a number.
        pytest.param(
            ChainError,
            1,
            "execution config: EthLib.Base.ExecutionConfig.ConfigError.notObject",
            lambda: chain.execution_blob_schedule(CONFIG, 5, 0, 0),  # ty: ignore[invalid-argument-type]
            id="chain-execution-config",
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
        # No Engine API error has the code 1.
        pytest.param(
            EngineError,
            0,
            "no Engine API error has the code 1",
            lambda: engine.error_object(1),
            id="engine-error-object",
        ),
        # A payload status has a status field.
        pytest.param(
            EngineError,
            32602,
            (
                "engine error: EthLib.Engine.EngineError.invalidParams "
                '"payloadStatus: no field status"'
            ),
            lambda: engine.read_payload_status({}),
            id="engine-read-status",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.new_payload(CONFIG, "engine_nope", []),
            id="engine-new-payload-method",
        ),
        # A terminal total difficulty is below 2^256.
        pytest.param(
            EngineError,
            0,
            (
                "config: a terminal total difficulty of "
                "115792089237316195423570985008687907853269984665640564039457584007913129639936, "
                "not below 2^256"
            ),
            lambda: engine.new_payload_on_chain(
                CONFIG,
                rlp.encode([]),
                [],
                "engine_newPayloadV1",
                [],
                terminal_total_difficulty=2**256,
                total_difficulty=0,
            ),
            id="engine-on-chain-ttd",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.new_payload_on_chain(
                CONFIG,
                rlp.encode([]),
                [],
                "engine_nope",
                [],
                terminal_total_difficulty=0,
                total_difficulty=0,
            ),
            id="engine-on-chain-method",
        ),
        # engine_newPayloadV1 takes one parameter, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: not 1 values"',
            lambda: engine.new_payload_on_chain(
                CONFIG,
                rlp.encode([]),
                [],
                "engine_newPayloadV1",
                [],
                terminal_total_difficulty=0,
                total_difficulty=0,
            ),
            id="engine-on-chain-params",
        ),
        # No forkchoice update has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.build_payload(
                CONFIG,
                rlp.encode([]),
                [],
                "engine_nope",
                {},
                fee_recipient=bytes(20),
                extra_data=b"",
                target_gas_limit=0,
                transactions=[],
            ),
            id="engine-build-method",
        ),
        # Payload attributes have a timestamp.
        pytest.param(
            EngineError,
            38003,
            "engine error: EthLib.Engine.EngineError.invalidPayloadAttributes",
            lambda: engine.build_payload(
                CONFIG,
                rlp.encode([]),
                [],
                "engine_forkchoiceUpdatedV1",
                {},
                fee_recipient=bytes(20),
                extra_data=b"",
                target_gas_limit=0,
                transactions=[],
            ),
            id="engine-build-attributes",
        ),
        # A chain without a recent block has no parent to build on.
        pytest.param(
            EngineError,
            226,
            "block invalid: noParent",
            lambda: engine.build_payload(
                CONFIG,
                rlp.encode([]),
                [],
                "engine_forkchoiceUpdatedV1",
                ATTRIBUTES,
                fee_recipient=bytes(20),
                extra_data=b"",
                target_gas_limit=0,
                transactions=[],
            ),
            id="engine-build-no-parent",
        ),
        # The chain activates no fork, so the attributes are at no fork.
        pytest.param(
            EngineError,
            38005,
            "engine error: EthLib.Engine.EngineError.unsupportedFork none",
            lambda: engine.build_payload(
                CONFIG,
                rlp.encode([]),
                [("frontier", rlp.encode(HEADER), [])],
                "engine_forkchoiceUpdatedV1",
                ATTRIBUTES,
                fee_recipient=bytes(20),
                extra_data=b"",
                target_gas_limit=0,
                transactions=[b""],
            ),
            id="engine-build-fork",
        ),
        # A transaction is not empty.
        pytest.param(
            EngineError,
            401,
            (
                "401: transaction 0 does not decode: "
                "EthLib.Execution.Transactions.TransactionError.emptyTransaction"
            ),
            lambda: engine.build_payload(
                PARIS_CONFIG,
                rlp.encode([]),
                [("paris", PARIS_GENESIS, [])],
                "engine_forkchoiceUpdatedV1",
                ATTRIBUTES | {"timestamp": "0x1"},
                fee_recipient=bytes(20),
                extra_data=b"",
                target_gas_limit=30_000_000,
                transactions=[b""],
            ),
            id="engine-build-transaction",
        ),
        # A terminal total difficulty is below 2^256.
        pytest.param(
            EngineError,
            0,
            (
                "config: a terminal total difficulty of "
                "115792089237316195423570985008687907853269984665640564039457584007913129639936, "
                "not below 2^256"
            ),
            lambda: engine.forkchoice_updated(
                CONFIG, [], "engine_forkchoiceUpdatedV1", [], terminal_total_difficulty=2**256
            ),
            id="engine-fcu-ttd",
        ),
        # A block of the tree says whether it is valid.
        pytest.param(
            EngineError,
            0,
            "tree: no validity",
            lambda: engine.forkchoice_updated(
                CONFIG, [{}], "engine_forkchoiceUpdatedV1", [], terminal_total_difficulty=0
            ),
            id="engine-fcu-tree-validity",
        ),
        # A block of the tree has a block hash.
        pytest.param(
            EngineError,
            0,
            'tree: EthLib.Engine.EngineError.invalidParams "blockHash: not a string"',
            lambda: engine.forkchoice_updated(
                CONFIG,
                [{"valid": True}],
                "engine_forkchoiceUpdatedV1",
                [],
                terminal_total_difficulty=0,
            ),
            id="engine-fcu-tree-hash",
        ),
        # A block of the tree has a number.
        pytest.param(
            EngineError,
            0,
            'tree: EthLib.Engine.EngineError.invalidParams "number: not a string"',
            lambda: engine.forkchoice_updated(
                CONFIG,
                [{"valid": True, "blockHash": "0x" + "00" * 32, "parentHash": "0x" + "00" * 32}],
                "engine_forkchoiceUpdatedV1",
                [],
                terminal_total_difficulty=0,
            ),
            id="engine-fcu-tree-number",
        ),
        # A total difficulty is a hex quantity.
        pytest.param(
            EngineError,
            0,
            'tree: EthLib.Engine.EngineError.invalidParams "totalDifficulty: no 0x marker"',
            lambda: engine.forkchoice_updated(
                CONFIG,
                [
                    {
                        "valid": True,
                        "blockHash": "0x" + "00" * 32,
                        "parentHash": "0x" + "00" * 32,
                        "number": "0x0",
                        "timestamp": "0x0",
                        "totalDifficulty": "x",
                        "parentTotalDifficulty": "0x0",
                    }
                ],
                "engine_forkchoiceUpdatedV1",
                [],
                terminal_total_difficulty=0,
            ),
            id="engine-fcu-tree-total",
        ),
        # A block of the tree has both totals or neither.
        pytest.param(
            EngineError,
            0,
            "tree: one total difficulty without the other",
            lambda: engine.forkchoice_updated(
                CONFIG,
                [{"valid": True, "totalDifficulty": "0x0"}],
                "engine_forkchoiceUpdatedV1",
                [],
                terminal_total_difficulty=0,
            ),
            id="engine-fcu-tree-one-total",
        ),
        # A tree holds each block hash once.
        pytest.param(
            EngineError,
            0,
            "tree: two payloads with one block hash",
            lambda: engine.forkchoice_updated(
                CONFIG,
                [
                    {
                        "valid": True,
                        "blockHash": "0x" + "00" * 32,
                        "parentHash": "0x" + "00" * 32,
                        "number": "0x0",
                        "timestamp": "0x0",
                    }
                ]
                * 2,
                "engine_forkchoiceUpdatedV1",
                [],
                terminal_total_difficulty=0,
            ),
            id="engine-fcu-tree-twice",
        ),
        # A finalized block hash is 32 bytes.
        pytest.param(
            EngineError,
            0,
            'finalized: EthLib.Engine.EngineError.invalidParams "finalized: 1 bytes, not 32"',
            lambda: engine.forkchoice_updated(
                CONFIG, [], "engine_forkchoiceUpdatedV1", [], "0x00", terminal_total_difficulty=0
            ),
            id="engine-fcu-finalized",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.forkchoice_updated(
                CONFIG, [], "engine_nope", [], terminal_total_difficulty=0
            ),
            id="engine-fcu-method",
        ),
        # engine_forkchoiceUpdatedV1 takes two parameters, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 0, expected 2"',
            lambda: engine.forkchoice_updated(
                CONFIG, [], "engine_forkchoiceUpdatedV1", [], terminal_total_difficulty=0
            ),
            id="engine-fcu-params",
        ),
        # A forkchoice response has a payload status.
        pytest.param(
            EngineError,
            32602,
            (
                "engine error: EthLib.Engine.EngineError.invalidParams "
                '"forkchoiceUpdatedResponse: no field payloadStatus"'
            ),
            lambda: engine.read_forkchoice_response({}),
            id="engine-read-fcu",
        ),
        # A pool entry holds 128 cells, not one.
        pytest.param(
            EngineError,
            0,
            "pool: 1 cells, not 128",
            lambda: engine.get_blobs(
                [(bytes(32), None, None, [None])], "dencun", "engine_getBlobsV1", []
            ),
            id="engine-blobs-cells",
        ),
        # A pool holds each versioned hash once.
        pytest.param(
            EngineError,
            0,
            "pool: two entries with one versioned hash",
            lambda: engine.get_blobs(
                [(bytes(32), None, None, None)] * 2, "dencun", "engine_getBlobsV1", []
            ),
            id="engine-blobs-twice",
        ),
        # A pool takes requests of at least 128 hashes.
        pytest.param(
            EngineError,
            0,
            "pool: a limit of 1, below 128",
            lambda: engine.get_blobs([], "dencun", "engine_getBlobsV1", [], max_request=1),
            id="engine-blobs-limit",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.get_blobs([], "dencun", "engine_nope", []),
            id="engine-blobs-method",
        ),
        # engine_getBlobsV1 takes one parameter, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 0, expected 1"',
            lambda: engine.get_blobs([], "dencun", "engine_getBlobsV1", []),
            id="engine-blobs-params",
        ),
        # A result of engine_getBlobsV1 is an array.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "result: not an array"',
            lambda: engine.read_get_blobs_result("engine_getBlobsV1", 0),
            id="engine-read-blobs",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.read_get_blobs_result("engine_nope", 0),
            id="engine-read-blobs-method",
        ),
        # A Frontier body has no withdrawals.
        pytest.param(
            EngineError,
            0,
            "store: withdrawals: present before its fork",
            lambda: engine.get_payload_bodies(
                [(bytes(32), 0, "frontier", [], [], None)], 0, "engine_getPayloadBodiesByHashV1", []
            ),
            id="engine-bodies-field",
        ),
        # A store holds each block hash once.
        pytest.param(
            EngineError,
            0,
            "store: two entries with one block hash",
            lambda: engine.get_payload_bodies(
                [(bytes(32), None, "frontier", [], None, None)] * 2,
                0,
                "engine_getPayloadBodiesByHashV1",
                [],
            ),
            id="engine-bodies-twice",
        ),
        # A store holds one canonical block at each number.
        pytest.param(
            EngineError,
            0,
            "store: two canonical entries at a number",
            lambda: engine.get_payload_bodies(
                [
                    (bytes(32), 0, "frontier", [], None, None),
                    (b"\x01" * 32, 0, "frontier", [], None, None),
                ],
                0,
                "engine_getPayloadBodiesByHashV1",
                [],
            ),
            id="engine-bodies-number",
        ),
        # A store holds the latest known block.
        pytest.param(
            EngineError,
            0,
            "store: no canonical entry at the latest known block 0",
            lambda: engine.get_payload_bodies([], 0, "engine_getPayloadBodiesByHashV1", []),
            id="engine-bodies-latest",
        ),
        # A store takes requests of at least 32 bodies.
        pytest.param(
            EngineError,
            0,
            "store: a limit of 1, below 32",
            lambda: engine.get_payload_bodies(
                [(bytes(32), 0, "frontier", [], None, None)],
                0,
                "engine_getPayloadBodiesByHashV1",
                [],
                max_request=1,
            ),
            id="engine-bodies-limit",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.get_payload_bodies(
                [(bytes(32), 0, "frontier", [], None, None)], 0, "engine_nope", []
            ),
            id="engine-bodies-method",
        ),
        # engine_getPayloadBodiesByHashV1 takes one parameter, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 0, expected 1"',
            lambda: engine.get_payload_bodies(
                [(bytes(32), 0, "frontier", [], None, None)],
                0,
                "engine_getPayloadBodiesByHashV1",
                [],
            ),
            id="engine-bodies-params",
        ),
        # engine_getPayloadBodiesByRangeV2 takes two parameters, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 0, expected 2"',
            lambda: engine.get_payload_bodies(
                [(bytes(32), 0, "frontier", [], None, None)],
                0,
                "engine_getPayloadBodiesByRangeV2",
                [],
            ),
            id="engine-bodies-range-params",
        ),
        # A result of engine_getPayloadBodiesByHashV1 is an array.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "result: not an array"',
            lambda: engine.read_payload_bodies_result("engine_getPayloadBodiesByHashV1", 0),
            id="engine-read-bodies",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.read_payload_bodies_result("engine_nope", 0),
            id="engine-read-bodies-method",
        ),
        # A stored block is an RLP list, not an empty string.
        pytest.param(
            EngineError,
            0,
            "store: block rejected: EthLib.Serialization.Rlp.RlpError.bytesAsList",
            lambda: engine.get_payload(
                CONFIG,
                [(bytes(8), "frontier", b"\x80", b"", [], 0, [], False, None)],
                "engine_getPayloadV1",
                [],
            ),
            id="engine-get-payload-block",
        ),
        # A transaction of a stored block is not empty.
        pytest.param(
            EngineError,
            0,
            (
                "store: transaction rejected: "
                "EthLib.Execution.Transactions.TransactionError.emptyTransaction"
            ),
            lambda: engine.get_payload(
                CONFIG,
                [
                    (
                        bytes(8),
                        "frontier",
                        rlp.encode([HEADER, [b""], []]),
                        b"",
                        [],
                        0,
                        [],
                        False,
                        None,
                    )
                ],
                "engine_getPayloadV1",
                [],
            ),
            id="engine-get-payload-transaction",
        ),
        # The accounts after a stored block are an RLP list.
        pytest.param(
            EngineError,
            0,
            "store: state is not an RLP list",
            lambda: engine.get_payload(
                CONFIG,
                [
                    (
                        bytes(8),
                        "frontier",
                        rlp.encode([HEADER, [], []]),
                        b"\x80",
                        [],
                        0,
                        [],
                        False,
                        None,
                    )
                ],
                "engine_getPayloadV1",
                [],
            ),
            id="engine-get-payload-state",
        ),
        # A Frontier block has no block access list.
        pytest.param(
            EngineError,
            0,
            "store: block access list: present before its fork",
            lambda: engine.get_payload(
                CONFIG,
                [
                    (
                        bytes(8),
                        "frontier",
                        rlp.encode([HEADER, [], []]),
                        rlp.encode([]),
                        [],
                        0,
                        [],
                        False,
                        b"",
                    )
                ],
                "engine_getPayloadV1",
                [],
            ),
            id="engine-get-payload-access-list",
        ),
        # A store holds each payload ID once.
        pytest.param(
            EngineError,
            0,
            "store: two entries with one payload ID",
            lambda: engine.get_payload(
                CONFIG,
                [
                    (
                        bytes(8),
                        "frontier",
                        rlp.encode([HEADER, [], []]),
                        rlp.encode([]),
                        [],
                        0,
                        [],
                        False,
                        None,
                    )
                ]
                * 2,
                "engine_getPayloadV1",
                [],
            ),
            id="engine-get-payload-twice",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.get_payload(CONFIG, [], "engine_nope", []),
            id="engine-get-payload-method",
        ),
        # engine_getPayloadV1 takes one parameter, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 0, expected 1"',
            lambda: engine.get_payload(CONFIG, [], "engine_getPayloadV1", []),
            id="engine-get-payload-params",
        ),
        # The store holds no payload with the ID.
        pytest.param(
            EngineError,
            38001,
            "engine error: EthLib.Engine.EngineError.unknownPayload 0x0000000000000000",
            lambda: engine.get_payload(CONFIG, [], "engine_getPayloadV1", ["0x" + "00" * 8]),
            id="engine-get-payload-unknown",
        ),
        # The chain runs Paris at block 0, not Frontier.
        pytest.param(
            EngineError,
            0,
            "store: the fork frontier is not the configured fork at the block, paris",
            lambda: engine.get_payload(
                PARIS_CONFIG,
                [
                    (
                        bytes(8),
                        "frontier",
                        rlp.encode([HEADER, [], []]),
                        rlp.encode([]),
                        [],
                        0,
                        [],
                        False,
                        None,
                    )
                ],
                "engine_getPayloadV1",
                ["0x" + "00" * 8],
            ),
            id="engine-get-payload-wrong-fork",
        ),
        # A block value is below 2^256.
        pytest.param(
            EngineError,
            0,
            (
                "store: block value "
                "115792089237316195423570985008687907853269984665640564039457584007913129639936 "
                "is 2^256 or more"
            ),
            lambda: engine.get_payload(
                PARIS_CONFIG,
                [
                    (
                        bytes(8),
                        "paris",
                        rlp.encode([rlp.decode(PARIS_GENESIS), [], []]),
                        rlp.encode([]),
                        [],
                        2**256,
                        [],
                        False,
                        None,
                    )
                ],
                "engine_getPayloadV1",
                ["0x" + "00" * 8],
            ),
            id="engine-get-payload-value",
        ),
        # A Paris block has no execution requests.
        pytest.param(
            EngineError,
            0,
            "store: execution requests out of order, too short or before Pectra",
            lambda: engine.get_payload(
                PARIS_CONFIG,
                [
                    (
                        bytes(8),
                        "paris",
                        rlp.encode([rlp.decode(PARIS_GENESIS), [], []]),
                        rlp.encode([]),
                        [b""],
                        0,
                        [],
                        False,
                        None,
                    )
                ],
                "engine_getPayloadV1",
                ["0x" + "00" * 8],
            ),
            id="engine-get-payload-requests",
        ),
        # A payload has the fields of a version.
        pytest.param(
            EngineError,
            32602,
            (
                "engine error: EthLib.Engine.EngineError.invalidParams "
                '"payload: the fields of no version"'
            ),
            lambda: engine.read_get_payload_result("engine_getPayloadV1", "paris", {}),
            id="engine-read-get-payload",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.read_get_payload_result("engine_nope", "paris", {}),
            id="engine-read-get-payload-method",
        ),
        # Only engine_exchangeCapabilities is accepted.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.exchange_capabilities("engine_nope", []),
            id="engine-capabilities-method",
        ),
        # engine_exchangeCapabilities takes one parameter, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 0, expected 1"',
            lambda: engine.exchange_capabilities("engine_exchangeCapabilities", []),
            id="engine-capabilities-params",
        ),
        # A client code is two letters.
        pytest.param(
            EngineError,
            0,
            "own: a code abc, not two letters",
            lambda: engine.get_client_version(
                "abc", "n", "v", bytes(4), "engine_getClientVersionV1", []
            ),
            id="engine-client-code",
        ),
        # engine_getClientVersionV1 takes one parameter, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 0, expected 1"',
            lambda: engine.get_client_version(
                "EL", "n", "v", bytes(4), "engine_getClientVersionV1", []
            ),
            id="engine-client-params",
        ),
        # Only engine_getInclusionListV1 is accepted.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.get_inclusion_list([], "engine_nope", []),
            id="engine-inclusion-method",
        ),
        # engine_getInclusionListV1 takes no parameter, not two.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 2, expected 0"',
            lambda: engine.get_inclusion_list([], "engine_getInclusionListV1", [1, 2]),
            id="engine-inclusion-params",
        ),
        # A terminal total difficulty is below 2^256.
        pytest.param(
            EngineError,
            0,
            (
                "config: a total difficulty of "
                "115792089237316195423570985008687907853269984665640564039457584007913129639936, "
                "not below 2^256"
            ),
            lambda: engine.exchange_transition_configuration(
                2**256, bytes(32), 0, "engine_exchangeTransitionConfigurationV1", []
            ),
            id="engine-transition-difficulty",
        ),
        # A terminal block number is below 2^64.
        pytest.param(
            EngineError,
            0,
            "config: a block number of 18446744073709551616, not below 2^64",
            lambda: engine.exchange_transition_configuration(
                0, bytes(32), 2**64, "engine_exchangeTransitionConfigurationV1", []
            ),
            id="engine-transition-number",
        ),
        # Only engine_exchangeTransitionConfigurationV1 is accepted.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.exchange_transition_configuration(0, bytes(32), 0, "engine_nope", []),
            id="engine-transition-method",
        ),
        # engine_exchangeTransitionConfigurationV1 takes one parameter, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 0, expected 1"',
            lambda: engine.exchange_transition_configuration(
                0, bytes(32), 0, "engine_exchangeTransitionConfigurationV1", []
            ),
            id="engine-transition-params",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.rewrite_params("engine_nope", []),
            id="engine-rewrite-method",
        ),
        # engine_newPayloadV1 takes one parameter, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: not 1 values"',
            lambda: engine.rewrite_params("engine_newPayloadV1", []),
            id="engine-rewrite-params",
        ),
        # engine_getPayloadBodiesByRangeV1 takes two parameters, not none.
        pytest.param(
            EngineError,
            32602,
            'engine error: EthLib.Engine.EngineError.invalidParams "params: got 0, expected 2"',
            lambda: engine.rewrite_params("engine_getPayloadBodiesByRangeV1", []),
            id="engine-rewrite-bodies",
        ),
        # A terminal total difficulty is below 2^256.
        pytest.param(
            EngineError,
            0,
            (
                "config: a terminal total difficulty of "
                "115792089237316195423570985008687907853269984665640564039457584007913129639936, "
                "not below 2^256"
            ),
            lambda: engine.run_node(
                CONFIG,
                rlp.encode([]),
                ("frontier", rlp.encode(HEADER), []),
                [],
                terminal_total_difficulty=2**256,
            ),
            id="engine-node-ttd",
        ),
        # A header of zeros does not commit to an empty body.
        pytest.param(
            EngineError,
            0,
            "anchor: no hash, a body that is not empty, or a total below the difficulty",
            lambda: engine.run_node(
                CONFIG, rlp.encode([]), ("frontier", rlp.encode(HEADER), []), []
            ),
            id="engine-node-anchor",
        ),
        # A request names its method.
        pytest.param(
            EngineError,
            0,
            "request: no method",
            lambda: engine.run_node(
                PARIS_CONFIG, rlp.encode([]), ("paris", PARIS_GENESIS, []), [{}]
            ),
            id="engine-node-request",
        ),
        # No Engine API method has the name engine_nope.
        pytest.param(
            EngineError,
            0,
            "no method engine_nope",
            lambda: engine.run_node(
                PARIS_CONFIG,
                rlp.encode([]),
                ("paris", PARIS_GENESIS, []),
                [{"method": "engine_nope"}],
            ),
            id="engine-node-method",
        ),
        # A state root is 32 bytes.
        pytest.param(
            TrieError,
            0,
            "bad root size: 31, expected 32",
            lambda: trie.verify_account_proof(bytes(31), ACCOUNT_ANSWER),
            id="engine-proof-root",
        ),
        # An answer of eth_getProof has an address.
        pytest.param(
            TrieError,
            0,
            "answer: no field address",
            lambda: trie.verify_account_proof(bytes(32), {}),
            id="engine-proof-field",
        ),
        # An empty account proof shows no node of a root that is not empty.
        pytest.param(
            TrieError,
            501,
            (
                "answer does not hold: EthLib.Execution.State.AccountProofError.account "
                "(EthLib.Execution.Trie.ProofError.missingNode "
                "(hash := some 0x0101010101010101010101010101010101010101010101010101010101010101))"
            ),
            lambda: trie.verify_account_proof(b"\x01" * 32, ACCOUNT_ANSWER),
            id="engine-proof-fails",
        ),
        # No preset has the name nope.
        pytest.param(
            ProposerError,
            0,
            "no preset is named nope",
            lambda: engine.payload_attributes_event(
                "nope", "bellatrix", b"", bytes(32), bytes(32), bytes(20)
            ),
            id="engine-event-name",
        ),
        # A payload is prepared from Bellatrix on.
        pytest.param(
            ProposerError,
            0,
            "no payload preparation at phase0",
            lambda: engine.payload_attributes_event(
                "minimal", "phase0", b"", bytes(32), bytes(32), bytes(20)
            ),
            id="engine-event-fork",
        ),
        # A state is not empty.
        pytest.param(
            ProposerError,
            0,
            "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 10233 0",
            lambda: engine.payload_attributes_event(
                "minimal", "bellatrix", b"", bytes(32), bytes(32), bytes(20)
            ),
            id="engine-event-state",
        ),
        # A payload attributes event on a store starts at Gloas.
        pytest.param(
            ProposerError,
            0,
            "no payload attributes event on a store at phase0",
            lambda: engine.payload_attributes_event_gloas(
                "minimal", "phase0", b"", b"", [], bytes(32), 0, b"", bytes(32), bytes(20), 0
            ),
            id="engine-event-gloas-fork",
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
