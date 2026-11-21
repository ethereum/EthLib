"""The code and message of the errors that the execution and Engine exports pass to Python."""

from collections.abc import Callable

import pytest

from ethlib import chain, engine, precompiles, state
from ethlib.errors import (
    BlockError,
    ChainError,
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
from raising import raises

# An export turns the typed error of an operation into a code and a message.
# Each case pins one way of doing so, with the code and the message that Python sees.


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
