"""EIP-7910 configuration reports at fork boundaries and with chain-specific blob parameters."""

import json
import zlib
from collections.abc import Mapping
from dataclasses import replace
from functools import cache
from typing import Any

import pytest

from ethlib.execution import blocks, rpc
from ethlib.serialization import rlp
from raising import raises

from .chain import FIXTURES, ReplayChain, block_hash, replay_chain

# The fixture pin and licence are in fixtures/README.md.
# Other expectations apply EIP-7910 at EIPs commit 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445.
# The independent CRC-32 below applies EIP-2124 and EIP-6122 with Python's zlib.
REQUEST = '{"jsonrpc":"2.0","id":1,"method":"eth_config"}'
ZERO = bytes(32)


INTERNAL_ERROR = {"code": -32603, "message": "Internal error"}
NOT_SUPPORTED = {"code": -32004, "message": "Method not supported"}


def answer(chain: ReplayChain, request: str = REQUEST) -> dict[str, Any]:
    """The response to one configuration request."""
    (text,) = chain.serve([request])
    assert text is not None
    return json.loads(text)


def error(chain: ReplayChain, request: str = REQUEST) -> dict[str, Any]:
    """The error object of the response to one configuration request."""
    response = answer(chain, request)
    assert set(response) == {"jsonrpc", "id", "error"}
    return response["error"]


@cache
def genesis_file() -> dict[str, Any]:
    """The pinned genesis file of the test chain."""
    return json.loads((FIXTURES / "genesis.json").read_text())


def at_block(number: int) -> ReplayChain:
    """The pinned test chain through one head, without safe or finalized checkpoints."""
    chain = replay_chain()
    return replace(
        chain,
        blocks=chain.blocks[: number + 1],
        forkchoice=(block_hash(chain.blocks[number]), ZERO, ZERO),
    )


def fork_hash(chain: ReplayChain, timestamp: int) -> str:
    """The post-Merge FORK_HASH, computed independently from the pinned genesis configuration."""
    config = genesis_file()["config"]
    genesis_time = int(genesis_file()["timestamp"], 16)
    # Each positive block key counts once; mergeNetsplitBlock is the FORK_NEXT_VALUE of EIP-3675.
    heights = sorted(
        {value for name, value in config.items() if name.endswith("Block") and value > 0}
    )
    times = sorted(
        {
            value
            for name, value in config.items()
            if name.endswith("Time") and genesis_time < value <= timestamp
        }
    )
    data = block_hash(chain.blocks[0]) + b"".join(
        number.to_bytes(8, "big") for number in heights + times
    )
    return f"0x{zlib.crc32(data):08x}"


@pytest.mark.parametrize(
    ("head", "current", "next_time", "last_time", "count"),
    [
        (42, 420, 450, 570, 10),
        (44, 420, 450, 570, 10),
        (45, 450, 480, 570, 17),
        (47, 450, 480, 570, 17),
        (48, 480, 510, 570, 18),
        (51, 510, 540, 570, 18),
        (54, 540, 570, 570, 18),
        (57, 570, None, None, 18),
        (60, 570, None, None, 18),
    ],
)
def test_config_boundaries(
    head: int, current: int, next_time: int | None, last_time: int | None, count: int
) -> None:
    """Current, next and last follow activation times, including every BPO boundary."""
    chain = at_block(head)
    report = answer(chain)["result"]
    assert report["current"]["activationTime"] == current
    assert len(report["current"]["precompiles"]) == count
    for name, time in [("current", current), ("next", next_time), ("last", last_time)]:
        config = report[name]
        if time is None:
            assert config is None
            continue
        assert config["activationTime"] == time
        assert config["chainId"] == hex(genesis_file()["config"]["chainId"])
        assert config["forkId"] == fork_hash(chain, time)
        assert list(config) == [
            "activationTime",
            "blobSchedule",
            "chainId",
            "forkId",
            "precompiles",
            "systemContracts",
        ]
        assert list(config["blobSchedule"]) == ["baseFeeUpdateFraction", "max", "target"]
        assert list(config["precompiles"]) == sorted(config["precompiles"])
        assert list(config["systemContracts"]) == sorted(config["systemContracts"])
    if next_time == last_time:
        assert report["next"] == report["last"]


def test_bpo_configurations() -> None:
    """BPO reports keep Osaka's contracts and use each activation's own blob schedule."""
    osaka = answer(at_block(48))["result"]["current"]
    bpo1 = answer(at_block(51))["result"]["current"]
    bpo2 = answer(at_block(54))["result"]["current"]
    assert [c["blobSchedule"] for c in [osaka, bpo1, bpo2]] == [
        {"baseFeeUpdateFraction": 5007716, "max": 9, "target": 6},
        {"baseFeeUpdateFraction": 8346193, "max": 15, "target": 10},
        {"baseFeeUpdateFraction": 11684671, "max": 21, "target": 14},
    ]
    assert osaka["precompiles"] == bpo1["precompiles"] == bpo2["precompiles"]
    assert osaka["systemContracts"] == bpo1["systemContracts"] == bpo2["systemContracts"]
    assert osaka["precompiles"]["P256VERIFY"] == "0x" + "00" * 18 + "0100"


def test_chain_blob_schedule_at_fork() -> None:
    """A chain blob schedule at a fork time sets the blob parameters of that configuration."""
    chain = at_block(54)
    schedule = ["time", 570, 14, 22, 11684671]
    chain = replace(
        chain,
        config={**chain.config, "blobSchedules": [*chain.config["blobSchedules"], schedule]},
    )
    report = answer(chain)["result"]
    assert report["current"]["blobSchedule"]["max"] == 21
    assert report["next"]["activationTime"] == 570
    assert report["next"]["blobSchedule"]["max"] == 22
    assert report["next"]["forkId"] == fork_hash(chain, 570)


def test_chain_blob_schedule_without_fork() -> None:
    """EIP-7892 ties each blob schedule to a fork, so a schedule at no fork time is refused."""
    chain = at_block(54)
    schedule = ["time", 555, 14, 22, 11684671]
    chain = replace(
        chain,
        config={**chain.config, "blobSchedules": [*chain.config["blobSchedules"], schedule]},
    )
    assert error(chain) == {**INTERNAL_ERROR, "data": "eth_config: blob schedule without a fork"}


def synthetic_genesis(fork: str, state: bytes) -> bytes:
    """An empty genesis block of a fork at time 100."""
    return blocks.genesis_block(
        fork,
        state,
        timestamp=100,
        coinbase=bytes(20),
        difficulty=0,
        gas_limit=30000000,
        extra_data=b"",
        mix_hash=ZERO,
        nonce=bytes(8),
    )


def genesis_chain() -> ReplayChain:
    """A Cancun genesis at time 100, with two scheduled timestamp upgrades."""
    state = rlp.encode([])
    config = {
        "chainId": 1,
        "depositContractAddress": "0x" + "12" * 20,
        "activations": [["dencun", "block", 0], ["pectra", "time", 200], ["fusaka", "time", 300]],
    }
    first = (
        "dencun",
        synthetic_genesis("dencun", state),
    )
    return ReplayChain(
        config=config,
        state=state,
        blocks=(first,),
        forkchoice=(block_hash(first), ZERO, ZERO),
        network_id=1,
    )


def test_genesis_activation() -> None:
    """A fork active at a nonzero genesis timestamp reports activationTime zero."""
    chain = genesis_chain()
    report = answer(chain)["result"]
    assert report["current"]["activationTime"] == 0
    assert report["current"]["forkId"] == f"0x{zlib.crc32(block_hash(chain.blocks[0])):08x}"
    assert report["next"]["activationTime"] == 200
    assert report["last"]["activationTime"] == 300
    assert report["next"]["systemContracts"]["DEPOSIT_CONTRACT_ADDRESS"] == "0x" + "12" * 20


def pruned_chain() -> ReplayChain:
    """A retained empty block at number 100, with its state supplied as an input."""
    chain = genesis_chain()
    item = rlp.decode(chain.blocks[0][1])
    # The number is the ninth field of the header.
    item[0][8] = (100).to_bytes(1, "big")
    first = ("dencun", rlp.encode(item))
    return replace(chain, blocks=(first,), forkchoice=(block_hash(first), ZERO, ZERO))


def test_pruned_genesis_context() -> None:
    """A pruned view answers only with explicit genesis context, and then as from genesis."""
    original = genesis_chain()
    chain = pruned_chain()
    assert error(chain) == {**INTERNAL_ERROR, "data": "eth_config: genesis context unavailable"}
    context = {"genesisHash": "0x" + block_hash(original.blocks[0]).hex(), "genesisTime": 100}
    chain = replace(chain, config={**chain.config, **context})
    assert answer(chain)["result"] == answer(original)["result"]


def test_merge_fork_id_block() -> None:
    """The Merge fork-ID block enters the checksum, and the actual Paris activation does not."""
    chain = pruned_chain()
    genesis_hash = block_hash(genesis_chain().blocks[0])
    # A synthetic genesis context: time 0 makes Dencun at time 100 a fork, not a genesis rule.
    config = {
        **chain.config,
        "genesisHash": "0x" + genesis_hash.hex(),
        "genesisTime": 0,
        "activations": [["frontier", "block", 0], ["paris", "block", 80], ["dencun", "time", 100]],
    }
    current = answer(replace(chain, config=config))["result"]["current"]
    data = genesis_hash + (100).to_bytes(8, "big")
    assert current["forkId"] == f"0x{zlib.crc32(data):08x}"
    current = answer(replace(chain, config={**config, "mergeForkBlock": 90}))["result"]["current"]
    data = genesis_hash + (90).to_bytes(8, "big") + (100).to_bytes(8, "big")
    assert current["forkId"] == f"0x{zlib.crc32(data):08x}"


def test_fork_block_not_reached() -> None:
    """A head below a fork block cannot report the fork IDs of its activations."""
    chain = genesis_chain()
    chain = replace(chain, config={**chain.config, "mergeForkBlock": 50})
    assert error(chain) == {**INTERNAL_ERROR, "data": "eth_config: fork block not reached"}


def test_matching_genesis_context() -> None:
    """At block zero, a genesis context equal to the block is accepted and changes nothing."""
    chain = genesis_chain()
    context = {"genesisHash": "0x" + block_hash(chain.blocks[0]).hex(), "genesisTime": 100}
    given = replace(chain, config={**chain.config, **context})
    assert answer(given)["result"] == answer(chain)["result"]
    late = replace(chain, config={**chain.config, **context, "genesisTime": 101})
    with raises(rpc.RpcError, "config: genesis context disagrees with block zero") as caught:
        answer(late)
    assert caught.value.code == 0


def with_activations(chain: ReplayChain, *activations: list[object]) -> ReplayChain:
    """The chain with more fork activations appended to its configuration."""
    config = {**chain.config, "activations": [*chain.config["activations"], *activations]}
    return replace(chain, config=config)


def test_unsupported_future_fork() -> None:
    """EIP-7910 leaves out a future fork that the node does not support."""
    chain = genesis_chain()
    later = answer(with_activations(chain, ["hegota", "time", 400]))["result"]
    assert later == answer(chain)["result"]
    assert later["last"]["activationTime"] == 300


def test_only_unsupported_future_fork() -> None:
    """With no supported fork after the head, the next and last configurations are null."""
    chain = genesis_chain()
    activations = [["dencun", "block", 0], ["hegota", "time", 400]]
    chain = replace(chain, config={**chain.config, "activations": activations})
    report = answer(chain)["result"]
    assert (report["next"], report["last"]) == (None, None)
    assert report["current"]["activationTime"] == 0


def time_chain(*activations: list[object]) -> ReplayChain:
    """A Prague head at number 100 and time 100, with a genesis context and these forks."""
    chain = genesis_chain()
    header = rlp.decode(synthetic_genesis("pectra", rlp.encode([])))
    # Number 100 puts the head after the fork blocks of the activations below.
    header[0][8] = (100).to_bytes(1, "big")
    first = ("pectra", rlp.encode(header))
    chain = replace(chain, blocks=(first,), forkchoice=(block_hash(first), ZERO, ZERO))
    genesis_hash = block_hash(genesis_chain().blocks[0])
    config = {
        **chain.config,
        "genesisHash": "0x" + genesis_hash.hex(),
        "genesisTime": 0,
        "activations": [["frontier", "block", 0], *activations],
    }
    return replace(chain, config=config)


def test_fork_without_activation_time() -> None:
    """A passed fork set by block, other than the current one, no longer fails the report."""
    chain = time_chain(["dencun", "block", 90], ["pectra", "time", 100], ["fusaka", "time", 300])
    report = answer(chain)["result"]
    times = [report[name]["activationTime"] for name in ("current", "next", "last")]
    assert times == [100, 300, 300]


def test_current_fork_without_activation_time() -> None:
    """The current configuration cannot be left out, so its unknown time fails the method."""
    chain = time_chain(["dencun", "block", 50], ["pectra", "block", 90], ["fusaka", "time", 300])
    assert error(chain) == {**INTERNAL_ERROR, "data": "eth_config: activation time is unknown"}


def test_config_extra_parameters() -> None:
    """The method rejects parameters before computing its configuration."""
    request = '{"jsonrpc":"2.0","id":1,"method":"eth_config","params":[1]}'
    assert error(at_block(41), request) == {
        "code": -32602,
        "message": "Invalid params",
        "data": "the method takes no parameter",
    }


def test_config_before_cancun() -> None:
    """EthLib declines the nonstandard reports that EIP-7910 permits before Cancun."""
    assert error(at_block(41)) == {**NOT_SUPPORTED, "data": "eth_config: before Cancun"}


def test_config_zero_chain_id() -> None:
    """EIP-7910 excludes a chain ID of zero."""
    chain = genesis_chain()
    chain = replace(chain, config={**chain.config, "chainId": 0})
    assert error(chain) == {**INTERNAL_ERROR, "data": "eth_config: zero chain ID"}


def test_config_activation_overflow() -> None:
    """An activation that the fork ID cannot encode is rejected instead of truncated."""
    chain = genesis_chain()
    chain = replace(
        chain,
        config={**chain.config, "activations": [["dencun", "block", 0], ["pectra", "time", 2**64]]},
    )
    assert error(chain) == {**INTERNAL_ERROR, "data": "eth_config: activation is not below 2^64"}


def test_pending_fork_block() -> None:
    """A fork block above the head leaves the fork IDs of the reported activations unknown."""
    chain = genesis_chain()
    activations = [["dencun", "block", 0], ["pectra", "block", 10]]
    chain = replace(chain, config={**chain.config, "activations": activations})
    assert error(chain) == {**INTERNAL_ERROR, "data": "eth_config: fork block not reached"}


def test_blob_schedule_by_block() -> None:
    """EIP-7892 ties each blob schedule to a fork, so one at a block after genesis is refused."""
    chain = genesis_chain()
    schedules = [["block", 10, 3, 6, 3338477]]
    chain = replace(chain, config={**chain.config, "blobSchedules": schedules})
    assert error(chain) == {**INTERNAL_ERROR, "data": "eth_config: blob schedule without a fork"}


@pytest.mark.parametrize(
    ("fields", "message"),
    [
        ({"mergeForkBlock": "36"}, "config: mergeForkBlock is not a number"),
        ({"mergeForkBlock": 2**64}, "config: mergeForkBlock is not below 2^64"),
        ({"genesisTime": 2**64}, "config: genesisTime is not below 2^64"),
        ({"genesisTime": 100}, "config: genesisHash and genesisTime must be given together"),
        (
            {"genesisHash": "0x" + "00" * 32},
            "config: genesisHash and genesisTime must be given together",
        ),
        (
            {"genesisHash": "0x" + "00" * 32, "genesisTime": 100},
            "config: genesis context disagrees with block zero",
        ),
    ],
)
def test_bad_genesis_context(fields: Mapping[str, object], message: str) -> None:
    """Malformed or contradictory fork-ID context is rejected at the export boundary."""
    chain = genesis_chain()
    with raises(rpc.RpcError, message) as caught:
        answer(replace(chain, config={**chain.config, **fields}))
    assert caught.value.code == 0
