"""EIP-7910 configuration reports at fork boundaries and with chain-specific blob parameters."""

import json
import zlib
from dataclasses import replace
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


def answer(chain: ReplayChain, request: str = REQUEST) -> dict[str, Any]:
    """The response to one configuration request."""
    (text,) = chain.serve([request])
    assert text is not None
    return json.loads(text)


def at_block(number: int) -> ReplayChain:
    """The pinned test chain through one head, without safe or finalized checkpoints."""
    chain = replay_chain()
    return replace(
        chain,
        blocks=chain.blocks[: number + 1],
        forkchoice=(block_hash(chain.blocks[number]), ZERO, ZERO),
    )


def checksum(chain: ReplayChain, timestamp: int) -> str:
    """The post-Merge checksum, computed independently from the pinned genesis configuration."""
    config = json.loads((FIXTURES / "genesis.json").read_text())["config"]
    # EIP-3675 uses mergeNetsplitBlock, rather than the actual Paris activation block.
    heights = sorted(
        {value for name, value in config.items() if name.endswith("Block") and value > 0}
    )
    times = sorted(
        {value for name, value in config.items() if name.endswith("Time") and value <= timestamp}
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
    assert report["current"]["chainId"] == "0xc72dd9d5e883e"
    assert len(report["current"]["precompiles"]) == count
    for name, time in [("current", current), ("next", next_time), ("last", last_time)]:
        config = report[name]
        if time is None:
            assert config is None
            continue
        assert config["activationTime"] == time
        assert config["forkId"] == checksum(chain, time)
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


def test_chain_specific_blob_activation() -> None:
    """A blob-only activation without a named fork gets its own report and keeps the fork ID."""
    chain = at_block(54)
    schedule = ["time", 555, 14, 22, 11684671]
    chain = replace(
        chain,
        config={**chain.config, "blobSchedules": [*chain.config["blobSchedules"], schedule]},
    )
    report = answer(chain)["result"]
    assert report["current"]["activationTime"] == 540
    assert report["current"]["blobSchedule"]["max"] == 21
    assert report["next"]["activationTime"] == 555
    assert report["next"]["blobSchedule"]["max"] == 22
    assert report["next"]["forkId"] == report["current"]["forkId"] == checksum(chain, 555)
    assert report["next"]["precompiles"] == report["current"]["precompiles"]
    assert report["next"]["systemContracts"] == report["current"]["systemContracts"]
    assert report["last"]["activationTime"] == 570
    assert report["last"]["blobSchedule"]["max"] == 22
    assert report["last"]["forkId"] == checksum(chain, 570)


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
        blocks.genesis_block(
            "dencun",
            state,
            timestamp=100,
            coinbase=bytes(20),
            difficulty=0,
            gas_limit=30000000,
            extra_data=b"",
            mix_hash=ZERO,
            nonce=bytes(8),
        ),
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
    item[0][8] = b"\x64"
    first = ("dencun", rlp.encode(item))
    return replace(chain, blocks=(first,), forkchoice=(block_hash(first), ZERO, ZERO))


def test_pruned_genesis_context() -> None:
    """A pruned view needs explicit genesis context to report the correct checksum."""
    original = genesis_chain()
    chain = pruned_chain()
    assert answer(chain)["error"]["data"] == "eth_config: genesis context unavailable"
    context = {"genesisHash": "0x" + block_hash(original.blocks[0]).hex(), "genesisTime": 100}
    chain = replace(chain, config={**chain.config, **context})
    assert answer(chain)["result"] == answer(original)["result"]


def test_merge_fork_id_block() -> None:
    """The Merge fork-ID block enters the checksum, and the actual Paris activation does not."""
    chain = pruned_chain()
    genesis_hash = block_hash(genesis_chain().blocks[0])
    config = {
        **chain.config,
        "genesisHash": "0x" + genesis_hash.hex(),
        "genesisTime": 0,
        "mergeForkBlock": 90,
        "activations": [["frontier", "block", 0], ["paris", "block", 80], ["dencun", "time", 100]],
    }
    current = answer(replace(chain, config=config))["result"]["current"]
    data = genesis_hash + (90).to_bytes(8, "big") + (100).to_bytes(8, "big")
    assert current["forkId"] == f"0x{zlib.crc32(data):08x}"


def test_unsupported_future_fork() -> None:
    """A configured fork beyond the implemented report range gets no invented contract set."""
    chain = genesis_chain()
    chain = replace(
        chain,
        config={
            **chain.config,
            "activations": [*chain.config["activations"], ["hegota", "time", 400]],
        },
    )
    assert answer(chain)["error"]["data"] == "eth_config: unsupported fork"


def test_config_extra_parameters() -> None:
    """The method rejects parameters before computing its configuration."""
    request = '{"jsonrpc":"2.0","id":1,"method":"eth_config","params":[1]}'
    assert answer(at_block(41), request)["error"]["code"] == -32602


def test_config_before_cancun() -> None:
    """EthLib declines the nonstandard reports that EIP-7910 permits before Cancun."""
    assert answer(at_block(41))["error"]["code"] == -32004


def test_config_zero_chain_id() -> None:
    """EIP-7910 excludes a chain ID of zero."""
    chain = genesis_chain()
    chain = replace(chain, config={**chain.config, "chainId": 0})
    assert answer(chain)["error"]["data"] == "eth_config: zero chain ID"


def test_config_activation_overflow() -> None:
    """An activation that the fork ID cannot encode is rejected instead of truncated."""
    chain = genesis_chain()
    chain = replace(
        chain,
        config={**chain.config, "activations": [["dencun", "block", 0], ["pectra", "time", 2**64]]},
    )
    assert answer(chain)["error"]["data"] == "eth_config: activation is not below 2^64"


@pytest.mark.parametrize("blob_only", [False, True])
def test_config_unknown_activation_time(blob_only: bool) -> None:
    """A positive block activation cannot be reported as a fork active at genesis."""
    chain = genesis_chain()
    changes = (
        {"blobSchedules": [["block", 10, 3, 6, 3338477]]}
        if blob_only
        else {"activations": [["dencun", "block", 0], ["pectra", "block", 10]]}
    )
    assert answer(replace(chain, config={**chain.config, **changes}))["error"]["data"] == (
        "eth_config: activation time is unknown"
    )


@pytest.mark.parametrize(
    ("fields", "message"),
    [
        ({"mergeForkBlock": "36"}, "config: mergeForkBlock is not a number"),
        ({"mergeForkBlock": 2**64}, "config: mergeForkBlock is not below 2^64"),
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
def test_bad_genesis_context(fields: dict[str, Any], message: str) -> None:
    """Malformed or contradictory fork-ID context is rejected at the export boundary."""
    chain = genesis_chain()
    with raises(rpc.RpcError, message):
        answer(replace(chain, config={**chain.config, **fields}))
