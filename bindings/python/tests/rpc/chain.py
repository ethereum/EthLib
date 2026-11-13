"""The test chain of ethereum/execution-apis, and the exchanges of its `.io` fixtures."""

import json
from collections.abc import Iterator, Mapping
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import Any, Final

from ethlib.chain import active_fork
from ethlib.cryptography.keccak import keccak256
from ethlib.execution import blocks, rpc
from ethlib.serialization import rlp

# `fixtures/README.md` gives the origin of the files and their licence.
FIXTURES: Final = Path(__file__).resolve().parent / "fixtures"

# Each fork of the genesis configuration, by its key, with the name of its EthLib fork.
# The key `eip158Block` is left out: it equals `eip155Block`, and both start Spurious Dragon.
# The chain merges at block 36, where its terminal total difficulty of 4732480 is reached.
GENESIS_FORKS: Final = {
    "homesteadBlock": "homestead",
    "eip150Block": "tangerineWhistle",
    "eip155Block": "spuriousDragon",
    "byzantiumBlock": "byzantium",
    "constantinopleBlock": "constantinople",
    "petersburgBlock": "petersburg",
    "istanbulBlock": "istanbul",
    "muirGlacierBlock": "muirGlacier",
    "berlinBlock": "berlin",
    "londonBlock": "london",
    "arrowGlacierBlock": "arrowGlacier",
    "grayGlacierBlock": "grayGlacier",
    "mergeNetsplitBlock": "paris",
    "shanghaiTime": "shapella",
    "cancunTime": "dencun",
    "pragueTime": "pectra",
    "osakaTime": "fusaka",
    "bpo1Time": "bpo1",
    "bpo2Time": "bpo2",
    "amsterdamTime": "glamsterdam",
}

# The keys of the configuration that hold no fork activation.
OTHER_KEYS: Final = {
    "chainId",
    "eip158Block",
    "terminalTotalDifficulty",
    "depositContractAddress",
    "ethash",
    "blobSchedule",
}


def _scalar(value: str | int) -> bytes:
    number = int(value, 16) if isinstance(value, str) else value
    return number.to_bytes((number.bit_length() + 7) // 8, "big")


def _hex(value: str) -> bytes:
    return bytes.fromhex(value.removeprefix("0x"))


def chain_config(config: Mapping[str, Any]) -> dict[str, Any]:
    """The chain configuration of a genesis file, in the form that the exports read."""
    assert set(config) == set(GENESIS_FORKS) | OTHER_KEYS
    assert config["eip158Block"] == config["eip155Block"]
    activations = [["frontier", "block", 0]] + [
        [fork, "block" if key.endswith("Block") else "time", config[key]]
        for key, fork in GENESIS_FORKS.items()
    ]
    # Each blob schedule starts at the time of the fork whose name it carries.
    schedules = [
        ["time", config[f"{name}Time"], s["target"], s["max"], s["baseFeeUpdateFraction"]]
        for name, s in config["blobSchedule"].items()
    ]
    return {
        "chainId": config["chainId"],
        "depositContractAddress": config["depositContractAddress"],
        "activations": activations,
        "blobSchedules": schedules,
        # The FORK_NEXT_VALUE of EIP-3675; without it, the fork ID would omit the Merge.
        "mergeForkBlock": config["mergeNetsplitBlock"],
    }


def genesis_state(alloc: Mapping[str, Mapping[str, Any]]) -> bytes:
    """The state of a genesis file, in the form of the state root export."""
    return rlp.encode(
        [
            [
                _hex(address),
                _scalar(account.get("nonce", 0)),
                _scalar(account.get("balance", 0)),
                _hex(account.get("code", "0x")),
                [
                    [_hex(key).rjust(32, b"\0"), _scalar(value)]
                    for key, value in account.get("storage", {}).items()
                ],
            ]
            for address, account in alloc.items()
        ]
    )


def rlp_items(data: bytes) -> Iterator[bytes]:
    """The RLP lists that a byte string holds one after the other."""
    start = 0
    while start < len(data):
        prefix = data[start]
        assert prefix >= 0xC0, "a block is an RLP list"
        if prefix <= 0xF7:
            end = start + 1 + prefix - 0xC0
        else:
            width = prefix - 0xF7
            end = start + 1 + width + int.from_bytes(data[start + 1 : start + 1 + width], "big")
        yield data[start:end]
        start = end


@dataclass(frozen=True, slots=True, kw_only=True)
class ReplayChain:
    """The test chain: its configuration, genesis state, blocks, forkchoice and network ID."""

    config: dict[str, Any]
    state: bytes
    blocks: tuple[rpc.ChainBlock, ...]
    forkchoice: tuple[bytes, bytes, bytes]
    network_id: int

    def serve(self, requests: list[str]) -> list[str | None]:
        """The texts of the responses of the chain to the texts of requests."""
        return rpc.serve(
            self.config,
            self.state,
            self.blocks,
            self.forkchoice,
            self.network_id,
            requests,
            check_seal=False,
        )


def _fork_of(config: dict[str, Any], header: list[Any]) -> str:
    number, timestamp = int.from_bytes(header[8], "big"), int.from_bytes(header[11], "big")
    fork = active_fork(config, number, timestamp)
    assert fork is not None
    return fork


@cache
def replay_chain() -> ReplayChain:
    """The chain of the fixtures, from genesis to the head of its forkchoice update."""
    genesis = json.loads((FIXTURES / "genesis.json").read_text())
    config = chain_config(genesis["config"])
    state = genesis_state(genesis["alloc"])
    fork = active_fork(config, int(genesis["number"], 16), int(genesis["timestamp"], 16))
    assert fork is not None
    first = blocks.genesis_block(
        fork,
        state,
        coinbase=_hex(genesis["coinbase"]),
        difficulty=int(genesis["difficulty"], 16),
        gas_limit=int(genesis["gasLimit"], 16),
        timestamp=int(genesis["timestamp"], 16),
        extra_data=_hex(genesis["extraData"]),
        mix_hash=_hex(genesis["mixHash"]),
        nonce=int(genesis["nonce"], 16).to_bytes(8, "big"),
    )
    chain: list[rpc.ChainBlock] = [(fork, first)]
    for raw in rlp_items((FIXTURES / "chain.rlp").read_bytes()):
        chain.append((_fork_of(config, rlp.decode(raw)[0]), raw))
    # The forkchoice update of the fixtures names the head, safe and finalized blocks.
    update = json.loads((FIXTURES / "headfcu.json").read_text())
    names = update["params"][0]
    forkchoice = (
        _hex(names["headBlockHash"]),
        _hex(names["safeBlockHash"]),
        _hex(names["finalizedBlockHash"]),
    )
    environment = json.loads((FIXTURES / "forkenv.json").read_text())
    return ReplayChain(
        config=config,
        state=state,
        blocks=tuple(chain),
        forkchoice=forkchoice,
        network_id=int(environment["HIVE_NETWORK_ID"]),
    )


def block_hash(block: rpc.ChainBlock) -> bytes:
    """The hash of the header of a block of the chain."""
    _, raw = block
    return keccak256(rlp.encode(rlp.decode(raw)[0]))


@dataclass(frozen=True, slots=True, kw_only=True)
class Exchange:
    """One request of a fixture and the response that it expects."""

    request: str
    response: dict[str, Any]


@dataclass(frozen=True, slots=True, kw_only=True)
class Fixture:
    """A `.io` fixture: its method, its exchanges, and whether it checks the schema only."""

    method: str
    exchanges: tuple[Exchange, ...]
    speconly: bool


def read_fixture(path: Path) -> Fixture:
    """The exchanges of a `.io` file, without its comments and its validation script."""
    lines = path.read_text().splitlines()
    if "--" in lines:
        lines = lines[: lines.index("--")]
    speconly = any(line.startswith("// speconly:") for line in lines)
    requests = [line[3:] for line in lines if line.startswith(">> ")]
    responses = [json.loads(line[3:]) for line in lines if line.startswith("<< ")]
    assert len(requests) == len(responses), path
    exchanges = tuple(
        Exchange(request=request, response=response)
        for request, response in zip(requests, responses, strict=True)
    )
    return Fixture(method=path.parent.name, exchanges=exchanges, speconly=speconly)
