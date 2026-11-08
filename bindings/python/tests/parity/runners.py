"""The runner of each group of cases that EthLib can run, and the plan for every other group."""

import json
import re
from collections import Counter
from collections.abc import Callable
from functools import cache, lru_cache
from pathlib import Path
from typing import cast

import pytest
from ruamel.yaml import YAML

from consensus.containers import CONTAINERS, FORKS as CONSENSUS_FORK
from consensus.test_epoch_processing import HANDLERS as EPOCH_STEPS, runs as runs_epoch_step
from consensus.test_fork import runs as runs_upgrade
from consensus.test_fork_choice import (
    FAST_CONFIRMATION,
    GLOAS_HANDLERS as GLOAS_FORK_CHOICE,
    HANDLERS as FORK_CHOICE,
    runs as runs_fork_choice,
)
from consensus.test_genesis import HANDLERS as GENESIS, runs as runs_genesis
from consensus.test_gossip_validation import TOPICS as GOSSIP_TOPICS, runs as runs_gossip
from consensus.test_light_client_data_collection import runs_data_collection
from consensus.test_light_client_sync import SPECIFIED as LIGHT_CLIENT_FORKS, runs_sync
from consensus.test_operations import HANDLERS as OPERATIONS, runs as runs_operation
from consensus.test_rewards import HANDLERS as REWARDS, runs as runs_rewards
from consensus.test_transition import GROUPS as TRANSITION_GROUPS, runs as runs_transition
from engine.cases import EXCEPTIONS as ENGINE_EXCEPTIONS
from raising import raises_shape
from transactions.expected_errors import expected_template
from transactions.test_inclusion_archive import names_in_block
from transactions.test_transactions import CHAIN_ID, FORK_OF_NETWORK

from . import legacy
from .catalogue import BOGOTA_NETWORKS, Case

# The groups that no runner covers yet, with the pull requests of the plan that bring them.
# A key is a runner, or a runner and a handler, of consensus-spec-tests.
# A key may also be a format of execution-spec-tests.
NOT_YET = {
    "epoch_processing": "beacon state transition (consensus track C13 to C40)",
    "finality": "a fork or handler that the runner of finality does not cover yet",
    "fork": "beacon state transition (consensus track C13 to C40)",
    "genesis": "the genesis after Phase 0 (consensus track C26 to C40)",
    "operations": "beacon state transition (consensus track C13 to C40)",
    "random": "a fork or handler that the runner of random does not cover yet",
    "sanity": "a fork or handler that the runner of sanity does not cover yet",
    "transition": "a fork or handler that the runner of transition does not cover yet",
}

# The plan at Gloas and Heze, by the steps of the track for Glamsterdam and Hegotá.
# A key is a runner, a runner and a handler, or a format, as in NOT_YET.
# At these forks an entry here comes before the entry of NOT_YET.
_GLOAS: dict[str, str] = {}
_HEZE: dict[str, str] = {}
# The plan for the Bogota networks of each devnet, whose EIPs differ.
# The steps wait for a merge into the Bogota fork branch, or a release of Bogota.
_BOGOTA = {
    "tests-heze-devnet": "the Bogota of the Heze devnet: EIP-7805 (G89) and EIP-8198 (G94)",
    "tests-bogota-devnet": (
        "the Bogota of the Bogota devnet: EIP-8141 (G90 to G93) and "
        "EIP-8250, 8272, 7906, 8298, 8151, 4758 and 8253 (G95 to G101)"
    ),
}
NOT_YET_AT = {
    "gloas": _GLOAS,
    "heze": _HEZE,
}

_YAML = YAML(typ="safe")


def _yaml(path: Path):
    return _YAML.load(path.read_text())


# A state test file can hold many megabytes, so only the last files read stay in memory.
@lru_cache(maxsize=16)
def _fixtures(path: Path) -> dict:
    return json.loads(path.read_text())


def _transaction(root: Path, case: Case) -> None:
    from ethlib.execution import transactions

    fixture = _fixtures(root / case.path)[case.id]
    tx = bytes.fromhex(fixture["txbytes"].removeprefix("0x"))
    outcome = fixture["result"][case.fork]
    fork = FORK_OF_NETWORK[case.fork]
    if "exception" in outcome:
        intrinsic = int(outcome.get("intrinsicGas", "0x0"), 16) or None
        template = expected_template(outcome["exception"], fork, tx, CHAIN_ID, intrinsic)
        with raises_shape(ValueError, template):
            transactions.check(fork, CHAIN_ID, tx)
    else:
        checked = transactions.check(fork, CHAIN_ID, tx)
        assert checked.sender == bytes.fromhex(outcome["sender"].removeprefix("0x"))
        assert checked.intrinsic_gas == int(outcome["intrinsicGas"], 16)
        assert transactions.tx_hash(fork, tx) == bytes.fromhex(outcome["hash"].removeprefix("0x"))


def _scalar(value: str) -> bytes:
    number = int(value, 16)
    return number.to_bytes((number.bit_length() + 7) // 8, "big")


def _hex(value: str) -> bytes:
    return bytes.fromhex(value.removeprefix("0x"))


def _pre_state(pre: dict) -> bytes:
    """The state in the form of the state root export: address, nonce, balance, code, storage."""
    from ethlib.serialization import rlp

    return rlp.encode(
        [
            [
                _hex(address),
                _scalar(a["nonce"]),
                _scalar(a["balance"]),
                _hex(a["code"]),
                [[int(k, 16).to_bytes(32, "big"), _scalar(v)] for k, v in a["storage"].items()],
            ]
            for address, a in pre.items()
        ]
    )


def _block_hashes(number: int) -> list[bytes]:
    """The hashes of the 256 blocks before a state test, oldest first."""
    # A state test has no chain, so block `n` has the hash `keccak256(str(n))` by convention.
    # The test `test_blockhash_zero_in_window_control` of execution-spec-tests states it.
    from ethlib.cryptography.keccak import keccak256

    return [keccak256(str(n).encode()) for n in range(max(0, number - 256), number)]


def _environment(env: dict) -> bytes:
    """The ten fields of the block that a run reads, with 0 for a field the fork lacks."""
    from ethlib.serialization import rlp

    random = int(env.get("currentRandom", "0x0"), 16).to_bytes(32, "big")
    return rlp.encode(
        [
            _hex(env["currentCoinbase"]),
            _scalar(env["currentGasLimit"]),
            _scalar(env["currentNumber"]),
            _scalar(env["currentTimestamp"]),
            _scalar(env["currentDifficulty"]),
            _scalar(env.get("currentBaseFee", "0x0")),
            random,
            _scalar(env.get("currentExcessBlobGas", "0x0")),
            _block_hashes(int(env["currentNumber"], 16)),
            _scalar(env.get("slotNumber", "0x0")),
        ]
    )


def _accounts(accounts: list) -> dict:
    """The accounts of a run, by address, in the form of the post state of a fixture."""
    return {
        "0x" + address.hex(): {
            "nonce": int.from_bytes(nonce, "big"),
            "balance": int.from_bytes(balance, "big"),
            "code": "0x" + code.hex(),
            "storage": {int.from_bytes(k, "big"): int.from_bytes(v, "big") for k, v in storage},
        }
        for address, nonce, balance, code, storage in accounts
    }


def _expected_accounts(state: dict) -> dict:
    return {
        address: {
            "nonce": int(a["nonce"], 16),
            "balance": int(a["balance"], 16),
            "code": a["code"],
            "storage": {int(k, 16): int(v, 16) for k, v in a["storage"].items() if int(v, 16)},
        }
        for address, a in state.items()
    }


def _state_diff(got: dict, expected: dict) -> list:
    """The accounts where a run and a fixture differ, for the message of a failure."""
    return [
        (address, got.get(address), expected.get(address))
        for address in sorted(set(got) | set(expected))
        if got.get(address) != expected.get(address)
    ]


def _state_test(root: Path, case: Case) -> None:
    from ethlib.execution import transactions

    fixture = _fixtures(root / case.path)[case.id]
    (post,) = fixture["post"][case.fork]
    fork = FORK_OF_NETWORK[case.fork]
    args = (
        fork,
        int(fixture["config"]["chainid"], 16),
        _hex(post["txbytes"]),
        _pre_state(fixture["pre"]),
        _environment(fixture["env"]),
    )
    if "expectException" in post:
        with pytest.raises(ValueError) as error:
            transactions.run(*args)
        expected = post["expectException"].split("|")
        assert any(names_in_block(e, str(error.value)) for e in expected), (
            expected,
            str(error.value),
        )
        return
    run = transactions.run(*args)
    if run.state_root != _hex(post["hash"]):
        got, expected = _accounts(run.accounts), _expected_accounts(post["state"])
        raise AssertionError(_state_diff(got, expected))
    assert run.logs_hash == _hex(post["logs"])
    receipt = post.get("receipt", {})
    if "cumulativeGasUsed" in receipt:
        assert run.gas_used == int(receipt["cumulativeGasUsed"], 16)
    # A receipt before Byzantium holds a state root instead of a status.
    if "status" in receipt:
        assert run.succeeded == receipt["status"]


# The forks of a network of the blockchain tests, in order, and how each activates.
_BLOCK_FORKS = [
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
_TIME_FORKS = [
    "shapella",
    "dencun",
    "pectra",
    "fusaka",
    "bpo1",
    "bpo2",
    "bpo3",
    "bpo4",
    "bpo5",
    "glamsterdam",
]
_NETWORK_FORK = {**FORK_OF_NETWORK, "BPO1": "bpo1", "BPO2": "bpo2", "BPO3": "bpo3", "BPO4": "bpo4"}

# The block exceptions of the blockchain tests, by the error of the state transition.
_BLOCK_EXCEPTIONS = {
    "INCORRECT_EXCESS_BLOB_GAS": r"wrongExcessBlobGas",
    "INCORRECT_BLOB_GAS_USED": r"wrongBlobGasUsed",
    "INVALID_REQUESTS": r"wrongRequestsHash",
    "INVALID_DEPOSIT_EVENT_LAYOUT": r"deposit",
    "INVALID_GASLIMIT": r"invalidGasLimit",
    "INVALID_BASEFEE_PER_GAS": r"wrongBaseFee",
    "INVALID_WITHDRAWALS_ROOT": r"wrongWithdrawalsRoot",
    "SYSTEM_CONTRACT_EMPTY": r"systemContractEmpty",
    "SYSTEM_CONTRACT_CALL_FAILED": r"system call to .* failed",
    "RLP_STRUCTURES_ENCODING": r"does not decode|block rejected",
    "RLP_BLOCK_LIMIT_EXCEEDED": r"blockTooLarge",
    # From Amsterdam, a block carries only the hash of its access list.
    # So a list that breaks a rule of its form shows as a wrong hash.
    "INCORRECT_BLOCK_FORMAT": r"block rejected|wrongBlockAccessListHash",
    "INVALID_GAS_USED": r"wrongGasUsed",
    "INVALID_BLOCK_ACCESS_LIST": r"wrongBlockAccessListHash|blockAccessList",
    "BLOCK_ACCESS_LIST_GAS_LIMIT_EXCEEDED": r"blockAccessList .*tooManyItems",
    # A header without the field of the hash, or with one too many, does not decode.
    "INVALID_BAL_HASH": r"wrongBlockAccessListHash|block rejected",
    "INVALID_BLOCK_HASH": r"block rejected",
}


def names_block_error(exception: str, message: str) -> bool:
    """Whether an error message of the state transition names a fixture exception."""
    kind, _, name = exception.partition(".")
    if kind == "BlockException":
        return name in _BLOCK_EXCEPTIONS and re.search(_BLOCK_EXCEPTIONS[name], message) is not None
    return names_in_block(exception, message)


# The networks after Amsterdam that only set a blob schedule of their own, with its name and time.
_SCENARIOS = {
    "AmsterdamBPOIncrease": ("AmsterdamBPOIncrease", 0),
    "AmsterdamBPODecrease": ("AmsterdamBPODecrease", 0),
    "AmsterdamToBPOIncreaseAtTime15k": ("AmsterdamBPOIncrease", 15_000),
    "AmsterdamToBPODecreaseAtTime15k": ("AmsterdamBPODecrease", 15_000),
}


def chain_of(fixture: dict) -> tuple[dict, list]:
    """The chain configuration of a blockchain test, and its activations as tuples."""
    scenario = _SCENARIOS.get(fixture["network"])
    network = "Amsterdam" if scenario else fixture["network"]
    before, _, after = network.removesuffix("AtTime15k").partition("To")
    first = _NETWORK_FORK[before]
    forks = _BLOCK_FORKS + _TIME_FORKS
    activations = [
        (fork, "block" if fork in _BLOCK_FORKS else "time", 0)
        for fork in forks[: forks.index(first) + 1]
    ]
    if after:
        activations.append((_NETWORK_FORK[after], "time", 15_000))
    # The fixture names each blob schedule by its network, which gives its activation.
    schedules = []
    for network, schedule in fixture["config"].get("blobSchedule", {}).items():
        for fork, kind, number in activations:
            if fork == _NETWORK_FORK.get(network, network.lower()):
                schedules.append(
                    [
                        kind,
                        number,
                        int(schedule["target"], 16),
                        int(schedule["max"], 16),
                        int(schedule["baseFeeUpdateFraction"], 16),
                    ]
                )
    if scenario:
        name, time = scenario
        own = fixture["config"]["blobSchedule"][name]
        schedules.append(
            [
                "time",
                time,
                int(own["target"], 16),
                int(own["max"], 16),
                int(own["baseFeeUpdateFraction"], 16),
            ]
        )
    config = {
        "chainId": int(fixture["config"]["chainid"], 16),
        "activations": [list(a) for a in activations],
        "blobSchedules": sorted(schedules, key=lambda s: s[1]),
    }
    return config, activations


def active_fork(activations: list, header: list) -> str:
    """The fork of a header: the last one whose activation its number or its time reached."""
    number, timestamp = int.from_bytes(header[8], "big"), int.from_bytes(header[11], "big")
    reached = [
        fork for fork, kind, n in activations if (number if kind == "block" else timestamp) >= n
    ]
    return reached[-1]


def genesis_of(fork: str, header: dict, pre: dict) -> bytes:
    """The genesis block of a chain, from its header in the JSON of a fixture and its state."""
    from ethlib.execution import blocks

    def number(name: str, default: int = 0) -> int:
        return int(header[name], 16) if name in header else default

    return blocks.genesis_block(
        fork,
        _pre_state(pre),
        coinbase=_hex(header["coinbase"]),
        difficulty=number("difficulty"),
        gas_limit=number("gasLimit"),
        timestamp=number("timestamp"),
        extra_data=_hex(header["extraData"]),
        mix_hash=_hex(header["mixHash"]),
        nonce=_hex(header["nonce"]),
        base_fee=number("baseFeePerGas", blocks.INITIAL_BASE_FEE),
        excess_blob_gas=number("excessBlobGas"),
        slot_number=number("slotNumber"),
    )


def _blockchain_test(root: Path, case: Case) -> None:
    from ethlib.cryptography.keccak import keccak256
    from ethlib.execution import blocks
    from ethlib.serialization import rlp

    fixture = _fixtures(root / case.path)[case.id]
    config, activations = chain_of(fixture)
    seal = fixture.get("sealEngine", "NoProof") != "NoProof"
    genesis = rlp.decode(_hex(fixture["genesisRLP"]))[0]
    recent = [(active_fork(activations, genesis), rlp.encode(genesis), [])]
    # The genesis block follows from the fields of its header that the chain chooses, and the state.
    assert genesis_of(recent[0][0], fixture["genesisBlockHeader"], fixture["pre"]) == _hex(
        fixture["genesisRLP"]
    )
    state = _pre_state(fixture["pre"])
    for block in fixture["blocks"]:
        raw = _hex(block["rlp"])
        expected = block.get("expectException")
        try:
            item = rlp.decode(raw)
            fork = active_fork(activations, item[0])
        except Exception:
            # A block that is not even an RLP list of headers is invalid.
            assert expected, block
            continue
        if expected:
            with pytest.raises(ValueError) as error:
                blocks.state_transition(config, state, recent, fork, raw, seal)
            names = expected.split("|")
            assert any(names_block_error(e, str(error.value)) for e in names), (
                names,
                str(error.value),
            )
            continue
        _, accounts = blocks.state_transition(config, state, recent, fork, raw, seal)
        state = rlp.encode(accounts)
        recent = (recent + [(fork, rlp.encode(item[0]), [rlp.encode(o) for o in item[2]])])[-256:]
    assert "0x" + keccak256(recent[-1][1]).hex() == fixture["lastblockhash"]


# The fields of a header in the order of its RLP form; a header holds those of its fork.
HEADER_FIELDS = [
    "parentHash",
    "uncleHash",
    "coinbase",
    "stateRoot",
    "transactionsTrie",
    "receiptTrie",
    "bloom",
    "difficulty",
    "number",
    "gasLimit",
    "gasUsed",
    "timestamp",
    "extraData",
    "mixHash",
    "nonce",
    "baseFeePerGas",
    "withdrawalsRoot",
    "blobGasUsed",
    "excessBlobGas",
    "parentBeaconBlockRoot",
    "requestsHash",
    "blockAccessListHash",
    "slotNumber",
]

# The fields that are numbers, which RLP writes without leading zeros.
NUMBERS = {
    "difficulty",
    "number",
    "gasLimit",
    "gasUsed",
    "timestamp",
    "baseFeePerGas",
    "blobGasUsed",
    "excessBlobGas",
    "slotNumber",
}


def _header_of_json(fields: dict) -> bytes:
    """The RLP form of a header given as the JSON of a fixture."""
    from ethlib.serialization import rlp

    items = []
    for name in HEADER_FIELDS:
        if name in fields:
            raw = bytes.fromhex(fields[name].removeprefix("0x"))
            items.append(raw.lstrip(b"\0") if name in NUMBERS else raw)
    return rlp.encode(items)


def _engine_payload(fixture: dict, payload: dict, state: bytes, recent: list) -> tuple:
    """Run one payload on the chain; return its kind, and the next state and recent blocks."""
    from ethlib import engine
    from ethlib.cryptography.keccak import keccak256
    from ethlib.serialization import rlp

    config, _ = chain_of(fixture)
    method = f"engine_newPayloadV{payload['newPayloadVersion']}"
    if "errorCode" in payload:
        with pytest.raises(engine.EngineError) as error:
            engine.new_payload_on_chain(config, state, recent, method, payload["params"])
        assert -error.value.code == int(payload["errorCode"])
        return "error", state, recent
    status, header, accounts = engine.new_payload_on_chain(
        config, state, recent, method, payload["params"]
    )
    expected = payload.get("validationError")
    if not expected:
        assert status["status"] == "VALID", status
        assert status["latestValidHash"] == payload["params"][0]["blockHash"]
        # A valid payload gives its header and the accounts after it.
        header, accounts = cast(bytes, header), cast(bytes, accounts)
        fork = active_fork(chain_of(fixture)[1], rlp.decode(header))
        return "valid", accounts, (recent + [(fork, header, [])])[-256:]
    names = expected.split("|")
    code, _, message = status["validationError"].partition(": ")
    if int(code) == 405:
        assert status["status"] == "INVALID", status
        assert any(names_block_error(e, message) for e in names), (status, names)
        # A payload invalid in execution names its most recent valid ancestor.
        # That is the head of the chain, which is its parent.
        # The zero hash for an ancestor before Paris never applies: engine chains start at Paris.
        assert status["latestValidHash"] == "0x" + keccak256(recent[-1][1]).hex(), status
        return "execution", state, recent
    assert ENGINE_EXCEPTIONS[int(code)] & set(names), (status, names)
    # A payload that a check before execution rejects has a null latest valid hash.
    assert status["latestValidHash"] is None, status
    return "invalid", state, recent


def _start(pre: dict, genesis: dict, fork: str) -> tuple[bytes, bytes]:
    """The state of a chain before its first payload, and the header of its genesis block."""
    from ethlib.serialization import rlp

    return _pre_state(pre), rlp.encode(rlp.decode(genesis_of(fork, genesis, pre))[0])


# The fixtures of a group of blockchain_test_engine_x share one state, of up to 14 MB of JSON.
# Their state and genesis block take most of the time of a case, so a process computes them once.
@cache
def _shared_start(path: Path, fork: str) -> tuple[bytes, bytes]:
    shared = _fixtures(path)
    return _start(shared["pre"], shared["genesis"], fork)


def run_engine_chain(
    fixture: dict,
    pre: dict,
    genesis: dict,
    start: Callable[[str], tuple[bytes, bytes]] | None = None,
) -> Counter:
    """Run every payload of an engine fixture on its chain; return the kind of each outcome.

    The function `start` gives the state and the genesis header at a fork, when they are known.
    """
    from ethlib.cryptography.keccak import keccak256
    from ethlib.serialization import rlp

    header = _header_of_json(genesis)
    assert "0x" + keccak256(header).hex() == genesis["hash"]
    fork = active_fork(chain_of(fixture)[1], rlp.decode(header))
    state, computed = start(fork) if start else _start(pre, genesis, fork)
    recent = [(fork, header, [])]
    assert computed == header
    kinds = Counter()
    for payload in fixture["engineNewPayloads"]:
        kind, state, recent = _engine_payload(fixture, payload, state, recent)
        kinds[kind] += 1
    assert "0x" + keccak256(recent[-1][1]).hex() == fixture["lastblockhash"]
    return kinds


def _blockchain_test_engine(root: Path, case: Case) -> None:
    fixture = _fixtures(root / case.path)[case.id]
    run_engine_chain(fixture, fixture["pre"], fixture["genesisBlockHeader"])


def _blockchain_test_engine_x(root: Path, case: Case) -> None:
    # The fixtures of one group share their state and genesis in a file named by its hash.
    fixture = _fixtures(root / case.path)[case.id]
    directory = root.joinpath(*case.path.split("/")[:2])
    path = directory / "pre_alloc" / f"{fixture['preHash']}.json"
    shared = _fixtures(path)
    run_engine_chain(
        fixture, shared["pre"], shared["genesis"], lambda fork: _shared_start(path, fork)
    )


def _shuffle(root: Path, case: Case) -> None:
    from ethlib import consensus

    vector = _yaml(root / case.path / "mapping.yaml")
    seed = bytes.fromhex(vector["seed"].removeprefix("0x"))
    assert (
        consensus.compute_shuffled_permutation(vector["count"], seed, case.preset)
        == vector["mapping"]
    )


def _custody_groups(root: Path, case: Case) -> None:
    from ethlib import consensus

    meta = _yaml(root / case.path / "meta.yaml")
    groups = consensus.get_custody_groups(
        int(meta["node_id"]), meta["custody_group_count"], case.preset
    )
    assert groups == meta["result"]


def _custody_columns(root: Path, case: Case) -> None:
    from ethlib import consensus

    meta = _yaml(root / case.path / "meta.yaml")
    assert (
        consensus.compute_columns_for_custody_group(meta["custody_group"], case.preset)
        == meta["result"]
    )


def _gossip_data_column_sidecar(root: Path, case: Case) -> None:
    from consensus.test_data_column import run_gossip_case
    from consensus.test_gossip_validation import run_case

    # Where the store is specified, the whole validation runs.
    # Elsewhere only the sidecar checks that read no store do.
    if runs_gossip(case.fork, "gossip_data_column_sidecar"):
        run_case(case.preset, case.fork, root / case.path)
    else:
        run_gossip_case(root / case.path, case.preset)


def _gossip(root: Path, case: Case) -> None:
    from consensus.test_gossip_validation import run_case

    run_case(case.preset, case.fork, root / case.path)


def _ssz_static(root: Path, case: Case) -> None:
    from ethlib import consensus
    from ethlib.networking import snappy

    container = case.group.split("/")[1]
    data = snappy.decompress((root / case.path / "serialized.ssz_snappy").read_bytes())
    expected = _yaml(root / case.path / "roots.yaml")["root"]
    got_root, encoded = consensus.ssz_static(
        case.preset, CONSENSUS_FORK[case.fork], container, data
    )
    assert "0x" + got_root.hex() == expected
    assert encoded == data


def _single_merkle_proof(root: Path, case: Case) -> None:
    from consensus.test_light_client_proofs import _check

    # tests/<preset>/<fork>/light_client/single_merkle_proof/<container>/<case>
    container = case.path.split("/")[5]
    _check(case.preset, case.fork, container, root / case.path)


def _light_client_sync(root: Path, case: Case) -> None:
    from consensus.test_light_client_sync import run_sync_case

    run_sync_case(root / case.path, case.preset, case.fork)


def _update_ranking(root: Path, case: Case) -> None:
    from consensus.test_light_client_sync import run_ranking_case

    run_ranking_case(root / case.path, case.preset, case.fork)


def _data_collection(root: Path, case: Case) -> None:
    from consensus.test_light_client_data_collection import run_data_collection_case

    run_data_collection_case(root / case.path, case.preset)


def _merkle_proof(root: Path, case: Case) -> None:
    from consensus.test_merkle_proof import run_case

    run_case(case.preset, case.fork, root / case.path)


def _operation(root: Path, case: Case) -> None:
    from consensus.test_operations import run_case

    # tests/<preset>/<fork>/operations/<handler>/<suite>/<case>
    run_case(case.preset, case.fork, case.group.split("/")[1], root / case.path)


def _epoch_step(root: Path, case: Case) -> None:
    from consensus.test_epoch_processing import run_case

    # tests/<preset>/<fork>/epoch_processing/<handler>/<suite>/<case>
    run_case(case.preset, case.fork, case.group.split("/")[1], root / case.path)


def _rewards(root: Path, case: Case) -> None:
    from consensus.test_rewards import run_case

    # tests/<preset>/<fork>/rewards/<handler>/<suite>/<case>
    run_case(case.preset, case.fork, root / case.path)


def _transition(root: Path, case: Case) -> None:
    from consensus.test_transition import run_case

    # tests/<preset>/<fork>/<runner>/<handler>/<suite>/<case>
    run_case(case.preset, case.fork, case.group, root / case.path)


def _fork_choice(root: Path, case: Case) -> None:
    from consensus.test_fork_choice import run_case

    # tests/<preset>/<fork>/<fork_choice, sync or fast_confirmation>/<handler>/<suite>/<case>
    run_case(case.preset, case.fork, root / case.path)


def _genesis(root: Path, case: Case) -> None:
    from consensus.test_genesis import run_case

    # tests/<preset>/<fork>/genesis/<handler>/<suite>/<case>
    run_case(case.preset, case.fork, case.group.split("/")[1], root / case.path)


def _upgrade(root: Path, case: Case) -> None:
    from consensus.test_fork import run_case

    # tests/<preset>/<fork>/fork/fork/<suite>/<case>
    run_case(case.preset, case.fork, root / case.path)


def _container_forks(container: str) -> tuple[str, ...]:
    first, dropped = CONTAINERS[container]
    forks = list(CONSENSUS_FORK)
    return tuple(forks[forks.index(first) : forks.index(dropped) if dropped else len(forks)])


# The runner of each group, by format or by runner and handler.
RUNNERS = {
    "transaction_test": _transaction,
    "state_test": _state_test,
    "blockchain_test": _blockchain_test,
    "blockchain_test_engine": _blockchain_test_engine,
    "blockchain_test_engine_x": _blockchain_test_engine_x,
    "shuffling/core": _shuffle,
    "networking/get_custody_groups": _custody_groups,
    "networking/compute_columns_for_custody_group": _custody_columns,
    # The whole validation before Gloas; from Gloas the checks of the sidecar alone.
    "networking/gossip_data_column_sidecar": _gossip_data_column_sidecar,
    **{
        f"networking/gossip_{topic}": _gossip
        for topic in GOSSIP_TOPICS
        if topic != "data_column_sidecar"
    },
    **{f"ssz_static/{container}": _ssz_static for container in CONTAINERS},
    "light_client/single_merkle_proof": _single_merkle_proof,
    "merkle_proof/single_merkle_proof": _merkle_proof,
    "light_client/sync": _light_client_sync,
    "light_client/update_ranking": _update_ranking,
    # The served data against the blocks; choosing it needs the state transition (C23).
    "light_client/data_collection": _data_collection,
    "legacy_header": legacy.run_headers,
    **{f"operations/{handler}": _operation for handler in OPERATIONS},
    **{f"epoch_processing/{handler}": _epoch_step for handler in EPOCH_STEPS},
    **{f"rewards/{handler}": _rewards for handler in REWARDS},
    "fork/fork": _upgrade,
    **{f"fork_choice/{handler}": _fork_choice for handler in FORK_CHOICE + GLOAS_FORK_CHOICE},
    # Optimistic sync runs as a fork choice case, with the verdicts of the execution layer.
    "sync/optimistic": _fork_choice,
    # The fast confirmation cases are fork choice cases whose checks also read the rule's store.
    **{f"fast_confirmation/{suite}": _fork_choice for suite in FAST_CONFIRMATION},
    **{group: _transition for group in TRANSITION_GROUPS},
    **{f"genesis/{handler}": _genesis for handler in GENESIS},
    "legacy_ommers": legacy.run_ommers,
    "legacy_dao": legacy.run_dao,
    "legacy_blockchain": legacy.run_blockchain,
}


def runner(case: Case):
    """The runner of a case, or `None` if EthLib cannot run it yet."""
    if case.fork in BOGOTA_NETWORKS:
        return None
    run = RUNNERS.get(case.group)
    if run is _ssz_static and case.fork not in _container_forks(case.group.split("/")[1]):
        return None
    if run is _operation and not runs_operation(case.fork, case.group.split("/")[1]):
        return None
    if run is _light_client_sync and not runs_sync(case.fork, Path(case.path).name):
        return None
    if run is _data_collection and not runs_data_collection(case.fork, Path(case.path).name):
        return None
    if run is _update_ranking and case.fork not in LIGHT_CLIENT_FORKS:
        return None
    if run is _epoch_step and not runs_epoch_step(case.fork, case.group.split("/")[1]):
        return None
    if run is _rewards and not runs_rewards(case.fork):
        return None
    if run is _upgrade and not runs_upgrade(case.fork):
        return None
    if run is _fork_choice and not runs_fork_choice(case.fork, *case.group.split("/")):
        return None
    if run is _transition and not runs_transition(case.fork, case.group):
        return None
    if run is _genesis and not runs_genesis(case.fork, case.group.split("/")[1]):
        return None
    if run is _gossip and not runs_gossip(case.fork, case.group.split("/")[1]):
        return None
    return run


def plan(case: Case) -> str | None:
    """The plan for a case that no runner covers: its fork's entry first, then the general one."""
    if case.fork in BOGOTA_NETWORKS:
        return _BOGOTA[case.suite]
    for table in (NOT_YET_AT.get(case.fork, {}), NOT_YET):
        if entry := table.get(case.group) or table.get(case.group.split("/")[0]):
            return entry
    return None
