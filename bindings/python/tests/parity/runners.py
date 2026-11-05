"""The runner of each group of cases that EthLib can run, and the plan for every other group."""

import json
import re
from collections import Counter
from functools import lru_cache
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from consensus.containers import CONTAINERS
from consensus.containers import FORKS as CONSENSUS_FORK
from consensus.test_epoch_processing import HANDLERS as EPOCH_STEPS
from consensus.test_epoch_processing import runs as runs_epoch_step
from consensus.test_fork import runs as runs_upgrade
from consensus.test_fork_choice import HANDLERS as FORK_CHOICE
from consensus.test_fork_choice import runs as runs_fork_choice
from consensus.test_operations import HANDLERS as OPERATIONS
from consensus.test_light_client_data_collection import runs_data_collection
from consensus.test_light_client_sync import SPECIFIED as LIGHT_CLIENT_FORKS
from consensus.test_light_client_sync import runs_sync
from consensus.test_operations import runs as runs_operation
from consensus.test_rewards import HANDLERS as REWARDS
from consensus.test_rewards import runs as runs_rewards
from engine.cases import EXCEPTIONS as ENGINE_EXCEPTIONS
from consensus.test_transition import GROUPS as TRANSITION_GROUPS
from consensus.test_transition import runs as runs_transition
from transactions.test_inclusion_archive import names_in_block
from transactions.test_transactions import CHAIN_ID, FORK_OF_NETWORK, names

from . import legacy
from .catalogue import CONSENSUS_FORKS, EXECUTION_FORKS, Case

# The groups that no runner covers yet, with the pull requests of the plan that bring them.
# A key is a runner, or a runner and a handler, of consensus-spec-tests, or a format of
# execution-spec-tests.
NOT_YET = {
    "epoch_processing": "beacon state transition (consensus track C13 to C40)",
    "finality": "the state transition after Phase 0 (consensus track C26 to C40)",
    "fork": "beacon state transition (consensus track C13 to C40)",
    "genesis": "beacon state transition (consensus track C13 to C40)",
    "operations": "beacon state transition (consensus track C13 to C40)",
    "random": "the state transition after Phase 0 (consensus track C26 to C40)",
    "sanity": "the state transition after Phase 0 (consensus track C26 to C40)",
    "transition": "beacon state transition (consensus track C13 to C40)",
    "fork_choice": "the Bellatrix to Fulu blocks (C47)",
    "fast_confirmation": "fast confirmation rule (consensus track, decision 9)",
    "sync": "optimistic sync (consensus track C48)",
    "networking": "gossip validation (consensus track C63 and C64)",
    "ssz_static": "the remaining beacon containers (consensus track C2, C6 to C12)",
}

# The plan at Gloas, Heze and the Amsterdam networks, by the steps of the track for Glamsterdam
# and Hegotá. A key is a runner, a runner and a handler, or a format, as in NOT_YET.
# At these forks an entry here comes before the entry of NOT_YET.
_GLOAS = {
    "epoch_processing": "the Gloas slot and epoch processing (G51)",
    "finality": "the Gloas block processing and state transition (G52)",
    "random": "the Gloas block processing and state transition (G52)",
    "sanity": "the Gloas block processing and state transition (G52)",
    "transition": "the upgrade to Gloas (G53) and the Gloas state transition (G52)",
    "operations": "the Gloas attestations, slashings and operations (G50)",
    "operations/parent_execution_payload": "the parent execution payload (G48)",
    "operations/deposit_request": "the parent execution payload (G48)",
    "operations/withdrawal_request": "the parent execution payload (G48)",
    "operations/consolidation_request": "the parent execution payload (G48)",
    "fork_choice": "the Gloas block and payload handlers (G70)",
    "fast_confirmation": "the Gloas fast confirmation (G73)",
    "networking": "the Gloas data columns and unchanged topics (G77)",
    "networking/gossip_execution_payload_bid": "bids and proposer preferences (G74)",
    "networking/gossip_proposer_preferences": "bids and proposer preferences (G74)",
    "networking/gossip_execution_payload_envelope": "envelopes and payload attestations (G75)",
    "networking/gossip_payload_attestation_message": "envelopes and payload attestations (G75)",
    "networking/gossip_beacon_block": "Gloas blocks and attestations (G76)",
    "networking/gossip_beacon_attestation": "Gloas blocks and attestations (G76)",
    "networking/gossip_beacon_aggregate_and_proof": "Gloas blocks and attestations (G76)",
    "networking/gossip_partial_data_column_sidecar": "Gloas partial data columns (G78)",
    "ssz_static": "the remaining Gloas containers (G36 to G41, G65)",
}
_HEZE = {
    "epoch_processing": "Heze blocks and epochs (G84)",
    "rewards": "Heze blocks and epochs (G84)",
    "finality": "Heze blocks and epochs (G84)",
    "random": "Heze blocks and epochs (G84)",
    "sanity": "Heze blocks and epochs (G84)",
    "operations": "Heze blocks and epochs (G84)",
    "transition": "the Gloas state transition (G52) and Heze blocks and epochs (G84)",
    "fork_choice": "inclusion lists in the Heze fork choice (G86)",
    "fast_confirmation": "the Gloas fast confirmation (G73) on the Heze fork choice (G86)",
    "networking": "the Heze gossip and req/resp rules (G87)",
    "ssz_static": "the Heze containers (G80, G81)",
}
_AMSTERDAM = {
    "state_test": "the pre-execution phase and block transition of Amsterdam (G20, G23), then G24",
    "blockchain_test": "the Amsterdam block transition (G23), then G24",
    "blockchain_test_engine": "the Amsterdam payload on the Engine layer (G39), after G23",
    "blockchain_test_engine_x": "the Amsterdam payload on the Engine layer (G39), after G23",
}
NOT_YET_AT = {
    "gloas": _GLOAS,
    "heze": _HEZE,
    **{network: _AMSTERDAM for network in (
        "BPO2ToAmsterdamAtTime15k", "Amsterdam", "AmsterdamToBPOIncreaseAtTime15k",
        "AmsterdamBPOIncrease", "AmsterdamToBPODecreaseAtTime15k", "AmsterdamBPODecrease")},
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
        with pytest.raises(ValueError) as error:
            transactions.check(fork, CHAIN_ID, tx)
        expected = outcome["exception"].split("|")
        assert any(names(e, str(error.value)) for e in expected), (expected, str(error.value))
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

    return rlp.encode([
        [_hex(address), _scalar(a["nonce"]), _scalar(a["balance"]), _hex(a["code"]),
         [[int(k, 16).to_bytes(32, "big"), _scalar(v)] for k, v in a["storage"].items()]]
        for address, a in pre.items()])


def _block_hashes(number: int) -> list[bytes]:
    """The hashes of the 256 blocks before a state test, oldest first."""
    # A state test has no chain, so block `n` has the hash `keccak256(str(n))` by convention.
    # The test `test_blockhash_zero_in_window_control` of execution-spec-tests states it.
    from ethlib.cryptography.keccak import keccak256

    return [keccak256(str(n).encode()) for n in range(max(0, number - 256), number)]


def _environment(env: dict) -> bytes:
    """The nine fields of the block that a run reads, with 0 for a field the fork lacks."""
    from ethlib.serialization import rlp

    random = int(env.get("currentRandom", "0x0"), 16).to_bytes(32, "big")
    return rlp.encode([
        _hex(env["currentCoinbase"]), _scalar(env["currentGasLimit"]),
        _scalar(env["currentNumber"]), _scalar(env["currentTimestamp"]),
        _scalar(env["currentDifficulty"]), _scalar(env.get("currentBaseFee", "0x0")), random,
        _scalar(env.get("currentExcessBlobGas", "0x0")),
        _block_hashes(int(env["currentNumber"], 16))])


def _accounts(accounts: list) -> dict:
    """The accounts of a run, by address, in the form of the post state of a fixture."""
    return {"0x" + address.hex(): {
        "nonce": int.from_bytes(nonce, "big"), "balance": int.from_bytes(balance, "big"),
        "code": "0x" + code.hex(),
        "storage": {int.from_bytes(k, "big"): int.from_bytes(v, "big") for k, v in storage}}
        for address, nonce, balance, code, storage in accounts}


def _expected_accounts(state: dict) -> dict:
    return {address: {
        "nonce": int(a["nonce"], 16), "balance": int(a["balance"], 16), "code": a["code"],
        "storage": {int(k, 16): int(v, 16) for k, v in a["storage"].items() if int(v, 16)}}
        for address, a in state.items()}


def _state_diff(got: dict, expected: dict) -> list:
    """The accounts where a run and a fixture differ, for the message of a failure."""
    return [(address, got.get(address), expected.get(address))
            for address in sorted(set(got) | set(expected))
            if got.get(address) != expected.get(address)]


def _state_test(root: Path, case: Case) -> None:
    from ethlib.execution import transactions

    fixture = _fixtures(root / case.path)[case.id]
    (post,) = fixture["post"][case.fork]
    fork = FORK_OF_NETWORK[case.fork]
    args = (fork, int(fixture["config"]["chainid"], 16), _hex(post["txbytes"]),
            _pre_state(fixture["pre"]), _environment(fixture["env"]))
    if "expectException" in post:
        with pytest.raises(ValueError) as error:
            transactions.run(*args)
        expected = post["expectException"].split("|")
        assert any(names_in_block(e, str(error.value)) for e in expected), \
            (expected, str(error.value))
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
_BLOCK_FORKS = ["frontier", "homestead", "tangerineWhistle", "spuriousDragon", "byzantium",
                "constantinople", "petersburg", "istanbul", "berlin", "london", "paris"]
_TIME_FORKS = ["shapella", "dencun", "pectra", "fusaka", "bpo1", "bpo2"]
_NETWORK_FORK = {**FORK_OF_NETWORK, "BPO1": "bpo1", "BPO2": "bpo2"}

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
    "INCORRECT_BLOCK_FORMAT": r"block rejected",
}


def names_block_error(exception: str, message: str) -> bool:
    """Whether an error message of the state transition names a fixture exception."""
    kind, _, name = exception.partition(".")
    if kind == "BlockException":
        return name in _BLOCK_EXCEPTIONS and re.search(_BLOCK_EXCEPTIONS[name], message) is not None
    return names_in_block(exception, message)


def chain_of(fixture: dict) -> tuple[dict, list]:
    """The chain configuration of a blockchain test, and its activations as tuples."""
    before, _, after = fixture["network"].removesuffix("AtTime15k").partition("To")
    first = _NETWORK_FORK[before]
    forks = _BLOCK_FORKS + _TIME_FORKS
    activations = [(fork, "block" if fork in _BLOCK_FORKS else "time", 0)
                   for fork in forks[:forks.index(first) + 1]]
    if after:
        activations.append((_NETWORK_FORK[after], "time", 15_000))
    # The fixture names each blob schedule by its network, which gives its activation.
    schedules = []
    for network, schedule in fixture["config"].get("blobSchedule", {}).items():
        for fork, kind, number in activations:
            if fork == _NETWORK_FORK.get(network, network.lower()):
                schedules.append([kind, number, int(schedule["target"], 16),
                                  int(schedule["max"], 16),
                                  int(schedule["baseFeeUpdateFraction"], 16)])
    config = {"chainId": int(fixture["config"]["chainid"], 16),
              "activations": [list(a) for a in activations],
              "blobSchedules": sorted(schedules, key=lambda s: s[1])}
    return config, activations


def active_fork(activations: list, header: list) -> str:
    """The fork of a header: the last one whose activation its number or its time reached."""
    number, timestamp = int.from_bytes(header[8], "big"), int.from_bytes(header[11], "big")
    reached = [fork for fork, kind, n in activations
               if (number if kind == "block" else timestamp) >= n]
    return reached[-1]


def genesis_of(fork: str, header: dict, pre: dict) -> bytes:
    """The genesis block of a chain, from its header in the JSON of a fixture and its state."""
    from ethlib.execution import blocks

    def number(name: str, default: int = 0) -> int:
        return int(header[name], 16) if name in header else default

    return blocks.genesis_block(
        fork, _pre_state(pre), coinbase=_hex(header["coinbase"]),
        difficulty=number("difficulty"), gas_limit=number("gasLimit"),
        timestamp=number("timestamp"), extra_data=_hex(header["extraData"]),
        mix_hash=_hex(header["mixHash"]), nonce=_hex(header["nonce"]),
        base_fee=number("baseFeePerGas", blocks.INITIAL_BASE_FEE),
        excess_blob_gas=number("excessBlobGas"), slot_number=number("slotNumber"))


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
    assert genesis_of(recent[0][0], fixture["genesisBlockHeader"], fixture["pre"]) == \
        _hex(fixture["genesisRLP"])
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
            assert any(names_block_error(e, str(error.value)) for e in names), \
                (names, str(error.value))
            continue
        _, accounts = blocks.state_transition(config, state, recent, fork, raw, seal)
        state = rlp.encode(accounts)
        recent = (recent + [(fork, rlp.encode(item[0]), [rlp.encode(o) for o in item[2]])])[-256:]
    assert "0x" + keccak256(recent[-1][1]).hex() == fixture["lastblockhash"]


# The fields of a header in the order of its RLP form; a header holds those of its fork.
HEADER_FIELDS = ["parentHash", "uncleHash", "coinbase", "stateRoot", "transactionsTrie",
                 "receiptTrie", "bloom", "difficulty", "number", "gasLimit", "gasUsed",
                 "timestamp", "extraData", "mixHash", "nonce", "baseFeePerGas", "withdrawalsRoot",
                 "blobGasUsed", "excessBlobGas", "parentBeaconBlockRoot", "requestsHash"]

# The fields that are numbers, which RLP writes without leading zeros.
NUMBERS = {"difficulty", "number", "gasLimit", "gasUsed", "timestamp", "baseFeePerGas",
           "blobGasUsed", "excessBlobGas"}


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
    from ethlib.serialization import rlp

    from ethlib import engine

    config, _ = chain_of(fixture)
    method = f"engine_newPayloadV{payload['newPayloadVersion']}"
    if "errorCode" in payload:
        with pytest.raises(engine.EngineError) as error:
            engine.new_payload_on_chain(config, state, recent, method, payload["params"])
        assert -error.value.code == int(payload["errorCode"])
        return "error", state, recent
    status, header, accounts = engine.new_payload_on_chain(config, state, recent, method,
                                                           payload["params"])
    expected = payload.get("validationError")
    if not expected:
        assert status["status"] == "VALID", status
        assert status["latestValidHash"] == payload["params"][0]["blockHash"]
        fork = active_fork(chain_of(fixture)[1], rlp.decode(header))
        return "valid", rlp.encode(accounts), (recent + [(fork, header, [])])[-256:]
    names = expected.split("|")
    code, _, message = status["validationError"].partition(": ")
    if int(code) == 405:
        assert status["status"] == "INVALID", status
        assert any(names_block_error(e, message) for e in names), (status, names)
        return "execution", state, recent
    assert ENGINE_EXCEPTIONS[int(code)] & set(names), (status, names)
    return "invalid", state, recent


def run_engine_chain(fixture: dict, pre: dict, genesis: dict) -> Counter:
    """Run every payload of an engine fixture on its chain; return the kind of each outcome."""
    from ethlib.cryptography.keccak import keccak256
    from ethlib.serialization import rlp

    header = _header_of_json(genesis)
    assert "0x" + keccak256(header).hex() == genesis["hash"]
    state = _pre_state(pre)
    recent = [(active_fork(chain_of(fixture)[1], rlp.decode(header)), header, [])]
    assert rlp.encode(rlp.decode(genesis_of(recent[0][0], genesis, pre))[0]) == header
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
    shared = _fixtures(directory / "pre_alloc" / f"{fixture['preHash']}.json")
    run_engine_chain(fixture, shared["pre"], shared["genesis"])


def _shuffle(root: Path, case: Case) -> None:
    from ethlib import consensus

    vector = _yaml(root / case.path / "mapping.yaml")
    seed = bytes.fromhex(vector["seed"].removeprefix("0x"))
    assert consensus.compute_shuffled_permutation(vector["count"], seed, case.preset) == \
        vector["mapping"]


def _custody_groups(root: Path, case: Case) -> None:
    from ethlib import consensus

    meta = _yaml(root / case.path / "meta.yaml")
    groups = consensus.get_custody_groups(int(meta["node_id"]), meta["custody_group_count"],
                                          case.preset)
    assert groups == meta["result"]


def _custody_columns(root: Path, case: Case) -> None:
    from ethlib import consensus

    meta = _yaml(root / case.path / "meta.yaml")
    assert consensus.compute_columns_for_custody_group(meta["custody_group"], case.preset) == \
        meta["result"]


def _gossip_data_column_sidecar(root: Path, case: Case) -> None:
    from consensus.test_data_column import run_gossip_case

    run_gossip_case(root / case.path, case.preset)


def _gossip_partial_data_column_sidecar(root: Path, case: Case) -> None:
    from consensus.test_partial_data_column import run_partial_gossip_case

    run_partial_gossip_case(root / case.path, case.preset)


def _ssz_static(root: Path, case: Case) -> None:
    from ethlib import consensus
    from ethlib.networking import snappy

    container = case.group.split("/")[1]
    data = snappy.decompress((root / case.path / "serialized.ssz_snappy").read_bytes())
    expected = _yaml(root / case.path / "roots.yaml")["root"]
    got_root, encoded = consensus.ssz_static(case.preset, CONSENSUS_FORK[case.fork], container,
                                             data)
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

    # tests/<preset>/<fork>/fork_choice/<handler>/<suite>/<case>
    run_case(case.preset, case.fork, root / case.path)


def _upgrade(root: Path, case: Case) -> None:
    from consensus.test_fork import run_case

    # tests/<preset>/<fork>/fork/fork/<suite>/<case>
    run_case(case.preset, case.fork, root / case.path)


def _container_forks(container: str) -> tuple[str, ...]:
    first, dropped = CONTAINERS[container]
    forks = list(CONSENSUS_FORK)
    return tuple(forks[forks.index(first):forks.index(dropped) if dropped else len(forks)])


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
    # The checks of the sidecar alone; the checks that read the store come with C63.
    "networking/gossip_data_column_sidecar": _gossip_data_column_sidecar,
    # The checks of a partial message that read no store; the others wait for C63.
    "networking/gossip_partial_data_column_sidecar": _gossip_partial_data_column_sidecar,
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
    **{f"fork_choice/{handler}": _fork_choice for handler in FORK_CHOICE},
    **{group: _transition for group in TRANSITION_GROUPS},
    "legacy_ommers": legacy.run_ommers,
    "legacy_dao": legacy.run_dao,
}


# The runners that stop before a fork, with the first fork that they do not run.
# Processing a transaction is not yet specified from Amsterdam on.
# The partial column checks read the forms of Fulu.
_STOPS = {
    "state_test": "BPO2ToAmsterdamAtTime15k",
    "blockchain_test": "BPO2ToAmsterdamAtTime15k",
    "blockchain_test_engine": "BPO2ToAmsterdamAtTime15k",
    "blockchain_test_engine_x": "BPO2ToAmsterdamAtTime15k",
    "networking/gossip_partial_data_column_sidecar": "gloas",
}


def _stopped(case: Case) -> bool:
    stop = _STOPS.get(case.group)
    if stop is None:
        return False
    forks = (EXECUTION_FORKS if case.suite == "execution-spec-tests" else CONSENSUS_FORKS)
    return case.rank >= forks.index(stop)


def runner(case: Case):
    """The runner of a case, or `None` if EthLib cannot run it yet."""
    if _stopped(case):
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
    if run is _fork_choice and not runs_fork_choice(case.fork, case.group.split("/")[1]):
        return None
    if run is _transition and not runs_transition(case.fork, case.group):
        return None
    return run


def plan(case: Case) -> str | None:
    """The plan for a case that no runner covers: its fork's entry first, then the general one."""
    for table in (NOT_YET_AT.get(case.fork, {}), NOT_YET):
        if entry := table.get(case.group) or table.get(case.group.split("/")[0]):
            return entry
    return None
