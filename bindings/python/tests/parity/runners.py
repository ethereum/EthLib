"""The runner of each group of cases that EthLib can run, and the plan for every other group."""

import json
from functools import lru_cache
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from consensus.containers import CONTAINERS
from consensus.containers import FORKS as CONSENSUS_FORK
from consensus.test_operations import HANDLERS as OPERATIONS
from consensus.test_operations import runs as runs_operation
from transactions.test_inclusion_archive import names_in_block
from transactions.test_transactions import CHAIN_ID, FORK_OF_NETWORK, names

from . import legacy
from .catalogue import Case

# The groups that no runner covers yet, with the pull requests of the plan that bring them.
# A key is a runner, or a runner and a handler, of consensus-spec-tests, or a format of
# execution-spec-tests.
NOT_YET = {
    "blockchain_test": "block state transition (E36), then T19",
    "blockchain_test_engine": "the Engine API on the Engine layer (T26), after E36",
    "blockchain_test_engine_x": "the Engine API on the Engine layer (T26), after E36",
    "epoch_processing": "beacon state transition (consensus track C13 to C40)",
    "finality": "beacon state transition (consensus track C13 to C40)",
    "fork": "beacon state transition (consensus track C13 to C40)",
    "genesis": "beacon state transition (consensus track C13 to C40)",
    "operations": "beacon state transition (consensus track C13 to C40)",
    "random": "beacon state transition (consensus track C13 to C40)",
    "rewards": "beacon state transition (consensus track C13 to C40)",
    "sanity": "beacon state transition (consensus track C13 to C40)",
    "transition": "beacon state transition (consensus track C13 to C40)",
    "fork_choice": "fork choice (consensus track C43 to C50)",
    "fast_confirmation": "fast confirmation rule (consensus track, decision 9)",
    "sync": "optimistic sync (consensus track C48)",
    "light_client": "light client (consensus track C54 to C56)",
    "networking": "gossip validation (consensus track C63 and C64)",
    "ssz_static": "the remaining beacon containers (consensus track C2, C6 to C12)",
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


def _merkle_proof(root: Path, case: Case) -> None:
    from consensus.test_merkle_proof import run_case

    run_case(case.preset, case.fork, root / case.path)


def _operation(root: Path, case: Case) -> None:
    from consensus.test_operations import run_case

    # tests/<preset>/<fork>/operations/<handler>/<suite>/<case>
    run_case(case.preset, case.fork, case.group.split("/")[1], root / case.path)


def _container_forks(container: str) -> tuple[str, ...]:
    first, dropped = CONTAINERS[container]
    forks = list(CONSENSUS_FORK)
    return tuple(forks[forks.index(first):forks.index(dropped) if dropped else len(forks)])


# The runner of each group, by format or by runner and handler.
RUNNERS = {
    "transaction_test": _transaction,
    "state_test": _state_test,
    "shuffling/core": _shuffle,
    "networking/get_custody_groups": _custody_groups,
    "networking/compute_columns_for_custody_group": _custody_columns,
    # The checks of the sidecar alone; the checks that read the store come with C63.
    "networking/gossip_data_column_sidecar": _gossip_data_column_sidecar,
    **{f"ssz_static/{container}": _ssz_static for container in CONTAINERS},
    "light_client/single_merkle_proof": _single_merkle_proof,
    "merkle_proof/single_merkle_proof": _merkle_proof,
    "legacy_header": legacy.run_headers,
    **{f"operations/{handler}": _operation for handler in OPERATIONS},
    "legacy_ommers": legacy.run_ommers,
    "legacy_dao": legacy.run_dao,
}


def runner(case: Case):
    """The runner of a case, or `None` if EthLib cannot run it yet."""
    run = RUNNERS.get(case.group)
    if run is _ssz_static and case.fork not in _container_forks(case.group.split("/")[1]):
        return None
    if run is _operation and not runs_operation(case.fork, case.group.split("/")[1]):
        return None
    return run


def plan(case: Case) -> str | None:
    """The plan for a case that no runner covers: its handler's entry, or else its runner's."""
    return NOT_YET.get(case.group) or NOT_YET.get(case.group.split("/")[0])
