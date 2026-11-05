"""The runner of each group of cases that EthLib can run, and the plan for every other group."""

import json
from functools import cache
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from consensus.containers import CONTAINERS
from consensus.containers import FORKS as CONSENSUS_FORK
from transactions.test_transactions import CHAIN_ID, FORK_OF_NETWORK, names

from . import legacy
from .catalogue import Case

# The groups that no runner covers yet, with the pull requests of the plan that bring them.
# A key is a runner, or a runner and a handler, of consensus-spec-tests, or a format of
# execution-spec-tests.
NOT_YET = {
    "state_test": "EVM message call and gas settlement (E2 to E21), then T18",
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
    "merkle_proof": "Merkle proofs of the beacon state (consensus track C54 to C56)",
    "networking": "gossip validation (consensus track C63 and C64)",
    "ssz_static": "the remaining beacon containers (consensus track C2, C6 to C12)",
}

_YAML = YAML(typ="safe")


def _yaml(path: Path):
    return _YAML.load(path.read_text())


@cache
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


def _container_forks(container: str) -> tuple[str, ...]:
    first, dropped = CONTAINERS[container]
    forks = list(CONSENSUS_FORK)
    return tuple(forks[forks.index(first):forks.index(dropped) if dropped else len(forks)])


# The runner of each group, by format or by runner and handler.
RUNNERS = {
    "transaction_test": _transaction,
    "shuffling/core": _shuffle,
    "networking/get_custody_groups": _custody_groups,
    "networking/compute_columns_for_custody_group": _custody_columns,
    # The checks of the sidecar alone; the checks that read the store come with C63.
    "networking/gossip_data_column_sidecar": _gossip_data_column_sidecar,
    **{f"ssz_static/{container}": _ssz_static for container in CONTAINERS},
    "light_client/single_merkle_proof": _single_merkle_proof,
    "legacy_header": legacy.run_headers,
}


def runner(case: Case):
    """The runner of a case, or `None` if EthLib cannot run it yet."""
    run = RUNNERS.get(case.group)
    if run is _ssz_static and case.fork not in _container_forks(case.group.split("/")[1]):
        return None
    return run


def plan(case: Case) -> str | None:
    """The plan for a case that no runner covers: its handler's entry, or else its runner's."""
    return NOT_YET.get(case.group) or NOT_YET.get(case.group.split("/")[0])
