"""The light client sync and update ranking vectors of consensus-specs."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "light_client"

# The forks that have a light client.
SPECIFIED = ["altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze"]

# The fork whose light client containers each fork uses.
SHAPE = {
    "altair": "altair",
    "bellatrix": "altair",
    "capella": "capella",
    "deneb": "deneb",
    "electra": "electra",
    "fulu": "electra",
    "gloas": "gloas",
    "heze": "gloas",
}

_YAML = YAML(typ="safe")


def store_fork(version_fork: str, fork: str) -> str:
    """The fork of a store: a version names the fork of its containers, shared by later forks."""
    if SHAPE[version_fork] == SHAPE[fork] and SPECIFIED.index(fork) > SPECIFIED.index(version_fork):
        return fork
    return version_fork


def runs_sync(fork: str, name: str) -> bool:
    """Whether EthLib runs a sync case: every case from Altair."""
    return fork in SPECIFIED


def _read(case: Path, name: str) -> bytes:
    return snappy.decompress((case / f"{name}.ssz_snappy").read_bytes())


def _hex(text: str) -> bytes:
    return bytes.fromhex(text[2:])


def fork_digests(case_config: dict, preset: str, root: bytes, config: dict | None) -> dict:
    """The fork of each digest that a fork takes over its epochs, from Altair."""
    # From Fulu the digest also changes at each blob schedule entry.
    starts = {fork: case_config[f"{fork.upper()}_FORK_EPOCH"] for fork in SPECIFIED}
    digests = {}
    for fork in SPECIFIED:
        first = starts[fork]
        end = min([epoch for epoch in starts.values() if epoch > first], default=2**64)
        epochs = {first} | {
            entry["EPOCH"] for entry in case_config["BLOB_SCHEDULE"] if first < entry["EPOCH"] < end
        }
        for epoch in epochs:
            digest = consensus.compute_fork_digest(preset, root, epoch, config)
            # Two forks that start at one epoch share its digest, which the later one takes.
            digests["0x" + digest.hex()] = fork
    return digests


def case_config(case: Path, preset: str) -> tuple[dict, dict | None]:
    """The configuration of a case with the named one under it, and the case's replacements."""
    config_file = case / "config.yaml"
    values = _YAML.load(config_file.read_text()) if config_file.exists() else {}
    return {**consensus.config(preset), **values}, replacements(values, preset) if values else None


def version(value: int | str) -> int:
    """A fork version, which YAML reads as an integer and the named configuration as hex."""
    return int(value, 16) if isinstance(value, str) else value


def run_sync_case(case: Path, preset: str, fork: str) -> None:
    """Sync a store from the bootstrap of a case, and compare its headers after each step."""
    meta = _YAML.load((case / "meta.yaml").read_text())
    steps = _YAML.load((case / "steps.yaml").read_text())
    values, config = case_config(case, preset)
    root = _hex(meta["genesis_validators_root"])
    # Each digest names the fork of the data that it marks.
    digests = fork_digests(values, preset, root, config)
    # YAML reads the unquoted versions of the configuration as integers.
    versions = {version(values[f"{name.upper()}_FORK_VERSION"]): name for name in SPECIFIED}
    start = store_fork(versions[int(meta["store_fork_version"], 16)], fork)
    inputs, checks = [], []
    for step in steps:
        ((kind, body),) = step.items()
        if kind == "process_update":
            inputs.append(
                (
                    "update",
                    FORKS[digests[body["update_fork_digest"]]],
                    body["current_slot"],
                    _read(case, body["update"]),
                )
            )
        elif kind == "force_update":
            inputs.append(("force", body["current_slot"]))
        else:
            assert kind == "upgrade_store"
            target = store_fork(versions[int(body["store_fork_version"], 16)], fork)
            inputs.append(("upgrade", FORKS[target]))
        checks.append(body["checks"])
    headers = consensus.light_client_sync(
        preset,
        FORKS[start],
        FORKS[digests[meta["bootstrap_fork_digest"]]],
        _hex(meta["trusted_block_root"]),
        root,
        _read(case, "bootstrap"),
        inputs,
        config,
    )
    assert len(headers) == len(checks)
    for (finalized, optimistic), expected in zip(headers, checks, strict=True):
        for (slot, beacon, execution), want in (
            (finalized, expected["finalized_header"]),
            (optimistic, expected["optimistic_header"]),
        ):
            assert slot == want["slot"]
            assert "0x" + beacon.hex() == want["beacon_root"]
            if "execution_root" in want:
                assert "0x" + execution.hex() == want["execution_root"]


def run_ranking_case(case: Path, preset: str, fork: str) -> None:
    """Check that no update of a ranking case ranks above an update listed before it."""
    count = _YAML.load((case / "meta.yaml").read_text())["updates_count"]
    updates = [_read(case, f"updates_{index}") for index in range(count)]
    better = 0
    for i, first in enumerate(updates):
        for second in updates[i + 1 :]:
            assert not consensus.is_better_update(preset, FORKS[fork], second, first)
            better += consensus.is_better_update(preset, FORKS[fork], first, second)
    # The order is not only ties: most pairs rank strictly.
    assert better > 0


def _cases(handler: str) -> list:
    """Every vendored case of a handler that EthLib runs, as its preset, fork and directory."""
    cases = []
    for meta in sorted(FILES.rglob(f"light_client/{handler}/pyspec_tests/*/meta.yaml")):
        case = meta.parent
        preset, fork = case.relative_to(FILES).parts[:2]
        if handler != "sync" or runs_sync(fork, case.name):
            cases.append(pytest.param(preset, fork, case, id=case.relative_to(FILES).as_posix()))
    return cases


@pytest.mark.parametrize("preset, fork, case", _cases("sync"))
def test_sync_case(preset, fork, case):
    run_sync_case(case, preset, fork)


@pytest.mark.parametrize("preset, fork, case", _cases("update_ranking"))
def test_ranking_case(preset, fork, case):
    run_ranking_case(case, preset, fork)


def test_every_fork_has_cases():
    # Each fork to Gloas has its four single-fork sync cases, and the earlier ones add upgrades.
    # Heze has no case of its own.
    counts = {
        "altair": 8,
        "bellatrix": 11,
        "capella": 10,
        "deneb": 8,
        "electra": 5,
        "fulu": 6,
        "gloas": 4,
        "heze": 0,
    }
    rankings = {**dict.fromkeys(SPECIFIED, 1), "heze": 0}
    for handler, per_fork in (("sync", counts), ("update_ranking", rankings)):
        forks = [param.values[1] for param in _cases(handler)]
        assert {fork: forks.count(fork) for fork in SPECIFIED} == per_fork
