"""The light client sync and update ranking vectors of consensus-specs."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy

from .containers import FORKS
from .test_data_column import replacements

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "light_client"

# The forks whose light client containers EthLib defines; those of Gloas are not yet.
SPECIFIED = ["altair", "bellatrix", "capella", "deneb", "electra", "fulu"]

# The fork whose light client containers each fork uses.
SHAPE = {"altair": "altair", "bellatrix": "altair", "capella": "capella", "deneb": "deneb",
         "electra": "electra", "fulu": "electra"}

_YAML = YAML(typ="safe")


def runs_sync(fork: str, name: str) -> bool:
    """Whether a sync case keeps one fork throughout, so it needs no upgrade of the store."""
    # A case of a fork transition, or of a store of a later fork, upgrades its data first.
    return fork in SPECIFIED and not name.endswith(("_fork", "_store_with_legacy_data"))


def _read(case: Path, name: str) -> bytes:
    return snappy.decompress((case / f"{name}.ssz_snappy").read_bytes())


def _hex(text: str) -> bytes:
    return bytes.fromhex(text[2:])


def _fork_digests(case_config: dict, preset: str, fork: str, root: bytes,
                  config: dict | None) -> set:
    """The digests that a fork takes over its epochs, which change at each blob schedule entry."""
    first = case_config.get(f"{fork.upper()}_FORK_EPOCH", 0)
    later = [case_config.get(f"{name.upper()}_FORK_EPOCH") for name in SPECIFIED[1:] + ["gloas"]]
    end = min([epoch for epoch in later if epoch is not None and epoch > first], default=2 ** 64)
    epochs = {first} | {entry["EPOCH"] for entry in case_config.get("BLOB_SCHEDULE", [])
                        if first < entry["EPOCH"] < end}
    return {"0x" + consensus.compute_fork_digest(preset, root, epoch, config).hex()
            for epoch in epochs}


def run_sync_case(case: Path, preset: str, fork: str) -> None:
    """Sync a store from the bootstrap of a case, and compare its headers after each step."""
    meta = _YAML.load((case / "meta.yaml").read_text())
    steps = _YAML.load((case / "steps.yaml").read_text())
    config_file = case / "config.yaml"
    case_config = _YAML.load(config_file.read_text()) if config_file.exists() else {}
    config = replacements(case_config, preset) if case_config else None
    root = _hex(meta["genesis_validators_root"])
    # The bootstrap and every update carry a digest of the fork of the case.
    digests = _fork_digests(case_config, preset, fork, root, config)
    assert meta["bootstrap_fork_digest"] in digests
    # The store uses the light client containers of the fork of the case.
    # YAML reads the unquoted versions of the configuration as integers.
    versions = {case_config.get(f"{name.upper()}_FORK_VERSION"): name for name in SPECIFIED}
    store_fork = versions.get(int(meta["store_fork_version"], 16))
    assert store_fork is not None and SHAPE[store_fork] == SHAPE[fork]
    inputs, checks = [], []
    for step in steps:
        (kind, body), = step.items()
        if kind == "process_update":
            assert body["update_fork_digest"] in digests
            inputs.append((body["current_slot"], _read(case, body["update"])))
        else:
            assert kind == "force_update"
            inputs.append((body["current_slot"], None))
        checks.append(body["checks"])
    headers = consensus.light_client_sync(preset, FORKS[fork], _hex(meta["trusted_block_root"]),
                                          root, _read(case, "bootstrap"), inputs, config)
    assert len(headers) == len(checks)
    for (finalized, optimistic), expected in zip(headers, checks):
        for (slot, beacon, execution), want in ((finalized, expected["finalized_header"]),
                                                (optimistic, expected["optimistic_header"])):
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
        for second in updates[i + 1:]:
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
            cases.append(pytest.param(preset, fork, case,
                                      id=case.relative_to(FILES).as_posix()))
    return cases


@pytest.mark.parametrize("preset, fork, case", _cases("sync"))
def test_sync_case(preset, fork, case):
    run_sync_case(case, preset, fork)


@pytest.mark.parametrize("preset, fork, case", _cases("update_ranking"))
def test_ranking_case(preset, fork, case):
    run_ranking_case(case, preset, fork)


def test_every_fork_has_cases():
    for handler, per_fork in (("sync", 4), ("update_ranking", 1)):
        forks = [param.values[1] for param in _cases(handler)]
        assert {fork: forks.count(fork) for fork in SPECIFIED} == dict.fromkeys(SPECIFIED, per_fork)
