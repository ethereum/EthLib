"""The Beacon API answers on the configuration and the genesis, against consensus-specs files."""

from collections.abc import Callable

import pytest

from ethlib import consensus
from raising import raises

from .test_parameters import FORKS, NOT_IN_CONFIG, PRESETS, _load

# The version and epoch names of each fork from Altair, in the order of the schedule.
SCHEDULED = ("ALTAIR", "BELLATRIX", "CAPELLA", "DENEB", "ELECTRA", "FULU", "GLOAS", "HEZE")


def _api_form(value):
    """A YAML value as the spec map writes it: text as it is, with hex in lowercase."""
    if isinstance(value, list):
        return [_api_form(item) for item in value]
    if isinstance(value, dict):
        return {key: _api_form(item) for key, item in value.items()}
    return value.lower() if value.startswith("0x") else value


@pytest.mark.parametrize("name", PRESETS)
def test_spec_map_is_the_files(name: str) -> None:
    expected = {}
    for fork in FORKS:
        expected.update(_load(f"presets/{name}/{fork}.yaml"))
    source = _load(f"configs/{name}.yaml")
    expected.update({key: value for key, value in source.items() if key not in NOT_IN_CONFIG})
    assert consensus.api_spec(name) == _api_form(expected)


def test_spec_map_example() -> None:
    """Known values of the mainnet map, written apart from the conversion of the files."""
    spec = consensus.api_spec("mainnet")
    assert spec["SLOTS_PER_EPOCH"] == "32"
    assert spec["GENESIS_FORK_VERSION"] == "0x00000000"
    assert spec["DEPOSIT_CHAIN_ID"] == "1"
    assert spec["PRESET_BASE"] == "mainnet"
    assert spec["TERMINAL_TOTAL_DIFFICULTY"] == "58750000000000000000000"
    assert spec["BLOB_SCHEDULE"] == [
        {"EPOCH": "412672", "MAX_BLOBS_PER_BLOCK": "15"},
        {"EPOCH": "419072", "MAX_BLOBS_PER_BLOCK": "21"},
    ]


def test_spec_map_follows_replacements() -> None:
    spec = consensus.api_spec("minimal", {"ALTAIR_FORK_EPOCH": 7})
    assert spec["ALTAIR_FORK_EPOCH"] == "7"


@pytest.mark.parametrize("name", PRESETS)
def test_fork_schedule_is_the_configuration(name: str) -> None:
    config = _load(f"configs/{name}.yaml")
    genesis = config["GENESIS_FORK_VERSION"].lower()
    expected = [{"previous_version": genesis, "current_version": genesis, "epoch": "0"}]
    for fork in SCHEDULED:
        expected.append(
            {
                "previous_version": expected[-1]["current_version"],
                "current_version": config[f"{fork}_FORK_VERSION"].lower(),
                "epoch": config[f"{fork}_FORK_EPOCH"],
            }
        )
    assert consensus.api_fork_schedule(name) == expected


def test_fork_schedule_deneb_entry() -> None:
    deneb = consensus.api_fork_schedule("mainnet")[4]
    assert deneb == {
        "previous_version": "0x03000000",
        "current_version": "0x04000000",
        "epoch": "269568",
    }


def test_fork_schedule_follows_replacements() -> None:
    schedule = consensus.api_fork_schedule("mainnet", {"GLOAS_FORK_EPOCH": 500000})
    assert schedule[7]["epoch"] == "500000"


@pytest.mark.parametrize("name", PRESETS)
def test_deposit_contract(name: str) -> None:
    config = _load(f"configs/{name}.yaml")
    assert consensus.api_deposit_contract(name) == {
        "chain_id": config["DEPOSIT_CHAIN_ID"],
        "address": config["DEPOSIT_CONTRACT_ADDRESS"].lower(),
    }


def test_deposit_contract_mainnet() -> None:
    assert consensus.api_deposit_contract("mainnet") == {
        "chain_id": "1",
        "address": "0x00000000219ab540356cbb839cbe05303d7705fa",
    }


def test_deposit_contract_follows_replacements() -> None:
    assert consensus.api_deposit_contract("minimal", {"DEPOSIT_CHAIN_ID": 5})["chain_id"] == "5"


@pytest.mark.parametrize("name", PRESETS)
def test_genesis_reads_the_state(name: str) -> None:
    """The time and the root are fields of the state, set here to values that nothing else holds."""
    state = consensus.initialize_genesis(name, "phase0", bytes(range(32)), 1_600_000_000, [])
    document = consensus.api_json(name, "phase0", "BeaconState", state)
    document["genesis_time"] = "1234567"
    document["genesis_validators_root"] = "0x" + "ab" * 32
    document["fork"]["current_version"] = "0xdeadbeef"
    edited = consensus.api_ssz(name, "phase0", "BeaconState", document)
    # The version is the one of the configuration, not the one that the state holds.
    assert consensus.api_genesis(name, "phase0", edited) == {
        "genesis_time": "1234567",
        "genesis_validators_root": "0x" + "ab" * 32,
        "genesis_fork_version": _load(f"configs/{name}.yaml")["GENESIS_FORK_VERSION"].lower(),
    }
    replaced = consensus.api_genesis(name, "phase0", edited, {"GENESIS_FORK_VERSION": "0x0000abcd"})
    assert replaced["genesis_fork_version"] == "0x0000abcd"


@pytest.mark.parametrize(
    ("answer", "message"),
    [
        (consensus.api_spec, "no preset is named holesky"),
        (consensus.api_fork_schedule, "no configuration is named holesky"),
        (consensus.api_deposit_contract, "no configuration is named holesky"),
    ],
)
def test_unknown_name(answer: Callable[[str], object], message: str) -> None:
    with raises(consensus.ConsensusError, message) as error:
        answer("holesky")
    assert error.value.code == 0


def test_genesis_of_bytes_that_are_no_state() -> None:
    message = "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 7057 1"
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_genesis("minimal", "phase0", b"\x00")
    assert error.value.code == 0
