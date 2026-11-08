"""The presets, configurations and parameters of EthLib against the files of consensus-specs."""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.errors import SszError
from raising import raises

# The files are the mainnet and minimal presets from Phase 0 to Heze, and the two configurations.
# They are byte-for-byte copies from ethereum/consensus-specs, at the pin of `tests/sources.toml`.
# They sit in `tests/consensus/parameters/`, whose `SHA256SUMS` fixes their digests.

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "parameters"

PRESETS = ("mainnet", "minimal")

# The forks of the beacon chain up to Heze, in order, as consensus-specs names them.
FORKS = ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas", "heze")

# Each fork of the shared timeline from Phase 0 on, with the fork of the beacon chain in force.
TIMELINE = {
    "phase0": "phase0",
    "berlin": "phase0",
    "london": "phase0",
    "altair": "altair",
    "arrowGlacier": "altair",
    "grayGlacier": "altair",
    "bellatrix": "bellatrix",
    "paris": "bellatrix",
    "shapella": "capella",
    "dencun": "deneb",
    "pectra": "electra",
    "fusaka": "fulu",
    "bpo1": "fulu",
    "bpo2": "fulu",
    "glamsterdam": "gloas",
    "hegota": "heze",
}

# The preset values that a fork replaces.
# A replacement takes its fork's name as a suffix, such as INACTIVITY_PENALTY_QUOTIENT_ALTAIR.
# It sits in the preset file of that fork.
REPLACED = (
    "INACTIVITY_PENALTY_QUOTIENT",
    "MIN_SLASHING_PENALTY_QUOTIENT",
    "PROPORTIONAL_SLASHING_MULTIPLIER",
    "WHISTLEBLOWER_REWARD_QUOTIENT",
    "MAX_ATTESTER_SLASHINGS",
    "MAX_ATTESTATIONS",
    "MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE",
)

# A suffixed preset value that is a new value, not a replacement.
# From Electra, it is the largest effective balance of a compounding validator.
# MIN_ACTIVATION_BALANCE takes the other role of MAX_EFFECTIVE_BALANCE.
NEW_WITH_SUFFIX = {"MAX_EFFECTIVE_BALANCE_ELECTRA"}

# Configuration values that EthLib does not hold in the configuration.
# The gossip message ID defines the two message domains as constants.
# The rest belong to the feature forks of EIP-8198 and EIP-8321, which no fork schedules.
NOT_IN_CONFIG = {
    "MESSAGE_DOMAIN_INVALID_SNAPPY",
    "MESSAGE_DOMAIN_VALID_SNAPPY",
    "EIP8198_FORK_VERSION",
    "EIP8198_FORK_EPOCH",
    "SLOT_DURATION_MS_EIP8198",
    "MIN_BLOB_DATA_RETENTION_MS",
    "EIP8321_FORK_VERSION",
    "EIP8321_FORK_EPOCH",
}


def _load(relative: str) -> dict:
    # The base loader reads every scalar as text, so hex keeps its length and its leading zeros.
    return YAML(typ="base").load((FILES / relative).read_text(encoding="utf-8"))


def _canonical(value):
    """A YAML value in the form that the exports give: an int, lowercase hex, or text."""
    if isinstance(value, list):
        return [_canonical(item) for item in value]
    if isinstance(value, dict):
        return {key: _canonical(item) for key, item in value.items()}
    if value.startswith("0x"):
        return value.lower()
    if value.isdigit():
        return int(value)
    return value


def _preset_files(name: str) -> dict:
    return {fork: _load(f"presets/{name}/{fork}.yaml") for fork in FORKS}


def test_files_match_their_digests() -> None:
    lines = (FILES / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    listed = {}
    for line in lines:
        if not line.startswith("#"):
            digest, path = line.split("  ", 1)
            listed[path] = digest
    found = {p.relative_to(FILES).as_posix() for p in FILES.rglob("*.yaml")}
    assert set(listed) == found
    for path, digest in listed.items():
        assert hashlib.sha256((FILES / path).read_bytes()).hexdigest() == digest, path


@pytest.mark.parametrize("name", PRESETS)
def test_preset(name: str) -> None:
    expected = {}
    for values in _preset_files(name).values():
        expected.update(values)
    assert consensus.preset(name) == _canonical(expected)


@pytest.mark.parametrize("name", PRESETS)
def test_suffixes_are_known(name: str) -> None:
    # A suffixed value is either a replacement listed above or a new value.
    suffixes = tuple("_" + fork.upper() for fork in FORKS)
    suffixed = {
        key for values in _preset_files(name).values() for key in values if key.endswith(suffixes)
    }
    replacements = {key for key in suffixed if key.rsplit("_", 1)[0] in REPLACED}
    assert suffixed - replacements == NEW_WITH_SUFFIX


@pytest.mark.parametrize("name", PRESETS)
@pytest.mark.parametrize("fork", TIMELINE)
def test_parameters(name: str, fork: str) -> None:
    files = _preset_files(name)
    expected = {}
    for key in REPLACED:
        # The value in force is the one of the latest fork up to this one that names it.
        # Before the fork that adds a value, the value of that fork stands in.
        first = next(name for name in FORKS if key in files[name])
        expected[key] = files[first][key]
        for earlier in FORKS[FORKS.index(first) + 1 : FORKS.index(TIMELINE[fork]) + 1]:
            replacement = f"{key}_{earlier.upper()}"
            if replacement in files[earlier]:
                expected[key] = files[earlier][replacement]
    assert consensus.parameters(name, fork) == _canonical(expected)


@pytest.mark.parametrize("name", PRESETS)
def test_config(name: str) -> None:
    source = _load(f"configs/{name}.yaml")
    assert NOT_IN_CONFIG <= set(source)
    expected = {key: value for key, value in source.items() if key not in NOT_IN_CONFIG}
    assert consensus.config(name) == _canonical(expected)


def test_values_are_typed() -> None:
    """An integer comes back as an int, even past 64 bits, and a byte string as hex."""
    config = consensus.config("mainnet")
    assert config["TERMINAL_TOTAL_DIFFICULTY"] == 58750000000000000000000
    assert config["SLOT_DURATION_MS"] == 12000
    assert config["GENESIS_FORK_VERSION"] == "0x00000000"
    assert config["PRESET_BASE"] == "mainnet"
    assert consensus.preset("minimal")["SLOTS_PER_EPOCH"] == 8


def test_unknown_names_are_rejected() -> None:
    with raises(ValueError, "no preset is named holesky"):
        consensus.preset("holesky")
    with raises(ValueError, "no configuration is named holesky"):
        consensus.config("holesky")
    with raises(ValueError, "frontier is not a fork of the beacon chain"):
        consensus.parameters("mainnet", "frontier")


def test_name_must_be_text() -> None:
    """A name given as bytes is not read, and fails with code 0."""
    with raises(consensus.ConsensusError, "expected a str") as error:
        consensus.preset(b"mainnet")
    assert error.value.code == 0


@pytest.mark.parametrize("epoch", [0, "0"])
def test_replacement_as_int_or_digits(epoch: int | str) -> None:
    """A 64-bit replacement reads the same from an int and from its digits."""
    root = bytes(32)
    expected = consensus.compute_fork_digest("mainnet", root, 0, {"ALTAIR_FORK_EPOCH": 0})
    assert (
        consensus.compute_fork_digest("mainnet", root, 0, {"ALTAIR_FORK_EPOCH": epoch}) == expected
    )
    assert expected != consensus.compute_fork_digest("mainnet", root, 0)


def test_replacement_out_of_range() -> None:
    """A 64-bit replacement of 2^64 does not fit, and fails with code 0."""
    field = "EthLib.Consensus.Config.ALTAIR_FORK_EPOCH"
    message = f"configuration: {field}: {2**64} does not fit in 64 bits"
    with raises(SszError, message) as error:
        consensus.compute_fork_digest("mainnet", bytes(32), 0, {"ALTAIR_FORK_EPOCH": 2**64})
    assert error.value.code == 0
