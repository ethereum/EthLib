"""The presets, configurations and parameters of EthLib against the files of consensus-specs.

The files are the mainnet and minimal presets from Phase 0 to Fulu, and the two configurations.
They are copied byte for byte from ethereum/consensus-specs, at the pin that `tests/sources.toml`
records, into `tests/consensus/parameters/`, and `SHA256SUMS` there fixes their digests.
"""

import hashlib
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "parameters"

PRESETS = ("mainnet", "minimal")

# The forks of the beacon chain up to Fulu, in order, as consensus-specs names them.
FORKS = ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu")

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
}

# The preset values that a fork replaces. A replacement carries the name of its fork as a suffix,
# such as INACTIVITY_PENALTY_QUOTIENT_ALTAIR, in the preset file of that fork.
REPLACED = (
    "INACTIVITY_PENALTY_QUOTIENT",
    "MIN_SLASHING_PENALTY_QUOTIENT",
    "PROPORTIONAL_SLASHING_MULTIPLIER",
    "WHISTLEBLOWER_REWARD_QUOTIENT",
    "MAX_ATTESTER_SLASHINGS",
    "MAX_ATTESTATIONS",
)

# A suffixed preset value that is a new value, not a replacement: from Electra, the largest
# effective balance of a compounding validator. MIN_ACTIVATION_BALANCE takes the other role of
# MAX_EFFECTIVE_BALANCE.
NEW_WITH_SUFFIX = {"MAX_EFFECTIVE_BALANCE_ELECTRA"}

# Configuration values that EthLib does not hold in the configuration.
# The gossip message ID defines the two message domains as constants.
# The rest belong to Gloas and Heze, the forks after Fulu.
NOT_IN_CONFIG = {
    "MESSAGE_DOMAIN_INVALID_SNAPPY",
    "MESSAGE_DOMAIN_VALID_SNAPPY",
    "GLOAS_FORK_VERSION",
    "GLOAS_FORK_EPOCH",
    "HEZE_FORK_VERSION",
    "HEZE_FORK_EPOCH",
    "MIN_BUILDER_WITHDRAWABILITY_DELAY",
    "ATTESTATION_DUE_BPS_GLOAS",
    "AGGREGATE_DUE_BPS_GLOAS",
    "SYNC_MESSAGE_DUE_BPS_GLOAS",
    "CONTRIBUTION_DUE_BPS_GLOAS",
    "PAYLOAD_DUE_BPS",
    "PAYLOAD_ATTESTATION_DUE_BPS",
    "INCLUSION_LIST_DUE_BPS",
    "CHURN_LIMIT_QUOTIENT_GLOAS",
    "CONSOLIDATION_CHURN_LIMIT_QUOTIENT",
    "MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS",
    "MAX_REQUEST_PAYLOADS",
    "MAX_REQUEST_INCLUSION_LIST",
    "MAX_BYTES_PER_INCLUSION_LIST",
}


def _load(relative: str) -> dict:
    # The base loader reads every scalar as text, so hex keeps its length and its leading zeros.
    return YAML(typ="base").load((FILES / relative).read_text(encoding="utf-8"))


def _canonical(value):
    """A value as text that compares equal across YAML and the exports."""
    if isinstance(value, list):
        return [_canonical(item) for item in value]
    if isinstance(value, dict):
        return {key: _canonical(item) for key, item in value.items()}
    if isinstance(value, int):
        return str(value)
    if value.startswith("0x"):
        return value.lower()
    if value.isdigit():
        return str(int(value))
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
    assert _canonical(consensus.preset(name)) == _canonical(expected)


@pytest.mark.parametrize("name", PRESETS)
def test_suffixes_are_known(name: str) -> None:
    # A suffixed value is either a replacement listed above or a new value.
    suffixes = tuple("_" + fork.upper() for fork in FORKS)
    suffixed = {key for values in _preset_files(name).values() for key in values
                if key.endswith(suffixes)}
    replacements = {key for key in suffixed if key.rsplit("_", 1)[0] in REPLACED}
    assert suffixed - replacements == NEW_WITH_SUFFIX


@pytest.mark.parametrize("name", PRESETS)
@pytest.mark.parametrize("fork", TIMELINE)
def test_parameters(name: str, fork: str) -> None:
    files = _preset_files(name)
    expected = {}
    for key in REPLACED:
        # The value in force is the one of the latest fork up to this one that names it.
        expected[key] = files["phase0"][key]
        for earlier in FORKS[1:FORKS.index(TIMELINE[fork]) + 1]:
            replacement = f"{key}_{earlier.upper()}"
            if replacement in files[earlier]:
                expected[key] = files[earlier][replacement]
    assert _canonical(consensus.parameters(name, fork)) == _canonical(expected)


@pytest.mark.parametrize("name", PRESETS)
def test_config(name: str) -> None:
    source = _load(f"configs/{name}.yaml")
    assert NOT_IN_CONFIG <= set(source)
    expected = {key: value for key, value in source.items() if key not in NOT_IN_CONFIG}
    assert _canonical(consensus.config(name)) == _canonical(expected)


def test_unknown_names_are_rejected() -> None:
    with pytest.raises(ValueError):
        consensus.preset("holesky")
    with pytest.raises(ValueError):
        consensus.config("holesky")
    with pytest.raises(ValueError):
        consensus.parameters("mainnet", "frontier")
