"""The light client data collection vectors of consensus-specs, without the state transition."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy

from .containers import FORKS
from .test_light_client_sync import FILES, SPECIFIED, case_config, fork_digests

_YAML = YAML(typ="safe")

# The size of a beacon block header, the first field of a light client header.
BEACON = 112


def runs_data_collection(fork: str, name: str) -> bool:
    """Whether EthLib runs a data collection case: from Altair to Fulu, with no Gloas block."""
    return fork in SPECIFIED and "gloas" not in name


def _read(case: Path, name: str) -> bytes:
    return snappy.decompress((case / f"{name}.ssz_snappy").read_bytes())


def _uint(data: bytes) -> int:
    return int.from_bytes(data, "little")


class Shapes:
    """The sizes of the fields of the light client containers, for a preset and a fork."""

    def __init__(self, preset: str, fork: str):
        size = consensus.preset(preset)["SYNC_COMMITTEE_SIZE"]
        self.committee = size * 48 + 48
        self.aggregate = size // 8 + 96
        # From Capella a header has variable size; from Electra the state is one level deeper.
        self.variable = SPECIFIED.index(fork) >= SPECIFIED.index("capella")
        electra = SPECIFIED.index(fork) >= SPECIFIED.index("electra")
        self.committee_branch = 32 * (6 if electra else 5)
        self.finality_branch = 32 * (7 if electra else 6)
        self.slot = 8

    def split(self, data: bytes, fields: list) -> list:
        """The bytes of each field of a container; a field named `header` is a header."""
        sizes = [None if field == "header" else getattr(self, field) for field in fields]
        if not self.variable:
            sizes = [BEACON if size is None else size for size in sizes]
        parts, offsets, at = [], [], 0
        for size in sizes:
            if size is None:
                offsets.append(len(parts))
                parts.append(_uint(data[at:at + 4]))
                at += 4
            else:
                parts.append(data[at:at + size])
                at += size
        # Each variable field runs from its offset to the next offset, or to the end.
        ends = [parts[i] for i in offsets[1:]] + [len(data)]
        for i, end in zip(offsets, ends):
            parts[i] = data[parts[i]:end]
        return parts


class Chain:
    """The blocks of a case, with the light client header that EthLib derives from each."""

    def __init__(self, case: Path, preset: str):
        self.case, self.preset = case, preset
        self.values, self.config = case_config(case, preset)
        state = _read(case, "initial_state")
        root = state[8:40]
        self.digests = fork_digests(self.values, preset, root, self.config)
        self.genesis_validators_root = root
        # The block of the initial state is not in the case, so its header comes from the state.
        epoch = _uint(state[40:48]) // consensus.preset(preset)["SLOTS_PER_EPOCH"]
        state_fork = [fork for fork in SPECIFIED
                      if self.values[f"{fork.upper()}_FORK_EPOCH"] <= epoch][-1]
        latest = state[64:64 + BEACON]
        if not any(latest[48:80]):
            state_root = consensus.ssz_static(preset, FORKS[state_fork], "BeaconState", state)[0]
            latest = latest[:48] + state_root + latest[80:]
        self.headers = {self.beacon_root(latest): (None, latest)}
        self.slots = {}

    def beacon_root(self, beacon: bytes) -> bytes:
        return consensus.ssz_static(self.preset, FORKS["altair"], "BeaconBlockHeader", beacon)[0]

    def add_block(self, fork: str, name: str) -> None:
        """Derive the header of a block, and index it by its root and its slot."""
        root, header = consensus.block_to_light_client_header(
            self.preset, FORKS[fork], _read(self.case, name), self.config)
        assert self.beacon_root(header[:BEACON]) == root
        self.headers[root] = (header, header[:BEACON])
        self.slots.setdefault(_uint(header[:8]), []).append(header[:BEACON])

    def check_header(self, header: bytes, empty_allowed: bool = False) -> bytes:
        """Check a served header against the block it names, and return that block's root."""
        # The proof check already holds the rest of a header with a zero beacon header to zero.
        if empty_allowed and not any(header[:BEACON]):
            return bytes(32)
        root = self.beacon_root(header[:BEACON])
        derived, beacon = self.headers[root]
        assert header[:BEACON] == beacon
        if derived is not None:
            assert header == derived
        return root

    def check_signature_slot(self, attested: bytes, slot: int) -> None:
        """A block of the case at the signature slot has the attested block as its parent."""
        assert any(beacon[16:48] == attested for beacon in self.slots.get(slot, []))


def _check_new_head(chain: Chain, checks: dict) -> None:
    preset, config = chain.preset, chain.config
    for entry in checks["bootstraps"]:
        if "bootstrap" not in entry:
            continue
        fork = chain.digests[entry["bootstrap"]["fork_digest"]]
        data = _read(chain.case, entry["bootstrap"]["data"])
        # A store starts from the bootstrap only if it proves its committee for that block.
        root = bytes.fromhex(entry["block_root"][2:])
        consensus.light_client_sync(preset, FORKS[fork], FORKS[fork], root,
                                    chain.genesis_validators_root, data, [], config)
        header, _, _ = Shapes(preset, fork).split(data, ["header", "committee",
                                                         "committee_branch"])
        assert chain.check_header(header) == root
    for entry in checks["best_updates"]:
        if "update" not in entry:
            continue
        fork = chain.digests[entry["update"]["fork_digest"]]
        data = _read(chain.case, entry["update"]["data"])
        consensus.light_client_update_proofs(preset, FORKS[fork], "LightClientUpdate", data,
                                             config)
        attested, _, _, finalized, _, _, slot = Shapes(preset, fork).split(
            data, ["header", "committee", "committee_branch", "header", "finality_branch",
                   "aggregate"] + ["slot"])
        root = chain.check_header(attested)
        chain.check_header(finalized, empty_allowed=True)
        chain.check_signature_slot(root, _uint(slot))
        # An update counts for the period of its attested header, signed in that period.
        period = _period(preset)
        assert _uint(attested[:8]) // period == entry["period"] == _uint(slot) // period
    if "latest_finality_update" in checks:
        fork = chain.digests[checks["latest_finality_update"]["fork_digest"]]
        data = _read(chain.case, checks["latest_finality_update"]["data"])
        consensus.light_client_update_proofs(preset, FORKS[fork], "LightClientFinalityUpdate",
                                             data, config)
        attested, finalized, _, _, slot = Shapes(preset, fork).split(
            data, ["header", "header", "finality_branch", "aggregate", "slot"])
        chain.check_signature_slot(chain.check_header(attested), _uint(slot))
        chain.check_header(finalized, empty_allowed=True)
    if "latest_optimistic_update" in checks:
        fork = chain.digests[checks["latest_optimistic_update"]["fork_digest"]]
        data = _read(chain.case, checks["latest_optimistic_update"]["data"])
        attested, _, slot = Shapes(preset, fork).split(data, ["header", "aggregate", "slot"])
        chain.check_signature_slot(chain.check_header(attested), _uint(slot))


def _period(preset: str) -> int:
    """The number of slots of a sync committee period."""
    parameters = consensus.preset(preset)
    return parameters["SLOTS_PER_EPOCH"] * parameters["EPOCHS_PER_SYNC_COMMITTEE_PERIOD"]


def run_data_collection_case(case: Path, preset: str) -> None:
    """Check the light client data that a case serves after each new head, against its blocks."""
    # Each header must be the one that EthLib derives from its block, and each proof must verify.
    # Choosing the best update and the finalized checkpoint needs the state transition.
    chain = Chain(case, preset)
    for step in _YAML.load((case / "steps.yaml").read_text()):
        (kind, body), = step.items()
        if kind == "new_block":
            chain.add_block(chain.digests[body["fork_digest"]], body["data"])
        else:
            assert kind == "new_head"
            _check_new_head(chain, body["checks"])


def _cases() -> list:
    cases = []
    for steps in sorted(FILES.rglob("light_client/data_collection/pyspec_tests/*/steps.yaml")):
        case = steps.parent
        preset, fork = case.relative_to(FILES).parts[:2]
        if runs_data_collection(fork, case.name):
            cases.append(pytest.param(preset, case, id=case.relative_to(FILES).as_posix()))
    return cases


@pytest.mark.parametrize("preset, case", _cases())
def test_data_collection_case(preset, case):
    run_data_collection_case(case, preset)
