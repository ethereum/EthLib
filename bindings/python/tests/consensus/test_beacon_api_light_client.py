"""The Beacon API light client answers, on the pinned light client and fork choice vectors."""

from pathlib import Path
from typing import Any, Literal

import pytest

from ethlib import consensus
from raising import raises

from .containers import FORKS
from .test_beacon_api_blocks import ANCHOR_ROOT, FORK_CASE, HEAD_ROOT, _store_case
from .test_light_client_sync import _YAML, FILES, _read, case_config, fork_digests

# Every data collection case of the minimal preset.
DATA_COLLECTION = sorted((FILES / "minimal").glob("*/light_client/data_collection/pyspec_tests/*"))

# The Altair case, whose best updates are those of periods 0 and 1.
ALTAIR_CASE = (
    FILES / "minimal/altair/light_client/data_collection/pyspec_tests/light_client_data_collection"
)

# The fields that the finality and the optimistic updates keep from an update.
FINALITY_FIELDS = (
    "attested_header",
    "finalized_header",
    "finality_branch",
    "sync_aggregate",
    "signature_slot",
)
OPTIMISTIC_FIELDS = ("attested_header", "sync_aggregate", "signature_slot")

# The forks of the beacon chain, from Altair to Gloas, all at epoch 0, as a Gloas case runs.
GLOAS_EPOCHS = {
    f"{fork.upper()}_FORK_EPOCH": 0
    for fork in ("altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas")
}


class Served:
    """The best update of each period that a data collection case serves at its last check."""

    def __init__(self, case: Path):
        values, self.config = case_config(case, "minimal")
        self.root = _read(case, "initial_state")[8:40]
        digests = fork_digests(values, "minimal", self.root, self.config)
        steps = _YAML.load((case / "steps.yaml").read_text())
        checks = [
            body["checks"]
            for step in steps
            for kind, body in step.items()
            if kind == "new_head" and "best_updates" in body["checks"]
        ]
        # Each entry holds its period, the digest of its chunk, its fork and its bytes.
        self.updates: list[tuple[int, bytes, str, bytes]] = [
            (
                entry["period"],
                bytes.fromhex(entry["update"]["fork_digest"][2:]),
                FORKS[digests[entry["update"]["fork_digest"]]],
                _read(case, entry["update"]["data"]),
            )
            for entry in checks[-1]["best_updates"]
            if "update" in entry
        ]

    def known(self) -> list[consensus.KnownUpdate]:
        return [(period, fork, data) for period, _, fork, data in self.updates]

    def ssz(self, start: int, count: int) -> bytes:
        return consensus.api_light_client_updates_ssz(
            "minimal", self.root, self.known(), start, count, self.config
        )


def _chunks(body: bytes) -> list[tuple[bytes, bytes]]:
    """The digest and the payload of each chunk of an SSZ updates body, read independently."""
    chunks, at = [], 0
    while at < len(body):
        length = int.from_bytes(body[at : at + 8], "little")
        chunks.append((body[at + 8 : at + 12], body[at + 12 : at + 8 + length]))
        at += 8 + length
    assert at == len(body)
    return chunks


def _case_id(case: Path) -> str:
    return f"{case.parents[3].name}-{case.name}"


@pytest.mark.parametrize("case", DATA_COLLECTION, ids=_case_id)
def test_updates_chunks_carry_the_digests_of_the_vectors(case: Path) -> None:
    served = Served(case)
    assert served.updates
    first = served.updates[0][0]
    body = served.ssz(first, len(served.updates) + 3)
    # Each chunk has the digest and the bytes that the case serves, in increasing period order.
    expected = [(digest, data) for _, digest, _, data in served.updates]
    assert _chunks(body) == expected
    decoded = consensus.api_light_client_decode_updates("minimal", served.root, body, served.config)
    assert decoded == [(update_fork, data) for _, _, update_fork, data in served.updates]


@pytest.mark.parametrize("case", DATA_COLLECTION, ids=_case_id)
def test_updates_json_names_the_version_of_each_update(case: Path) -> None:
    served = Served(case)
    answer = consensus.api_light_client_updates(
        "minimal", served.known(), 0, 2**64 - 1, served.config
    )
    assert len(answer) == len(served.updates)
    names = {lean: spec for spec, lean in FORKS.items()}
    for item, (_, _, update_fork, data) in zip(answer, served.updates, strict=True):
        assert item["version"] == names[update_fork]
        assert consensus.api_ssz("minimal", update_fork, "LightClientUpdate", item["data"]) == data


def test_updates_answer_starts_at_the_earliest_known_period() -> None:
    served = Served(ALTAIR_CASE)
    period, _, fork, data = served.updates[0]
    other = served.updates[1][3]
    # The node knows the updates of two periods, five and seven after the first one.
    known = [(period + 5, fork, data), (period + 7, fork, other)]

    def payloads(start: int, count: int) -> list[bytes]:
        body = consensus.api_light_client_updates_ssz(
            "minimal", served.root, known, start, count, served.config
        )
        return [payload for _, payload in _chunks(body)]

    # A range that starts before the first known period starts with its update.
    assert payloads(period, 6) == [data]
    # A period with no update inside the range is skipped.
    assert payloads(period, 10) == [data, other]
    # A count of one gives only the first known update of the range, if the range holds one.
    assert payloads(period + 3, 1) == []
    assert payloads(period + 5, 1) == [data]
    # A range past every known period is empty, and so is a count of zero.
    assert payloads(period + 8, 10) == []
    assert payloads(period + 5, 0) == []


def test_updates_answer_holds_at_most_128_updates() -> None:
    served = Served(ALTAIR_CASE)
    period, _, fork, data = served.updates[0]
    # The same update under 140 periods: the range drops the first two and keeps 128 of the rest.
    known = [(period + offset, fork, data) for offset in range(140)]
    body = consensus.api_light_client_updates_ssz(
        "minimal", served.root, known, period + 2, 200, served.config
    )
    assert len(_chunks(body)) == 128
    answer = consensus.api_light_client_updates("minimal", known, period + 2, 200, served.config)
    assert len(answer) == 128


def test_update_of_another_fork_than_its_epoch_is_refused() -> None:
    served = Served(ALTAIR_CASE)
    period, _, _, data = served.updates[0]
    known = [(period, "altair", data)]
    # Under the named configuration Altair has not started, so the epoch is of Phase 0.
    message = (
        "chunk rejected: EthLib.Consensus.BeaconApi.ChunkError.forkMismatch "
        "(EthLib.Base.Fork.altair) (EthLib.Base.Fork.phase0)"
    )
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_light_client_updates_ssz("minimal", served.root, known, period, 1, None)
    assert error.value.code == 0
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_light_client_updates("minimal", known, period, 1, None)
    assert error.value.code == 0


def test_decode_refuses_a_truncated_body() -> None:
    served = Served(ALTAIR_CASE)
    body = served.ssz(served.updates[0][0], 1)
    message = "chunk rejected: EthLib.Consensus.BeaconApi.ChunkError.truncated"
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_light_client_decode_updates("minimal", served.root, body[:-1], served.config)
    assert error.value.code == 0


def _bootstrap(root: str, **kwargs: Any) -> dict[str, Any]:
    return consensus.api_light_client_bootstrap(
        *_store_case(FORK_CASE), bytes.fromhex(root[2:]), GLOAS_EPOCHS, **kwargs
    )


@pytest.mark.parametrize("root", [HEAD_ROOT, ANCHOR_ROOT])
def test_bootstrap_starts_a_light_client_that_trusts_the_block(root: str) -> None:
    trusted = bytes.fromhex(root[2:])
    answer = _bootstrap(root)
    assert answer["version"] == "gloas"
    body = consensus.api_light_client_bootstrap_ssz(*_store_case(FORK_CASE), trusted, GLOAS_EPOCHS)
    data = consensus.api_json("minimal", FORKS["gloas"], "LightClientBootstrap", body)
    assert data == answer["data"]
    # The light client takes the bootstrap for the trusted root, with no step after it.
    gloas = FORKS["gloas"]
    synced = consensus.light_client_sync(
        "minimal", gloas, gloas, trusted, bytes(32), body, [], GLOAS_EPOCHS
    )
    assert synced == []


def test_bootstrap_of_an_unknown_block_is_404() -> None:
    with raises(consensus.ForkChoiceError, "No bootstrap for block 0x" + "11" * 32) as error:
        _bootstrap("0x" + "11" * 32)
    assert error.value.code == 404


def test_bootstrap_under_a_schedule_before_altair_is_404() -> None:
    # Under the named configuration Altair has not started, so the bootstrap cannot be built.
    # The fork choice runs under that configuration in every case; only the bootstrap reads it.
    with raises(consensus.ForkChoiceError, f"No bootstrap for block {HEAD_ROOT}") as error:
        consensus.api_light_client_bootstrap(
            *_store_case(FORK_CASE), bytes.fromhex(HEAD_ROOT[2:]), None
        )
    assert error.value.code == 404


@pytest.mark.parametrize(
    ("kind", "fields"), [("finality", FINALITY_FIELDS), ("optimistic", OPTIMISTIC_FIELDS)]
)
def test_latest_update_keeps_the_fields_of_the_update(
    kind: Literal["finality", "optimistic"], fields: tuple[str, ...]
) -> None:
    served = Served(ALTAIR_CASE)
    _, _, fork, data = served.updates[0]
    full = consensus.api_json("minimal", fork, "LightClientUpdate", data)
    answer = consensus.api_light_client_latest("minimal", fork, kind, data)
    assert answer["version"] == "altair"
    assert answer["data"] == {field: full[field] for field in fields}
    with raises(consensus.ConsensusError, f"No {kind} update is available") as error:
        consensus.api_light_client_latest("minimal", fork, kind, None)
    assert error.value.code == 404
