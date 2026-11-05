"""Header checks on the test networks that set a blob schedule of their own."""

import json
from pathlib import Path

import pytest

from ethlib.execution import blocks

from .test_blocks import _first_item

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"

# The networks of the release that run the rules of Amsterdam under a blob schedule of their own.
# Each sets its schedule from genesis, or from the time 15,000 that its name gives.
ACTIVATION = {
    "AmsterdamBPOIncrease": 0,
    "AmsterdamBPODecrease": 0,
    "AmsterdamToBPOIncreaseAtTime15k": 15_000,
    "AmsterdamToBPODecreaseAtTime15k": 15_000,
}
SCHEDULE_NAME = {
    "AmsterdamBPOIncrease": "AmsterdamBPOIncrease",
    "AmsterdamBPODecrease": "AmsterdamBPODecrease",
    "AmsterdamToBPOIncreaseAtTime15k": "AmsterdamBPOIncrease",
    "AmsterdamToBPODecreaseAtTime15k": "AmsterdamBPODecrease",
}
DIRECTORIES = [
    "for_amsterdambpoincrease",
    "for_amsterdambpodecrease",
    "for_amsterdamtobpoincreaseattime15k",
    "for_amsterdamtobpodecreaseattime15k",
]
SOURCES = [f"fixtures/blockchain_tests/{d}" for d in DIRECTORIES]

# The fork whose rules every block of these networks follows.
FORK = "glamsterdam"
WRONG_EXCESS_BLOB_GAS = 202

_CASES = json.loads(
    (
        Path(__file__).resolve().parents[4]
        / "tests"
        / "execution"
        / "blocks"
        / "blob_schedules.json"
    ).read_text()
)


def _hex(value: str) -> bytes:
    return bytes.fromhex(value.removeprefix("0x"))


def schedules(network: str, config: dict) -> list[blocks.BlobSchedule]:
    """The blob schedule that a network sets itself, from the schedule of its fixture config."""
    entry = config[SCHEDULE_NAME[network]]
    return [
        (
            ACTIVATION[network],
            int(entry["target"], 16),
            int(entry["max"], 16),
            int(entry["baseFeeUpdateFraction"], 16),
        )
    ]


@pytest.mark.parametrize(
    "case",
    _CASES,
    ids=[f"{c['network']}-{c['test'].split('::')[-1][:60]}-{c['block']}" for c in _CASES],
)
def test_fixture_header(case) -> None:
    parent, header = bytes.fromhex(case["parent"]), bytes.fromhex(case["header"])
    own = schedules(case["network"], case["blobSchedule"])
    if case["exception"] is None:
        blocks.validate_header(FORK, FORK, parent, header, own)
        return
    with pytest.raises(blocks.BlockError) as error:
        blocks.validate_header(FORK, FORK, parent, header, own)
    assert error.value.code == WRONG_EXCESS_BLOB_GAS


def test_schedule_decides_some_header() -> None:
    # Some valid header fails under the schedule of its fork alone, so the cases test the schedule.
    failed = 0
    for case in _CASES:
        if case["exception"] is None:
            try:
                blocks.validate_header(
                    FORK, FORK, bytes.fromhex(case["parent"]), bytes.fromhex(case["header"])
                )
            except blocks.BlockError as error:
                assert error.code == WRONG_EXCESS_BLOB_GAS
                failed += 1
    assert failed > 0


def test_cases_cover_each_network() -> None:
    assert {c["network"] for c in _CASES} == set(ACTIVATION)
    assert {c["exception"] for c in _CASES} == {None, "BlockException.INCORRECT_EXCESS_BLOB_GAS"}


@pytest.mark.parametrize("schedule", [(0, 7, 6, 3338477), (0, 0, 0, 3338477), (0, 1, 2, 0)])
def test_schedule_out_of_bounds_rejected(schedule) -> None:
    case = _CASES[0]
    with pytest.raises(blocks.BlockError) as error:
        blocks.validate_header(
            FORK, FORK, bytes.fromhex(case["parent"]), bytes.fromhex(case["header"]), [schedule]
        )
    assert error.value.code == 0


def test_later_schedule_wins() -> None:
    # Of two schedules that a header has reached, the one listed last holds.
    case = next(
        c for c in _CASES if c["exception"] is None and c["network"] == "AmsterdamBPOIncrease"
    )
    parent, header = bytes.fromhex(case["parent"]), bytes.fromhex(case["header"])
    own = schedules(case["network"], case["blobSchedule"])
    blocks.validate_header(FORK, FORK, parent, header, [(0, 1, 2, 3338477)] + own)
    with pytest.raises(blocks.BlockError) as error:
        blocks.validate_header(FORK, FORK, parent, header, own + [(0, 1, 2, 3338477)])
    assert error.value.code == WRONG_EXCESS_BLOB_GAS


@pytest.mark.archive(ARCHIVE, *SOURCES)
@pytest.mark.parametrize("directory", DIRECTORIES)
def test_headers_of_every_fixture(archive: Path, directory: str) -> None:
    checked = 0
    for path in sorted((archive / "fixtures" / "blockchain_tests" / directory).rglob("*.json")):
        for name, fixture in json.loads(path.read_text()).items():
            own = schedules(fixture["network"], fixture["config"]["blobSchedule"])
            headers = {
                fixture["genesisBlockHeader"]["hash"]: _first_item(_hex(fixture["genesisRLP"]))
            }
            for block in fixture["blocks"]:
                header = _first_item(_hex(block["rlp"]))
                exception = block.get("expectException")
                if not exception:
                    blocks.check_header(
                        FORK, FORK, headers[block["blockHeader"]["parentHash"]], header, own
                    )
                    headers[block["blockHeader"]["hash"]] = header
                    checked += 1
                    continue
                if exception != "BlockException.INCORRECT_EXCESS_BLOB_GAS":
                    # A transaction check of the block, which a header check does not see.
                    continue
                with pytest.raises(blocks.BlockError) as error:
                    blocks.check_header(FORK, FORK, headers["0x" + header[4:36].hex()], header, own)
                assert error.value.code == WRONG_EXCESS_BLOB_GAS, f"{path.name}::{name}"
    assert checked > 0
