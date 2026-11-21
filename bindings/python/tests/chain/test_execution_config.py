"""The fork times and blob schedules of a client configuration file, per EIP-7840 and EIP-7892."""

import copy
from typing import Any, cast

import pytest

from ethlib import chain
from raising import raises

# A chain of the rules of Paris from block 0, which takes its later forks from the file.
BASE: dict[str, Any] = {
    "chainId": 1,
    "depositContractAddress": bytes(20),
    "activations": [["paris", "block", 0]],
}

# The configuration of EIP-7892, "Execution layer configuration".
EXAMPLE: dict[str, Any] = {
    "blobSchedule": {
        "cancun": {"target": 3, "max": 6, "baseFeeUpdateFraction": 3338477},
        "prague": {"target": 6, "max": 9, "baseFeeUpdateFraction": 5007716},
        "osaka": {"target": 6, "max": 9, "baseFeeUpdateFraction": 5007716},
        "bpo1": {"target": 10, "max": 15, "baseFeeUpdateFraction": 8346193},
        "bpo2": {"target": 14, "max": 21, "baseFeeUpdateFraction": 11684671},
    },
    "cancunTime": 0,
    "pragueTime": 0,
    "osakaTime": 1747387400,
    "bpo1Time": 1757387400,
    "bpo2Time": 1767387784,
}

# The same chain in the shape of the other exports, each schedule with its fork.
CONFIG: dict[str, Any] = {
    **BASE,
    "activations": [
        ["paris", "block", 0],
        ["dencun", "time", 0],
        ["pectra", "time", 0],
        ["fusaka", "time", 1747387400],
        ["bpo1", "time", 1757387400],
        ["bpo2", "time", 1767387784],
    ],
    "blobSchedules": [
        ["dencun", "time", 0, 3, 6, 3338477],
        ["pectra", "time", 0, 6, 9, 5007716],
        ["fusaka", "time", 1747387400, 6, 9, 5007716],
        ["bpo1", "time", 1757387400, 10, 15, 8346193],
        ["bpo2", "time", 1767387784, 14, 21, 11684671],
    ],
}

# The codes of the errors of the reader.
NOT_OBJECT = 1
SCHEDULES_NOT_OBJECT = 2
TIME_NOT_NUMBER = 3
SCHEDULE_MALFORMED = 4
SCHEDULE_OUT_OF_BOUNDS = 5
SCHEDULE_WITHOUT_TIME = 6
NOT_ORDERED = 7

PREFIX = "execution config: EthLib.Base.ExecutionConfig.ConfigError."


def without(path: list[str]) -> dict[str, Any]:
    """The example with one key removed, given by its path."""
    config = copy.deepcopy(EXAMPLE)
    parent: dict[str, Any] = config
    for key in path[:-1]:
        parent = parent[key]
    del parent[path[-1]]
    return config


@pytest.mark.parametrize(
    ("timestamp", "schedule"),
    [
        (0, (6, 9, 5007716)),
        (1747387400, (6, 9, 5007716)),
        (1760000000, (10, 15, 8346193)),
        (1767387784, (14, 21, 11684671)),
    ],
    ids=["genesis", "osaka", "bpo1", "bpo2"],
)
def test_example_schedule(timestamp: int, schedule: tuple[int, int, int]) -> None:
    """At each time the schedule is the entry of the latest fork that has activated."""
    assert chain.execution_blob_schedule(BASE, EXAMPLE, 0, timestamp) == schedule


def test_missing_entry_inherits() -> None:
    """A fork with a time and no entry keeps the schedule of the fork before it."""
    config = without(["blobSchedule", "bpo2"])
    assert chain.execution_blob_schedule(BASE, config, 0, 1767387784) == (10, 15, 8346193)


def test_prague_without_entry_inherits() -> None:
    """A file that breaks the rule of EIP-7892 by giving Prague no entry runs it under Cancun's."""
    config: dict[str, Any] = {"blobSchedule": {"cancun": EXAMPLE["blobSchedule"]["cancun"]}}
    config |= {"cancunTime": 0, "pragueTime": 100}
    assert chain.execution_blob_schedule(BASE, config, 0, 200) == (3, 6, 3338477)


def test_amsterdam_time_read() -> None:
    """The time of Amsterdam comes after BPO2, and keeps the schedule of BPO2 without an entry."""
    config = {**EXAMPLE, "amsterdamTime": 1793036568}
    assert chain.execution_blob_schedule(BASE, config, 0, 1793036568) == (14, 21, 11684671)
    with raises(chain.ChainError, f"{PREFIX}notOrdered") as error:
        chain.execution_blob_schedule(BASE, {**EXAMPLE, "amsterdamTime": 1}, 0, 0)
    assert error.value.code == NOT_ORDERED


def test_prague_time_from_base() -> None:
    """EIP-7892 requires times only after Prague, so the base may give the time of Prague."""
    base = {**BASE, "activations": [["paris", "block", 0], ["pectra", "time", 0]]}
    assert chain.execution_blob_schedule(base, without(["pragueTime"]), 0, 1) == (6, 9, 5007716)


def test_no_time_refused() -> None:
    """An entry whose fork has a time in neither the file nor the base is refused."""
    with raises(chain.ChainError, f"{PREFIX}scheduleWithoutTime (EthLib.Base.Fork.pectra)") as e:
        chain.execution_blob_schedule(BASE, without(["pragueTime"]), 0, 0)
    assert e.value.code == SCHEDULE_WITHOUT_TIME


@pytest.mark.parametrize(
    ("entry", "code", "fault"),
    [
        ({"target": 3, "max": 6}, SCHEDULE_MALFORMED, "scheduleMalformed"),
        (
            {"target": "3", "max": 6, "baseFeeUpdateFraction": 1},
            SCHEDULE_MALFORMED,
            "scheduleMalformed",
        ),
        (
            {"target": 7, "max": 6, "baseFeeUpdateFraction": 1},
            SCHEDULE_OUT_OF_BOUNDS,
            "scheduleOutOfBounds",
        ),
        (
            {"target": 0, "max": 0, "baseFeeUpdateFraction": 1},
            SCHEDULE_OUT_OF_BOUNDS,
            "scheduleOutOfBounds",
        ),
        (
            {"target": 3, "max": 6, "baseFeeUpdateFraction": 0},
            SCHEDULE_OUT_OF_BOUNDS,
            "scheduleOutOfBounds",
        ),
    ],
    ids=["no-fraction", "text", "target-above-max", "max-zero", "fraction-zero"],
)
def test_bad_entry_refused(entry: dict, code: int, fault: str) -> None:
    """An entry without three natural numbers, or out of the bounds of a schedule, is refused."""
    config = copy.deepcopy(EXAMPLE)
    config["blobSchedule"]["cancun"] = entry
    with raises(chain.ChainError, f"{PREFIX}{fault} (EthLib.Base.Fork.dencun)") as error:
        chain.execution_blob_schedule(BASE, config, 0, 0)
    assert error.value.code == code


@pytest.mark.parametrize("time", ["1747387400", 2**64], ids=["text", "2^64"])
def test_time_not_number_refused(time: object) -> None:
    """A time that is not a natural number below 2^64 is refused."""
    with raises(chain.ChainError, f"{PREFIX}timeNotNumber (EthLib.Base.Fork.fusaka)") as error:
        chain.execution_blob_schedule(BASE, {**EXAMPLE, "osakaTime": time}, 0, 0)
    assert error.value.code == TIME_NOT_NUMBER


def test_schedules_not_object_refused() -> None:
    """Blob schedules that are not an object are refused."""
    with raises(chain.ChainError, f"{PREFIX}schedulesNotObject") as error:
        chain.execution_blob_schedule(BASE, {**EXAMPLE, "blobSchedule": []}, 0, 0)
    assert error.value.code == SCHEDULES_NOT_OBJECT


def test_file_not_object_refused() -> None:
    """A file that is not an object is refused."""
    with raises(chain.ChainError, f"{PREFIX}notObject") as error:
        chain.execution_blob_schedule(BASE, cast(dict[str, Any], []), 0, 0)
    assert error.value.code == NOT_OBJECT


def test_times_out_of_order_refused() -> None:
    """Prague before Cancun breaks the order of the timeline."""
    with raises(chain.ChainError, f"{PREFIX}notOrdered") as error:
        chain.execution_blob_schedule(BASE, {**EXAMPLE, "cancunTime": 100, "pragueTime": 5}, 0, 0)
    assert error.value.code == NOT_ORDERED


def test_unknown_and_early_names_ignored() -> None:
    """An entry under a name that no fork has, or of Shanghai, is ignored."""
    config = copy.deepcopy(EXAMPLE)
    config["shanghaiTime"] = 0
    for name in ["shanghai", "bogota"]:
        config["blobSchedule"][name] = {"target": 1, "max": 2, "baseFeeUpdateFraction": 3}
    assert chain.execution_blob_schedule(BASE, config, 0, 0) == (6, 9, 5007716)
    assert chain.execution_blob_schedule(BASE, config, 0, 1767387784) == (14, 21, 11684671)


def test_write_gives_example() -> None:
    """Writing the chain of the example gives the file of the example."""
    assert chain.write_execution_config(CONFIG) == EXAMPLE


def test_write_refuses_what_a_file_cannot_hold() -> None:
    """A schedule without a fork has no name in a file, so the writer refuses the configuration."""
    config = {**CONFIG, "blobSchedules": [*CONFIG["blobSchedules"], ["time", 1800000000, 1, 2, 3]]}
    with raises(chain.ChainError, "config: a configuration file cannot hold it whole") as error:
        chain.write_execution_config(config)
    assert error.value.code == 0
