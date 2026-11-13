"""The error codes of the execution JSON-RPC API against the groups of ethereum/execution-apis."""

from pathlib import Path

from ruamel.yaml import YAML

from ethlib.execution import rpc

# `fixtures/README.md` gives the origin of the files and their licence.
GROUPS = Path(__file__).resolve().parent / "fixtures" / "error-groups"
LOADER = YAML(typ="safe", pure=True)

# The files in the order of the table of reserved ranges in `src/error-groups/README.md`.
FILES = [
    "rpc-standard-errors.yaml",
    "rpc-non-standard-errors.yaml",
    "execution-errors.yaml",
    "gas-errors.yaml",
    "txpool-errors.yaml",
    "zk-execution-errors.yaml",
]


def group_of_file(name: str) -> rpc.ErrorGroup:
    """The one group that a file of the source defines."""
    ((group_name, group),) = LOADER.load((GROUPS / name).read_text()).items()
    bounds = group.get("range")
    return rpc.ErrorGroup(
        name=group_name,
        range=None if bounds is None else (bounds["min"], bounds["max"]),
        errors=tuple(
            rpc.ErrorCode(code=error["code"], message=error["message"]) for error in group["errors"]
        ),
    )


def test_groups_are_those_of_the_source() -> None:
    """Every group, its range and its codes with their messages, are those of the source files."""
    assert rpc.error_groups() == tuple(group_of_file(name) for name in FILES)


def test_codes_lie_in_their_range() -> None:
    """The source data keeps each code of a group that declares a range inside that range."""
    for group in rpc.error_groups():
        if group.range is not None:
            least, greatest = group.range
            assert all(least <= error.code <= greatest for error in group.errors), group.name


def test_pruned_history_is_outside_every_group() -> None:
    """The code 4444 of pruned history, as `src/debug/getters.yaml` lists it, is in no group."""
    pruned = rpc.pruned_history_unavailable()
    assert pruned == rpc.ErrorCode(code=4444, message="Pruned history unavailable")
    assert all(error.code != 4444 for group in rpc.error_groups() for error in group.errors)
