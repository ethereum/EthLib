"""The map from each rejection of EthLib to the exception of the source at the same step."""

import re
from pathlib import Path

import pytest

from raising import raises

from . import rejections

ROOT = Path(__file__).resolve().parents[4]

# Each error type of the tables, and the Lean file that declares it.
SOURCES = {
    "TransitionError": "EthLib/Consensus/Transition/Basic.lean",
    "AccessorError": "EthLib/Consensus/Accessors.lean",
    "ArithError": "EthLib/Base/Uint64.lean",
    "ShuffleError": "EthLib/Consensus/Shuffle.lean",
}


def constructors(error_type: str, path: str) -> list[str]:
    """The constructors of an inductive type, in the order of its declaration."""
    text = (ROOT / path).read_text()
    body = re.search(rf"^inductive {error_type} where\n(.*?)^  deriving", text, re.M | re.S)
    assert body is not None, error_type
    return re.findall(r"^  \| (\w+)", body.group(1), re.M)


@pytest.mark.parametrize("error_type", list(SOURCES))
def test_every_constructor_has_a_decision(error_type):
    # A new constructor fails here until the table says what the source raises at its step.
    table = rejections.TABLES[error_type]
    assert sorted(table) == sorted(constructors(error_type, SOURCES[error_type]))


def test_every_fork_choice_code_has_a_decision():
    # The codes of the fork choice errors, as the C exports give them.
    text = (ROOT / "EthLib/Consensus/ForkChoice/Store.lean").read_text()
    body = re.search(r"^def ForkChoiceError\.code.*?\n(.*?)\n\n", text, re.M | re.S)
    assert body is not None
    codes = {int(code): name for name, code in re.findall(r"\| \.(\w+) .*=> (\d+)", body.group(1))}
    assert {code: name for code, (name, _) in rejections.FORK_CHOICE.items()} == codes
    assert sorted(codes.values()) == sorted(
        constructors("ForkChoiceError", "EthLib/Consensus/ForkChoice/Store.lean")
    )


@pytest.mark.parametrize(
    ("message", "kind"),
    [
        # A failed assert of the rule.
        ("EthLib.Consensus.TransitionError.proposerSlashed 3", AssertionError),
        # A read past the end of the registry, inside an accessor.
        (
            "EthLib.Consensus.TransitionError.accessor "
            "(EthLib.Consensus.AccessorError.indexOutOfRange 64)",
            IndexError,
        ),
        # A uint64 overflow, two wrappers deep.
        (
            "EthLib.Consensus.TransitionError.accessor "
            "(EthLib.Consensus.AccessorError.arith (EthLib.Base.ArithError.overflow))",
            ValueError,
        ),
        # A key that no validator holds.
        (
            "EthLib.Consensus.TransitionError.unknownSyncCommitteeMember 0x" + "00" * 48,
            ValueError,
        ),
        # A root that has no value, where the source never fails.
        ("EthLib.Consensus.TransitionError.ssz EthLib.Serialization.Ssz.Err.typeMismatch", None),
    ],
)
def test_kind_of_message(message, kind):
    assert rejections.kind_of_message(message) is kind


def test_kind_of_fork_choice():
    # A block that the state transition rejects takes the exception of the wrapped error.
    message = "the state transition fails: EthLib.Consensus.TransitionError.wrongStateRoot 0x0 0x1"
    assert rejections.kind_of_fork_choice(10, message) is AssertionError
    # An unknown proof-of-work block is the exception of the source's block step.
    assert rejections.kind_of_fork_choice(25, "") is rejections.BlockNotFoundError


def test_message_without_constructor():
    with raises(LookupError, "no constructor of an EthLib error in the message 'no operation'"):
        rejections.kind_of_message("no operation")


def test_check_accepts_a_caught_exception():
    rejections.check(IndexError, rejections.CAUGHT, "case", "message")


@pytest.mark.parametrize(
    ("kind", "name"),
    [(ValueError, "ValueError"), (ZeroDivisionError, "ZeroDivisionError"), (None, "no exception")],
)
def test_check_refuses_an_uncaught_exception(kind, name):
    with raises(AssertionError, f"case: the source raises {name} here, not caught: message"):
        rejections.check(kind, rejections.CAUGHT, "case", "message")


def test_block_step_refuses_an_index_error():
    # The block step of the source catches an assert and an unknown proof-of-work block only.
    message = "case: the source raises IndexError here, not caught: message"
    with raises(AssertionError, message):
        rejections.check(IndexError, rejections.CAUGHT_BY_BLOCK_STEP, "case", "message")


def test_uncaught_constructors():
    # A decision that the source catches a step accepts more cases, so each one is listed here too.
    uncaught = {
        f"{error_type}.{name}"
        for error_type, table in rejections.TABLES.items()
        for name, kind in table.items()
        if kind is not rejections.NESTED and kind not in rejections.CAUGHT
    } | {
        f"ForkChoiceError.{name}"
        for name, kind in rejections.FORK_CHOICE.values()
        if kind is not rejections.NESTED and kind not in rejections.CAUGHT
    }
    assert uncaught == {
        "TransitionError.ssz",
        "TransitionError.tooManyEth1Votes",
        "TransitionError.tooManyPendingAttestations",
        "TransitionError.registryFull",
        "TransitionError.zeroInclusionDelay",
        "TransitionError.historicalRootsFull",
        "TransitionError.historicalSummariesFull",
        "TransitionError.unknownSyncCommitteeMember",
        "TransitionError.blockForkMismatch",
        "AccessorError.balanceOverflow",
        "AccessorError.ssz",
        "AccessorError.tooManyAttesters",
        "AccessorError.forkNotYetSpecified",
        "AccessorError.listFull",
        "ArithError.overflow",
        "ArithError.underflow",
        "ArithError.divisionByZero",
        "ShuffleError.noCommittee",
        "ShuffleError.overflow",
        "ShuffleError.countTooLarge",
        "ForkChoiceError.unknownCheckpointState",
        "ForkChoiceError.unknownUnrealizedJustification",
        "ForkChoiceError.parentSlotNotLower",
        "ForkChoiceError.ssz",
        "ForkChoiceError.unknownBlockTimeliness",
        "ForkChoiceError.tickNotAdvancing",
        "ForkChoiceError.forkNotYetSpecified",
        "ForkChoiceError.unknownPowBlock",
        "ForkChoiceError.payloadNotOptimistic",
        "ForkChoiceError.supportDiscountAboveMaximum",
    }
