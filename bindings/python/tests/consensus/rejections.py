"""The Python exception that the source of the consensus vectors raises where EthLib rejects."""

import re

# The source writes an invalid case only when the helper of its test catches the failure.
# That helper catches `AssertionError`, a failed assert, and `IndexError`, a read past a list end.
# So EthLib must reject an invalid case where the source raises one of the two.
# The runners narrow or widen that set where the test of the source does:
# - one epoch case catches the `ValueError` of an overflow;
# - the block step of a fork choice case catches no `IndexError`;
# - the steps of a compliance case catch `AssertionError` only.
#
# Each table maps a constructor of an EthLib error to the exception of the source at that step.
# None means that the source never fails at that step.
# Line numbers are those of consensus-specs at the pin of `tests/sources.toml`.
# An entry without a comment is an assert of the rule.
# The SSZ library of the source raises a `ValueError` for an integer out of range or a full list.


class BlockNotFoundError(Exception):
    """The exception of the source's fork choice tests for a proof-of-work block that is unknown."""


class Nested:
    """The mark of a constructor that wraps another error, whose constructor decides."""


NESTED = Nested()

# The exception of each rejection, or None, or the mark of a wrapped error.
Kind = type[Exception] | None | Nested

ARITH: dict[str, Kind] = {
    # A uint64 of the source raises `ValueError` out of its range.
    "overflow": ValueError,
    "underflow": ValueError,
    # A division of the source raises `ZeroDivisionError` on a zero divisor.
    "divisionByZero": ZeroDivisionError,
}

SHUFFLE: dict[str, Kind] = {
    "indexOutOfRange": AssertionError,
    # The start of a committee divides by the committee count (phase0/beacon-chain.md line 1279).
    "noCommittee": ZeroDivisionError,
    # The end of a committee is a uint64 product (phase0/beacon-chain.md line 1280).
    "overflow": ValueError,
    # The bucket of a position is a uint32 (phase0/beacon-chain.md line 1228).
    "countTooLarge": ValueError,
}

ACCESSOR: dict[str, Kind] = {
    # A validator past the end of the registry (phase0/beacon-chain.md, any `state.validators[i]`).
    "indexOutOfRange": IndexError,
    # A total balance is a Gwei, a uint64 (phase0/beacon-chain.md line 1565).
    "balanceOverflow": ValueError,
    "slotOutOfRange": AssertionError,
    "arith": NESTED,
    "shuffle": NESTED,
    # The source computes every root, so it never fails there.
    "ssz": None,
    "noCandidates": AssertionError,
    # A bit past the end of the aggregation bits (electra/beacon-chain.md, `get_attesting_indices`).
    "bitOutOfRange": IndexError,
    # The indexed form is a list with a limit (phase0/beacon-chain.md line 1610).
    "tooManyAttesters": ValueError,
    # The source holds every fork, so it never fails there.
    "forkNotYetSpecified": None,
    "epochTooFar": AssertionError,
    # A builder or a payment past the end of its list (gloas/beacon-chain.md).
    "builderIndexOutOfRange": IndexError,
    "paymentIndexOutOfRange": IndexError,
    "ptcSlotOutOfRange": AssertionError,
    # An append to a full list of the state (electra/beacon-chain.md, any `append`).
    "listFull": ValueError,
    "epochNotRecent": AssertionError,
    "invalidPubkeys": AssertionError,
    "wrongSource": AssertionError,
    "sameSlotIndexNotZero": AssertionError,
}

TRANSITION: dict[str, Kind] = {
    "accessor": NESTED,
    # The source computes every root, so it never fails there.
    "ssz": None,
    "slotMismatch": AssertionError,
    "notNewer": AssertionError,
    "wrongProposer": AssertionError,
    "wrongParent": AssertionError,
    "proposerSlashed": AssertionError,
    "invalidRandaoReveal": AssertionError,
    # An append to the votes of a full voting period (phase0/beacon-chain.md line 2391).
    "tooManyEth1Votes": ValueError,
    "headerSlotsDiffer": AssertionError,
    "headerProposersDiffer": AssertionError,
    "sameHeaders": AssertionError,
    "notSlashable": AssertionError,
    "invalidHeaderSignature": AssertionError,
    "notSlashableData": AssertionError,
    "invalidIndexedAttestation": AssertionError,
    "noneSlashed": AssertionError,
    "payloadAttestationNotForParent": AssertionError,
    "payloadAttestationWrongSlot": AssertionError,
    "invalidPayloadAttestation": AssertionError,
    "selfBuildBidPaid": AssertionError,
    "builderNotActive": AssertionError,
    "notPayloadBuilder": AssertionError,
    "bidNotCovered": AssertionError,
    "invalidBidSignature": AssertionError,
    # The envelope appends its hashes to a list with a limit, a `ValueError`.
    # The assert on the bid bounds that count first, so only the assert is reachable.
    "tooManyBlobCommitments": AssertionError,
    "bidWrongSlot": AssertionError,
    "bidAtGenesis": AssertionError,
    "bidWrongParentHash": AssertionError,
    "bidRepeatsParentHash": AssertionError,
    "bidWrongParentRoot": AssertionError,
    "bidWrongRandao": AssertionError,
    "attestationTargetNotRecent": AssertionError,
    "attestationTargetNotSlotEpoch": AssertionError,
    "attestationTooEarly": AssertionError,
    "attestationTooLate": AssertionError,
    "committeeIndexOutOfRange": AssertionError,
    "aggregationBitsLength": AssertionError,
    "wrongAttestationSource": AssertionError,
    # An append to a full list of pending attestations (phase0/beacon-chain.md lines 2487 and 2490).
    "tooManyPendingAttestations": ValueError,
    "invalidAttestation": AssertionError,
    "wrongDepositCount": AssertionError,
    "invalidDepositProof": AssertionError,
    # An append to a full registry (phase0/beacon-chain.md line 2520).
    "registryFull": ValueError,
    "exitingValidatorNotActive": AssertionError,
    "exitAlreadyInitiated": AssertionError,
    "exitNotYetValid": AssertionError,
    "exitTooSoon": AssertionError,
    "invalidExitSignature": AssertionError,
    # The reward of an attester divides by its inclusion delay (phase0/beacon-chain.md line 2127).
    "zeroInclusionDelay": ZeroDivisionError,
    "priorWithdrawalsAtLimit": AssertionError,
    "wrongWithdrawals": AssertionError,
    "notBlsCredentials": AssertionError,
    "wrongBlsKey": AssertionError,
    "invalidBlsChangeSignature": AssertionError,
    # An append to full historical roots (phase0/beacon-chain.md line 2325).
    "historicalRootsFull": ValueError,
    "slotNotAfter": AssertionError,
    "invalidBlockSignature": AssertionError,
    "wrongStateRoot": AssertionError,
    "wrongPayloadParentHash": AssertionError,
    "wrongPayloadRandao": AssertionError,
    "wrongPayloadTimestamp": AssertionError,
    "invalidExecutionPayload": AssertionError,
    # An append to full historical summaries (capella/beacon-chain.md line 387).
    "historicalSummariesFull": ValueError,
    "invalidSyncAggregate": AssertionError,
    # The sum of the keys of the members that did not sign asserts that each key is valid.
    # An aggregate key of the committee that does not decode raises a `ValueError` in the source.
    # One constructor covers both steps, so this entry accepts more than the source catches there.
    "invalidSyncCommitteeKey": AssertionError,
    # A `list.index` that finds no validator with the key (altair/beacon-chain.md line 686).
    "unknownSyncCommitteeMember": ValueError,
    # The runner of the source gives each block its fork, so it never fails there.
    "blockForkMismatch": None,
    "attestationIndexNotZero": AssertionError,
    "noCommitteeAttester": AssertionError,
    "exitPendingWithdrawal": AssertionError,
    "parentRequestsNotEmpty": AssertionError,
    "wrongParentRequestsRoot": AssertionError,
    "tooManyOperations": AssertionError,
    "attestationIndexAboveOne": AssertionError,
    "invalidEnvelopeSignature": AssertionError,
    "envelopeWrongBlockRoot": AssertionError,
    "envelopeWrongParentRoot": AssertionError,
    "envelopeWrongBuilder": AssertionError,
    "wrongPayloadGasLimit": AssertionError,
    "wrongPayloadBlockHash": AssertionError,
    "wrongPayloadRequestsRoot": AssertionError,
    "wrongPayloadSlot": AssertionError,
}

# The constructor of each code of a fork choice error, and its exception.
# The message of a fork choice error is prose, so the code names the constructor.
FORK_CHOICE: dict[int, tuple[str, Kind]] = {
    1: ("anchorStateMismatch", AssertionError),
    # The handlers assert that a block is in the store before they read it.
    # A read inside the store is a `KeyError`, which a consistent store never meets.
    2: ("unknownBlock", AssertionError),
    # A dictionary of the store without the checkpoint (phase0/fork-choice.md line 370).
    3: ("unknownCheckpointState", KeyError),
    # As for a block: an assert in the handlers, a `KeyError` that cannot happen elsewhere.
    4: ("unknownBlockState", AssertionError),
    # A dictionary of the store without the block (phase0/fork-choice.md line 406).
    5: ("unknownUnrealizedJustification", KeyError),
    # Every parent of the store has a lower slot, so the source never fails there.
    6: ("parentSlotNotLower", None),
    7: ("arith", NESTED),
    # The source computes every root, so it never fails there.
    8: ("ssz", None),
    9: ("accessor", NESTED),
    10: ("transition", NESTED),
    # A dictionary of the store without the block (phase0/fork-choice.md line 609).
    11: ("unknownBlockTimeliness", KeyError),
    12: ("futureBlock", AssertionError),
    13: ("blockNotAfterFinalized", AssertionError),
    14: ("notDescendantOfFinalized", AssertionError),
    15: ("targetEpochNotRecent", AssertionError),
    16: ("targetEpochMismatch", AssertionError),
    17: ("futureVote", AssertionError),
    18: ("targetNotCheckpointBlock", AssertionError),
    19: ("attestationNotYetDue", AssertionError),
    20: ("invalidIndexedAttestation", AssertionError),
    21: ("notSlashable", AssertionError),
    22: ("boostNotWornOff", AssertionError),
    # Each tick of the source moves its clock, so it never fails there.
    23: ("tickNotAdvancing", None),
    # The source holds every fork, so it never fails there.
    24: ("forkNotYetSpecified", None),
    # The tests of the merge raise their own exception for a proof-of-work block they do not know.
    25: ("unknownPowBlock", BlockNotFoundError),
    26: ("notTerminalPowBlock", AssertionError),
    27: ("terminalBlockHashNotActive", AssertionError),
    28: ("notTerminalBlockHash", AssertionError),
    # The tests of the source give the blobs and the columns, and assert that they are there.
    29: ("blobsUnavailable", AssertionError),
    30: ("kzg", AssertionError),
    31: ("blobsNotMatching", AssertionError),
    32: ("columnsUnavailable", AssertionError),
    33: ("invalidColumns", AssertionError),
    34: ("unknownPayloadVotes", AssertionError),
    35: ("pendingNode", AssertionError),
    36: ("notPreviousSlot", AssertionError),
    37: ("invalidAttestationIndex", AssertionError),
    38: ("sameSlotPayloadVote", AssertionError),
    39: ("payloadNotVerified", AssertionError),
    40: ("notInPtc", AssertionError),
    41: ("ptcVoteNotCurrent", AssertionError),
    42: ("invalidPayloadAttestation", AssertionError),
    43: ("unknownInclusionListSatisfaction", AssertionError),
    44: ("futureInclusionList", AssertionError),
    45: ("inclusionListTooOld", AssertionError),
    46: ("invalidInclusionListSize", AssertionError),
    47: ("emptyInclusionListTransaction", AssertionError),
    48: ("dependentBlockTooLate", AssertionError),
    49: ("notPossibleDependentBlock", AssertionError),
    50: ("notInInclusionListCommittee", AssertionError),
    51: ("invalidInclusionListSignature", AssertionError),
    # The source has no check that a payload is optimistic.
    52: ("payloadNotOptimistic", None),
    # The source never fails there: it returns 0 when the discount reaches its bound.
    # That bound is in phase0/fast-confirmation.md line 599.
    53: ("supportDiscountAboveMaximum", None),
}

# The table of each error type whose constructors a message names.
TABLES = {
    "TransitionError": TRANSITION,
    "AccessorError": ACCESSOR,
    "ArithError": ARITH,
    "ShuffleError": SHUFFLE,
}

# A constructor in a message: `EthLib.<path>.<type>.<name>`, for each type of the tables.
CONSTRUCTOR = re.compile(r"\bEthLib(?:\.\w+)*?\.(" + "|".join(TABLES) + r")\.(\w+)")

# The exceptions that the helper of the source catches, for almost every invalid case.
CAUGHT = (AssertionError, IndexError)

# The exceptions that the block step of a fork choice case catches.
CAUGHT_BY_BLOCK_STEP = (AssertionError, BlockNotFoundError)

# The exceptions that each step of a fork choice compliance case catches.
CAUGHT_BY_COMPLIANCE = (AssertionError,)


def kind_of_message(message: str) -> Kind:
    """The exception of the first constructor in a message that wraps no other error."""
    for error_type, name in CONSTRUCTOR.findall(message):
        kind = TABLES[error_type][name]
        if kind is not NESTED:
            return kind
    raise LookupError(f"no constructor of an EthLib error in the message {message!r}")


def kind_of_fork_choice(code: int, message: str) -> Kind:
    """The exception of a fork choice error, from its code, or from the error that it wraps."""
    _, kind = FORK_CHOICE[code]
    return kind_of_message(message) if kind is NESTED else kind


def check_transition(error: Exception, case: object) -> None:
    """Fail unless the helper of the source catches what it raises where EthLib rejects a case."""
    check(kind_of_message(str(error)), CAUGHT, case, str(error))


def check(kind: Kind, caught: tuple[type[Exception], ...], case: object, message: str) -> None:
    """Fail unless the source catches the exception of a rejection, so that it wrote the case."""
    if not (isinstance(kind, type) and issubclass(kind, caught)):
        name = kind.__name__ if isinstance(kind, type) else "no exception"
        raise AssertionError(f"{case}: the source raises {name} here, not caught: {message}")
