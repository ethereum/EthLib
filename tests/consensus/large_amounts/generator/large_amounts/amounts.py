"""The amounts of the large-amount cases, and the check that an overflow rejects the step."""

import re

# The smallest odd integer above 2^53, which a 64-bit float cannot hold.
ABOVE_FLOAT = 2**53 + 1
# The largest value of a uint64.
UINT64_MAX = 2**64 - 1
# The whole message of the error that a uint64 type of the specification raises out of its range.
OUT_OF_RANGE = re.compile(rf"\d+ is out of range for \w+ \[0, {UINT64_MAX}\]")


def is_above_float(value: int) -> bool:
    """Whether `value` is an odd integer above 2^53, which no 64-bit float holds."""
    return value > 2**53 and value % 2 == 1


def rejects_overflow(step) -> None:
    """Run `step`, which must fail because a uint64 passes 2^64 - 1."""
    try:
        step()
    except ValueError as error:
        if not OUT_OF_RANGE.fullmatch(str(error)):
            raise
        return
    raise AssertionError("the step did not overflow")
