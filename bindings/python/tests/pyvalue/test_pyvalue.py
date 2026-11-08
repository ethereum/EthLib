"""The generic converter between Python values and Lean values, through an export that echoes."""

import string
from collections.abc import Callable
from enum import IntEnum
from typing import NoReturn

import pytest
from hypothesis import given, settings, strategies as st

from ethlib.cryptography import _native
from ethlib.errors import BindingError
from raising import raises

# The deepest nesting that the converter accepts, as the C layer bounds it.
MAX_DEPTH = 64

# The widest int that the converter accepts, in bits.
MAX_INT_BITS = 65536

# The most parts that one call may pass, counting each value inside a container.
MAX_PARTS = 1 << 22

# The most bytes that one call may pass, over its bytes, its str and its large int.
MAX_BYTES = 1 << 29

# Values of every kind that the converter knows, small and large.
leaves = st.one_of(
    st.none(),
    st.booleans(),
    st.integers(min_value=0, max_value=2**64 + 1),
    st.integers(min_value=0, max_value=2**4096),
    st.binary(max_size=64),
    st.text(st.characters(exclude_categories=("Cs",)), max_size=16),
)


def containers(children: st.SearchStrategy[object]) -> st.SearchStrategy[object]:
    """Lists, tuples and dicts with keys of text, of values from the children."""
    return st.one_of(
        st.lists(children, max_size=4),
        st.lists(children, max_size=4).map(tuple),
        st.dictionaries(st.text(max_size=4), children, max_size=4),
    )


values = st.recursive(leaves, containers, max_leaves=40)


def same(left: object, right: object) -> bool:
    """Whether two values are equal, with the same type at every position."""
    if type(left) is not type(right):
        return False
    if isinstance(left, list | tuple):
        assert isinstance(right, list | tuple)
        return len(left) == len(right) and all(map(same, left, right))
    if isinstance(left, dict):
        assert isinstance(right, dict)
        return list(left) == list(right) and all(same(left[k], right[k]) for k in left)
    if isinstance(left, BindingError):
        assert isinstance(right, BindingError)
        return (left.code, left.message) == (right.code, right.message)
    return left == right


def nested(depth: int, leaf: object = 0) -> object:
    """A leaf inside lists, nested to a depth."""
    value = leaf
    for _ in range(depth):
        value = [value]
    return value


@settings(max_examples=300)
@given(values)
def test_a_value_comes_back_unchanged(value: object) -> None:
    assert same(_native.pyvalue_echo(value), value)


def with_failures(value: object, failures: Callable[[int, str], object]) -> object:
    """The value with each tuple ("failure", code, message) replaced by what failures make of it."""
    if isinstance(value, tuple) and len(value) == 3 and value[0] == "failure":
        _, code, message = value
        if isinstance(code, int) and not isinstance(code, bool) and code < 2**32:
            if isinstance(message, str):
                return failures(code, message)
    if isinstance(value, list):
        return [with_failures(item, failures) for item in value]
    if isinstance(value, tuple):
        return tuple(with_failures(item, failures) for item in value)
    if isinstance(value, dict):
        return {key: with_failures(item, failures) for key, item in value.items()}
    return value


failure_tuples = st.tuples(
    st.just("failure"),
    st.integers(min_value=0, max_value=2**32 - 1),
    st.text(st.characters(exclude_categories=("Cs",)), max_size=16),
)

values_with_failures = st.recursive(st.one_of(leaves, failure_tuples), containers, max_leaves=40)


@settings(max_examples=300)
@given(values_with_failures)
def test_a_failure_becomes_an_error_of_the_method_at_any_position(value: object) -> None:
    expected = with_failures(value, BindingError)
    assert same(_native.pyvalue_echo(value), expected)


def test_a_failure_at_the_top_is_returned_not_raised() -> None:
    error = _native.pyvalue_echo(("failure", 7, "bad step"))
    assert isinstance(error, BindingError)
    assert (error.code, error.message) == (7, "bad step")


def test_a_code_beyond_32_bits_is_no_failure() -> None:
    value = ("failure", 2**32, "bad step")
    assert same(_native.pyvalue_echo(value), value)


def test_a_subclass_of_int_comes_back_as_an_int() -> None:
    class Kind(IntEnum):
        BLOCK = 3

    assert same(_native.pyvalue_echo(Kind.BLOCK), 3)


def test_the_deepest_nesting_passes() -> None:
    value = nested(MAX_DEPTH)
    assert same(_native.pyvalue_echo(value), value)


def test_a_deeper_nesting_fails() -> None:
    with raises(ValueError, f"cannot pass a value nested deeper than {MAX_DEPTH} to Lean"):
        _native.pyvalue_echo(nested(MAX_DEPTH + 1))


def test_a_very_deep_nesting_fails_without_a_crash() -> None:
    with raises(ValueError, f"cannot pass a value nested deeper than {MAX_DEPTH} to Lean"):
        _native.pyvalue_echo(nested(100_000))


def test_the_widest_int_passes() -> None:
    value = 2**MAX_INT_BITS - 1
    assert same(_native.pyvalue_echo(value), value)


def test_a_wider_int_fails() -> None:
    with raises(ValueError, f"cannot pass an int of more than {MAX_INT_BITS} bits to Lean"):
        _native.pyvalue_echo([2**MAX_INT_BITS])


def test_a_huge_int_fails_at_once() -> None:
    with raises(ValueError, f"cannot pass an int of more than {MAX_INT_BITS} bits to Lean"):
        _native.pyvalue_echo(1 << 8_000_000)


def test_a_negative_int_fails() -> None:
    with raises(ValueError, "cannot pass a negative int to Lean"):
        _native.pyvalue_echo([1, -(2**70)])


@pytest.mark.parametrize(
    ("value", "kind"),
    [
        (1.5, "float"),
        ({1, 2}, "set"),
        (bytearray(b"ab"), "bytearray"),
        (memoryview(b"ab"), "memoryview"),
        (object(), "object"),
    ],
)
def test_a_value_of_another_type_fails(value: object, kind: str) -> None:
    with raises(TypeError, f"cannot pass a value of type {kind} to Lean"):
        _native.pyvalue_echo([value])


def test_a_key_that_is_not_text_fails() -> None:
    with raises(TypeError, "cannot pass a dict key of type int to Lean"):
        _native.pyvalue_echo({1: 2})


def test_a_lone_surrogate_fails() -> None:
    message = "'utf-8' codec can't encode character '\\ud800' in position 0: surrogates not allowed"
    with raises(UnicodeEncodeError, message):
        _native.pyvalue_echo("\ud800")


def test_shared_lists_count_each_time_they_appear() -> None:
    # Forty objects stand for 2^40 parts, so the converter must stop before it builds them.
    value: object = 0
    for _ in range(40):
        value = [value, value]
    with raises(ValueError, f"cannot pass more than {MAX_PARTS} parts to Lean in one call"):
        _native.pyvalue_echo(value)


def test_the_most_parts_pass() -> None:
    # The tuple of the arguments, the list and its items are the parts.
    value = [0] * (MAX_PARTS - 2)
    assert same(_native.pyvalue_echo(value), value)
    with raises(ValueError, f"cannot pass more than {MAX_PARTS} parts to Lean in one call"):
        _native.pyvalue_echo([0] * (MAX_PARTS - 1))


# The zero bytes of `bytes(n)` take no memory until something writes them.
def test_too_many_bytes_fail() -> None:
    with raises(ValueError, f"cannot pass more than {MAX_BYTES} bytes to Lean in one call"):
        _native.pyvalue_echo(bytes(MAX_BYTES + 1))


def test_one_bytes_passed_twice_counts_twice() -> None:
    with raises(ValueError, f"cannot pass more than {MAX_BYTES} bytes to Lean in one call"):
        _native.pyvalue_echo([bytes(MAX_BYTES // 2 + 1)] * 2)


class Keys(dict):
    """A dict whose methods lie about its keys."""

    def __iter__(self) -> NoReturn:
        raise RuntimeError("never read through iteration")

    def keys(self) -> NoReturn:
        raise RuntimeError("never read through keys")


def test_a_dict_is_read_from_its_storage() -> None:
    value = Keys({"k": 1})
    assert same(_native.pyvalue_echo([value]), [{"k": 1}])


# Values that the converter may refuse, mixed with values that it accepts.
hostile_leaves = st.one_of(
    leaves,
    st.integers(max_value=-1),
    st.floats(),
    st.binary().map(bytearray),
    st.sets(st.integers(), max_size=2),
    st.text(alphabet=string.printable + "𐏿", max_size=4),
    st.integers(min_value=MAX_DEPTH - 2, max_value=MAX_DEPTH + 2).map(nested),
)


def hostile_containers(children: st.SearchStrategy[object]) -> st.SearchStrategy[object]:
    """Containers, with dicts whose keys may not be text."""
    return st.one_of(
        containers(children),
        st.dictionaries(st.one_of(st.integers(), st.binary(max_size=2)), children, max_size=2),
    )


@settings(max_examples=500)
@given(st.recursive(hostile_leaves, hostile_containers, max_leaves=30))
def test_any_value_comes_back_or_fails_with_a_typed_error(value: object) -> None:
    try:
        out = _native.pyvalue_echo(value)
    except (TypeError, ValueError):
        return
    assert same(out, value)
