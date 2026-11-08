"""The contract that `lake exe gen-bindings` writes agrees with the built extension."""

import inspect
import json
import re
from pathlib import Path

import pytest

from ethlib import errors
from ethlib.cryptography import _native

CONTRACT = json.loads((Path(__file__).parents[3] / "contract" / "contract.json").read_text())[
    "methods"
]


# The C body of each wrapper, from its name to the closing brace at the start of a line.
WRAPPERS = {
    m.group(1): m.group(2)
    for path in (Path(__file__).parents[2]).glob("*.c")
    for m in re.finditer(r"\n(py_[a-z0-9_]+)\(\n.*?\) \{\n(.*?)\n\}\n", path.read_text(), re.S)
}

# The calls by which a wrapper builds each kind of result.
SIMPLE_RESULTS = {
    "bool": ("except_into_pybool", "Py_RETURN_TRUE"),
    "int": ("except_into_pyint", "PyLong_From"),
    "Any": ("except_into_pyitem",),
    "None": ("Py_None", "Py_RETURN_NONE"),
    "tuple": ("PyTuple_Pack",),
}
RESULT_MARKERS = {
    **SIMPLE_RESULTS,
    "bytes": ("except_into_pybytes", "pybytes_of_bytearray", "PyBytes_FromStringAndSize"),
    "bytes | None": ("Py_None", "Py_RETURN_NONE"),
    "list[bytes]": ("PyList_New", "bytes_list("),
    "tuple[bytes, bytes]": ("PyTuple_Pack",),
    "tuple[list[bytes], list[bytes]]": ("PyTuple_Pack", "cells_and_proofs("),
}


def arity(method) -> int:
    """The number of arguments a wrapper takes, read from the TypeError of a short call."""
    try:
        method()
    except TypeError as error:
        found = re.search(r"(?:exactly|expected) (\d+) arguments?", str(error))
        if found:
            return int(found.group(1))
    raise AssertionError(f"{method.__name__} does not state its arity")


def parameter_count(params: str) -> int:
    """The number of parameters in a signature, whose types may hold commas inside brackets."""
    if not params.strip():
        return 0
    depth = 0
    commas = 0
    for char in params:
        if char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
        elif char == "," and depth == 0:
            commas += 1
    return commas + 1


@pytest.mark.parametrize("entry", CONTRACT, ids=[m["method"] for m in CONTRACT])
def test_method_matches_contract(entry: dict) -> None:
    method = getattr(_native, entry["method"])
    # The method table carries the one-line docstring that the generator wrote.
    assert method.__doc__ == entry["summary"]
    assert "\n" not in method.__doc__
    # The class that the method raises exists in ethlib.errors.
    if entry["error_class"] is not None:
        assert inspect.isclass(getattr(errors, entry["error_class"]))
    # The wrapper states how many arguments it takes when it gets too few.
    params = entry["signature"].split(") ->")[0].lstrip("(")
    assert arity(method) == parameter_count(params)
    # The C wrapper builds the result type that the signature declares.
    returns = entry["signature"].split(") -> ")[1]
    body = WRAPPERS["py_" + entry["method"]]
    # The generic converter of typed values builds a result of any type.
    # Only that converter builds a result of a type that the markers do not name.
    uses_converter = "call_pyvalue_export" in body
    assert uses_converter or returns in RESULT_MARKERS, returns
    assert uses_converter or any(marker in body for marker in RESULT_MARKERS[returns]), returns
    for other, markers in SIMPLE_RESULTS.items():
        if other not in returns:
            assert not any(marker in body for marker in markers), other


def test_contract_covers_every_method() -> None:
    methods = {name for name in dir(_native) if callable(getattr(_native, name))}
    assert methods == {m["method"] for m in CONTRACT}
