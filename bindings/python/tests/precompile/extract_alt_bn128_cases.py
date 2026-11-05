"""Write `alt_bn128_cases.json` from the EIP-196 and EIP-197 tests of execution-specs."""

# Run it on the pinned commit of execution-specs, whose code it never runs:
#
#     python -I extract_alt_bn128_cases.py <execution-specs>/tests/byzantium alt_bn128_cases.json
#
# Python's `ast` parses each test file, and the evaluator below reads each `pytest.param`.
# It knows only literals, arithmetic, the `Spec` constants of each `spec.py` and the encodings.

import ast
import itertools
import json
import operator
import sys
from collections import defaultdict
from pathlib import Path


def fp(x: int) -> bytes:
    """A field element or a scalar as 32 big-endian bytes."""
    return x.to_bytes(32, "big")


class Raw:
    """A byte string that joins with `+`, as the encodings of execution-specs do."""

    def __init__(self, data: bytes):
        self.data = bytes(data)

    def __bytes__(self) -> bytes:
        return self.data

    def __add__(self, other) -> "Raw":
        return Raw(self.data + bytes(other))

    def __radd__(self, other) -> "Raw":
        return Raw(bytes(other) + self.data)

    def __getitem__(self, index) -> "Raw":
        return Raw(self.data[index])


class PointG1(Raw):
    """A G1 point: `x ‖ y`."""

    def __init__(self, x: int = 0, y: int = 0):
        self.x, self.y = x, y
        super().__init__(fp(x) + fp(y))


class PointG2(Raw):
    """A G2 point: the two components of `x`, then those of `y`, in the order given."""

    def __init__(self, x: tuple = (0, 0), y: tuple = (0, 0)):
        self.x, self.y = x, y
        super().__init__(fp(x[0]) + fp(x[1]) + fp(y[0]) + fp(y[1]))


class FP(Raw):
    """One field element or scalar."""

    def __init__(self, x: int = 0):
        self.x = x
        super().__init__(fp(x))


class Namespace:
    """An object with attributes, for `Spec` and `pytest`."""


def int_to_bytes(n: int, length: int, byteorder: str) -> bytes:
    return n.to_bytes(length, byteorder)


BINOPS = {
    ast.Add: operator.add,
    ast.Sub: operator.sub,
    ast.Mult: operator.mul,
    ast.LShift: operator.lshift,
    ast.RShift: operator.rshift,
    ast.BitOr: operator.or_,
    ast.BitAnd: operator.and_,
    ast.BitXor: operator.xor,
    ast.Pow: operator.pow,
    ast.FloorDiv: operator.floordiv,
    ast.Mod: operator.mod,
}
CALLS = {PointG1, PointG2, FP, int, bytes, int_to_bytes}
PYTEST = Namespace()


class Evaluate:
    """The value of an expression node, over a table of names."""

    def __init__(self, names: dict):
        self.names = names

    def __call__(self, node: ast.expr):
        method = getattr(self, "node_" + type(node).__name__, None)
        if method is None:
            raise ValueError(f"unsupported expression: {ast.dump(node)[:120]}")
        return method(node)

    def node_Constant(self, node):
        return node.value

    def node_Name(self, node):
        return self.names[node.id]

    def node_Attribute(self, node):
        base = self(node.value)
        if base is int and node.attr == "to_bytes":
            return int_to_bytes
        if base is PYTEST and node.attr == "HIDDEN_PARAM":
            return None
        return getattr(base, node.attr)

    def node_BinOp(self, node):
        return BINOPS[type(node.op)](self(node.left), self(node.right))

    def node_UnaryOp(self, node):
        if not isinstance(node.op, ast.USub):
            raise ValueError("unsupported unary operator")
        return -self(node.operand)

    def node_Tuple(self, node):
        return tuple(self(e) for e in node.elts)

    def node_Subscript(self, node):
        return self(node.value)[self(node.slice)]

    def node_Slice(self, node):
        part = lambda n: None if n is None else self(n)  # noqa: E731
        return slice(part(node.lower), part(node.upper), part(node.step))

    def node_Call(self, node):
        function = self(node.func)
        if function not in CALLS:
            raise ValueError(f"unsupported call: {function}")
        return function(
            *[self(a) for a in node.args], **{k.arg: self(k.value) for k in node.keywords}
        )


def load_spec(path: Path, names: dict) -> Namespace:
    """The class `Spec` of a `spec.py`, its constants evaluated in order."""
    spec = Namespace()
    evaluate = Evaluate(
        {
            "PointG1": PointG1,
            "PointG2": PointG2,
            "FP": FP,
            "Scalar": FP,
            "Address": int,
            "int": int,
            "bytes": bytes,
            **names,
        }
    )
    for node in ast.parse(path.read_text()).body:
        if isinstance(node, ast.ClassDef) and node.name == "Spec":
            for statement in node.body:
                if isinstance(statement, ast.Assign):
                    value = evaluate(statement.value)
                    for target in statement.targets:
                        setattr(spec, target.id, value)
                        evaluate.names[target.id] = value
    return spec


def is_parametrize(node) -> bool:
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "parametrize"
    )


def rows(node: ast.Call, evaluate: Evaluate) -> tuple[list, list]:
    """The argument names of one `parametrize`, and its rows as (values, id)."""
    names = [s.strip() for s in node.args[0].value.split(",")]
    result = []
    for element in node.args[1].elts:
        if isinstance(element, ast.Call) and getattr(element.func, "attr", "") == "param":
            values = [evaluate(a) for a in element.args]
            case_id = next((evaluate(k.value) for k in element.keywords if k.arg == "id"), None)
        else:
            value = evaluate(element)
            values, case_id = (list(value) if len(names) > 1 else [value]), None
        result.append((values, case_id))
    return names, result


def cases(path: Path, spec: Namespace):
    """Each case of the test functions of one file that take `input_data`."""
    evaluate = Evaluate(
        {
            "Spec": spec,
            "PointG1": PointG1,
            "PointG2": PointG2,
            "FP": FP,
            "Scalar": FP,
            "pytest": PYTEST,
            "int": int,
            "bytes": bytes,
        }
    )
    tree = ast.parse(path.read_text())
    module = [
        d
        for node in tree.body
        if isinstance(node, ast.Assign) and node.targets[0].id == "pytestmark"
        for d in node.value.elts
        if is_parametrize(d)
    ]
    count = defaultdict(int)
    for node in tree.body:
        if not isinstance(node, ast.FunctionDef):
            continue
        sets = [rows(d, evaluate) for d in node.decorator_list if is_parametrize(d)]
        sets += [rows(d, evaluate) for d in module]
        if "input_data" not in [n for names, _ in sets for n in names]:
            continue
        for combination in itertools.product(*[r for _, r in sets]):
            row, ids = {}, []
            for (names, _), (values, case_id) in zip(sets, combination):
                row.update(zip(names, values))
                if case_id is not None:
                    ids.append(case_id)
            # A case with no id gets the one pytest gives it, by its place in the test.
            index = count[node.name]
            count[node.name] += 1
            case_id = "-".join(ids) or f"input_data{index}"
            yield {
                "id": f"{path.stem}::{node.name}[{case_id}]",
                "address": int(row["precompile_address"]),
                "input": bytes(row["input_data"]).hex(),
                "output": bytes(row["expected_output"]).hex(),
                "gas_modifier": row.get("precompile_gas_modifier", 0),
            }


def gas_cases(path: Path, spec: Namespace, address: int):
    """Each case of a `test_gas.py`, which gives a gas modifier but no output."""
    evaluate = Evaluate(
        {
            "Spec": spec,
            "PointG1": PointG1,
            "PointG2": PointG2,
            "FP": FP,
            "Scalar": FP,
            "pytest": PYTEST,
            "int": int,
            "bytes": bytes,
        }
    )
    for node in ast.parse(path.read_text()).body:
        if not isinstance(node, ast.FunctionDef) or not node.name.startswith("test_"):
            continue
        sets = [rows(d, evaluate) for d in node.decorator_list if is_parametrize(d)]
        for combination in itertools.product(*[r for _, r in sets]):
            # The input defaults to the empty call data of the test's STATICCALL.
            row, ids = {"input_data": b"", "precompile_address": address}, []
            for (names, _), (values, case_id) in zip(sets, combination):
                row.update(zip(names, values))
                ids.append(str(case_id if case_id is not None else values[0]))
            # The EIP-196 file names its invalid input `invalid_input`.
            row["input_data"] = row.get("invalid_input", row["input_data"])
            if "enough_gas" in row:
                # A call with its price succeeds, with an output the file does not give.
                # One unit of gas less fails.
                modifier, output = (0, None) if row["enough_gas"] else (-1, "")
            else:
                # An invalid input fails with its price, and with extra gas too.
                modifier, output = row["extra_gas"], ""
            yield {
                "id": f"{path.parent.name}/{path.stem}::{node.name}[{'-'.join(ids)}]",
                "address": int(row["precompile_address"]),
                "input": bytes(row["input_data"]).hex(),
                "output": output,
                "gas_modifier": modifier,
            }


def main() -> None:
    byzantium, out = Path(sys.argv[1]), Path(sys.argv[2])
    add_mul, pairing = byzantium / "eip196_ec_add_mul", byzantium / "eip197_ec_pairing"
    spec196 = load_spec(add_mul / "spec.py", {})
    spec197 = load_spec(pairing / "spec.py", {"Spec196": spec196})
    result = [
        c for name in ("test_ecadd.py", "test_ecmul.py") for c in cases(add_mul / name, spec196)
    ]
    result += [
        c
        for name in ("test_ecpairing.py", "test_ecpairing_fuzzed.py")
        for c in cases(pairing / name, spec197)
    ]
    result += list(gas_cases(add_mul / "test_gas.py", spec196, 0x06))
    result += list(gas_cases(pairing / "test_gas.py", spec197, 0x08))
    assert len({c["id"] for c in result}) == len(result), "duplicate id"
    out.write_text(json.dumps(result, indent=1) + "\n")


if __name__ == "__main__":
    main()
