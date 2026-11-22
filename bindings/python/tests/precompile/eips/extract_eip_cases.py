"""Write the three case files of this directory from the EIP-2537 and EIP-7951 assets of EIPs."""

# Run it on the pinned commit of EIPs, with the directory of this file as the output:
#
#     python -I extract_eip_cases.py <EIPs>/assets .
#
# It keeps the fields that the tests read, in the order of the assets, and drops the others.

import json
import sys
from pathlib import Path

# The EIP-2537 files that succeed, in the order the cases file keeps them.
# Each has a file of failing cases, named with the prefix `fail-`.
EIP2537 = [
    "add_G1_bls",
    "add_G2_bls",
    "mul_G1_bls",
    "mul_G2_bls",
    "msm_G1_bls",
    "msm_G2_bls",
    "map_fp_to_G1_bls",
    "map_fp2_to_G2_bls",
    "pairing_check_bls",
]

# The size in bytes of one MSM pair: a point and a 32-byte scalar.
# A G1 point takes 128 bytes, and a G2 point 256.
PAIR_SIZE = {"msm_G1_bls": 160, "msm_G2_bls": 288}

# An MSM with more pairs than this is kept apart, as one pair and a count.
MAX_PAIRS = 8


def pairs(name: str, case: dict) -> int:
    """The number of MSM pairs in the input of a case."""
    return len(bytes.fromhex(case["Input"])) // PAIR_SIZE[name]


def is_large(name: str, case: dict) -> bool:
    """Whether a case is an MSM with more than `MAX_PAIRS` pairs."""
    return name in PAIR_SIZE and pairs(name, case) > MAX_PAIRS


def eip2537_cases(assets: Path) -> dict:
    """Every EIP-2537 case except the large MSMs, keyed by file name."""
    result = {}
    for name in EIP2537:
        rows = json.loads((assets / "eip-2537" / f"{name}.json").read_text())
        result[name] = [
            {"Name": c["Name"], "Input": c["Input"], "Expected": c["Expected"], "Gas": c["Gas"]}
            for c in rows
            if not is_large(name, c)
        ]
    for name in EIP2537:
        rows = json.loads((assets / "eip-2537" / f"fail-{name}.json").read_text())
        result[f"fail-{name}"] = [
            {"Name": c["Name"], "Input": c["Input"], "ExpectedError": c["ExpectedError"]}
            for c in rows
        ]
    return result


def eip2537_msm_repeated(assets: Path) -> dict:
    """The large MSM cases, each input written as one pair and its count."""
    result = {}
    for name, size in PAIR_SIZE.items():
        rows = json.loads((assets / "eip-2537" / f"{name}.json").read_text())
        large = [c for c in rows if is_large(name, c)]
        # Every large input repeats one pair, so the pair and the count give the input back.
        pair = large[0]["Input"][: 2 * size]
        cases = []
        for c in large:
            count = pairs(name, c)
            assert c["Input"] == pair * count, c["Name"]
            cases.append(
                {"Name": c["Name"], "Count": count, "Expected": c["Expected"], "Gas": c["Gas"]}
            )
        result[name] = {"Pair": pair, "Cases": cases}
    return result


def eip7951_cases(assets: Path) -> list:
    """Every EIP-7951 case, without its price and its benchmark flag."""
    rows = json.loads((assets / "eip-7951" / "test-vectors.json").read_text())
    return [{"Name": c["Name"], "Input": c["Input"], "Expected": c["Expected"]} for c in rows]


def main() -> None:
    assets, out = Path(sys.argv[1]), Path(sys.argv[2])
    (out / "eip2537_cases.json").write_text(json.dumps(eip2537_cases(assets), indent=1) + "\n")
    (out / "eip2537_msm_repeated.json").write_text(
        json.dumps(eip2537_msm_repeated(assets), indent=1) + "\n"
    )
    (out / "eip7951_cases.json").write_text(json.dumps(eip7951_cases(assets), indent=1))


if __name__ == "__main__":
    main()
