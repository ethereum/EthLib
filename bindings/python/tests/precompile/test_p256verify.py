"""P256VERIFY against every vector of EIP-7951.

`eip7951_cases.json` holds every case of `assets/eip-7951/test-vectors.json` in `ethereum/EIPs`,
at commit `d386b29b5a31bd5cfd8d21bbf4e8a0c87734085e`.

The EIP derives them from `ecdsa_secp256r1_sha256_p1363_test.json` of `C2SP/wycheproof`,
under the Apache License 2.0, a copy of which is `scripts/Apache-2.0.txt`.

Each case runs with the price, 6900 gas.
The EIP lists 3450 gas, the price of an earlier draft, so that field is dropped.
"""

import json
from pathlib import Path

import pytest

from ethlib.precompiles import run

CASES = json.loads((Path(__file__).parent / "eip7951_cases.json").read_text())


@pytest.mark.parametrize("case", CASES, ids=[case["Name"] for case in CASES])
def test_vector(case: dict) -> None:
    # A valid signature gives the word 1, and every invalid input gives empty output.
    assert run(0x100, bytes.fromhex(case["Input"]), 6900).hex() == case["Expected"]


def test_out_of_gas() -> None:
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x100, bytes.fromhex(CASES[0]["Input"]), 6899)
