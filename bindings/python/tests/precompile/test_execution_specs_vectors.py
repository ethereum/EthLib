"""The precompiles against the vector files of execution-specs."""

# `tests/execution/precompiles/README.md` gives the origin of the files and their licence.

import hashlib
import json
from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib.precompiles import price, run

from .forks import ends, since

ROOT = Path(__file__).resolve().parents[4]
FILES = ROOT / "tests" / "execution" / "precompiles"
BLS = FILES / "prague" / "eip2537_bls_12_381_precompiles" / "vectors"
P256 = FILES / "osaka" / "eip7951_p256verify_precompiles" / "vectors"
MODEXP = FILES / "osaka" / "eip7883_modexp_gas_increase" / "vector"
KZG = FILES / "cancun" / "eip4844_blobs" / "point_evaluation_vectors"


def _load(path: Path) -> list:
    return json.loads(path.read_text())


def _hex(text: str) -> bytes:
    # One input of legacy.json, legacy-case-24, carries a 0x prefix; the others do not.
    return bytes.fromhex(text.removeprefix("0x"))


def test_digests():
    lines = (FILES / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    entries = [line.split() for line in lines if not line.startswith("#")]
    assert len(entries) == sum(1 for _ in FILES.rglob("*.json")) == 30
    for digest, name in entries:
        assert hashlib.sha256((FILES / name).read_bytes()).hexdigest() == digest, name


# ---- EIP-2537 --------------------------------------------------------------------------------

# The address of the precompile that each file tests.
BLS_ADDRESS = {
    "add_G1_bls": 0x0B,
    "msm_G1_bls": 0x0C,
    "mul_G1_bls": 0x0C,
    "add_G2_bls": 0x0D,
    "msm_G2_bls": 0x0E,
    "mul_G2_bls": 0x0E,
    "pairing_check_bls": 0x0F,
    "map_fp_to_G1_bls": 0x10,
    "map_fp2_to_G2_bls": 0x11,
}

# The error of the Lean specification for each error that the files name.
BLS_ERROR = {
    "invalid input length": "invalidInputLength",
    "invalid field element top bytes": "invalidPadding",
    "invalid fp.Element encoding": "invalidFieldElement",
    "invalid point: not on curve": "notOnCurve",
    "g1 point is not in the correct subgroup": "notInSubgroup",
    "g2 point is not in the correct subgroup": "notInSubgroup",
}

# The MSM cases with at most 8 pairs, copied from msm_G1_bls.json and msm_G2_bls.json.
# The larger cases repeat the inputs that `test_eip2537.py` already runs from the EIP.
MSM = _load(FILES / "msm_up_to_8_pairs.json")

BLS_SUCCESS = [
    pytest.param(BLS_ADDRESS[name], case, id=f"{name}:{case['Name']}")
    for name in sorted(BLS_ADDRESS)
    for case in (MSM[name] if name in MSM else _load(BLS / f"{name}.json"))
]

BLS_FAILURE = [
    pytest.param(BLS_ADDRESS[name], case, id=f"fail-{name}:{case['Name']}")
    for name in sorted(BLS_ADDRESS)
    for case in _load(BLS / f"fail-{name}.json")
]

# A failing case lists no gas, so it runs with more than any of these calls costs.
AMPLE_GAS = 10**9


# The EIP-2537 cases that `test_eip2537.py` runs, keyed by file.
EIP2537 = _load(Path(__file__).parent / "eip2537_cases.json")


def _outcome(case: dict) -> tuple:
    """What a case expects: its output and price, or its error."""
    return (case.get("Expected"), case.get("Gas"), case.get("ExpectedError"))


def _eip_outcomes(names) -> dict:
    """The outcome of each input of the EIP-2537 cases of the given files."""
    return {_hex(case["Input"]): _outcome(case) for name in names for case in EIP2537[name]}


def _new(params: list, eip: dict) -> list:
    """The cases whose input the EIP-2537 files do not hold."""
    return [param for param in params if _hex(param.values[1]["Input"]) not in eip]


BLS_EIP = _eip_outcomes(name for name in EIP2537 if not name.startswith("fail-"))
BLS_FAIL_EIP = _eip_outcomes(name for name in EIP2537 if name.startswith("fail-"))


def test_bls_counts():
    assert (len(BLS_SUCCESS), len(BLS_FAILURE)) == (110, 74)
    # Only two inputs are new: the others repeat those of the EIP-2537 files.
    assert (len(_new(BLS_SUCCESS, BLS_EIP)), len(_new(BLS_FAILURE, BLS_FAIL_EIP))) == (1, 1)


@pytest.mark.parametrize("params, eip", [(BLS_SUCCESS, BLS_EIP), (BLS_FAILURE, BLS_FAIL_EIP)],
                         ids=["success", "failure"])
def test_bls_repeats_agree(params: list, eip: dict) -> None:
    # A repeated input expects the same output, price or error in both sources.
    for param in params:
        case = param.values[1]
        data = _hex(case["Input"])
        if data in eip:
            assert eip[data] == _outcome(case), case["Name"]


@pytest.mark.parametrize("fork", ends("pectra"))
@pytest.mark.parametrize("address, case", BLS_SUCCESS)
def test_bls_price(fork: str, address: int, case: dict) -> None:
    assert price(fork, address, _hex(case["Input"])) == case["Gas"]


@pytest.mark.parametrize("fork", ends("pectra"))
@pytest.mark.parametrize("address, case", _new(BLS_SUCCESS, BLS_EIP))
def test_bls(fork: str, address: int, case: dict) -> None:
    assert run(fork, address, _hex(case["Input"]), case["Gas"]).hex() == case["Expected"]


@pytest.mark.parametrize("fork", ends("pectra"))
@pytest.mark.parametrize("address, case", _new(BLS_FAILURE, BLS_FAIL_EIP))
def test_bls_error(fork: str, address: int, case: dict) -> None:
    with pytest.raises(ValueError, match=rf"\.{BLS_ERROR[case['ExpectedError']]}\b"):
        run(fork, address, _hex(case["Input"]), AMPLE_GAS)


# ---- P256VERIFY (EIP-7951) -------------------------------------------------------------------

P256_CASES = [
    pytest.param(case, id=f"{path.stem}:{case['Name']}")
    for path in sorted(P256.glob("*.json"))
    for case in _load(path)
]

# The cases of EIP-7951 that `test_p256verify.py` runs, by input.
EIP7951 = {_hex(case["Input"]): case["Expected"]
           for case in _load(Path(__file__).parent / "eip7951_cases.json")}


def test_p256_count():
    assert len(P256_CASES) == 294


@pytest.mark.parametrize("case", P256_CASES)
def test_p256verify(case: dict) -> None:
    # Every input repeats one of EIP-7951, with the same output; a signature that does not
    # verify returns no data, which both write as "".
    data = _hex(case["Input"])
    assert EIP7951[data] == case["Expected"]
    for fork in ends("fusaka"):
        assert price(fork, 0x100, data) == case["Gas"]


# ---- MODEXP (EIP-198, EIP-2565, EIP-7883) ----------------------------------------------------

MODEXP_CASES = [pytest.param(case, id=case["Name"]) for case in _load(MODEXP / "vectors.json")]
LEGACY_CASES = [pytest.param(case, id=case["Name"]) for case in _load(MODEXP / "legacy.json")]


def test_modexp_counts():
    assert (len(MODEXP_CASES), len(LEGACY_CASES)) == (46, 32)


@pytest.mark.parametrize("case", MODEXP_CASES)
def test_modexp_prices(case: dict) -> None:
    # GasOld is the price of EIP-2565, from Berlin to Pectra; GasNew that of EIP-7883.
    data = _hex(case["Input"])
    for fork in since("berlin", "fusaka"):
        assert price(fork, 0x05, data) == case["GasOld"], fork
    for fork in since("fusaka"):
        assert price(fork, 0x05, data) == case["GasNew"], fork


@pytest.mark.parametrize("fork", ("byzantium", "berlin", "fusaka", "bpo2"))
@pytest.mark.parametrize("case", MODEXP_CASES + LEGACY_CASES)
def test_modexp_output(fork: str, case: dict) -> None:
    data = _hex(case["Input"])
    assert run(fork, 0x05, data, price(fork, 0x05, data)).hex() == case["Expected"]


# ---- Point evaluation (EIP-4844) -------------------------------------------------------------

def _kzg_key(case: dict) -> tuple:
    fields = case["input"]
    return (fields["commitment"], fields["z"], fields["y"], fields["proof"], case["output"])


def test_point_evaluation_vectors_already_run():
    # The file holds the same 122 cases as tests/cryptography/kzg/verify_kzg_proof, which
    # `test_point_evaluation.py` runs through the precompile; this test checks that they agree.
    # Both repeat 12 inputs under a second name, so each holds 110 distinct cases.
    vectors = ROOT / "tests" / "cryptography" / "kzg" / "verify_kzg_proof"
    ours = {_kzg_key(YAML(typ="safe").load((case / "data.yaml").read_text()))
            for case in vectors.iterdir() if case.is_dir()}
    theirs = [_kzg_key(case) for case in _load(KZG / "go_kzg_4844_verify_kzg_proof.json")]
    assert (len(theirs), len(set(theirs))) == (122, 110)
    assert set(theirs) == ours
