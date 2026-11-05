"""Write the SSZ vectors of the EIP-8450 containers with the Python SSZ of ssz-specs."""

import hashlib
import sys
from pathlib import Path

from ssz import ByteVector, Container, ProgressiveList, Uint64, hash_tree_root


class Bytes32(ByteVector):
    LENGTH = 32


class Bytes48(ByteVector):
    LENGTH = 48


class Bytes96(ByteVector):
    LENGTH = 96


class XMSSPublicKey(ByteVector):
    LENGTH = 32


class XMSSSignature(ByteVector):
    LENGTH = 2404


class PQKeyMaterial(Container):
    xmss_public_key: XMSSPublicKey
    vrf_root: Bytes32


class PQKeyRegistration(Container):
    index: Uint64
    key_material: PQKeyMaterial
    previous_change_epoch: Uint64


class PQKeyPossession(Container):
    pubkey: Bytes48
    xmss_public_key: XMSSPublicKey


class SignedPQKeyRegistration(Container):
    message: PQKeyRegistration
    possession: XMSSSignature
    signature: Bytes96


class ValidatorPQKeyMaterial(ProgressiveList[PQKeyMaterial]):
    pass


class ValidatorPQKeyChangeEpochs(ProgressiveList[Uint64]):
    pass


class BuilderPQKeyMaterial(ProgressiveList[PQKeyMaterial]):
    pass


class BuilderPQKeyChangeEpochs(ProgressiveList[Uint64]):
    pass


class PQKeyRegistrations(ProgressiveList[SignedPQKeyRegistration]):
    pass


def stream(label: str, n: int) -> bytes:
    """The first n bytes of SHA-256 of a label and a counter, counter after counter."""
    out = b""
    counter = 0
    while len(out) < n:
        out += hashlib.sha256(f"{label}/{counter}".encode()).digest()
        counter += 1
    return out[:n]


def material(label: str) -> PQKeyMaterial:
    """Keys from a label."""
    data = stream(label, 64)
    return PQKeyMaterial(xmss_public_key=XMSSPublicKey(data[:32]), vrf_root=Bytes32(data[32:]))


def registration(label: str) -> PQKeyRegistration:
    """A registration message from a label."""
    data = stream(label, 16)
    return PQKeyRegistration(
        index=Uint64(int.from_bytes(data[:8], "little")),
        key_material=material(label + "/keys"),
        previous_change_epoch=Uint64(int.from_bytes(data[8:], "little")),
    )


def signed(label: str) -> SignedPQKeyRegistration:
    """A signed registration from a label."""
    data = stream(label, 2404 + 96)
    return SignedPQKeyRegistration(
        message=registration(label + "/message"),
        possession=XMSSSignature(data[:2404]),
        signature=Bytes96(data[2404:]),
    )


def epoch(label: str) -> Uint64:
    """An epoch from a label."""
    return Uint64(int.from_bytes(stream(label, 8), "little"))


def valid_cases() -> dict:
    """Every valid case, by container and case name."""
    builder_key = XMSSPublicKey(stream("builder", 32))
    cases = {
        "PQKeyMaterial": {
            "zero": PQKeyMaterial(),
            "ones": PQKeyMaterial(xmss_public_key=XMSSPublicKey(b"\xff" * 32),
                                  vrf_root=Bytes32(b"\xff" * 32)),
            "builder": PQKeyMaterial(xmss_public_key=builder_key),
            "random": material("random"),
        },
        "PQKeyRegistration": {
            "zero": PQKeyRegistration(),
            "never_registered": PQKeyRegistration(
                index=Uint64(7), key_material=material("first"),
                previous_change_epoch=Uint64(2**64 - 1)),
            "builder": PQKeyRegistration(
                index=Uint64(2**40), key_material=PQKeyMaterial(xmss_public_key=builder_key),
                previous_change_epoch=Uint64(5)),
            "random": registration("random"),
        },
        "PQKeyPossession": {
            "zero": PQKeyPossession(),
            "random": PQKeyPossession(pubkey=Bytes48(stream("pubkey", 48)),
                                      xmss_public_key=XMSSPublicKey(stream("xmss", 32))),
        },
        "SignedPQKeyRegistration": {
            "zero": SignedPQKeyRegistration(),
            "random": signed("random"),
        },
    }
    for name, cls, item in [
        ("ValidatorPQKeyMaterial", ValidatorPQKeyMaterial, material),
        ("BuilderPQKeyMaterial", BuilderPQKeyMaterial, material),
        ("ValidatorPQKeyChangeEpochs", ValidatorPQKeyChangeEpochs, epoch),
        ("BuilderPQKeyChangeEpochs", BuilderPQKeyChangeEpochs, epoch),
    ]:
        # The subtrees of a progressive list hold 1, 4, 16 and 64 chunks, so the lengths cross them.
        cases[name] = {
            f"length_{n}": cls(data=[item(f"{name}/{i}") for i in range(n)])
            for n in (0, 1, 2, 5, 21, 100)
        }
    cases["PQKeyRegistrations"] = {
        f"length_{n}": PQKeyRegistrations(data=[signed(f"block/{i}") for i in range(n)])
        for n in (0, 1, 2, 8)
    }
    return cases


def invalid_cases() -> dict:
    """Every invalid case, by container and case name: bytes that encode no value."""
    out = {}
    for name, size in [("PQKeyMaterial", 64), ("PQKeyRegistration", 80),
                       ("PQKeyPossession", 80), ("SignedPQKeyRegistration", 2580)]:
        out[name] = {"one_byte_short": stream(name, size - 1),
                     "one_byte_long": stream(name, size + 1), "empty": b""}
    for name, size in [("ValidatorPQKeyMaterial", 64), ("BuilderPQKeyMaterial", 64),
                       ("ValidatorPQKeyChangeEpochs", 8), ("BuilderPQKeyChangeEpochs", 8),
                       ("PQKeyRegistrations", 2580)]:
        out[name] = {"partial_element": stream(name, 2 * size + 1)}
    return out


def rejects(name: str, data: bytes) -> bool:
    """Whether the implementation rejects the bytes as the container."""
    try:
        globals()[name].decode_bytes(data)
    except Exception:
        return True
    return False


def main(out: Path) -> None:
    """Write one data.yaml per case under the directory."""
    for name, cases in valid_cases().items():
        for case, value in cases.items():
            data = value.encode_bytes()
            assert type(value).decode_bytes(data) == value
            path = out / name / case
            path.mkdir(parents=True, exist_ok=True)
            root = bytes(hash_tree_root(value)).hex()
            (path / "data.yaml").write_text(f"serialized: '0x{data.hex()}'\nroot: '0x{root}'\n")
    for name, cases in invalid_cases().items():
        for case, data in cases.items():
            assert rejects(name, data), (name, case)
            path = out / name / f"invalid_{case}"
            path.mkdir(parents=True, exist_ok=True)
            (path / "data.yaml").write_text(f"serialized: '0x{data.hex()}'\nroot: null\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
