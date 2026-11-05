"""The pairing of BLS12-381 against the value that the pairing-friendly curves draft publishes."""

import pytest
from py_ecc.bls.point_compression import compress_G1, compress_G2
from py_ecc.optimized_bls12_381 import G1, G2, Z1, Z2, multiply, neg

from ethlib.cryptography import bls
from ethlib.errors import BlsError
from raising import raises

# e(G1, G2), the coefficients e_0 to e_11 of draft-irtf-cfrg-pairing-friendly-curves-11,
# Appendix B, BLS12_381: https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11
PAIRING_OF_GENERATORS = [
    0x11619B45F61EDFE3B47A15FAC19442526FF489DCDA25E59121D9931438907DFD448299A87DDE3A649BDBA96E84D54558,
    0x153CE14A76A53E205BA8F275EF1137C56A566F638B52D34BA3BF3BF22F277D70F76316218C0DFD583A394B8448D2BE7F,
    0x095668FB4A02FE930ED44767834C915B283B1C6CA98C047BD4C272E9AC3F3BA6FF0B05A93E59C71FBA77BCE995F04692,
    0x16DEEDAA683124FE7260085184D88F7D036B86F53BB5B7F1FC5E248814782065413E7D958D17960109EA006B2AFDEB5F,
    0x09C92CF02F3CD3D2F9D34BC44EEE0DD50314ED44CA5D30CE6A9EC0539BE7A86B121EDC61839CCC908C4BDDE256CD6048,
    0x111061F398EFC2A97FF825B04D21089E24FD8B93A47E41E60EAE7E9B2A38D54FA4DEDCED0811C34CE528781AB9E929C7,
    0x01ECFCF31C86257AB00B4709C33F1C9C4E007659DD5FFC4A735192167CE197058CFB4C94225E7F1B6C26AD9BA68F63BC,
    0x08890726743A1F94A8193A166800B7787744A8AD8E2F9365DB76863E894B7A11D83F90D873567E9D645CCF725B32D26F,
    0x0E61C752414CA5DFD258E9606BAC08DAEC29B3E2C57062669556954FB227D3F1260EEDF25446A086B0844BCD43646C10,
    0x0FE63F185F56DD29150FC498BBEEA78969E7E783043620DB33F75A05A0A2CE5C442BEAFF9DA195FF15164C00AB66BDDE,
    0x10900338A92ED0B47AF211636F7CFDEC717B7EE43900EEE9B5FC24F0000C5874D4801372DB478987691C566A8C474978,
    0x1454814F3085F0E6602247671BC408BBCE2007201536818C901DBD4D2095DD86C1EC8B888E59611F60A301AF7776BE3D,
]

ONE = (1).to_bytes(48, "big") + bytes(48 * 11)


def g1(point) -> bytes:
    return compress_G1(point).to_bytes(48, "big")


def g2(point) -> bytes:
    z1, z2 = compress_G2(point)
    return z1.to_bytes(48, "big") + z2.to_bytes(48, "big")


def coefficients(out: bytes) -> list[int]:
    assert len(out) == 12 * 48
    return [int.from_bytes(out[48 * i : 48 * (i + 1)], "big") for i in range(12)]


def test_pairing_of_generators() -> None:
    # The evidence for the pairing law: EthLib's pairing of the generators is the published one.
    assert coefficients(bls.pairing(g1(G1), g2(G2))) == PAIRING_OF_GENERATORS


def test_pairing_is_not_one() -> None:
    # Non-degeneracy on the generators: e(G1, G2) is not the identity.
    assert bls.pairing(g1(G1), g2(G2)) != ONE


def test_pairing_bilinear() -> None:
    # e(6 G1, 5 G2) = e(30 G1, G2) = e(G1, 30 G2).
    left = bls.pairing(g1(multiply(G1, 6)), g2(multiply(G2, 5)))
    assert left == bls.pairing(g1(multiply(G1, 30)), g2(G2))
    assert left == bls.pairing(g1(G1), g2(multiply(G2, 30)))
    # Negating one argument gives another value.
    assert bls.pairing(g1(neg(G1)), g2(G2)) != bls.pairing(g1(G1), g2(G2))


@pytest.mark.parametrize("p, q", [(Z1, G2), (G1, Z2), (Z1, Z2)])
def test_pairing_with_infinity(p, q) -> None:
    assert bls.pairing(g1(p), g2(q)) == ONE


def test_pairing_rejects_bad_point() -> None:
    # 48 zero bytes lack the compression flag, so they encode no point.
    with raises(BlsError, "invalid G1 point"):
        bls.pairing(bytes(48), g2(G2))
