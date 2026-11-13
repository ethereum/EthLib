"""The pinned libp2p TLS certificates and their malformed boundaries."""

from typing import TYPE_CHECKING

import pytest

from ethlib.networking.libp2p import tls
from raising import raises

# libp2p/specs c750236de43cd8b246a824b377dfdb26bae686db, tls/tls.md, "Test vectors" 1 to 4.
# Vector 3 authenticates a secp256k1 identity.
# Vector 4 pairs a peer ID with a key that did not sign it, so its host signature fails.
CERTIFICATE = bytes.fromhex(
    "308201ba3082015fa0030201020204499602d2300a06082a8648ce3d040302302031123010060355040a13096c696270"
    "32702e696f310a300806035504051301313020170d3735303130313133303030305a180f343039363031303131333030"
    "30305a302031123010060355040a13096c69627032702e696f310a300806035504051301313059301306072a8648ce3d"
    "020106082a8648ce3d030107034200040c901d423c831ca85e27c73c263ba132721bb9d7a84c4f0380b2a6756fd60133"
    "1c8870234dec878504c174144fa4b14b66a651691606d8173e55bd37e381569ea38184308181307f060a2b0601040183"
    "a25a01010471306f0425080212210206dc6968726765b820f050263ececf7f71e4955892776c0970542efd689d238204"
    "4630440220145e15a991961f0d08cd15425bb95ec93f6ffa03c5a385eedc34ecf464c7a8ab022026b3109b8a3f40ef83"
    "3169777eb2aa337cfb6282f188de0666d1bcec2a4690dd300a06082a8648ce3d0403020349003046022100e1a217eeef"
    "9ec9204b3f774a08b70849646b6a1e6b8b27f93dc00ed58545d9fe022100b00dafa549d0f03547878338c7b15e750288"
    "8f6d45db387e5ae6b5d46899cef0"
)
WRONG_HOST_SIGNATURE = bytes.fromhex(
    "308201f73082019da0030201020204499602d2300a06082a8648ce3d040302302031123010060355040a13096c696270"
    "32702e696f310a300806035504051301313020170d3735303130313133303030305a180f343039363031303131333030"
    "30305a302031123010060355040a13096c69627032702e696f310a300806035504051301313059301306072a8648ce3d"
    "020106082a8648ce3d030107034200040c901d423c831ca85e27c73c263ba132721bb9d7a84c4f0380b2a6756fd60133"
    "1c8870234dec878504c174144fa4b14b66a651691606d8173e55bd37e381569ea381c23081bf3081bc060a2b06010401"
    "83a25a01010481ad3081aa045f0803125b3059301306072a8648ce3d020106082a8648ce3d03010703420004bf30511f"
    "909414ebdd3242178fd290f093a551cf75c973155de0bb5a96fedf6cb5d52da7563e794b512f66e60c7f55ba8a3acf3d"
    "d72a801980d205e8a1ad29f204473045022100bb6e03577b7cc7a3cd1558df0da2b117dfdcc0399bc2504ebe7de6f65c"
    "ade72802206de96e2a5be9b6202adba24ee0362e490641ac45c240db71fe955f2c5cf8df6e300a06082a8648ce3d0403"
    "020348003045022100e847f267f43717358f850355bdcabbefb2cfbf8a3c043b203a14788a092fe8db022027c1d04a2d"
    "41fd6b57a7e8b3989e470325de4406e52e084e34a3fd56eef0d0df"
)
# Vector 2 authenticates an ECDSA P-256 identity.
P256_HOST_CERTIFICATE = bytes.fromhex(
    "308201f63082019da0030201020204499602d2300a06082a8648ce3d040302302031123010060355040a13096c696270"
    "32702e696f310a300806035504051301313020170d3735303130313133303030305a180f343039363031303131333030"
    "30305a302031123010060355040a13096c69627032702e696f310a300806035504051301313059301306072a8648ce3d"
    "020106082a8648ce3d030107034200040c901d423c831ca85e27c73c263ba132721bb9d7a84c4f0380b2a6756fd60133"
    "1c8870234dec878504c174144fa4b14b66a651691606d8173e55bd37e381569ea381c23081bf3081bc060a2b06010401"
    "83a25a01010481ad3081aa045f0803125b3059301306072a8648ce3d020106082a8648ce3d03010703420004bf30511f"
    "909414ebdd3242178fd290f093a551cf75c973155de0bb5a96fedf6cb5d52da7563e794b512f66e60c7f55ba8a3acf3d"
    "d72a801980d205e8a1ad29f2044730450220064ea8124774caf8f50e57f436aa62350ce652418c019df5d98a3ac666c9"
    "386a022100aa59d704a931b5f72fb9222cb6cc51f954d04a4e2e5450f8805fe8918f71eaae300a06082a8648ce3d0403"
    "0203470030440220799395b0b6c1e940a7e4484705f610ab51ed376f19ff9d7c16757cfbf61b8d4302206205c03fbb0f"
    "95205c779be86581d3e31c01871ad5d1f3435bcf375cb0e5088a"
)
# Vector 1 authenticates an Ed25519 identity, a host-key type EthLib does not check.
ED25519_HOST_CERTIFICATE = bytes.fromhex(
    "308201ae30820156a0030201020204499602d2300a06082a8648ce3d040302302031123010060355040a13096c696270"
    "32702e696f310a300806035504051301313020170d3735303130313133303030305a180f343039363031303131333030"
    "30305a302031123010060355040a13096c69627032702e696f310a300806035504051301313059301306072a8648ce3d"
    "020106082a8648ce3d030107034200040c901d423c831ca85e27c73c263ba132721bb9d7a84c4f0380b2a6756fd60133"
    "1c8870234dec878504c174144fa4b14b66a651691606d8173e55bd37e381569ea37c307a3078060a2b0601040183a25a"
    "0101046a3068042408011220a77f1d92fedb59dddaea5a1c4abd1ac2fbde7d7b879ed364501809923d7c11b90440d90d"
    "2769db992d5e6195dbb08e706b6651e024fda6cfb8846694a435519941cac215a8207792e42849cccc6cd8136c6e4bde"
    "92a58c5e08cfd4206eb5fe0bf909300a06082a8648ce3d0403020346003043021f50f6b6c52711a881778718238f650c"
    "9fb48943ae6ee6d28427dc6071ae55e702203625f116a7a454db9c56986c82a25682f7248ea1cb764d322ea983ed36a3"
    "1b77"
)
# Binary form of vector 3's peer ID 16Uiu2HAkutTMoTzDw1tCvSRtu6YoixJwS46S1ZFxW8hSx9fWHiPs.
# It is the identity multihash 00 25 of the key protobuf.
PEER_ID = bytes.fromhex(
    "0025080212210206dc6968726765b820f050263ececf7f71e4955892776c0970542efd689d2382"
)
# Binary form of vector 2's peer ID QmfXbAwNjJLXfesgztEHe8HwgVDCMMpZ9Eax1HYq6hn9uE.
P256_PEER_ID = bytes.fromhex("1220ff6411214402e7c0b3dd3b1095b53b4eb2202f7fd3e84df88268a531b0a61a1d")
# The test explicitly enables implemented algorithms, without defining an application profile.
POLICY: tls.Policy = {
    "host_algorithms": ["secp256k1", "p256"],
    "certificate_algorithms": ["p256_sha256"],
    "reject_unique_ids": True,
}
# 2027-01-15, inside the validity interval of every vector.
NOW = 1_800_000_000
# 1975-01-01T13:00:00Z and 4096-01-01T13:00:00Z, the validity endpoints of every vector.
NOT_BEFORE = 157_813_200
NOT_AFTER = 67_090_165_200
ERROR = "TLS certificate rejected: EthLib.Networking.Libp2p.Tls.TlsCertError."


def test_published_secp256k1_certificate() -> None:
    assert tls.authenticate(POLICY, NOW, [CERTIFICATE]) == PEER_ID
    assert tls.authenticate_peer(POLICY, NOW, PEER_ID, [CERTIFICATE]) == PEER_ID


def test_published_wrong_host_signature() -> None:
    with raises(tls.TlsCertificateError, ERROR + "hostSignature") as info:
        tls.authenticate(POLICY, NOW, [WRONG_HOST_SIGNATURE])
    assert info.value.code == 12


def test_preserves_the_exact_signed_and_public_key_bytes() -> None:
    certificate = tls.read_certificate(CERTIFICATE)
    # RFC 5280 §4.1: the exact TBSCertificate includes its SEQUENCE tag and length.
    assert certificate.tbs == CERTIFICATE[4:359]
    assert certificate.spki == CERTIFICATE[133:224]
    assert certificate.not_before == (False, NOT_BEFORE)
    assert certificate.not_after == (False, NOT_AFTER)
    # The only extension is the non-critical libp2p one, holding the 113-byte SignedKey.
    signed_key_start = CERTIFICATE.index(bytes.fromhex("306f0425"))
    assert certificate.extensions == [
        {
            "oid": bytes.fromhex("2b0601040183a25a0101"),
            "critical": False,
            "value": CERTIFICATE[signed_key_start : signed_key_start + 113],
        }
    ]
    assert certificate.signature_algorithm == bytes.fromhex("2a8648ce3d040302")
    assert tls.verify_p256(certificate.spki, certificate.tbs, certificate.signature)
    assert not tls.verify_p256(certificate.spki, certificate.tbs + b"\x00", certificate.signature)
    assert (certificate.issuer_unique_id, certificate.subject_unique_id) == (False, False)


@pytest.mark.parametrize("chain", [[], [CERTIFICATE, CERTIFICATE]])
def test_chain_must_have_exactly_one_certificate(chain: list[bytes]) -> None:
    with raises(tls.TlsCertificateError, ERROR + "chain") as info:
        tls.authenticate(POLICY, NOW, chain)
    assert info.value.code == 4


def test_checks_the_dialled_peer() -> None:
    with raises(tls.TlsCertificateError, ERROR + "peerId") as info:
        tls.authenticate_peer(POLICY, NOW, P256_PEER_ID, [CERTIFICATE])
    assert info.value.code == 13


@pytest.mark.parametrize("now", [NOT_BEFORE - 1, NOT_AFTER + 1])
def test_rejects_times_outside_the_validity_interval(now: int) -> None:
    with raises(tls.TlsCertificateError, ERROR + "validity") as info:
        tls.authenticate(POLICY, now, [CERTIFICATE])
    assert info.value.code == 3


def test_requires_explicit_certificate_algorithm() -> None:
    policy: tls.Policy = {**POLICY, "certificate_algorithms": []}
    with raises(tls.TlsCertificateError, ERROR + "algorithm") as info:
        tls.authenticate(policy, NOW, [CERTIFICATE])
    assert info.value.code == 9


@pytest.mark.parametrize(
    ("allowed", "certificate"),
    [
        ([], CERTIFICATE),
        (["p256"], CERTIFICATE),
        (["secp256k1"], P256_HOST_CERTIFICATE),
        (["secp256k1", "p256"], ED25519_HOST_CERTIFICATE),
    ],
)
def test_requires_each_host_algorithm_explicitly(
    allowed: list[tls.HostAlgorithm], certificate: bytes
) -> None:
    policy: tls.Policy = {**POLICY, "host_algorithms": allowed}
    with raises(tls.TlsCertificateError, ERROR + "algorithm") as info:
        tls.authenticate(policy, NOW, [certificate])
    assert info.value.code == 9


@pytest.mark.parametrize(
    ("data", "error"),
    [
        # X.690 §10.1: indefinite and non-minimal long lengths are forbidden.
        (b"\x30\x80", "length"),
        (b"\x30\x81\x01\x00", "length"),
        (b"\x30\x82\x00\x80" + bytes(128), "length"),
        (CERTIFICATE[:-1], "truncated"),
        (CERTIFICATE + b"\x00", "trailing"),
    ],
)
def test_strict_der_lengths(data: bytes, error: str) -> None:
    with raises(
        tls.TlsCertificateError,
        ERROR + "der (EthLib.Serialization.Der.Error." + error + ")",
    ) as info:
        tls.read_certificate(data)
    assert info.value.code == 1


def test_rejects_changed_certificate_signature() -> None:
    data = CERTIFICATE[:-1] + bytes([CERTIFICATE[-1] ^ 1])
    with raises(tls.TlsCertificateError, ERROR + "selfSignature") as info:
        tls.authenticate(POLICY, NOW, [data])
    assert info.value.code == 11


def test_rejects_inner_outer_algorithm_mismatch() -> None:
    # The final OID byte of the outer signatureAlgorithm, before the signature BIT STRING.
    data = CERTIFICATE[:370] + b"\x03" + CERTIFICATE[371:]
    with raises(tls.TlsCertificateError, ERROR + "algorithm") as info:
        tls.read_certificate(data)
    assert info.value.code == 9


def test_rejects_a_nonexistent_calendar_date() -> None:
    index = CERTIFICATE.index(b"750101130000Z")
    data = CERTIFICATE[:index] + b"750229130000Z" + CERTIFICATE[index + 13 :]
    with raises(tls.TlsCertificateError, ERROR + "certificate") as info:
        tls.read_certificate(data)
    assert info.value.code == 2


def test_rejects_redundant_der_integer_sign_byte() -> None:
    index = CERTIFICATE.index(bytes.fromhex("0204499602d2")) + 2
    data = CERTIFICATE[:index] + b"\x00\x01" + CERTIFICATE[index + 2 :]
    with raises(
        tls.TlsCertificateError, ERROR + "der (EthLib.Serialization.Der.Error.value)"
    ) as info:
        tls.read_certificate(data)
    assert info.value.code == 1


@pytest.mark.parametrize("now", [NOT_BEFORE, NOT_AFTER])
def test_validity_endpoints_are_inclusive(now: int) -> None:
    assert tls.authenticate(POLICY, now, [CERTIFICATE]) == PEER_ID


def test_published_p256_host_certificate() -> None:
    assert tls.authenticate(POLICY, NOW, [P256_HOST_CERTIFICATE]) == P256_PEER_ID


def test_rejects_a_name_string_outside_the_reader_subset() -> None:
    index = CERTIFICATE.index(b"\x13\x09libp2p.io")
    data = CERTIFICATE[:index] + b"\x14" + CERTIFICATE[index + 1 :]
    with raises(
        tls.TlsCertificateError, ERROR + "der (EthLib.Serialization.Der.Error.tag)"
    ) as info:
        tls.read_certificate(data)
    assert info.value.code == 1


# The type checker checks the shapes of the certificate fields.
# These lines never run, since the suites also run on Python 3.10, which lacks `assert_type`.
if TYPE_CHECKING:
    from typing import assert_type

    def check_types() -> None:
        """A certificate is a typed record, and each extension a typed dictionary."""
        certificate = tls.read_certificate(CERTIFICATE)
        assert_type(certificate, tls.Certificate)
        assert_type(certificate.not_before, tuple[bool, int])
        assert_type(certificate.extensions[0]["oid"], bytes)
        assert_type(certificate.extensions[0]["critical"], bool)
