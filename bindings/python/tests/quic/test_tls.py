"""The no-PSK SHA-256 schedule and Finished values of RFC 8448 §3."""

import pytest

from ethlib.networking import quic
from raising import raises

# Source: RFC 8448 §3, https://www.rfc-editor.org/rfc/rfc8448#section-3.
# The messages include handshake headers and exclude record headers.
CLIENT_HELLO = bytes.fromhex(
    "010000c00303cb34ecb1e78163ba1c38c6dacb196a6dffa21a8d9912ec18a2ef6283"
    "024dece7000006130113031302010000910000000b0009000006736572766572ff01000100"
    "000a00140012001d0017001800190100010101020103010400230000003300260024001d"
    "002099381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c002b"
    "0003020304000d0020001e0403050306030203080408050806040105010601020104020502"
    "06020202002d00020101001c00024001"
)
SERVER_HELLO = bytes.fromhex(
    "020000560303a6af06a4121860dc5e6e60249cd34c95930c8ac5cb1434dac155772e"
    "d3e2692800130100002e00330024001d0020c9828876112095fe66762bdbf7c672e156"
    "d6cc253b833df1dd69b1b04e751f0f002b00020304"
)
# The 657-byte server payload in §3: EncryptedExtensions through Finished.
SERVER_FLIGHT = bytes.fromhex(
    "080000240022000a00140012001d00170018001901000101010201030104001c000240"
    "01000000000b0001b9000001b50001b0308201ac30820115a003020102020102300d06092a8648"
    "86f70d01010b0500300e310c300a06035504031303727361301e170d3136303733303031323335395a"
    "170d3236303733303031323335395a300e310c300a0603550403130372736130819f300d06092a864886f7"
    "0d010101050003818d0030818902818100b4bb498f8279303d980836399b36c6988c0c68de55e1bdb826"
    "d3901a2461eafd2de49a91d015abbc9a95137ace6c1af19eaa6af98c7ced43120998e187a80ee0ccb052"
    "4b1b018c3e0b63264d449a6d38e22a5fda430846748030530ef0461c8ca9d9efbfae8ea6d1d03e2bd193"
    "eff0ab9a8002c47428a6d35a8d88d79f7f1e3f0203010001a31a301830090603551d1304023000300b06"
    "03551d0f0404030205a0300d06092a864886f70d01010b05000381810085aad2a0e5b9276b908c65f73a726717"
    "0618a54c5f8a7b337d2df7a594365417f2eae8f8a58c8f8172f9319cf36b7fd6c55b80f21a0301515672"
    "6096fd335e5e67f2dbf102702e608ccae6bec1fc63a42a99be5c3eb7107c3c54e9b9eb2bd5203b1c3b84"
    "e0a8b2f759409ba3eac9d91d402dcc0cc8f8961229ac9187b42b4de100000f000084080400805a747c5d"
    "88fa9bd2e55ab085a61015b7211f824cd484145ab3ff52f1fda8477b0b7abc90db78e2d33a5c141a0786"
    "53fa6bef780c5ea248eeaaa785c4f394cab6d30bbe8d4859ee511f602957b15411ac027671459e46445c"
    "9ea58c181e818e95b8c3fb0bf3278409d3be152a3da5043e063dda65cdf5aea20d53dfacd42f74f31400"
    "00209b9b141d906337fbd2cbdce71df4deda4ab42c309572cb7fffee5454b78f0718"
)
HELLO_TRANSCRIPT = CLIENT_HELLO + SERVER_HELLO
SERVER_TRANSCRIPT = HELLO_TRANSCRIPT + SERVER_FLIGHT
SHARED_SECRET = bytes.fromhex("8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d")

SECRETS = quic.KeySchedule(
    early=bytes.fromhex("33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a"),
    handshake=bytes.fromhex("1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac"),
    master=bytes.fromhex("18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919"),
    client_handshake=bytes.fromhex(
        "b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21"
    ),
    server_handshake=bytes.fromhex(
        "b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38"
    ),
    client_application=bytes.fromhex(
        "9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5"
    ),
    server_application=bytes.fromhex(
        "a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643"
    ),
)


def test_key_schedule() -> None:
    # Each message length is its 4-byte header plus the length field the RFC prints.
    assert len(CLIENT_HELLO) == 196
    assert len(SERVER_HELLO) == 90
    assert len(SERVER_FLIGHT) == 657
    assert quic.tls_key_schedule(SHARED_SECRET, HELLO_TRANSCRIPT, SERVER_TRANSCRIPT) == SECRETS


def test_derived_secrets() -> None:
    assert quic.tls_derive_secret(SECRETS.early, b"derived", b"") == bytes.fromhex(
        "6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba"
    )
    assert quic.tls_derive_secret(SECRETS.handshake, b"derived", b"") == bytes.fromhex(
        "43de77e0c77713859a944db9db2590b53190a65b3ee2e4f12dd7a0bb7ce254b4"
    )
    assert (
        quic.tls_derive_secret(SECRETS.handshake, b"c hs traffic", HELLO_TRANSCRIPT)
        == SECRETS.client_handshake
    )
    assert (
        quic.tls_derive_secret(SECRETS.master, b"s ap traffic", SERVER_TRANSCRIPT)
        == SECRETS.server_application
    )


def test_finished() -> None:
    # The server authenticates the transcript before its 36-byte Finished message.
    assert quic.tls_finished(SECRETS.server_handshake, SERVER_TRANSCRIPT[:-36]) == bytes.fromhex(
        "9b9b141d906337fbd2cbdce71df4deda4ab42c309572cb7fffee5454b78f0718"
    )
    assert quic.tls_finished(SECRETS.client_handshake, SERVER_TRANSCRIPT) == bytes.fromhex(
        "a8ec436d677634ae525ac1fcebe11a039ec17694fac6e98527b642f2edd5ce61"
    )


@pytest.mark.parametrize("label", [b"", b"x" * 250])
def test_derive_label_bounds(label: bytes) -> None:
    # RFC 8446 §7.1 bounds the prefixed label to 7..255 bytes.
    with raises(quic.Tls13Error, f"EthLib.Cryptography.Hash.Tls13.Error.labelLength {len(label)}"):
        quic.tls_derive_secret(bytes(32), label, b"")


@pytest.mark.parametrize("size", [0, 31, 33])
def test_secret_length(size: int) -> None:
    with raises(quic.Tls13Error, f"expected 32 bytes, got {size}") as error:
        quic.tls_derive_secret(bytes(size), b"derived", b"")
    assert error.value.code == 0
    with raises(quic.Tls13Error, f"expected 32 bytes, got {size}"):
        quic.tls_finished(bytes(size), b"")
