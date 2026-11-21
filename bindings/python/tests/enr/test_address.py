"""The addresses and ports of a node record, against EIP-778 and hand-built records."""

from ethlib.networking import enr
from ethlib.serialization import rlp
from raising import raises

from .test_enr import TEXT

# The first test reads the record of "Test Vectors" in EIP-778, which test_enr.py pins.
# The EIP says that it holds the IPv4 address 127.0.0.1 and the UDP port 30303.
#
# The other records are RLP built here with a placeholder signature.
# The reader does not check the signature.
# Each value is written out by hand from the key table of EIP-778.

SIGNATURE = bytes(64)

LOCALHOST = bytes([127, 0, 0, 1])
# The IPv6 address ::1.
LOCALHOST6 = bytes(15) + b"\x01"
# The port 30303, a big-endian integer with no leading zero byte.
PORT = bytes.fromhex("765f")
# The port 9000.
OTHER_PORT = bytes.fromhex("2328")

PORT_ERROR = "entry is not a big-endian integer below 2^16 without leading zeros"


def _record(entries: dict[bytes, bytes]) -> bytes:
    pairs = sorted({b"id": b"v4", **entries}.items())
    return rlp.encode([SIGNATURE, b"\x01"] + [x for pair in pairs for x in pair])


def test_eip_vector() -> None:
    ipv4, ipv6 = enr.endpoints(enr.from_text(TEXT))
    assert ipv4 == enr.Endpoint(LOCALHOST, None, 30303, None)
    assert ipv6 is None


def test_ports_without_an_address() -> None:
    assert enr.endpoints(_record({b"udp": PORT})) == (None, None)


def test_ipv6_takes_the_ipv4_ports() -> None:
    # "If no tcp6 / udp6 port is provided, the tcp / udp port applies to both IP addresses."
    record = _record({b"ip": LOCALHOST, b"ip6": LOCALHOST6, b"tcp": OTHER_PORT, b"udp": PORT})
    ipv4, ipv6 = enr.endpoints(record)
    assert ipv4 == enr.Endpoint(LOCALHOST, 9000, 30303, None)
    assert ipv6 == enr.Endpoint(LOCALHOST6, 9000, 30303, None)


def test_ipv6_ports_come_first() -> None:
    record = _record({b"ip6": LOCALHOST6, b"tcp": PORT, b"tcp6": OTHER_PORT, b"udp6": PORT})
    assert enr.endpoints(record) == (None, enr.Endpoint(LOCALHOST6, 9000, 30303, None))


def test_one_ipv6_port_and_one_fallback() -> None:
    record = _record({b"ip6": LOCALHOST6, b"tcp": PORT, b"tcp6": OTHER_PORT, b"udp": PORT})
    assert enr.endpoints(record) == (None, enr.Endpoint(LOCALHOST6, 9000, 30303, None))


def test_quic_has_no_fallback() -> None:
    record = _record({b"ip": LOCALHOST, b"ip6": LOCALHOST6, b"quic": PORT})
    ipv4, ipv6 = enr.endpoints(record)
    assert ipv4 == enr.Endpoint(LOCALHOST, None, None, 30303)
    assert ipv6 == enr.Endpoint(LOCALHOST6, None, None, None)


def test_quic6() -> None:
    record = _record({b"ip6": LOCALHOST6, b"quic6": OTHER_PORT})
    assert enr.endpoints(record) == (None, enr.Endpoint(LOCALHOST6, None, None, 9000))


def test_port_zero_is_the_empty_string() -> None:
    record = _record({b"ip": LOCALHOST, b"udp": b""})
    assert enr.endpoints(record) == (enr.Endpoint(LOCALHOST, None, 0, None), None)


def test_rejects_a_short_ipv4_address() -> None:
    with raises(ValueError, "the 0x6970 entry is not an address of its size"):
        enr.endpoints(_record({b"ip": LOCALHOST[:3]}))


def test_rejects_an_ipv4_address_as_ipv6() -> None:
    with raises(ValueError, "the 0x697036 entry is not an address of its size"):
        enr.endpoints(_record({b"ip6": LOCALHOST}))


def test_rejects_a_leading_zero_port() -> None:
    with raises(ValueError, f"the 0x756470 {PORT_ERROR}"):
        enr.endpoints(_record({b"udp": b"\x00\x50"}))


def test_rejects_a_port_of_17_bits() -> None:
    with raises(ValueError, f"the 0x746370 {PORT_ERROR}"):
        enr.endpoints(_record({b"tcp": b"\x01\x00\x00"}))


def test_rejects_a_bad_port_without_its_address() -> None:
    # Every key is read, even when its address is absent.
    with raises(ValueError, f"the 0x7175696336 {PORT_ERROR}"):
        enr.endpoints(_record({b"ip": LOCALHOST, b"quic6": b"\x00"}))


def test_rejects_a_list_as_a_port() -> None:
    record = rlp.encode([SIGNATURE, b"\x01", b"id", b"v4", b"udp", [PORT]])
    with raises(ValueError, f"the 0x756470 {PORT_ERROR}"):
        enr.endpoints(record)
