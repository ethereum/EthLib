"""The default data of a Gloas request to a builder, from the builder's URL."""

import ipaddress
from urllib.parse import urlsplit

import pytest
from hypothesis import example, given, strategies as st

from ethlib import consensus
from ethlib.errors import ConsensusError
from raising import raises

# The examples of "Default auth data" in the Gloas validator document of the builder specification:
# https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/gloas/validator.md#default-auth-data
SOURCE_EXAMPLES = [
    ("https://builder.example.com/", b"builder.example.com"),
    ("HTTPS://Builder.Example.com:443/bids?x=1", b"builder.example.com"),
    ("https://builder.example.com:8080", b"builder.example.com"),
    ("https://user:pw@builder.example.com/", b"builder.example.com"),
    ("https://10.0.0.5:18550/eth/v1/builder", b"10.0.0.5"),
    ("https://[0:0:0:0:0:0:0:1]:8443/", b"[::1]"),
    ("https://[::ffff:192.0.2.1]/", b"[::ffff:c000:201]"),
]

# The examples of RFC 5952 section 4 with the text it recommends, and an upper case one for 4.3.
RFC_5952_EXAMPLES = [
    ("2001:0db8::0001", "2001:db8::1"),
    ("2001:db8:0:0:0:0:2:1", "2001:db8::2:1"),
    ("2001:db8::0:1", "2001:db8::1"),
    ("2001:db8:0:1:1:1:1:1", "2001:db8:0:1:1:1:1:1"),
    ("2001:0:0:1:0:0:0:1", "2001:0:0:1::1"),
    ("2001:db8:0:0:1:0:0:1", "2001:db8::1:0:0:1"),
    ("2001:DB8::AAAA", "2001:db8::aaaa"),
]

# URLs whose authority or IPv6 text reaches an edge of the grammar, with their data.
EDGES = [
    ("https://a@b@host/", b"host"),
    ("https://u[x]@host/", b"host"),
    ("https://host?q", b"host"),
    ("https://host#f", b"host"),
    ("https://host:/", b"host"),
    ("https://[1:2:3:4:5:6:7::]/", b"[1:2:3:4:5:6:7:0]"),
    ("https://[0:0:0:0:0:ffff:0:0]/", b"[::ffff:0:0]"),
    ("https://[1:0:0:2:0:0:0:3]/", b"[1:0:0:2::3]"),
]

PREFIX = "EthLib.Consensus.BuilderApi.AuthDataError."

REJECTED = [
    ("https://bücher.example/", "nonAscii"),
    ("builder.example.com", "noAuthority"),
    ("https:builder.example.com", "noAuthority"),
    ("https://user@:8080/", "noHost"),
    ("https://builder.example.com:80a/", "badPort"),
    ("https://[1:::2]/", "badIpv6"),
    ("https://[1::2::3]/", "badIpv6"),
    ("https://[1:2:3:4:5:6:7:8:9]/", "badIpv6"),
    ("https://[::ffff:192.0.2.01]/", "badIpv6"),
    ("https://[::1/", "badIpv6"),
    ("https://[::1]x/", "badPort"),
    ("https://[::1]:8a/", "badPort"),
    ("https://:8080/", "noHost"),
    ("1http://host/", "noAuthority"),
    ("://host/", "noAuthority"),
    ("//host/", "noAuthority"),
    ("https://[12345::]/", "badIpv6"),
    ("https://[1.2.3.4::]/", "badIpv6"),
    ("https://[::ffff:256.0.0.1]/", "badIpv6"),
    ("https://[1:2:3:4:5:6:7:1.2.3.4]/", "badIpv6"),
    ("https://[1:2:3:4::5:6:7:8]/", "badIpv6"),
    ("https://[]/", "badIpv6"),
    ("https://[v1.x]/", "badIpv6"),
    ("https://[fe80::1%25eth0]/", "badIpv6"),
    ("https://exa\tmple.com/", "badName"),
    ("https://exa mple.com/", "badName"),
    ("https://a]b/", "badName"),
    ("https://Ab%41Cd.COM/", "badName"),
    ('https://a"b{c}.com/', "badName"),
    ("https://\u212aey.example/", "nonAscii"),
]

# Registered names, userinfo, ports and the rest of a URL, which the source's own splitter reads.
NAME = st.text("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789.-", min_size=1)
URLS = st.builds(
    "{}://{}{}{}{}".format,
    st.sampled_from(["http", "https", "HTTPS"]),
    st.sampled_from(["", "user@", "user:pw@"]),
    NAME,
    st.sampled_from(["", ":", ":443", ":18550"]),
    st.sampled_from(["", "/", "/eth/v1/builder", "?x=1", "#f"]),
)

# The eight groups of an address, with zero groups common so that runs of them appear.
GROUPS = st.lists(
    st.sampled_from([0, 0, 0, 1, 0xFFFF]) | st.integers(0, 0xFFFF), min_size=8, max_size=8
) | st.tuples(st.integers(0, 0xFFFF), st.integers(0, 0xFFFF)).map(lambda t: [0] * 5 + [0xFFFF, *t])


@pytest.mark.parametrize(("url", "expected"), SOURCE_EXAMPLES)
def test_source_examples(url: str, expected: bytes) -> None:
    assert consensus.default_auth_data(url) == expected


@pytest.mark.parametrize(("text", "expected"), RFC_5952_EXAMPLES)
def test_rfc_5952_examples(text: str, expected: str) -> None:
    assert consensus.default_auth_data(f"https://[{text}]/") == f"[{expected}]".encode()


@pytest.mark.parametrize(("url", "expected"), EDGES)
def test_edges(url: str, expected: bytes) -> None:
    assert consensus.default_auth_data(url) == expected


@pytest.mark.parametrize(("url", "reason"), REJECTED)
def test_rejected(url: str, reason: str) -> None:
    with raises(ConsensusError, PREFIX + reason):
        consensus.default_auth_data(url)


@given(URLS)
def test_name_matches_urlsplit(url: str) -> None:
    """A registered name gives the host that the source's splitter reads, as ASCII bytes."""
    hostname = urlsplit(url).hostname
    assert hostname is not None
    assert consensus.default_auth_data(url) == hostname.encode("ascii")


@given(GROUPS)
@example([0, 0, 0, 0, 0, 0xFFFF, 0xC000, 0x201])
@example([0, 0, 0, 0, 0, 0xFFFF, 0, 0])
def test_ipv6_matches_ipaddress(groups: list[int]) -> None:
    """An address in several spellings gives its RFC 5952 text, which the standard library reads."""
    full = ":".join(f"{group:04X}" for group in groups)
    data = consensus.default_auth_data(f"https://[{full}]:8443/path")
    assert data[:1] == b"[" and data[-1:] == b"]"
    text = data[1:-1].decode("ascii")
    address = ipaddress.IPv6Address(int(full.replace(":", ""), 16))
    assert ipaddress.IPv6Address(text) == address
    if address.ipv4_mapped is None:
        assert text == address.compressed
    else:
        # The standard library writes this tail in dotted decimal; the source asks for two groups.
        assert text == f"::ffff:{groups[6]:x}:{groups[7]:x}"
    assert consensus.default_auth_data(f"http://u@[{address.exploded}]") == data
    tail = ipaddress.IPv4Address(int(address) & 0xFFFFFFFF)
    mixed = ":".join(f"{group:x}" for group in groups[:6]) + f":{tail}"
    assert consensus.default_auth_data(f"https://[{mixed}]/") == data
    assert consensus.default_auth_data(f"https://[{text}]/") == data
