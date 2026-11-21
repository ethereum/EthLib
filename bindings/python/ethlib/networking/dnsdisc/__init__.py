"""The node lists of EIP-1459, published as DNS TXT records."""

from typing import Any

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import DnsDiscError


def parse_entry(text: str) -> dict[str, Any]:
    """The type and the fields of an entry text: a root, a branch, a link or a node record."""
    return _native.dnsdisc_parse_entry(text)


def subdomain(text: str) -> str:
    """The subdomain of an entry text: the base32 of the first 16 bytes of its Keccak-256 hash."""
    return _native.dnsdisc_subdomain(text)


def verify_root(key: bytes, text: str) -> bool:
    """Whether a root text is signed by a compressed public key of 33 bytes."""
    return _native.dnsdisc_verify_root(key, text)


def parse_url(text: str) -> tuple[bytes, str]:
    """The compressed public key and the domain of a URL `enrtree://<key>@<domain>`."""
    return _native.dnsdisc_parse_url(text)


__all__ = ["DnsDiscError", "parse_entry", "parse_url", "subdomain", "verify_root"]
