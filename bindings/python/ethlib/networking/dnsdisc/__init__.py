"""The node lists of EIP-1459, published as DNS TXT records."""

from collections.abc import Mapping
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


def resolve(
    key: bytes, seen_seq: int, domain: str, budget: int, table: Mapping[str, str]
) -> tuple[int, list[bytes], list[str]]:
    """
    The sequence number, the RLP records and the links of the node list at a domain.

    The table maps each name to the text of its TXT record, and the budget bounds the entries read.
    """
    return _native.dnsdisc_resolve(key, seen_seq, domain, budget, list(table.items()))


def sign_root(secret_key: bytes, enr_root: bytes, link_root: bytes, seq: int) -> str:
    """The text of a root of two 16-byte hashes and a sequence number, signed with a private key."""
    return _native.dnsdisc_sign_root(secret_key, enr_root, link_root, seq)


__all__ = [
    "DnsDiscError",
    "parse_entry",
    "parse_url",
    "resolve",
    "sign_root",
    "subdomain",
    "verify_root",
]
