"""The walk of an EIP-1459 node list, on the example zone of dnsdisc.md and on signed zones."""

import base64

from ethlib.errors import DnsDiscError
from ethlib.networking import dnsdisc, enr
from ethlib.serialization import rlp
from raising import raises

from .test_dnsdisc import BRANCH, LINK, RECORD, RECORD_2, RECORD_3, ROOT, SIGNER

# The zone of "DNS Record Structure" in dnsdisc.md, at the commit that test_dnsdisc.py pins.
# The root sits at the domain, and every other entry at the subdomain of its hash.

DOMAIN = "nodes.example.org"
BUDGET = 100


def _zone(root: str, *entries: str) -> dict[str, str]:
    return {DOMAIN: root} | {f"{dnsdisc.subdomain(text)}.{DOMAIN}": text for text in entries}


ZONE = _zone(ROOT, BRANCH, LINK, RECORD, RECORD_2, RECORD_3)


def test_example_zone() -> None:
    seq, records, links = dnsdisc.resolve(SIGNER, 0, DOMAIN, BUDGET, ZONE)
    assert seq == 1
    assert records == [enr.from_text(text) for text in (RECORD, RECORD_2, RECORD_3)]
    assert links == [LINK]


def test_replaced_record_fails_its_hash() -> None:
    # A resolver puts another record at the name of the second one.
    name = f"{dnsdisc.subdomain(RECORD_2)}.{DOMAIN}"
    zone = ZONE | {name: RECORD_3}
    with raises(DnsDiscError, f"the text at {name} does not have the hash of its name"):
        dnsdisc.resolve(SIGNER, 0, DOMAIN, BUDGET, zone)


def test_older_root_is_refused() -> None:
    with raises(DnsDiscError, "sequence number 1 is below 2, the one seen last"):
        dnsdisc.resolve(SIGNER, 2, DOMAIN, BUDGET, ZONE)


def test_root_of_another_key_is_refused() -> None:
    key, _ = dnsdisc.parse_url(LINK)
    with raises(DnsDiscError, "the root is not signed by the key of the list"):
        dnsdisc.resolve(key, 0, DOMAIN, BUDGET, ZONE)


def test_missing_entry() -> None:
    name = f"{dnsdisc.subdomain(RECORD)}.{DOMAIN}"
    zone = {k: v for k, v in ZONE.items() if k != name}
    with raises(DnsDiscError, f"no TXT record at {name}"):
        dnsdisc.resolve(SIGNER, 0, DOMAIN, BUDGET, zone)


def test_budget() -> None:
    with raises(DnsDiscError, "the walk took more hashes than its budget"):
        dnsdisc.resolve(SIGNER, 0, DOMAIN, 3, ZONE)


# Zones signed here with a test key, since the key of the example zone is not known.
SECRET_KEY = (1).to_bytes(32, "big")
KEY = bytes.fromhex("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")


def _hash(text: str) -> bytes:
    # The 16 bytes of a hash name, as a branch of that one hash reads them.
    return dnsdisc.parse_entry(f"enrtree-branch:{dnsdisc.subdomain(text)}")["hashes"][0]


def test_hash_met_twice_is_read_once() -> None:
    # A branch lists the same record twice, and the client resolves it once.
    name = dnsdisc.subdomain(RECORD)
    branch = f"enrtree-branch:{name},{name}"
    links = "enrtree-branch:"
    root = dnsdisc.sign_root(SECRET_KEY, _hash(branch), _hash(links), 7)
    seq, records, found = dnsdisc.resolve(
        KEY, 7, DOMAIN, BUDGET, _zone(root, branch, links, RECORD)
    )
    assert (seq, records, found) == (7, [enr.from_text(RECORD)], [])


def test_link_under_the_records_is_refused() -> None:
    branch = f"enrtree-branch:{dnsdisc.subdomain(LINK)}"
    links = "enrtree-branch:"
    root = dnsdisc.sign_root(SECRET_KEY, _hash(branch), _hash(links), 1)
    name = f"{dnsdisc.subdomain(LINK)}.{DOMAIN}"
    with raises(DnsDiscError, f"the entry at {name} is in the wrong subtree"):
        dnsdisc.resolve(KEY, 0, DOMAIN, BUDGET, _zone(root, branch, links, LINK))


# The order of the group of secp256k1, from SEC 2 §2.4.1.
ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def _b64(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).decode().rstrip("=")


def _unb64(text: str) -> bytes:
    return base64.urlsafe_b64decode(text + "=" * (-len(text) % 4))


def test_swapped_signature_resolves_the_same_list() -> None:
    # The signature (r, n - s) with the other recovery id verifies too, and the list is the same.
    head, sig = ROOT.split(" sig=")
    raw = _unb64(sig)
    s = int.from_bytes(raw[32:64], "big")
    swapped = raw[:32] + (ORDER - s).to_bytes(32, "big") + bytes([1 - raw[64]])
    root = f"{head} sig={_b64(swapped)}"
    assert root != ROOT
    zone = ZONE | {DOMAIN: root}
    assert dnsdisc.resolve(SIGNER, 0, DOMAIN, BUDGET, zone) == dnsdisc.resolve(
        SIGNER, 0, DOMAIN, BUDGET, ZONE
    )


def test_record_that_does_not_verify_is_refused() -> None:
    # The first record with a zero signature still decodes, but no longer verifies.
    fields = rlp.decode(enr.from_text(RECORD))
    forged = "enr:" + _b64(rlp.encode([bytes(64), *fields[1:]]))
    branch = f"enrtree-branch:{dnsdisc.subdomain(forged)}"
    links = "enrtree-branch:"
    root = dnsdisc.sign_root(SECRET_KEY, _hash(branch), _hash(links), 1)
    name = f"{dnsdisc.subdomain(forged)}.{DOMAIN}"
    with raises(DnsDiscError, f"the node record at {name} does not verify"):
        dnsdisc.resolve(KEY, 0, DOMAIN, BUDGET, _zone(root, branch, links, forged))
