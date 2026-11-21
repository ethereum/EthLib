"""The entries of an EIP-1459 node list against the example zone of dnsdisc.md."""

import pytest

from ethlib.errors import DnsDiscError
from ethlib.networking import dnsdisc, enr
from raising import raises

# The zone of "DNS Record Structure" in dnsdisc.md, which is the maintained text of EIP-1459.
#
# File: dnsdisc.md
# Repository: ethereum/devp2p
# Commit: 277ceb399c15df86efb17d51eb58200c26879784
# Licence: CC0-1.0

ROOT = (
    "enrtree-root:v1 e=JWXYDBPXYWG6FX3GMDIBFA6CJ4 l=C7HRFPF3BLGF3YR4DY5KX3SMBE seq=1 "
    "sig=o908WmNp7LibOfPsr4btQwatZJ5URBr2ZAuxvK4UWHlsB9sUOTJQaGAlLPVAhM__XJesCHxLISo94z5Z2a463gA"
)
LINK = "enrtree://AM5FCQLWIZX2QFPNJAP7VUERCCRNGRHWZG3YYHIUV7BVDQ5FDPRT2@morenodes.example.org"
BRANCH = (
    "enrtree-branch:2XS2367YHAXJFGLZHVAWLQD4ZY,H4FHT4B454P6UXFD7JCYQ5PWDY,"
    "MHTDO6TMUBRIA2XWG5LUDACK24"
)
RECORD = (
    "enr:-HW4QOFzoVLaFJnNhbgMoDXPnOvcdVuj7pDpqRvh6BRDO68aVi5ZcjB3vzQRZH2IcLBGHzo8uUN3snqmgTiE56CH3AMB"
    "gmlkgnY0iXNlY3AyNTZrMaECC2_24YYkYHEgdzxlSNKQEnHhuNAbNlMlWJxrJxbAFvA"
)
RECORD_2 = (
    "enr:-HW4QAggRauloj2SDLtIHN1XBkvhFZ1vtf1raYQp9TBW2RD5EEawDzbtSmlXUfnaHcvwOizhVYLtr7e6vw7NAf6mTuoC"
    "gmlkgnY0iXNlY3AyNTZrMaECjrXI8TLNXU0f8cthpAMxEshUyQlK-AM0PW2wfrnacNI"
)
RECORD_3 = (
    "enr:-HW4QLAYqmrwllBEnzWWs7I5Ev2IAs7x_dZlbYdRdMUx5EyKHDXp7AV5CkuPGUPdvbv1_Ms1CPfhcGCvSElSosZmyoqA"
    "gmlkgnY0iXNlY3AyNTZrMaECriawHKWdDRk2xeZkrOXBQ0dfMFLHY4eENZwdufn1S1o"
)
# The key that the text names as the signer of the list: x, then y, of the uncompressed point.
# Its compressed form is 02 then x, since the last byte of y is even.
SIGNER = bytes.fromhex("029f88229042fef9200246f49f94d9b77c4e954721442714e85850cb6d9e5daf2d")


def test_branch_is_the_enr_root() -> None:
    assert dnsdisc.subdomain(BRANCH) == "JWXYDBPXYWG6FX3GMDIBFA6CJ4"


def test_link_is_the_link_root() -> None:
    assert dnsdisc.subdomain(LINK) == "C7HRFPF3BLGF3YR4DY5KX3SMBE"


def test_record_is_the_first_hash_of_the_branch() -> None:
    assert dnsdisc.subdomain(RECORD) == "2XS2367YHAXJFGLZHVAWLQD4ZY"


def test_other_records_are_the_other_hashes() -> None:
    assert dnsdisc.subdomain(RECORD_2) == "H4FHT4B454P6UXFD7JCYQ5PWDY"
    assert dnsdisc.subdomain(RECORD_3) == "MHTDO6TMUBRIA2XWG5LUDACK24"


def test_root_is_signed_by_the_named_key() -> None:
    assert dnsdisc.verify_root(SIGNER, ROOT)


def test_root_is_not_signed_by_the_key_of_the_example_url() -> None:
    # The example URL decodes to another key than the one that signed the root.
    key, domain = dnsdisc.parse_url(LINK)
    assert domain == "morenodes.example.org"
    assert key.hex().startswith("033a5141")
    assert not dnsdisc.verify_root(key, ROOT)


def test_root_fields() -> None:
    root = dnsdisc.parse_entry(ROOT)
    assert root["type"] == "root"
    assert root["seq"] == 1
    assert len(root["signature"]) == 65
    # The two roots are the hashes that the branch and the link entries name.
    branch = dnsdisc.parse_entry(f"enrtree-branch:{dnsdisc.subdomain(BRANCH)}")
    link = dnsdisc.parse_entry(f"enrtree-branch:{dnsdisc.subdomain(LINK)}")
    assert branch["hashes"] == [root["enr_root"]]
    assert link["hashes"] == [root["link_root"]]


def test_root_with_another_seq_does_not_verify() -> None:
    assert not dnsdisc.verify_root(SIGNER, ROOT.replace("seq=1", "seq=2"))


def test_branch_fields() -> None:
    branch = dnsdisc.parse_entry(BRANCH)
    assert branch["type"] == "branch"
    assert len(branch["hashes"]) == 3


def test_record_entry() -> None:
    entry = dnsdisc.parse_entry(RECORD)
    assert entry == {"type": "enr", "record": enr.from_text(RECORD)}


def test_link_entry() -> None:
    entry = dnsdisc.parse_entry(LINK)
    assert entry["type"] == "link"
    assert entry["domain"] == "morenodes.example.org"


def test_empty_branch() -> None:
    assert dnsdisc.parse_entry("enrtree-branch:") == {"type": "branch", "hashes": []}


@pytest.mark.parametrize(
    ("text", "message"),
    [
        ("enrtree-root=v1 e=X", "text is not a root, a branch, a link or a node record"),
        (
            ROOT.replace("seq=1", "seq=01"),
            "sequence number is not a decimal integer without leading zeros",
        ),
        (
            ROOT.replace(" l=", " x="),
            "root does not have the fields e=, l=, seq= and sig=, in that order",
        ),
        (BRANCH.replace(",", ";", 1), "the hashes of a branch are not separated by commas"),
        (
            BRANCH.replace("2XS2", "2xs2"),
            "a hash, a key or a signature is not base32 or base64 of its size",
        ),
        (LINK.replace("@", "#"), "link has no @ after its key"),
    ],
)
def test_rejects(text: str, message: str) -> None:
    with raises(DnsDiscError, message):
        dnsdisc.parse_entry(text)
