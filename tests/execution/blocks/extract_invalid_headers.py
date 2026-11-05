"""Write the invalid blocks from Paris to Osaka that fail a header check, with each parent."""

import collections
import json
import sys
from pathlib import Path

NETWORKS = ["Paris", "Shanghai", "Cancun", "Prague", "Osaka"]
CODES = {
    "BlockException.INCORRECT_EXCESS_BLOB_GAS": 202,
    "BlockException.INVALID_GASLIMIT": 204,
    "BlockException.INVALID_BASEFEE_PER_GAS": 205,
}
# The cases of the excess blob gas kept from each fixture file, to keep the file small.
PER_FILE = 2

root = Path(sys.argv[1])  # the directory that holds the unpacked `fixtures`
out = Path(sys.argv[2])


def first_item(data: bytes) -> bytes:
    """The encoding of the first item of the RLP list `data` (a long list of long lists)."""
    start = 1 + data[0] - 0xF7
    head = data[start]
    size = head - 0xF7
    length = int.from_bytes(data[start + 1 : start + 1 + size], "big")
    return data[start : start + 1 + size + length]


cases = []
for path in sorted(root.rglob("*.json")):
    data = json.loads(path.read_text())
    kept = 0
    for test in sorted(data):
        fixture = data[test]
        if fixture.get("network") not in NETWORKS:
            continue
        headers = {fixture["genesisBlockHeader"]["hash"]: fixture["genesisRLP"]}
        for number, block in enumerate(fixture["blocks"]):
            exception = block.get("expectException")
            if not exception:
                if "blockHeader" in block:
                    headers[block["blockHeader"]["hash"]] = block["rlp"]
                continue
            names = exception.split("|")
            codes = sorted({CODES[n] for n in names if n in CODES})
            if not codes or (codes == [202] and kept >= PER_FILE):
                continue
            rlp = bytes.fromhex(block["rlp"].removeprefix("0x"))
            header = first_item(rlp)
            parent_hash = "0x" + header[4:36].hex()  # the parent hash is the first field
            if parent_hash not in headers:
                continue
            parent = first_item(bytes.fromhex(headers[parent_hash].removeprefix("0x")))
            cases.append(
                {
                    "source": str(path.relative_to(root)),
                    "test": test,
                    "network": fixture["network"],
                    "block": number,
                    "exception": exception,
                    "codes": codes,
                    "parent": parent.hex(),
                    "header": header.hex(),
                }
            )
            kept += codes == [202]
out.write_text(json.dumps(cases, indent=1))
print(len(cases), "cases", out.stat().st_size, "bytes")
print(collections.Counter((c["network"], tuple(c["codes"])) for c in cases))
