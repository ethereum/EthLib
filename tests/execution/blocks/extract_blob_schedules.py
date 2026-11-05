"""Write header pairs of the networks with a blob schedule of their own, each with its config."""

import collections
import json
import sys
from pathlib import Path

NETWORKS = [
    "AmsterdamBPOIncrease",
    "AmsterdamBPODecrease",
    "AmsterdamToBPOIncreaseAtTime15k",
    "AmsterdamToBPODecreaseAtTime15k",
]
EXCEPTION = "BlockException.INCORRECT_EXCESS_BLOB_GAS"
# The valid pairs and the invalid pairs kept from each fixture file, to keep the file small.
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
    kept = collections.Counter()
    for test in sorted(data):
        fixture = data[test]
        if fixture.get("network") not in NETWORKS:
            continue
        headers = {fixture["genesisBlockHeader"]["hash"]: fixture["genesisRLP"]}
        for number, block in enumerate(fixture["blocks"]):
            exception = block.get("expectException")
            if exception not in (None, EXCEPTION) or kept[exception] >= PER_FILE:
                if not exception and "blockHeader" in block:
                    headers[block["blockHeader"]["hash"]] = block["rlp"]
                continue
            header = first_item(bytes.fromhex(block["rlp"].removeprefix("0x")))
            parent_hash = "0x" + header[4:36].hex()  # the parent hash is the first field
            if parent_hash in headers:
                parent = first_item(bytes.fromhex(headers[parent_hash].removeprefix("0x")))
                cases.append(
                    {
                        "source": str(path.relative_to(root)),
                        "test": test,
                        "network": fixture["network"],
                        "blobSchedule": fixture["config"]["blobSchedule"],
                        "block": number,
                        "exception": exception,
                        "parent": parent.hex(),
                        "header": header.hex(),
                    }
                )
                kept[exception] += 1
            if not exception:
                headers[block["blockHeader"]["hash"]] = block["rlp"]
out.write_text(json.dumps(cases, indent=1))
print(len(cases), "cases", out.stat().st_size, "bytes")
print(collections.Counter((c["network"], c["exception"]) for c in cases))
