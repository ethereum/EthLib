"""Write the fee fields of each parent and child header of the blockchain tests."""

import json
import sys
from pathlib import Path

FIELDS = ("gasLimit", "gasUsed", "baseFeePerGas", "blobGasUsed", "excessBlobGas", "timestamp")
NEGATIVE = "BlockException.INCORRECT_EXCESS_BLOB_GAS"


def fee_fields(header: dict) -> dict:
    """The fee fields of a header, as integers."""
    return {key: int(header[key], 16) for key in FIELDS if key in header}


root, out = Path(sys.argv[1]), Path(sys.argv[2])
cases = []
# The fixtures of the EIP-1559, EIP-4844 excess blob gas and EIP-7918 tests, at every network.
FAMILIES = (
    "*/london/eip1559_fee_market_change/**/*.json",
    "*/cancun/eip4844_blobs/excess_blob_gas*/**/*.json",
    "*/osaka/eip7918_blob_reserve_price/**/*.json",
)
paths = {path for family in FAMILIES for path in (root / "blockchain_tests").glob(family)}
for path in sorted(paths):
    relative = path.relative_to(root.parent).as_posix()
    if "amsterdam" in relative.lower():
        continue
    for name, test in sorted(json.loads(path.read_text()).items()):
        if "Amsterdam" in test["network"]:
            continue
        parent = fee_fields(test["genesisBlockHeader"])
        for index, block in enumerate(test["blocks"]):
            exception = block.get("expectException")
            header = block.get("blockHeader") or block.get("rlp_decoded", {}).get("blockHeader")
            if header is None:
                continue
            child = fee_fields(header)
            if exception is None or exception == NEGATIVE:
                cases.append({
                    "file": relative,
                    "test": name.split("::")[-1],
                    "block": index + 1,
                    "network": test["network"],
                    "valid": exception is None,
                    "parent": parent,
                    "child": child,
                })
            if exception is None:
                parent = child
# One pair per line, so that a change to one pair shows as one line of the diff.
lines = (json.dumps(case, sort_keys=True, separators=(",", ":")) for case in cases)
out.write_text("[\n" + ",\n".join(lines) + "\n]\n")
print(len(cases), sum(c["valid"] for c in cases))
