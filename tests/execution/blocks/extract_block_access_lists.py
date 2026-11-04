"""Write the block access list of each Engine API payload of the EIP-7928 tests."""

import json
import sys
from pathlib import Path

SUBDIRECTORY = "for_amsterdam/amsterdam/eip7928_block_level_access_lists"

root = Path(sys.argv[1])  # the directory that holds the unpacked `fixtures`
out = Path(sys.argv[2])

# The header of each valid block of the blockchain tests, by its hash.
headers = {}
for path in (root / "fixtures" / "blockchain_tests" / SUBDIRECTORY).rglob("*.json"):
    for test in json.loads(path.read_text()).values():
        for block in test["blocks"]:
            if "blockHeader" in block:
                headers[block["blockHeader"]["hash"]] = block["blockHeader"]

cases = []
for path in sorted((root / "fixtures" / "blockchain_tests_engine" / SUBDIRECTORY).rglob("*.json")):
    source = str(path.relative_to(root))
    for name, test in json.loads(path.read_text()).items():
        assert test["network"] == "Amsterdam"
        for index, payload in enumerate(test["engineNewPayloads"]):
            params = payload["params"][0]
            case = {
                "source": source,
                "test": name,
                "payload": index,
                "gasLimit": int(params["gasLimit"], 16),
                "bal": params["blockAccessList"].removeprefix("0x"),
                "error": payload.get("validationError"),
            }
            # A valid payload has a block in the blockchain test, whose header holds the hash.
            if case["error"] is None:
                header = headers[params["blockHash"]]
                case["hash"] = header["blockAccessListHash"].removeprefix("0x")
            cases.append(case)

out.write_text(json.dumps(cases, indent=0) + "\n")
print(len(cases), "cases", out.stat().st_size, "bytes")
