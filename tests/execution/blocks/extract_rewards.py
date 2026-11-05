"""Write the first blocks from Frontier to Paris that hold no transaction, with the state before."""

import json
import sys
from pathlib import Path

NETWORKS = [
    "Frontier",
    "Homestead",
    "TangerineWhistle",
    "SpuriousDragon",
    "Byzantium",
    "ConstantinopleFix",
    "Istanbul",
    "Berlin",
    "London",
    "Paris",
]

root = Path(sys.argv[1])  # the directory that holds the unpacked `fixtures`
out = Path(sys.argv[2])

cases = []
for path in sorted(root.rglob("*.json")):
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        continue
    for test in sorted(data):
        fixture = data[test]
        if not isinstance(fixture, dict) or fixture.get("network") not in NETWORKS:
            continue
        if not fixture.get("blocks"):
            continue
        block = fixture["blocks"][0]
        if block.get("expectException") or block.get("transactions") or "blockHeader" not in block:
            continue
        cases.append(
            {
                "source": str(path.relative_to(root)),
                "test": test,
                "network": fixture["network"],
                "pre": fixture["pre"],
                "preStateRoot": fixture["genesisBlockHeader"]["stateRoot"].removeprefix("0x"),
                "rlp": block["rlp"].removeprefix("0x"),
                "postStateRoot": block["blockHeader"]["stateRoot"].removeprefix("0x"),
            }
        )

out.write_text(json.dumps(cases, indent=1) + "\n")
