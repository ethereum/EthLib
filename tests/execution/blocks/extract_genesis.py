"""Write the genesis block of the test `block_intermediate_state` at each network, and its state."""

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
    "Shanghai",
    "Cancun",
    "Prague",
    "Osaka",
    "Amsterdam",
]

root = Path(sys.argv[1])  # the directory that holds the unpacked `fixtures`
out = Path(sys.argv[2])

cases = {}
for path in sorted(root.rglob("block_intermediate_state.json")):
    if "blockchain_tests" not in path.parts:
        continue
    data = json.loads(path.read_text())
    for test in sorted(data):
        fixture = data[test]
        network = fixture["network"]
        if network in NETWORKS and network not in cases:
            cases[network] = {
                "source": str(path.relative_to(root)),
                "test": test,
                "network": network,
                "pre": fixture["pre"],
                "genesisBlockHeader": fixture["genesisBlockHeader"],
                "genesisRLP": fixture["genesisRLP"].removeprefix("0x"),
            }

out.write_text(json.dumps([cases[n] for n in NETWORKS if n in cases], indent=1) + "\n")
