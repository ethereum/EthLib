"""Merge the rounds of the three sides into one Markdown table."""

# python compare.py <results directory>
#
# Each row gives the best time over the rounds and the spread.
# The spread is the slowest round's best over the fastest's.
# The row also gives the ratio of EthLib to the reference, and whether the output digests agree.

import glob
import json
import os
import sys

R = sys.argv[1]


def load(side):
    """The results of every round of one side."""
    runs = []
    for f in sorted(glob.glob(os.path.join(R, f"{side}_r*.json"))):
        runs.append(json.load(open(f))["results"])
    return runs


def merge(runs):
    """The best time, the spread and the output digests of each row over the rounds."""
    out = {}
    for run in runs:
        for k, v in run.items():
            e = out.setdefault(k, {"bests": [], "outs": set(), "errors": []})
            if "error" in v:
                e["errors"].append(v["error"])
            else:
                e["bests"].append(v["best"])
                e["outs"].add(v["out"])
    for e in out.values():
        if e["bests"]:
            e["best"] = min(e["bests"])
            e["spread"] = max(e["bests"]) / min(e["bests"])
    return out


eth = merge(load("ethlib"))
ref = merge(load("eels"))
for k, v in merge(load("pyspec")).items():
    if k in ref:
        ref[k + "#pyspec"] = v
    else:
        ref[k] = v


def fmt(t):
    """A time in seconds, in the unit that suits it."""
    if t >= 1:
        return f"{t:.2f} s"
    if t >= 1e-3:
        return f"{t * 1e3:.2f} ms"
    return f"{t * 1e6:.1f} µs"


rows = []
for name, e in eth.items():
    matches = [k for k in ref if k == name or k.split("@")[0] == name or k.split("#")[0] == name]
    if not matches:
        rows.append((name, e, None, None))
    for k in matches:
        rows.append((name, e, k, ref[k]))

print(
    "| operation | EthLib | spread | reference | ref. time | spread | EthLib / ref. | same output |"
)
print("|---|---|---|---|---|---|---|---|")
for name, e, k, r in rows:
    if "best" not in e:
        print(f"| {name} | error: {e['errors'][:1]} | | | | | | |")
        continue
    if r is None:
        print(f"| {name} | {fmt(e['best'])} | {e['spread']:.2f} | (none) | | | | |")
        continue
    if "best" not in r:
        print(f"| {name} | {fmt(e['best'])} | {e['spread']:.2f} | {k} | error | | | |")
        continue
    same = (
        "yes"
        if (len(e["outs"]) == 1 and e["outs"] == r["outs"])
        else f"NO {e['outs']} vs {r['outs']}"
    )
    ratio = e["best"] / r["best"]
    print(
        f"| {name} | {fmt(e['best'])} | {e['spread']:.2f} | {k} | {fmt(r['best'])} | "
        f"{r['spread']:.2f} | {ratio:.2f} | {same} |"
    )
# Reference rows with no EthLib counterpart.
for k, r in ref.items():
    base = k.split("@")[0].split("#")[0]
    if base not in eth and "best" in r:
        print(f"| {base} | (not exported) | | {k} | {fmt(r['best'])} | {r['spread']:.2f} | | |")
