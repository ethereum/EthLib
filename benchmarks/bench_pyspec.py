"""The consensus-specs side, with the Fulu mainnet pyspec and the libraries it calls."""

# python bench_pyspec.py <data directory> <results file>
#
# A row "<op>" runs the pyspec function, with BLS through py_arkworks_bls12381 as pyspec does.
# A row "<op>@ckzg" or "<op>@snappy" runs that library on the same input.

import sys
from pathlib import Path

import ckzg
import snappy
from eth_consensus_specs.fulu import mainnet as spec
from eth_consensus_specs.fulu import minimal as spec_min

from benchlib import Runner, load

inp = load(sys.argv[1], "inputs.json")
R = Runner("pyspec", sys.argv[2])
x = bytes.fromhex

d32, d100k = x(inp["bytes_32"]), x(inp["bytes_100k"])
R.run("sha256_32", lambda: spec.sha256_hash(d32).digest())
R.run("sha256_100k", lambda: spec.sha256_hash(d100k).digest())

# BLS, as pyspec runs it (py_arkworks_bls12381).
bls = spec.bls
sk = int.from_bytes(x(inp["bls_sk"]), "big")
msg = x(inp["bls_msg"])
pks = [x(p) for p in inp["bls_pks"]]
sig0 = x(inp["bls_sig0"])
sigs16, msgs16 = [x(s) for s in inp["bls_sigs16"]], [x(m) for m in inp["bls_msgs16"]]
agg16, fast = x(inp["bls_aggsig16"]), x(inp["bls_fast_sig"])
R.run("bls_sign", lambda: bytes(bls.Sign(sk, msg)))
R.run("bls_verify", lambda: bls.Verify(pks[0], msg, sig0))
R.run("bls_aggregate_16", lambda: bytes(bls.Aggregate(sigs16)))
R.run("bls_aggregate_verify_16", lambda: bls.AggregateVerify(pks[:16], msgs16, agg16))
R.run("bls_fast_aggregate_verify_512", lambda: bls.FastAggregateVerify(pks, msg, fast))
R.run("bls_eth_aggregate_pubkeys_512", lambda: bytes(spec.eth_aggregate_pubkeys(pks)))

# KZG: pyspec calls c-kzg-4844, so the rows call it directly, with no precomputation.
blobs = [x(b) for b in inp["blobs"]]
z = x(inp["kzg_z"])
ts = ckzg.load_trusted_setup(str(Path(sys.argv[1]).resolve() / "trusted_setup_4096.txt"), 0)
commits = [ckzg.blob_to_kzg_commitment(b, ts) for b in blobs]
proofs = [ckzg.compute_blob_kzg_proof(b, c, ts) for b, c in zip(blobs, commits)]
R.run("kzg_blob_to_commitment@ckzg", lambda: ckzg.blob_to_kzg_commitment(blobs[0], ts))
R.run("kzg_compute_kzg_proof@ckzg", lambda: ckzg.compute_kzg_proof(blobs[0], z, ts))
pz, yz = ckzg.compute_kzg_proof(blobs[0], z, ts)
R.run("kzg_verify_kzg_proof@ckzg", lambda: ckzg.verify_kzg_proof(commits[0], z, yz, pz, ts))
R.run("kzg_compute_blob_proof@ckzg", lambda: ckzg.compute_blob_kzg_proof(blobs[0], commits[0], ts))
R.run(
    "kzg_verify_blob_proof@ckzg",
    lambda: ckzg.verify_blob_kzg_proof(blobs[0], commits[0], proofs[0], ts),
)
R.run(
    "kzg_verify_blob_proof_batch_6@ckzg",
    lambda: ckzg.verify_blob_kzg_proof_batch(
        b"".join(blobs), b"".join(commits), b"".join(proofs), ts
    ),
)
R.run("kzg_compute_cells@ckzg", lambda: ckzg.compute_cells(blobs[0], ts))
R.run("kzg_compute_cells_and_proofs@ckzg", lambda: ckzg.compute_cells_and_kzg_proofs(blobs[0], ts))
cells, cproofs = ckzg.compute_cells_and_kzg_proofs(blobs[0], ts)
idx = list(range(128))
R.run(
    "kzg_verify_cell_batch_128@ckzg",
    lambda: ckzg.verify_cell_kzg_proof_batch([commits[0]] * 128, idx, cells, cproofs, ts),
)
half = list(range(0, 128, 2))
R.run(
    "kzg_recover_cells_64@ckzg",
    lambda: ckzg.recover_cells_and_kzg_proofs(half, [cells[i] for i in half], ts),
)

node = spec.NodeID(inp["node_id"])
R.run(
    "peerdas_get_custody_groups_128", lambda: [int(g) for g in spec.get_custody_groups(node, 128)]
)
R.run("peerdas_get_custody_groups_8", lambda: [int(g) for g in spec.get_custody_groups(node, 8)])
R.run(
    "peerdas_columns_for_group", lambda: [int(c) for c in spec.compute_columns_for_custody_group(5)]
)

# Snappy (python-snappy, the C++ library) and SSZ (pyspec's eth-ssz-specs).
ci = load(sys.argv[1], "cons_inputs.json")
comp, framed = x(ci["snappy_block"]), x(ci["snappy_framed"])
R.run("snappy_decompress_100k@snappy", lambda: snappy.decompress(comp))
R.run("snappy_decode_frames_100k@snappy", lambda: snappy.StreamDecompressor().decompress(framed))

TYPES = {
    "beacon_state_mainnet": spec.BeaconState,
    "beacon_state_minimal": spec_min.BeaconState,
    "validators": spec.BeaconState.model_fields["validators"].annotation,
    "balances": spec.BeaconState.model_fields["balances"].annotation,
}
for name, case in ci["ssz"].items():
    T = TYPES[name.rsplit("_", 1)[0]]
    b = x(case["bytes"])
    v = T.decode_bytes(b)
    R.run("ssz_serialize_" + name, lambda v=v: v.encode_bytes())
    R.run(
        "ssz_deserialize_" + name,
        lambda T=T, b=b: T.decode_bytes(b),
        norm=lambda r: r.encode_bytes(),
    )
    # hash_tree_root from scratch: decode a fresh value each time so no cached root is reused.
    R.run(
        "ssz_hash_tree_root_" + name,
        lambda T=T, b=b: bytes(T.decode_bytes(b).hash_tree_root()),
        budget=0,
    )
