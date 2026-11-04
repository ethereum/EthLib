"""The EthLib side: every row through the Python bindings."""

# python bench_ethlib.py <data directory> <results file>

import json
import sys

from ethlib.consensus import compute_columns_for_custody_group, get_custody_groups
from ethlib.cryptography import _native as N
from ethlib.cryptography import bls, keccak, kzg, secp256k1, sha256
from ethlib.execution import evm, fees, transactions, trie
from ethlib.networking import snappy
from ethlib.precompiles import run as precompile
from ethlib.serialization import rlp, ssz
from ethlib.state import state_root

from benchlib import Runner, load

inp = load(sys.argv[1], "inputs.json")
R = Runner("ethlib", sys.argv[2])
x = bytes.fromhex

d32, d100k = x(inp["bytes_32"]), x(inp["bytes_100k"])
R.run("keccak256_32", lambda: keccak.keccak256(d32))
R.run("keccak256_100k", lambda: keccak.keccak256(d100k))
R.run("keccak512_32", lambda: keccak.keccak512(d32))
R.run("keccak512_100k", lambda: keccak.keccak512(d100k))
R.run("sha256_32", lambda: sha256.sha256(d32))
R.run("sha256_100k", lambda: sha256.sha256(d100k))

block = x(inp["block"])
tx = x(inp["tx"])
block_item = rlp.decode(block)
tx_item = rlp.decode(tx[1:])
R.run("rlp_decode_block", lambda: rlp.decode(block))
R.run("rlp_encode_block", lambda: rlp.encode(block_item))
R.run("rlp_decode_tx", lambda: rlp.decode(tx[1:]))
R.run("rlp_encode_tx", lambda: rlp.encode(tx_item))
R.run("block_decode_encode", lambda: N.block_reencode("fusaka", block))
R.run("block_header_hash", lambda: N.block_header_hash("fusaka", rlp.encode(block_item[0])))

pairs = [(x(k), x(v)) for k, v in inp["trie_pairs"]]
R.run("trie_root_1000", lambda: trie.root(pairs, False))
R.run("trie_root_1000_secured", lambda: trie.root(pairs, True))


def num(n: int) -> bytes:
    """The minimal big-endian bytes of a number."""
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


state = rlp.encode(
    [
        [x(a), num(nonce), num(bal), x(code), [[x(k), num(v)] for k, v in st]]
        for a, nonce, bal, code, st in inp["state"]
    ]
)
R.run("state_root_200", lambda: state_root(state))

R.run("tx_hash", lambda: transactions.tx_hash("fusaka", tx))
R.run("tx_recover_sender", lambda: transactions.recover_sender("fusaka", tx))
R.run("tx_intrinsic_gas", lambda: transactions.intrinsic_gas("fusaka", tx))
R.run(
    "secp256k1_recover",
    lambda: secp256k1.recover(x(inp["secp_hash"]), x(inp["secp_sig"]), inp["secp_v"]),
    norm=lambda r: r[1:],
)

pc = inp["precompiles"]
ADDR = {
    "ecrecover": 1,
    "sha256": 2,
    "ripemd160": 3,
    "identity": 4,
    "modexp_small": 5,
    "modexp_large": 5,
    "bn_add": 6,
    "bn_mul": 7,
    "bn_pairing2": 8,
    "blake2f": 9,
    "blake2f_10k": 9,
    "point_evaluation": 10,
    "bls_g1add": 0x0B,
    "bls_g1msm": 0x0C,
    "bls_g2add": 0x0D,
    "bls_g2msm": 0x0E,
    "bls_pairing": 0x0F,
    "bls_map_fp_to_g1": 0x10,
    "bls_map_fp2_to_g2": 0x11,
    "p256verify": 0x100,
}
for name, addr in ADDR.items():
    data = x(pc[name])
    R.run("pc_" + name, lambda a=addr, d=data: precompile("fusaka", a, d, 10**9))

w = inp["words"]
OPS = {
    "ADD": (0x01, 2),
    "MUL": (0x02, 2),
    "DIV": (0x04, 2),
    "SDIV": (0x05, 2),
    "ADDMOD": (0x08, 3),
    "MULMOD": (0x09, 3),
    "EXP": (0x0A, 2),
    "SIGNEXTEND": (0x0B, 2),
    "BYTE": (0x1A, 2),
    "SHL": (0x1B, 2),
    "SAR": (0x1D, 2),
    "CLZ": (0x1E, 1),
}
SMALL = {"SIGNEXTEND": 15, "BYTE": 7, "SHL": 77, "SAR": 77}
for name, (op, k) in OPS.items():
    args = list(w[:k])
    if name in SMALL:
        args[0] = SMALL[name]
    R.run("evm_" + name, lambda op=op, a=args: evm.word_op(op, *a))
R.run("evm_memory_gas_cost", lambda: evm.memory_gas_cost(1 << 20))

R.run("fees_base_fee", lambda: fees.calculate_base_fee_per_gas(45_000_000, 30_000_000, 7 * 10**8))
R.run("fees_blob_base_fee", lambda: fees.get_base_fee_per_blob_gas("fusaka", 50_000_000))

sk, msg = x(inp["bls_sk"]), x(inp["bls_msg"])
pks = [x(p) for p in inp["bls_pks"]]
sig0 = x(inp["bls_sig0"])
R.run("bls_sign", lambda: bls.sign(sk, msg))
R.run("bls_verify", lambda: bls.verify(pks[0], msg, sig0))
sigs16, msgs16 = [x(s) for s in inp["bls_sigs16"]], [x(m) for m in inp["bls_msgs16"]]
R.run("bls_aggregate_16", lambda: bls.aggregate(sigs16))
R.run(
    "bls_aggregate_verify_16",
    lambda: bls.aggregate_verify(pks[:16], msgs16, x(inp["bls_aggsig16"])),
)
R.run(
    "bls_fast_aggregate_verify_512",
    lambda: bls.fast_aggregate_verify(pks, msg, x(inp["bls_fast_sig"])),
)
R.run("bls_eth_aggregate_pubkeys_512", lambda: bls.eth_aggregate_pubkeys(pks))

blobs = [x(b) for b in inp["blobs"]]
z = x(inp["kzg_z"])
commits = [kzg.blob_to_kzg_commitment(b) for b in blobs]
proofs = [kzg.compute_blob_kzg_proof(b, c) for b, c in zip(blobs, commits)]
R.run("kzg_blob_to_commitment", lambda: kzg.blob_to_kzg_commitment(blobs[0]))
R.run("kzg_compute_kzg_proof", lambda: kzg.compute_kzg_proof(blobs[0], z))
pz, yz = kzg.compute_kzg_proof(blobs[0], z)
R.run("kzg_verify_kzg_proof", lambda: kzg.verify_kzg_proof(commits[0], z, yz, pz))
R.run("kzg_compute_blob_proof", lambda: kzg.compute_blob_kzg_proof(blobs[0], commits[0]))
R.run("kzg_verify_blob_proof", lambda: kzg.verify_blob_kzg_proof(blobs[0], commits[0], proofs[0]))
R.run(
    "kzg_verify_blob_proof_batch_6", lambda: kzg.verify_blob_kzg_proof_batch(blobs, commits, proofs)
)
R.run("kzg_compute_cells", lambda: kzg.compute_cells(blobs[0]))
cells, cproofs = kzg.compute_cells_and_kzg_proofs(blobs[0])
R.run("kzg_compute_cells_and_proofs", lambda: kzg.compute_cells_and_kzg_proofs(blobs[0]), budget=0)
idx = list(range(128))
R.run(
    "kzg_verify_cell_batch_128",
    lambda: kzg.verify_cell_kzg_proof_batch([commits[0]] * 128, idx, cells, cproofs),
)
half = list(range(0, 128, 2))
R.run(
    "kzg_recover_cells_64",
    lambda: kzg.recover_cells_and_kzg_proofs(half, [cells[i] for i in half]),
    budget=0,
)

R.run("peerdas_get_custody_groups_128", lambda: get_custody_groups(inp["node_id"], 128))
R.run("peerdas_get_custody_groups_8", lambda: get_custody_groups(inp["node_id"], 8))
R.run("peerdas_columns_for_group", lambda: compute_columns_for_custody_group(5))

ci = load(sys.argv[1], "cons_inputs.json")
comp = x(ci["snappy_block"])
R.run("snappy_decompress_100k", lambda: snappy.decompress(comp))
framed = x(ci["snappy_framed"])
R.run("snappy_decode_frames_100k", lambda: snappy.decode_frames(framed))
for name, case in ci["ssz"].items():
    b = x(case["bytes"])
    # The native calls, with the JSON documents prepared outside the timing.
    tj, vj = ssz._dump(case["type"]), ssz._dump(case["value"])
    if case["serialize"]:
        R.run("ssz_serialize_" + name, lambda tj=tj, vj=vj: N.ssz_serialize(tj, vj))
    R.run(
        "ssz_deserialize_" + name,
        lambda tj=tj, b=b: N.ssz_deserialize(tj, b),
        norm=lambda r, t=case["type"]: ssz.serialize(t, json.loads(r)),
    )
