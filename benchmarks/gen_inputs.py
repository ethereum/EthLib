"""Write the deterministic inputs of the benchmarks, in the execution-specs environment."""

# python gen_inputs.py <EthLib checkout> <data directory>

import dataclasses
import hashlib
import json
import re
import sys
from pathlib import Path

import spec256k1
from ethereum.forks.osaka import transactions as T
from ethereum.forks.osaka.blocks import Block, Header, Withdrawal
from ethereum.forks.osaka.fork_types import Address
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes, Bytes8, Bytes32
from ethereum_types.numeric import U64, U256, Uint
from py_ecc.bls import G2ProofOfPossession as BLS
from py_ecc.optimized_bn128 import (
    G1 as BN_G1,
    G2 as BN_G2,
    multiply as bn_mul,
    neg as bn_neg,
    normalize as bn_norm,
)

ETHLIB = Path(sys.argv[1])  # the EthLib checkout, for its vector files
OUT = Path(sys.argv[2]) / "inputs.json"
R_BLS = 0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001


def h(seed: bytes) -> bytes:
    """SHA-256 of a seed."""
    return hashlib.sha256(seed).digest()


def stream(seed: bytes, n: int) -> bytes:
    """`n` pseudorandom bytes derived from a seed."""
    out = bytearray()
    i = 0
    while len(out) < n:
        out += h(seed + i.to_bytes(8, "big"))
        i += 1
    return bytes(out[:n])


inp = {}
inp["bytes_32"] = stream(b"short", 32).hex()
inp["bytes_100k"] = stream(b"long", 100_000).hex()

# Signed EIP-1559 transactions, chain 1.
keys = [spec256k1.PrivateKey(h(b"key" + bytes([i]))) for i in range(4)]


def signed_tx(i: int, data_len: int, n_access: int) -> T.FeeMarketTransaction:
    """The signed EIP-1559 transaction number `i`."""
    tx = T.FeeMarketTransaction(
        chain_id=U64(1),
        nonce=U256(i),
        max_priority_fee_per_gas=Uint(10**9),
        max_fee_per_gas=Uint(30 * 10**9),
        gas=Uint(100_000 + 16 * data_len),
        to=Address(h(b"to" + i.to_bytes(4, "big"))[:20]),
        value=U256(10**15 + i),
        data=Bytes(stream(b"data" + i.to_bytes(4, "big"), data_len)),
        access_list=tuple(
            T.Access(
                account=Address(h(b"al" + bytes([j]))[:20]),
                slots=(Bytes32(h(b"slot" + bytes([j]))),),
            )
            for j in range(n_access)
        ),
        y_parity=U256(0),
        r=U256(0),
        s=U256(0),
    )
    sh = T.signing_hash_1559(tx)
    sig = keys[i % 4].sign_recoverable(sh)
    r, s, v = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:64], "big"), sig[64]
    return dataclasses.replace(tx, y_parity=U256(v), r=U256(r), s=U256(s))


tx0 = signed_tx(0, 100, 2)
inp["tx"] = T.encode_transaction(tx0).hex()
inp["tx_sender"] = spec256k1.PublicKey.from_secret(h(b"key" + bytes([0]))).format(False).hex()

# A block of 150 type-2 transactions and 16 withdrawals, with the Osaka (Fusaka) header.
txs = tuple(T.encode_transaction(signed_tx(i, 200 + (i * 37) % 300, i % 3)) for i in range(150))
header = Header(
    parent_hash=Bytes32(h(b"parent")),
    ommers_hash=Bytes32(h(b"ommers")),
    coinbase=Address(h(b"coinbase")[:20]),
    state_root=Bytes32(h(b"state")),
    transactions_root=Bytes32(h(b"txroot")),
    receipt_root=Bytes32(h(b"rroot")),
    bloom=stream(b"bloom", 256),
    difficulty=Uint(0),
    number=Uint(23_000_000),
    gas_limit=Uint(45_000_000),
    gas_used=Uint(20_000_000),
    timestamp=U256(1_760_000_000),
    extra_data=Bytes(b"ethlib-bench"),
    prev_randao=Bytes32(h(b"randao")),
    nonce=Bytes8(bytes(8)),
    base_fee_per_gas=Uint(7 * 10**8),
    withdrawals_root=Bytes32(h(b"wroot")),
    blob_gas_used=U64(393216),
    excess_blob_gas=U64(0),
    parent_beacon_block_root=Bytes32(h(b"pbbr")),
    requests_hash=Bytes32(h(b"reqs")),
)
withdrawals = tuple(
    Withdrawal(
        index=U64(i),
        validator_index=U64(1000 + i),
        address=Address(h(b"w" + bytes([i]))[:20]),
        amount=U64(10**7 + i),
    )
    for i in range(16)
)
block = Block(header=header, transactions=txs, ommers=(), withdrawals=withdrawals)
inp["block"] = rlp.encode(block).hex()

# 1000 key/value pairs for the unsecured trie: 32-byte keys, RLP-sized values.
inp["trie_pairs"] = [
    [
        h(b"k" + i.to_bytes(4, "big")).hex(),
        stream(b"v" + i.to_bytes(4, "big"), 1 + (i * 13) % 80).hex(),
    ]
    for i in range(1000)
]

# A state of 200 accounts, 50 of them with 20 storage slots and code.
accounts = []
for i in range(200):
    addr = h(b"acct" + i.to_bytes(4, "big"))[:20]
    code = stream(b"code" + i.to_bytes(4, "big"), 300) if i % 4 == 0 else b""
    storage = (
        [
            [
                h(b"sk" + i.to_bytes(4, "big") + j.to_bytes(4, "big")).hex(),
                (int.from_bytes(h(b"sv" + bytes([j])), "big") >> (8 * (j % 30))) or 1,
            ]
            for j in range(20)
        ]
        if i % 4 == 0
        else []
    )
    accounts.append([addr.hex(), i, 10**18 * (i + 1), code.hex(), storage])
inp["state"] = accounts

# secp256k1 recover: the transaction's signing hash and signature.
sh = T.signing_hash_1559(tx0)
inp["secp_hash"] = bytes(sh).hex()
inp["secp_sig"] = (int(tx0.r).to_bytes(32, "big") + int(tx0.s).to_bytes(32, "big")).hex()
inp["secp_v"] = int(tx0.y_parity)

# Precompile call data.
pc = {}
pc["ecrecover"] = (
    bytes(sh) + (27 + int(tx0.y_parity)).to_bytes(32, "big") + bytes.fromhex(inp["secp_sig"])
).hex()
pc["sha256"] = stream(b"pc-sha", 1024).hex()
pc["ripemd160"] = stream(b"pc-ripemd", 1024).hex()
pc["identity"] = stream(b"pc-id", 1024).hex()


def modexp_input(b: int, e: int, m: int, tag: bytes) -> str:
    """MODEXP call data with a base, exponent and odd modulus of the given lengths."""
    base = stream(tag + b"b", b)
    exp = stream(tag + b"e", e)
    mod = stream(tag + b"m", m)
    mod = mod[:-1] + bytes([mod[-1] | 1])  # odd modulus
    return (
        b.to_bytes(32, "big") + e.to_bytes(32, "big") + m.to_bytes(32, "big") + base + exp + mod
    ).hex()


pc["modexp_small"] = modexp_input(32, 32, 32, b"ms")
pc["modexp_large"] = modexp_input(512, 512, 512, b"ml")


def fq32(x) -> bytes:
    """A field element as 32 big-endian bytes."""
    return int(x).to_bytes(32, "big")


p1 = bn_norm(bn_mul(BN_G1, 7))
p2 = bn_norm(bn_mul(BN_G1, 11))
pc["bn_add"] = (fq32(p1[0]) + fq32(p1[1]) + fq32(p2[0]) + fq32(p2[1])).hex()
pc["bn_mul"] = (fq32(p1[0]) + fq32(p1[1]) + h(b"bn-scalar")).hex()
q = bn_norm(BN_G2)
g2 = fq32(q[0].coeffs[1]) + fq32(q[0].coeffs[0]) + fq32(q[1].coeffs[1]) + fq32(q[1].coeffs[0])
np1 = bn_norm(bn_neg(bn_mul(BN_G1, 7)))
pc["bn_pairing2"] = (fq32(p1[0]) + fq32(p1[1]) + g2 + fq32(np1[0]) + fq32(np1[1]) + g2).hex()
# BLAKE2F: 12 rounds, the RFC 7693 'abc' example layout of EIP-152.
SHARED = (
    "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5"
    "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b"
    "616263" + "00" * 125 + "0300000000000000" + "0000000000000000"
)
pc["blake2f"] = "0000000c" + SHARED + "01"  # EIP-152 test vector 5
pc["blake2f_10k"] = (10000).to_bytes(4, "big").hex() + SHARED + "01"
# Point evaluation: EthLib's copy of the consensus-spec-tests vector correct_proof_0_0.
vec = (
    ETHLIB
    / "tests/cryptography/kzg/verify_kzg_proof/verify_kzg_proof_case_correct_proof_0_0/data.yaml"
).read_text()
fields = dict(re.findall(r"(\w+): '?0x([0-9a-f]+)'?", vec))
commit = bytes.fromhex(fields["commitment"])
pc["point_evaluation"] = (
    b"\x01"
    + hashlib.sha256(commit).digest()[1:]
    + bytes.fromhex(fields["z"])
    + bytes.fromhex(fields["y"])
    + commit
    + bytes.fromhex(fields["proof"])
).hex()
# EIP-2537 cases from EthLib's copy of the EIP vectors: the largest input of each kind.
PICK = {
    "add_G1_bls": "bls_g1add_g1+p1",
    "add_G2_bls": "bls_g2add_g2+p2",
    "msm_G1_bls": "bls_g1msm_multiple",
    "msm_G2_bls": "bls_g2msm_multiple",
    "pairing_check_bls": "bls_pairing_e(G1,G2)*e(G1,-G2)=1",
}
cases = json.loads((ETHLIB / "bindings/python/tests/precompile/eip2537_cases.json").read_text())
for key, name in [
    ("add_G1_bls", "bls_g1add"),
    ("add_G2_bls", "bls_g2add"),
    ("msm_G1_bls", "bls_g1msm"),
    ("msm_G2_bls", "bls_g2msm"),
    ("pairing_check_bls", "bls_pairing"),
    ("map_fp_to_G1_bls", "bls_map_fp_to_g1"),
    ("map_fp2_to_G2_bls", "bls_map_fp2_to_g2"),
]:
    c = next(c for c in cases[key] if c["Name"] == PICK[key]) if key in PICK else cases[key][0]
    pc[name] = c["Input"]
    pc[name + "_name"] = c["Name"]
p256 = json.loads((ETHLIB / "bindings/python/tests/precompile/eip7951_cases.json").read_text())
pc["p256verify"] = next(c["Input"] for c in p256 if c["Expected"].endswith("01"))
inp["precompiles"] = pc

# EVM word operands.
inp["words"] = [int.from_bytes(h(b"w" + bytes([i])), "big") for i in range(3)]

# BLS: keys, one message, signatures.
sks = [int.from_bytes(h(b"bls" + i.to_bytes(4, "big")), "big") % R_BLS for i in range(512)]
pks = [BLS.SkToPk(sk) for sk in sks]
msg = h(b"bls-message")
inp["bls_sk"] = sks[0].to_bytes(32, "big").hex()
inp["bls_msg"] = msg.hex()
inp["bls_pks"] = [pk.hex() for pk in pks]
inp["bls_sig0"] = BLS.Sign(sks[0], msg).hex()
inp["bls_fast_sig"] = BLS.Sign(
    sum(sks) % R_BLS, msg
).hex()  # the aggregate of 512 signatures on msg
msgs = [h(b"m" + bytes([i])) for i in range(16)]
sigs16 = [BLS.Sign(sks[i], msgs[i]) for i in range(16)]
inp["bls_msgs16"] = [m.hex() for m in msgs]
inp["bls_sigs16"] = [s.hex() for s in sigs16]
inp["bls_aggsig16"] = BLS.Aggregate(sigs16).hex()

# KZG blobs: 4096 canonical field elements each.


def blob(tag: bytes) -> bytes:
    """A blob of 4096 canonical field elements."""
    return b"".join(
        (int.from_bytes(h(tag + i.to_bytes(4, "big")), "big") % R_BLS).to_bytes(32, "big")
        for i in range(4096)
    )


inp["blobs"] = [blob(b"blob" + bytes([i])).hex() for i in range(6)]
inp["kzg_z"] = (int.from_bytes(h(b"z"), "big") % R_BLS).to_bytes(32, "big").hex()
inp["node_id"] = int.from_bytes(h(b"node"), "big")

OUT.write_text(json.dumps(inp))
print("wrote", OUT, OUT.stat().st_size)
