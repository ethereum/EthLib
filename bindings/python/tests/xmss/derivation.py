"""The one-time signatures of a leanXMSS seed at any digest, codeword or not."""

from typing import NamedTuple

from ethlib.cryptography import keccak, xmss

# `sign` reveals the chains of a key only at a codeword.
# A `verify` case that isolates the codeword check needs them at another digest.
# So this module restates the derivations of `EthLib/Cryptography/Xmss`, on EthLib's Keccak-256.
# It builds inputs of `verify`, and never an expected output.

# ---- Addresses -------------------------------------------------------------

# The address types, `AddressType.code`.
PRF = 0
CHAIN = 1
LEAF = 2
NODE = 3
PARAM = 5
MSG = 12

# The two layers, `Layer.toNat`.
BOTTOM_LAYER = 0
TOP_LAYER = 1


def encode_address(tau: int, mu: int, hi: int, lo: int) -> bytes:
    """`encodeAddress`: `[ lo: 4 | hi: 3 | tau + 32 mu: 1 | zero: 8 ]`, each field little-endian."""
    return lo.to_bytes(4, "little") + hi.to_bytes(3, "little") + bytes([tau + 32 * mu]) + bytes(8)


def layer_hi(layer: int, a: int = 0) -> int:
    """`layerHi`: the top layer sets bit 23 of `hi`."""
    return a + (1 << 23) * layer


def th(pp: bytes, address: bytes, payload: bytes) -> bytes:
    """`th`: the first half of the hash of `P | A | M`."""
    return keccak.keccak256(pp + address + payload)[: xmss.DIGEST_LEN]


# ---- Derivations from the seed ---------------------------------------------


def scheme_seed(seed: bytes) -> bytes:
    """`schemeSeed`: the hash of the scheme's name, then the seed."""
    return keccak.keccak256(b"leanXMSS" + seed)


def public_param(s: bytes) -> bytes:
    """`publicParamOf`: the first half of the derivation at the all-zero parameter and `A_param`."""
    zero = bytes(xmss.PUBLIC_PARAM_LEN)
    return keccak.keccak256(zero + encode_address(PARAM, 0, 0, 0) + s)[: xmss.PUBLIC_PARAM_LEN]


def chain_starts(pp: bytes, s: bytes, layer: int, e: int) -> list[bytes]:
    """`chainStarts`: chains `2j` and `2j + 1` of key `e` start at the halves of derivation `j`."""
    starts = []
    for j in range(xmss.CHAINS // 2):
        pair = keccak.keccak256(pp + encode_address(PRF, 0, layer_hi(layer, j), e) + s)
        starts += [pair[: xmss.DIGEST_LEN], pair[xmss.DIGEST_LEN :]]
    return starts


# ---- One-time signatures ---------------------------------------------------


def chain(pp: bytes, layer: int, e: int, i: int, start: int, steps: int, value: bytes) -> bytes:
    """`chain`: walk chain `i` of key `e` for `steps` steps from position `start`."""
    # `chainStep` hashes the value, then the chain index as `LE_128(i)`.
    index = i.to_bytes(16, "little")
    for mu in range(start, start + steps):
        value = th(pp, encode_address(CHAIN, mu, layer_hi(layer), e), value + index)
    return value


def message_digest(pp: bytes, layer: int, e: int, message: bytes, randomizer: bytes) -> bytes:
    """`messageDigest`: the digest key `e` signs under one randomizer."""
    return th(pp, encode_address(MSG, 0, layer_hi(layer), e), message + randomizer)


# The digits a digest carries, `DIGITS`.
# A digit names one of `CHAIN_LENGTH` positions, and the digits fill the digest.
DIGITS = 8 * xmss.DIGEST_LEN // (xmss.CHAIN_LENGTH.bit_length() - 1)


def digits(digest: bytes) -> list[int]:
    """`Internal.digits`: digit `i` has weight `CHAIN_LENGTH^i` in the little-endian digest."""
    value = int.from_bytes(digest, "little")
    return [value // xmss.CHAIN_LENGTH**i % xmss.CHAIN_LENGTH for i in range(DIGITS)]


def is_codeword(digest: bytes) -> bool:
    """`codeword?`: the digits after the chains are zero, and the others sum to the target."""
    x = digits(digest)
    return not any(x[xmss.CHAINS :]) and sum(x[: xmss.CHAINS]) == xmss.TARGET_SUM


def reveal(pp: bytes, s: bytes, layer: int, e: int, digest: bytes) -> list[bytes]:
    """The chains of key `e` at the positions that the digits of a digest name, as in `otsSign`."""
    starts = chain_starts(pp, s, layer, e)
    x = digits(digest)
    return [chain(pp, layer, e, i, 0, x[i], starts[i]) for i in range(xmss.CHAINS)]


def leaf(pp: bytes, layer: int, e: int, digest: bytes, values: list[bytes]) -> bytes:
    """The leaf that `otsLeaf` computes after its codeword check: the hash of the chain ends."""
    x = digits(digest)
    last = xmss.CHAIN_LENGTH - 1
    ends = [chain(pp, layer, e, i, x[i], last - x[i], values[i]) for i in range(xmss.CHAINS)]
    return th(pp, encode_address(LEAF, 0, layer_hi(layer), e), b"".join(ends))


# ---- Trees -----------------------------------------------------------------


def fold(pp: bytes, layer: int, e: int, node: bytes, path: list[bytes]) -> bytes:
    """`fold`: the root a path leads to from the leaf of key `e`."""
    j = e
    for level, sibling in enumerate(path, start=1):
        # `Merkle.climb`: the node is the left child when its index is even.
        left, right = (node, sibling) if j % 2 == 0 else (sibling, node)
        j //= 2
        node = th(pp, encode_address(NODE, 0, layer_hi(layer, level), j), left + right)
    return node


# ---- Signatures ------------------------------------------------------------


class LayerSignature(NamedTuple):
    """One layer of a signature: the randomizer, the chain values and the path."""

    randomizer: bytes
    chain_values: list[bytes]
    path: list[bytes]

    def encode(self) -> bytes:
        """`encodeLayerSignature`: the three fields, in order."""
        return self.randomizer + b"".join(self.chain_values) + b"".join(self.path)


def _digests(data: bytes) -> list[bytes]:
    return [data[i : i + xmss.DIGEST_LEN] for i in range(0, len(data), xmss.DIGEST_LEN)]


def _decode_layer(data: bytes) -> LayerSignature:
    path = xmss.RANDOMIZER_LEN + xmss.CHAINS * xmss.DIGEST_LEN
    return LayerSignature(
        data[: xmss.RANDOMIZER_LEN],
        _digests(data[xmss.RANDOMIZER_LEN : path]),
        _digests(data[path:]),
    )


def decode_signature(signature: bytes) -> tuple[int, LayerSignature, LayerSignature]:
    """`decodeSignature`: the leaf index, the bottom layer and the top layer."""
    assert len(signature) == xmss.SIG_SIZE
    top = (xmss.LEAF_INDEX_SIZE + xmss.SIG_SIZE) // 2
    return (
        int.from_bytes(signature[: xmss.LEAF_INDEX_SIZE], "little"),
        _decode_layer(signature[xmss.LEAF_INDEX_SIZE : top]),
        _decode_layer(signature[top:]),
    )


def layer_root(pp: bytes, layer: int, e: int, message: bytes, sig: LayerSignature) -> bytes:
    """The root that `layerRoot` computes after its codeword check."""
    digest = message_digest(pp, layer, e, message, sig.randomizer)
    return fold(pp, layer, e, leaf(pp, layer, e, digest, sig.chain_values), sig.path)


def layer_digests(pp: bytes, message: bytes, signature: bytes) -> tuple[bytes, bytes]:
    """The digests that the bottom and the top layer of a signature sign."""
    leaf_index, bottom, top = decode_signature(signature)
    # The top key signs the root that the bottom layer leads to.
    root = layer_root(pp, BOTTOM_LAYER, leaf_index, message, bottom)
    return (
        message_digest(pp, BOTTOM_LAYER, leaf_index, message, bottom.randomizer),
        message_digest(pp, TOP_LAYER, leaf_index >> xmss.LAYER_HEIGHT, root, top.randomizer),
    )


# ---- Near misses -----------------------------------------------------------


class NearMiss(NamedTuple):
    """A signature whose one changed layer leads to the leaf of the signature it comes from."""

    signature: bytes
    # The digest that the changed layer signs under its new randomizer.
    digest: bytes
    # The leaf that the changed layer leads to.
    leaf: bytes
    # The leaf that the same layer of the valid signature leads to.
    valid_leaf: bytes


def near_miss(
    seed: bytes, message: bytes, signature: bytes, layer: int, randomizer: bytes
) -> NearMiss:
    """
    A valid signature with one layer signed again under another randomizer.

    The new chain values are the key's own, revealed at the digits of the new digest.

    So they lead to the same leaf, and the path and the other layer still match.
    """
    s = scheme_seed(seed)
    pp = public_param(s)
    leaf_index, bottom, top = decode_signature(signature)
    if layer == BOTTOM_LAYER:
        e, signed, valid = leaf_index, message, bottom
    else:
        # The top key signs the root that the valid bottom layer leads to.
        e = leaf_index >> xmss.LAYER_HEIGHT
        signed = layer_root(pp, BOTTOM_LAYER, leaf_index, message, bottom)
        valid = top
    digest = message_digest(pp, layer, e, signed, randomizer)
    changed = LayerSignature(randomizer, reveal(pp, s, layer, e, digest), valid.path)
    layers = (changed, top) if layer == BOTTOM_LAYER else (bottom, changed)
    valid_digest = message_digest(pp, layer, e, signed, valid.randomizer)
    return NearMiss(
        signature=signature[: xmss.LEAF_INDEX_SIZE] + layers[0].encode() + layers[1].encode(),
        digest=digest,
        leaf=leaf(pp, layer, e, digest, changed.chain_values),
        valid_leaf=leaf(pp, layer, e, valid_digest, valid.chain_values),
    )
