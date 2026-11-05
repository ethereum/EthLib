"""The message of the transaction error that each exception name of a fixture maps to."""

from raising import NUMBER

# A message is a template: text, with {n} where the number comes from EthLib's decoder.
N = NUMBER
TOO_SHORT = f"decoding: inputTooShort {N} {N}"

# The first fork of each transaction type of EIP-2718.
FIRST_FORK_OF_TYPE = {0: "frontier", 1: "berlin", 2: "london", 3: "dencun", 4: "pectra"}

# The forks in activation order.
FORKS = [
    "frontier",
    "homestead",
    "tangerineWhistle",
    "spuriousDragon",
    "byzantium",
    "constantinople",
    "petersburg",
    "istanbul",
    "berlin",
    "london",
    "paris",
    "shapella",
    "dencun",
    "pectra",
    "fusaka",
    "bpo1",
    "bpo2",
    "bpo3",
    "bpo4",
    "bpo5",
    "glamsterdam",
]

# The fields of the payload of each type, by the names that the exceptions use (EIP-2718,
# EIP-2930, EIP-1559, EIP-4844 and EIP-7702).
_LEGACY = ["NONCE", "GASPRICE", "GASLIMIT", "TO", "VALUE", "DATA", "V", "R", "S"]
_ACCESS = ["CHAINID", "NONCE", "GASPRICE", "GASLIMIT", "TO", "VALUE", "DATA", "ACCESS_LIST"]
_FEE = ["CHAINID", "NONCE", "PRIORITY", "MAXFEE", "GASLIMIT", "TO", "VALUE", "DATA", "ACCESS_LIST"]
_SIGNATURE = ["V", "R", "S"]
FIELDS = {
    0: _LEGACY,
    1: _ACCESS + _SIGNATURE,
    2: _FEE + _SIGNATURE,
    3: _FEE + ["MAX_BLOB_FEE", "BLOB_HASHES"] + _SIGNATURE,
    4: _FEE + ["AUTHORIZATIONS"] + _SIGNATURE,
}
_BYTES = {"TO", "DATA"}

# The fields of an authorization of EIP-7702, with the bits of each scalar, or 0 for the address.
_AUTHORIZATION = [
    ("CHAINID", 256),
    ("ADDRESS", 0),
    ("NONCE", 64),
    ("Y_PARITY", 8),
    ("R", 256),
    ("S", 256),
]


def _field(kind: int, name: str) -> int:
    names = FIELDS[kind]
    if name in ("SIGNATURE_R", "SIGNATURE_S"):
        name = name.removeprefix("SIGNATURE_")
    if name in ("BASEFEE", "MAX_FEE"):
        name = "MAXFEE"
    if name == "PRIORITY_FEE":
        name = "PRIORITY"
    return names.index(name)


def _read(data: bytes) -> tuple[bytes | list | None, int, bool]:
    """The first RLP item of the data, the bytes it spans, and whether it is a list.

    The item is None when the data holds fewer bytes than its prefix announces.
    """
    if not data:
        return None, 0, False
    prefix = data[0]
    if prefix < 0x80:
        return data[:1], 1, False
    is_list = prefix >= 0xC0
    short = prefix - (0xC0 if is_list else 0x80)
    if short <= 55:
        start, length = 1, short
    else:
        size = short - 55
        start, length = 1 + size, int.from_bytes(data[1 : 1 + size], "big")
    if len(data) < start + length:
        return None, start + length, is_list
    body = data[start : start + length]
    if not is_list:
        return body, start + length, False
    items = []
    while body:
        item, span, _ = _read(body)
        if item is None:
            return None, start + length, True
        items.append(item)
        body = body[span:]
    return items, start + length, True


def kind_of(tx: bytes) -> int | None:
    """The EIP-2718 type of a transaction, 0 for a legacy one, or None for neither form."""
    if not tx or 0x80 <= tx[0] < 0xC0:
        return None
    return tx[0] if tx[0] < 0x80 else 0


def _payload(tx: bytes, kind: int) -> bytes:
    return tx if kind == 0 else tx[1:]


def _framing(payload: bytes) -> str | None:
    """The template of a fault in the framing of the payload, or None for a framed list."""
    item, span, _ = _read(payload)
    if item is None:
        return TOO_SHORT
    if span < len(payload):
        return f"decoding: trailingBytes {len(payload) - span}"
    return None


def _scalar_fault(prefix: str, value: bytes | list, bits: int = 256) -> str | None:
    """The template of a fault of a scalar field of `bits` bits, or None for a valid scalar."""
    if isinstance(value, list):
        return f"{prefix}listAsScalar"
    if value[:1] == b"\0":
        return f"{prefix}leadingZeroInScalar"
    if int.from_bytes(value, "big") >= 2**bits:
        return f"{prefix}scalarTooLarge {int.from_bytes(value, 'big')} {bits}"
    return None


def _fields(tx: bytes, kind: int) -> list:
    item, _, _ = _read(_payload(tx, kind))
    assert isinstance(item, list), tx.hex()
    return item


def _single_byte_with_prefix(data: bytes) -> int:
    """The first byte below 0x80 that the data writes with the prefix 0x81, depth first."""
    at = 0
    while at < len(data):
        prefix = data[at]
        if prefix == 0x81 and at + 1 < len(data) and data[at + 1] < 0x80:
            return data[at + 1]
        if prefix < 0x80:
            at += 1
        elif prefix < 0xB8:
            at += 1 + prefix - 0x80
        elif prefix < 0xC0:
            size = prefix - 0xB7
            at += 1 + size + int.from_bytes(data[at + 1 : at + 1 + size], "big")
        elif prefix < 0xF8:
            at += 1
        else:
            at += 1 + prefix - 0xF7
    raise ValueError(f"no single byte with a prefix in {data.hex()}")


def _access_list_fault(entries: list) -> tuple[int, int, int]:
    """The field, the expected length and the length of the first wrong item of an access list."""
    for address, keys in entries:
        if len(address) != 20:
            return 0, 20, len(address)
        for key in keys:
            if len(key) != 32:
                return 1, 32, len(key)
    raise ValueError("no access list entry with a wrong length")


def _floor_gas(data: bytes) -> int:
    """EIP-7623, Specification: the floor of the gas of a transaction, from its calldata."""
    tokens = data.count(0) + 4 * (len(data) - data.count(0))
    return 21000 + 10 * tokens


def _authorization_fault(authorizations: bytes | list) -> str | None:
    """The template of a fault of the authorization list of EIP-7702, or None."""
    field = f"decoding: field {FIELDS[4].index('AUTHORIZATIONS')}: "
    if not isinstance(authorizations, list):
        return field + "bytesAsList"
    for authorization in authorizations:
        if not isinstance(authorization, list):
            return field + "bytesAsList"
        if len(authorization) != len(_AUTHORIZATION):
            return f"{field}wrongFieldCount {len(_AUTHORIZATION)} {len(authorization)}"
        for index, value in enumerate(authorization):
            inner = f"{field}field {index}: "
            name, bits = _AUTHORIZATION[index]
            if name == "ADDRESS":
                if isinstance(value, list):
                    return inner + "listAsBytes"
                if len(value) != 20:
                    return f"{inner}wrongLength 20 {len(value)}"
            elif fault := _scalar_fault(inner, value, bits):
                return fault
    return None


def _signature_fault(fields: list, kind: int) -> str:
    """invalidSignature, unless r or s is no scalar of 256 bits."""
    for name in ("R", "S"):
        index = _field(kind, name)
        if fault := _scalar_fault(f"decoding: field {index}: ", fields[index]):
            return fault
    return "invalidSignature"


def _chain_fault(fields: list, kind: int, fork: str, chain_id: int) -> str:
    """wrongChainId when the transaction signs another chain, and else invalidSignature.

    From Spurious Dragon, EIP-155 lets a legacy v of 35 or more sign the chain (v - 35) // 2.
    EthLib, like execution-specs, takes a chain of 2^64 or more for an invalid signature.
    """
    if kind != 0:
        signed = int.from_bytes(fields[_field(kind, "CHAINID")], "big")
        return f"wrongChainId {chain_id} {signed}" if signed != chain_id else "invalidSignature"
    v = int.from_bytes(fields[_field(kind, "V")], "big")
    eip155 = FORKS.index(fork) >= FORKS.index("spuriousDragon")
    signed = (v - 35) // 2
    if eip155 and v >= 35 and signed < 2**64 and signed != chain_id:
        return f"wrongChainId {chain_id} {signed}"
    return "invalidSignature"


def _one(
    name: str, fork: str, tx: bytes, kind: int, chain_id: int, intrinsic: int | None
) -> str | None:
    """The template of one exception name, or None when the name cannot apply to the bytes."""
    if name == "TYPE_NOT_SUPPORTED":
        return None
    payload = _payload(tx, kind)
    if name in ("RLP_ERROR_EOF", "RLP_ERROR_SIZE", "RLP_INVALID_HEADER"):
        return _framing(payload)
    if name in ("RLP_ERROR_SIZE_LEADING_ZEROS", "RLP_LEADING_ZEROS_DATA_SIZE"):
        return "decoding: leadingZeroInLength"
    if name == "RLP_LEADING_ZEROS_NONCE_SIZE":
        return f"decoding: singleByteWithPrefix {_single_byte_with_prefix(payload)}"
    if fault := _framing(payload):
        return fault
    fields = _fields(tx, kind)
    if name in ("RLP_TOO_FEW_ELEMENTS", "RLP_TOO_MANY_ELEMENTS", "RLP_WrongAuthEncoding"):
        count, want = len(fields), len(FIELDS[kind])
        # The name itself says on which side of the count the fixture lies.
        side = {"RLP_TOO_FEW_ELEMENTS": count < want, "RLP_TOO_MANY_ELEMENTS": count > want}
        assert side.get(name, count != want), (name, count)
        return f"decoding: wrongFieldCount {want} {count}"
    if name in ("ADDRESS_TOO_LONG", "ADDRESS_TOO_SHORT"):
        index = _field(kind, "TO")
        length = len(fields[index])
        assert length > 20 if name.endswith("LONG") else length < 20, (name, length)
        return f"decoding: field {index}: wrongLength 20 {length}"
    if name.startswith("RLP_INVALID_ACCESS_LIST_"):
        index = _field(kind, "ACCESS_LIST")
        field, size, length = _access_list_fault(fields[index])
        # The name gives the item, an address of 20 bytes or a storage key of 32, and the side.
        assert size == (20 if "_ADDRESS_" in name else 32), (name, size)
        assert length > size if name.endswith("LONG") else length < size, (name, length)
        return f"decoding: field {index}: field {field}: wrongLength {size} {length}"
    if name in ("EC_RECOVERY_FAIL",):
        return "invalidSignature"
    if name == "INVALID_SIGNATURE_VRS":
        return _signature_fault(fields, kind)
    if name == "INVALID_CHAINID":
        return _chain_fault(fields, kind, fork, chain_id)
    if name == "NONCE_TOO_BIG":
        return "nonceOverflow"
    if name == "PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS_2":
        return "priorityFeeGreaterThanMaxFee"
    if name == "TYPE_4_EMPTY_AUTHORIZATION_LIST":
        return "emptyAuthorizationList"
    if name.startswith("TYPE_4_INVALID_AUTHORI"):
        return _authorization_fault(fields[FIELDS[4].index("AUTHORIZATIONS")])
    if name in ("INTRINSIC_GAS_TOO_LOW", "INTRINSIC_NO_FLOOR_GAS"):
        limit = int.from_bytes(fields[_field(kind, "GASLIMIT")], "big")
        if intrinsic is None:
            return f"insufficientGas {N} {limit}"
        if FORKS.index(fork) >= FORKS.index("pectra"):
            intrinsic = max(intrinsic, _floor_gas(fields[_field(kind, "DATA")]))
        return f"insufficientGas {intrinsic} {limit}"
    if name == "INITCODE_SIZE_EXCEEDED":
        return f"initCodeTooLarge {len(fields[_field(kind, 'DATA')])}"
    if name == "NONCE_OVERFLOW":
        index = _field(kind, "NONCE")
        return _scalar_fault(f"decoding: field {index}: ", fields[index]) or "nonceOverflow"
    if name.endswith("_OVERFLOW"):
        field = name.removesuffix("_OVERFLOW")
        if field == "GASPRICE" and kind >= 2:
            field = "MAXFEE"
        at = f"decoding: field {_field(kind, field)}: "
        fault = _scalar_fault(at, fields[_field(kind, field)])
        assert fault is not None, (name, tx.hex())
        return fault
    for prefix, fault in (("RLP_LEADING_ZEROS_", "leadingZeroInScalar"), ("RLP_INVALID_", None)):
        if name.startswith(prefix):
            field = name.removeprefix(prefix)
            index = _field(kind, field)
            at = f"decoding: field {index}: "
            if fault:
                return at + fault
            if field.removeprefix("SIGNATURE_") in _BYTES:
                return at + ("listAsBytes" if isinstance(fields[index], list) else "bytesAsList")
            return _scalar_fault(at, fields[index])
    raise KeyError(f"no message for the exception {name}")


def expected_template(
    exceptions: str, fork: str, tx: bytes, chain_id: int, intrinsic: int | None = None
) -> str:
    """The template of the error for the exception names of a fixture, joined by |."""
    if not tx:
        return "emptyTransaction"
    kind = kind_of(tx)
    # EIP-2718: a transaction is an RLP list, or a type byte below 0x80 and a payload.
    if kind is None or kind not in FIRST_FORK_OF_TYPE:
        return f"unsupportedType {tx[0]}"
    if FORKS.index(fork) < FORKS.index(FIRST_FORK_OF_TYPE[kind]):
        return f"unsupportedType {kind}"
    names = [e.removeprefix("TransactionException.") for e in exceptions.split("|")]
    found = {
        template
        for name in names
        if (template := _one(name, fork, tx, kind, chain_id, intrinsic)) is not None
    }
    # Of several names, the first check that fails reports: the decoding, then the chain, then
    # the signature, as the checks of EthLib run.
    for first in ("decoding: ", "wrongChainId ", "invalidSignature"):
        earliest = {template for template in found if template.startswith(first)}
        if earliest:
            found = earliest
            break
    assert len(found) == 1, (exceptions, found)
    return found.pop()
