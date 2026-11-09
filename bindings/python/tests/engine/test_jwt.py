"""Engine JWT authentication against RFC 7515 and independent HMAC computations."""

import base64
import hashlib
import hmac

import pytest

from ethlib import engine
from ethlib.cryptography.hmac import hmac_sha256
from ethlib.errors import JwtError
from raising import raises

SECRET = bytes(range(32))
NOW = 1700000000


def _base64(value: bytes) -> str:
    return base64.urlsafe_b64encode(value).rstrip(b"=").decode("ascii")


def _parts(header: str, claims: str, secret: bytes = SECRET) -> str:
    text = f"{header}.{claims}"
    tag = hmac.new(secret, text.encode("ascii"), hashlib.sha256).digest()
    return f"{text}.{_base64(tag)}"


def _token(header: str, claims: str, secret: bytes = SECRET) -> str:
    return _parts(_base64(header.encode()), _base64(claims.encode()), secret)


# RFC 7515, M. Jones, J. Bradley and N. Sakimura, May 2015: extracted vector begins.
# Copyright (c) 2015 IETF Trust and the persons identified as authors of the code.
# All rights reserved.
# Redistribution and use in source and binary forms, with or without modification, is permitted pursuant to, and subject to the license terms contained in, the Revised BSD License set forth in Section 4.c of the IETF Trust's Legal Provisions Relating to IETF Documents (https://trustee.ietf.org/license-info).  # noqa: E501


def test_rfc7515_signing_step() -> None:
    """RFC 7515 Appendix A.1 pins the MAC of the original encoded header and payload."""
    # https://www.rfc-editor.org/rfc/rfc7515#appendix-A.1
    key = base64.urlsafe_b64decode(
        "AyM1SysPpbyDfgZld3umj1qzKObwVMkoqQ-EstJQLr_T-1qS0gZH75aKtMN3Yj0iPS4hcgUuTwjAzZr1Z9CAow=="
    )
    signing_input = (
        b"eyJ0eXAiOiJKV1QiLA0KICJhbGciOiJIUzI1NiJ9."
        b"eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFt"
        b"cGxlLmNvbS9pc19yb290Ijp0cnVlfQ"
    )
    expected = bytes(
        [
            116,
            24,
            223,
            180,
            151,
            153,
            224,
            37,
            79,
            250,
            96,
            125,
            216,
            173,
            187,
            186,
            22,
            212,
            37,
            77,
            105,
            214,
            191,
            240,
            91,
            88,
            5,
            88,
            83,
            132,
            141,
            121,
        ]
    )
    assert hmac_sha256(key, signing_input) == expected


# The extracted RFC 7515 vector ends here.


@pytest.mark.parametrize("issued_at", [0, 1, 60, NOW, 2**53 + 1, 2**64 - 1, 10**80])
def test_build(issued_at: int) -> None:
    expected = _token('{"alg":"HS256","typ":"JWT"}', f'{{"iat":{issued_at}}}')
    token = engine.jwt_build(SECRET, issued_at)
    assert token == expected
    for clock in (max(0, issued_at - 60), issued_at, issued_at + 60):
        assert engine.jwt_check(SECRET, token, clock)
    assert not engine.jwt_check(SECRET, token, issued_at + 61)
    if issued_at > 60:
        assert not engine.jwt_check(SECRET, token, issued_at - 61)


def test_original_signing_input_and_unknown_claims() -> None:
    header = ' { "typ" : "JWT", "alg" : "HS256", "unknown" : [null, true] } '
    claims = (
        '{"exp":0,"nbf":9999999999,"aud":[],"id":"client","clv":"v1",'
        '"unknown":{"x":[true,false,null,{"y":"\\uD83D\\uDD11"}]},"iat":1700000000}'
    )
    token = _token(header, claims)
    assert engine.jwt_check(SECRET, token, NOW)
    assert not engine.jwt_check(bytes(reversed(SECRET)), token, NOW)
    # The MAC covers the original whitespace and field order, not re-encoded JSON.
    h, p, mac = token.split(".")
    assert not engine.jwt_check(SECRET, f"{_base64(header.strip().encode())}.{p}.{mac}", NOW)
    assert h != _base64(header.strip().encode())


@pytest.mark.parametrize(
    "iat, clock, accepted",
    [
        ("1700000000.5", NOW - 60, False),
        ("1700000000.5", NOW - 59, True),
        ("1700000000.5", NOW + 60, True),
        ("1700000000.5", NOW + 61, False),
        ("1.7e9", NOW, True),
        ("17E+8", NOW, True),
        ("170000000000e-2", NOW, True),
        ("-0.5", 0, True),
        ("-0.5", 60, False),
        ("-60", 0, True),
        ("-60.00000000000000001", 0, False),
        ("0e999999999999999999", 0, True),
        ("1e999999999999999999", 0, False),
        ("-1e999999999999999999", 0, False),
        ("1e-999999999999999999", 60, True),
        ("-1e-999999999999999999", 60, False),
    ],
)
def test_numeric_date(iat: str, clock: int, accepted: bool) -> None:
    token = _token('{"alg":"HS256"}', f'{{"iat":{iat}}}')
    assert engine.jwt_check(SECRET, token, clock) is accepted


def test_last_duplicate_and_escaped_names() -> None:
    assert engine.jwt_check(
        SECRET,
        _token('{"alg":"none","\\u0061lg":"HS256"}', '{"iat":0,"\\u0069at":1700000000}'),
        NOW,
    )
    assert not engine.jwt_check(
        SECRET, _token('{"alg":"HS256","alg":"none"}', '{"iat":1700000000}'), NOW
    )
    assert not engine.jwt_check(
        SECRET, _token('{"alg":"HS256"}', '{"iat":1700000000,"iat":0}'), NOW
    )


@pytest.mark.parametrize(
    "header",
    [
        "[]",
        "null",
        "{}",
        '{"alg":null}',
        '{"alg":256}',
        '{"alg":"none"}',
        '{"alg":"HS384"}',
        '{"alg":"RS256"}',
        '{"alg":"hs256"}',
        '{"alg":"HS256","crit":["unknown"],"unknown":true}',
        '{"alg":"HS256","crit":[]}',
        '{"alg":"HS256","crit":null}',
        '{"alg":"HS256",}',
        '{"alg":"HS256"} true',
        '{"alg":"HS256}',
        '{"alg":"HS256","unknown":"\\uD800"}',
    ],
)
def test_refuse_headers(header: str) -> None:
    assert not engine.jwt_check(SECRET, _token(header, '{"iat":1700000000}'), NOW)


@pytest.mark.parametrize(
    "claims",
    [
        "[]",
        "null",
        "{}",
        '{"iat":null}',
        '{"iat":true}',
        '{"iat":"1700000000"}',
        '{"iat":[]}',
        '{"iat":{}}',
        '{"iat":01700000000}',
        '{"iat":+1700000000}',
        '{"iat":1_700000000}',
        '{"iat":1700000000.}',
        '{"iat":1700000000e}',
        '{"iat":NaN}',
        '{"iat":Infinity}',
        '{"iat":1700000000}[]',
        '{"iat":1700000000,}',
        '{"iat":1700000000,"unknown":[true,]}',
        '{"iat":1700000000,"unknown":"bad\nstring"}',
        '{"iat":1700000000,"unknown":"\\uDD11"}',
        '{"iat":1700000000,"unknown":{"x" 1}}',
    ],
)
def test_refuse_claims(claims: str) -> None:
    assert not engine.jwt_check(SECRET, _token('{"alg":"HS256"}', claims), NOW)


@pytest.mark.parametrize("token", ["", ".", "..", "a.b.c", "a.b.c.d", "a.b", "=.a.b", "a.!.b"])
def test_refuse_compact(token: str) -> None:
    assert not engine.jwt_check(SECRET, token, NOW)


def test_base64_utf8_and_signature() -> None:
    header = _base64(b'{"alg":"HS256"} ')
    claims = _base64(b'{"iat":1700000000}')
    token = _parts(header, claims)
    assert engine.jwt_check(SECRET, token, NOW)
    assert not engine.jwt_check(SECRET, _parts(header + "=", claims), NOW)
    # The header ends in two characters; B adds nonzero unused bits to the final sextet.
    assert header.endswith("A")
    assert not engine.jwt_check(SECRET, _parts(header[:-1] + "B", claims), NOW)
    assert not engine.jwt_check(SECRET, _parts(_base64(b"\xff"), claims), NOW)
    assert not engine.jwt_check(SECRET, _parts(header, _base64(b"\xc0\xaf")), NOW)
    prefix, _ = token.rsplit(".", 1)
    for mac in ("", _base64(bytes(31)), _base64(bytes(33)), _base64(bytes(32))):
        assert not engine.jwt_check(SECRET, f"{prefix}.{mac}", NOW)


@pytest.mark.parametrize("length", [0, 1, 31, 33, 64])
def test_secret_length(length: int) -> None:
    secret = bytes(length)
    with raises(JwtError, "EthLib.Engine.Jwt.JwtError.secretLength") as error:
        engine.jwt_build(secret, NOW)
    assert error.value.code == 1
    assert not engine.jwt_check(secret, _token('{"alg":"HS256"}', '{"iat":1700000000}'), NOW)


def test_nested_unknown_claim() -> None:
    depth = 300
    claims = '{"iat":1700000000,"unknown":' + "[" * depth + "null" + "]" * depth + "}"
    assert engine.jwt_check(SECRET, _token('{"alg":"HS256"}', claims), NOW)
