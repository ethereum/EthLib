# Test format: hash to G2

The suite `BLS12381G2_XMD:SHA-256_SSWU_RO_` of [RFC 9380 §8.8.2](https://www.rfc-editor.org/rfc/rfc9380#section-8.8.2) hashes a message to a point of the BLS12-381 group G2.

## Test case format

```yaml
input:
  msg: bytes -- the message
  dst: bytes -- the domain separation tag
output:
  x: [Fp, Fp] -- the affine x coordinate, c0 then c1, for x = c0 + c1 * I
  y: [Fp, Fp] -- the affine y coordinate, in the same form
```

All byte fields are hexadecimal strings, prefixed with `0x`.
An `Fp` element is 48 big-endian bytes.

## Source

The cases are the five cases of RFC 9380, Appendix J.10.1.
A script transcribed each case from the text of the RFC.
