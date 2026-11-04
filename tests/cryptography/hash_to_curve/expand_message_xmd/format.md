# Test format: `expand_message_xmd` with SHA-256

`expand_message_xmd` of [RFC 9380 §5.3.1](https://www.rfc-editor.org/rfc/rfc9380#section-5.3.1) stretches a message into `len_in_bytes` uniform bytes.

## Test case format

```yaml
input:
  msg: bytes -- the message
  dst: bytes -- the domain separation tag
  len_in_bytes: int -- the number of output bytes
output: bytes -- the uniform bytes
```

All byte fields are hexadecimal strings, prefixed with `0x`.

## Source

The cases are the SHA-256 cases of RFC 9380, Appendix K.1 and Appendix K.2.
K.2 uses a tag longer than 255 bytes, which the expander first hashes, as §5.3.3 says.
A script transcribed each case from the text of the RFC.
The case name gives the message and `len_in_bytes`.
