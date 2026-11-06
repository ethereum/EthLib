/* Snappy and varint wrappers around the `eth_snappy_*` and `eth_varint_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_snappy_decompress(
  lean_object* block
);

extern lean_object*
eth_snappy_compress(
  lean_object* data
);

extern lean_object*
eth_snappy_decode_frames(
  lean_object* stream
);

extern lean_object*
eth_snappy_encode_frames_literal(
  lean_object* data
);

extern lean_object*
eth_snappy_encode_frames(
  lean_object* data
);

extern lean_object*
eth_snappy_masked_crc(
  lean_object* data
);

extern lean_object*
eth_varint_encode(
  uint64_t value
);

extern lean_object*
eth_varint_decode(
  lean_object* data
);

/* ---- Wrappers --------------------------------------------------------- */

/* The bytes of the one `bytes` argument, or NULL with an exception set. */
static lean_object*
parse_one_bytes(
  PyObject* args,
  const char* name
) {
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "O", &obj)) return NULL;
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", name);
    return NULL;
  }
  return mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj));
}

PyObject*
py_snappy_decompress(
  PyObject* self,
  PyObject* args
) {
  lean_object* block = parse_one_bytes(args, "block");
  if (!block) return NULL;
  return except_into_pybytes(eth_snappy_decompress(block), SNAPPY_ERROR);
}

PyObject*
py_snappy_compress(
  PyObject* self,
  PyObject* args
) {
  lean_object* data = parse_one_bytes(args, "data");
  if (!data) return NULL;
  return except_into_pybytes(eth_snappy_compress(data), SNAPPY_ERROR);
}

PyObject*
py_snappy_decode_frames(
  PyObject* self,
  PyObject* args
) {
  lean_object* stream = parse_one_bytes(args, "stream");
  if (!stream) return NULL;
  return except_into_pybytes(eth_snappy_decode_frames(stream), SNAPPY_ERROR);
}

PyObject*
py_snappy_encode_frames_literal(
  PyObject* self,
  PyObject* args
) {
  lean_object* data = parse_one_bytes(args, "data");
  if (!data) return NULL;
  return except_into_pybytes(
    eth_snappy_encode_frames_literal(data), SNAPPY_ERROR);
}

PyObject*
py_snappy_encode_frames(
  PyObject* self,
  PyObject* args
) {
  lean_object* data = parse_one_bytes(args, "data");
  if (!data) return NULL;
  return except_into_pybytes(eth_snappy_encode_frames(data), SNAPPY_ERROR);
}

PyObject*
py_snappy_masked_crc(
  PyObject* self,
  PyObject* args
) {
  lean_object* data = parse_one_bytes(args, "data");
  if (!data) return NULL;
  return except_into_pyint(eth_snappy_masked_crc(data), SNAPPY_ERROR);
}

PyObject*
py_varint_encode(
  PyObject* self,
  PyObject* args
) {
  PyObject* value_obj;
  if (!PyArg_ParseTuple(args, "O", &value_obj)) return NULL;
  uint64_t value;
  if (parse_uint64(value_obj, "value", &value)) return NULL;
  return except_into_pybytes(eth_varint_encode(value), VARINT_ERROR);
}

PyObject*
py_varint_decode(
  PyObject* self,
  PyObject* args
) {
  lean_object* data = parse_one_bytes(args, "data");
  if (!data) return NULL;
  return except_into_pyint(eth_varint_decode(data), VARINT_ERROR);
}
