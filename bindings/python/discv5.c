/* Node Discovery Protocol v5 wrappers around the `eth_discv5_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_discv5_log_distance(
  lean_object* a,
  lean_object* b
);

extern lean_object*
eth_discv5_ecdh(
  lean_object* sk,
  lean_object* pk
);

extern lean_object*
eth_discv5_derive_keys(
  lean_object* args
);

extern lean_object*
eth_discv5_id_sign(
  lean_object* static_key,
  lean_object* challenge_data,
  lean_object* ephemeral_pubkey,
  lean_object* node_id_b
);

extern lean_object*
eth_discv5_id_verify(
  lean_object* pubkey,
  lean_object* challenge_data,
  lean_object* ephemeral_pubkey,
  lean_object* node_id_b,
  lean_object* signature
);

extern lean_object*
eth_discv5_decode_packet(
  lean_object* args
);

extern lean_object*
eth_discv5_reencode_packet(
  lean_object* dest_id,
  lean_object* packet
);

extern lean_object*
eth_discv5_encrypt_message(
  lean_object* key,
  lean_object* nonce,
  lean_object* plaintext,
  lean_object* ad
);

extern lean_object*
eth_discv5_decrypt_message(
  lean_object* key,
  lean_object* nonce,
  lean_object* message,
  lean_object* ad
);

extern lean_object*
eth_discv5_decode_message(
  lean_object* args
);

extern lean_object*
eth_discv5_reencode_message(
  lean_object* plaintext
);

extern lean_object*
eth_discv5_make_whoareyou(
  lean_object* args
);

extern lean_object*
eth_discv5_read_whoareyou(
  lean_object* args
);

extern lean_object*
eth_discv5_seal_message(
  lean_object* key,
  lean_object* src_id,
  lean_object* dest_id,
  lean_object* masking_iv,
  lean_object* nonce,
  lean_object* plaintext
);

extern lean_object*
eth_discv5_open_message(
  lean_object* key,
  lean_object* src_id,
  lean_object* dest_id,
  lean_object* packet
);

extern lean_object*
eth_discv5_seal_handshake(
  lean_object* args
);

extern lean_object*
eth_discv5_open_handshake(
  lean_object* args
);

/* ---- Wrappers --------------------------------------------------------- */

/* Parse `n` arguments that must all be `bytes` into Lean byte arrays.
 *
 * On failure it releases what it built, sets a TypeError and returns 0. */
static int
parse_bytes_args(
  PyObject* args,
  Py_ssize_t n,
  lean_object** out
) {
  if (PyTuple_GET_SIZE(args) != n) {
    PyErr_Format(PyExc_TypeError, "expected %zd arguments", n);
    return 0;
  }
  for (Py_ssize_t i = 0; i < n; i++) {
    PyObject* obj = PyTuple_GET_ITEM(args, i);
    if (!PyBytes_Check(obj)) {
      for (Py_ssize_t j = 0; j < i; j++) lean_dec(out[j]);
      PyErr_Format(PyExc_TypeError, "argument %zd must be bytes", i + 1);
      return 0;
    }
    out[i] = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj));
  }
  return 1;
}

PyObject*
py_discv5_log_distance(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[2];
  if (!parse_bytes_args(args, 2, a)) return NULL;
  return except_into_pyint(eth_discv5_log_distance(a[0], a[1]), DISCV5_ERROR);
}

PyObject*
py_discv5_ecdh(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[2];
  if (!parse_bytes_args(args, 2, a)) return NULL;
  return except_into_pybytes(eth_discv5_ecdh(a[0], a[1]), DISCV5_ERROR);
}

PyObject*
py_discv5_derive_keys(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_discv5_derive_keys, args, 5, DISCV5_ERROR);
}

PyObject*
py_discv5_id_sign(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[4];
  if (!parse_bytes_args(args, 4, a)) return NULL;
  return except_into_pybytes(eth_discv5_id_sign(a[0], a[1], a[2], a[3]), DISCV5_ERROR);
}

PyObject*
py_discv5_id_verify(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[5];
  if (!parse_bytes_args(args, 5, a)) return NULL;
  return except_into_pybool(
    eth_discv5_id_verify(a[0], a[1], a[2], a[3], a[4]), DISCV5_ERROR);
}

PyObject*
py_discv5_decode_packet(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_discv5_decode_packet, args, 2, DISCV5_ERROR);
}

PyObject*
py_discv5_reencode_packet(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[2];
  if (!parse_bytes_args(args, 2, a)) return NULL;
  return except_into_pybytes(eth_discv5_reencode_packet(a[0], a[1]), DISCV5_ERROR);
}

PyObject*
py_discv5_encrypt_message(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[4];
  if (!parse_bytes_args(args, 4, a)) return NULL;
  return except_into_pybytes(
    eth_discv5_encrypt_message(a[0], a[1], a[2], a[3]), DISCV5_ERROR);
}

PyObject*
py_discv5_decrypt_message(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[4];
  if (!parse_bytes_args(args, 4, a)) return NULL;
  return except_into_pybytes(
    eth_discv5_decrypt_message(a[0], a[1], a[2], a[3]), DISCV5_ERROR);
}

PyObject*
py_discv5_decode_message(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_discv5_decode_message, args, 1, DISCV5_ERROR);
}

PyObject*
py_discv5_reencode_message(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[1];
  if (!parse_bytes_args(args, 1, a)) return NULL;
  return except_into_pybytes(eth_discv5_reencode_message(a[0]), DISCV5_ERROR);
}

PyObject*
py_discv5_make_whoareyou(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_discv5_make_whoareyou, args, 5, DISCV5_ERROR);
}

PyObject*
py_discv5_read_whoareyou(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_discv5_read_whoareyou, args, 2, DISCV5_ERROR);
}

PyObject*
py_discv5_seal_message(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[6];
  if (!parse_bytes_args(args, 6, a)) return NULL;
  return except_into_pybytes(
    eth_discv5_seal_message(a[0], a[1], a[2], a[3], a[4], a[5]), DISCV5_ERROR);
}

PyObject*
py_discv5_open_message(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[4];
  if (!parse_bytes_args(args, 4, a)) return NULL;
  return except_into_pybytes(
    eth_discv5_open_message(a[0], a[1], a[2], a[3]), DISCV5_ERROR);
}

PyObject*
py_discv5_seal_handshake(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_discv5_seal_handshake, args, 10, DISCV5_ERROR);
}

PyObject*
py_discv5_open_handshake(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_discv5_open_handshake, args, 5, DISCV5_ERROR);
}
