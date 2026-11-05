/* RLPx wrappers around the `eth_rlpx_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_rlpx_ecies_encrypt(
  lean_object* recipient,
  lean_object* ephemeral,
  lean_object* iv,
  lean_object* shared_mac,
  lean_object* message
);

extern lean_object*
eth_rlpx_ecies_decrypt(
  lean_object* key,
  lean_object* shared_mac,
  lean_object* ciphertext
);

extern lean_object*
eth_rlpx_make_auth(
  lean_object* static_key,
  lean_object* ephemeral_key,
  lean_object* nonce,
  lean_object* recipient,
  lean_object* r,
  lean_object* iv,
  lean_object* padding
);

extern lean_object*
eth_rlpx_respond(
  lean_object* static_key,
  lean_object* ephemeral_key,
  lean_object* nonce,
  lean_object* r,
  lean_object* iv,
  lean_object* padding,
  lean_object* auth,
  lean_object* probe
);

extern lean_object*
eth_rlpx_recipient_secrets(
  lean_object* static_key,
  lean_object* ephemeral_key,
  lean_object* nonce,
  lean_object* auth,
  lean_object* ack,
  lean_object* probe
);

extern lean_object*
eth_rlpx_finish(
  lean_object* static_key,
  lean_object* ephemeral_key,
  lean_object* nonce,
  lean_object* auth,
  lean_object* ack,
  lean_object* probe
);

extern lean_object*
eth_rlpx_write_frames(
  lean_object* aes_secret,
  lean_object* mac_secret,
  lean_object* mac_init,
  lean_object* frames
);

extern lean_object*
eth_rlpx_read_frames(
  lean_object* aes_secret,
  lean_object* mac_secret,
  lean_object* mac_init,
  lean_object* input
);

/* ---- Wrappers --------------------------------------------------------- */

/* Parse `n` arguments that must all be `bytes` into Lean byte arrays.
 *
 * Lengths are checked in Lean, which names the bad input in its error.
 *
 * Returns 0 with a TypeError set when an argument is not `bytes`. */
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
    if (!PyBytes_Check(PyTuple_GET_ITEM(args, i))) {
      PyErr_Format(PyExc_TypeError, "argument %zd must be bytes", i + 1);
      return 0;
    }
  }
  for (Py_ssize_t i = 0; i < n; i++) {
    PyObject* obj = PyTuple_GET_ITEM(args, i);
    out[i] = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj));
  }
  return 1;
}

PyObject*
py_rlpx_ecies_encrypt(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[5];
  if (!parse_bytes_args(args, 5, a)) return NULL;
  return except_into_pybytes(eth_rlpx_ecies_encrypt(a[0], a[1], a[2], a[3], a[4]), RLPX_ERROR);
}

PyObject*
py_rlpx_ecies_decrypt(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[3];
  if (!parse_bytes_args(args, 3, a)) return NULL;
  return except_into_pybytes(eth_rlpx_ecies_decrypt(a[0], a[1], a[2]), RLPX_ERROR);
}

PyObject*
py_rlpx_make_auth(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[7];
  if (!parse_bytes_args(args, 7, a)) return NULL;
  lean_object* res = eth_rlpx_make_auth(a[0], a[1], a[2], a[3], a[4], a[5], a[6]);
  return except_into_pybytes(res, RLPX_ERROR);
}

PyObject*
py_rlpx_respond(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[8];
  if (!parse_bytes_args(args, 8, a)) return NULL;
  lean_object* res = eth_rlpx_respond(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]);
  return except_into_pybytes(res, RLPX_ERROR);
}

PyObject*
py_rlpx_recipient_secrets(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[6];
  if (!parse_bytes_args(args, 6, a)) return NULL;
  lean_object* res = eth_rlpx_recipient_secrets(a[0], a[1], a[2], a[3], a[4], a[5]);
  return except_into_pybytes(res, RLPX_ERROR);
}

PyObject*
py_rlpx_finish(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[6];
  if (!parse_bytes_args(args, 6, a)) return NULL;
  return except_into_pybytes(eth_rlpx_finish(a[0], a[1], a[2], a[3], a[4], a[5]), RLPX_ERROR);
}

PyObject*
py_rlpx_write_frames(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[4];
  if (!parse_bytes_args(args, 4, a)) return NULL;
  return except_into_pybytes(eth_rlpx_write_frames(a[0], a[1], a[2], a[3]), RLPX_ERROR);
}

PyObject*
py_rlpx_read_frames(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[4];
  if (!parse_bytes_args(args, 4, a)) return NULL;
  return except_into_pybytes(eth_rlpx_read_frames(a[0], a[1], a[2], a[3]), RLPX_ERROR);
}
