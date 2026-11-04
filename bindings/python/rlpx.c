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
  return run_io_into_pybytes(eth_rlpx_ecies_encrypt(a[0], a[1], a[2], a[3], a[4]),
    "rlpx ecies_encrypt");
}

PyObject*
py_rlpx_ecies_decrypt(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[3];
  if (!parse_bytes_args(args, 3, a)) return NULL;
  return run_io_into_pybytes(eth_rlpx_ecies_decrypt(a[0], a[1], a[2]), "rlpx ecies_decrypt");
}
