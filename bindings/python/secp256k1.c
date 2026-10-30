/* secp256k1 wrappers around the `eth_secp256k1_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_secp256k1_verify(
  lean_object* public_key,
  lean_object* hash,
  lean_object* signature
);

extern lean_object*
eth_secp256k1_is_low_s(
  lean_object* signature
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_secp256k1_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pk_obj, *hash_obj, *sig_obj;
  if (!PyArg_ParseTuple(args, "OOO", &pk_obj, &hash_obj, &sig_obj)) return NULL;
  if (!PyBytes_Check(pk_obj)) {
    PyErr_SetString(PyExc_TypeError, "public_key must be bytes");
    return NULL;
  }
  if (!PyBytes_Check(hash_obj)) {
    PyErr_SetString(PyExc_TypeError, "msg_hash must be bytes");
    return NULL;
  }
  if (!PyBytes_Check(sig_obj)) {
    PyErr_SetString(PyExc_TypeError, "signature must be bytes");
    return NULL;
  }
  /* Lengths are checked in Lean, which names the bad input in its error. */
  lean_object* res = eth_secp256k1_verify(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(pk_obj), PyBytes_GET_SIZE(pk_obj)),
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(hash_obj), PyBytes_GET_SIZE(hash_obj)),
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(sig_obj), PyBytes_GET_SIZE(sig_obj)));
  return run_io_into_pybool(res, "secp256k1 verify");
}

PyObject*
py_secp256k1_is_low_s(
  PyObject* self,
  PyObject* args
) {
  PyObject *sig_obj;
  if (!PyArg_ParseTuple(args, "O", &sig_obj)) return NULL;
  if (!PyBytes_Check(sig_obj)) {
    PyErr_SetString(PyExc_TypeError, "signature must be bytes");
    return NULL;
  }
  lean_object* res = eth_secp256k1_is_low_s(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(sig_obj), PyBytes_GET_SIZE(sig_obj)));
  return run_io_into_pybool(res, "secp256k1 is_low_s");
}
