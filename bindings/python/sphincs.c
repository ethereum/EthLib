/* leanSPHINCS wrappers around the `eth_sphincs_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_sphincs_key_gen(
  lean_object* seed
);

extern lean_object*
eth_sphincs_sign(
  lean_object* seed,
  lean_object* msg
);

extern lean_object*
eth_sphincs_verify(
  lean_object* pk,
  lean_object* msg,
  lean_object* sig
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_sphincs_key_gen(
  PyObject* self,
  PyObject* args
) {
  PyObject *seed_obj;
  if (!PyArg_ParseTuple(args, "O", &seed_obj)) return NULL;
  const uint8_t* seed = parse_bytes_of_size(seed_obj, SPHINCS_SEED_LEN, "seed");
  if (!seed) return NULL;

  uint8_t out[SPHINCS_PUB_KEY_SIZE];
  lean_object* res = eth_sphincs_key_gen(mk_bytearray(seed, SPHINCS_SEED_LEN));
  if (run_io_into_bytearray(res, out, SPHINCS_PUB_KEY_SIZE)) {
    PyErr_SetString(PyExc_RuntimeError, "key_gen failed");
    return NULL;
  }
  return PyBytes_FromStringAndSize((const char*) out, SPHINCS_PUB_KEY_SIZE);
}

PyObject*
py_sphincs_sign(
  PyObject* self,
  PyObject* args
) {
  PyObject *seed_obj, *msg_obj;
  if (!PyArg_ParseTuple(args, "OO", &seed_obj, &msg_obj)) return NULL;
  const uint8_t* seed = parse_bytes_of_size(seed_obj, SPHINCS_SEED_LEN, "seed");
  if (!seed) return NULL;
  const uint8_t* msg = parse_bytes_of_size(msg_obj, SPHINCS_MESSAGE_LEN, "message");
  if (!msg) return NULL;

  uint8_t out[SPHINCS_SIG_SIZE];
  lean_object* res = eth_sphincs_sign(
    mk_bytearray(seed, SPHINCS_SEED_LEN),
    mk_bytearray(msg, SPHINCS_MESSAGE_LEN));
  if (run_io_into_bytearray(res, out, SPHINCS_SIG_SIZE)) {
    PyErr_SetString(PyExc_RuntimeError, "sign failed");
    return NULL;
  }
  return PyBytes_FromStringAndSize((const char*) out, SPHINCS_SIG_SIZE);
}

PyObject*
py_sphincs_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pk_obj, *msg_obj, *sig_obj;
  if (!PyArg_ParseTuple(args, "OOO", &pk_obj, &msg_obj, &sig_obj)) return NULL;
  const uint8_t* pk = parse_bytes_of_size(pk_obj, SPHINCS_PUB_KEY_SIZE, "public key");
  if (!pk) return NULL;
  const uint8_t* msg = parse_bytes_of_size(msg_obj, SPHINCS_MESSAGE_LEN, "message");
  if (!msg) return NULL;
  const uint8_t* sig = parse_bytes_of_size(sig_obj, SPHINCS_SIG_SIZE, "signature");
  if (!sig) return NULL;

  uint8_t ok = 0;
  lean_object* res = eth_sphincs_verify(
    mk_bytearray(pk, SPHINCS_PUB_KEY_SIZE),
    mk_bytearray(msg, SPHINCS_MESSAGE_LEN),
    mk_bytearray(sig, SPHINCS_SIG_SIZE));
  if (run_io_into_bool(res, &ok)) {
    PyErr_SetString(PyExc_RuntimeError, "verify failed");
    return NULL;
  }
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}
