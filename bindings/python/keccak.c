/* Python wrappers of the Keccak-256, Keccak-512 and Keccak-f[1600] exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_keccak256(
  lean_object* data
);

extern lean_object*
eth_keccak512(
  lean_object* data
);

extern lean_object*
eth_keccak_f1600(
  lean_object* state
);

/* The size of a Keccak-f[1600] state: 25 lanes of 8 bytes. */
#define KECCAK_STATE_SIZE 200

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_keccak256(
  PyObject* self,
  PyObject* args
) {
  /* Take exactly one argument, and only `bytes`. */
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "O", &data_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* Copy the message into a Lean ByteArray.
   * The export takes ownership of it and frees it. */
  lean_object* res = eth_keccak256(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)));
  /* The export is total, so its result is the digest itself, not an `IO` result. */
  PyObject* out = PyBytes_FromStringAndSize(
    (const char*) lean_sarray_cptr(res),
    (Py_ssize_t) lean_sarray_size(res));
  /* The wrapper owns the digest, so it frees it after the copy.
   * On a failed copy, the result is NULL with a Python error already set. */
  lean_dec(res);
  return out;
}

PyObject*
py_keccak512(
  PyObject* self,
  PyObject* args
) {
  /* Take exactly one argument, and only `bytes`. */
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "O", &data_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* The export takes ownership of the copy, and returns the digest itself.
   * The helper copies the digest into `bytes` and frees it. */
  return pybytes_of_bytearray(eth_keccak512(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj))));
}

PyObject*
py_keccak_f1600(
  PyObject* self,
  PyObject* args
) {
  /* Take exactly one argument: `bytes` of the state size. */
  PyObject* state_obj;
  if (!PyArg_ParseTuple(args, "O", &state_obj)) return NULL;
  const uint8_t* state = parse_bytes_of_size(state_obj, KECCAK_STATE_SIZE, "state");
  if (!state) return NULL;
  /* The export takes ownership of the copy, and returns the permuted state. */
  lean_object* res = eth_keccak_f1600(mk_bytearray(state, KECCAK_STATE_SIZE));
  return except_into_pybytes(res, KECCAK_ERROR);
}
