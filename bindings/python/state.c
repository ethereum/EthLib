/* State root wrappers around the `eth_state_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* The export consumes its object argument, so the caller never releases it. */

extern lean_object*
eth_state_root(
  lean_object* state
);

extern lean_object*
eth_state_withdrawals_root(
  lean_object* fork,
  lean_object* state,
  lean_object* block
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_state_root(
  PyObject* self,
  PyObject* args
) {
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "O", &obj)) return NULL;
  if (!PyBytes_Check(obj)) {
    PyErr_SetString(PyExc_TypeError, "state must be bytes");
    return NULL;
  }
  lean_object* state = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj));
  return except_into_pybytes(eth_state_root(state), STATE_ERROR);
}

PyObject*
py_state_withdrawals_root(
  PyObject* self,
  PyObject* args
) {
  PyObject *fork_obj, *state_obj, *block_obj;
  if (!PyArg_ParseTuple(args, "OOO", &fork_obj, &state_obj, &block_obj)) return NULL;
  if (!PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "fork must be str");
    return NULL;
  }
  if (!PyBytes_Check(state_obj) || !PyBytes_Check(block_obj)) {
    PyErr_SetString(PyExc_TypeError, "state and block must be bytes");
    return NULL;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &len);
  if (!utf8) return NULL;
  lean_object* fork = mk_bytearray((const uint8_t*) utf8, len);
  lean_object* state = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(state_obj), PyBytes_GET_SIZE(state_obj));
  lean_object* block = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(block_obj), PyBytes_GET_SIZE(block_obj));
  return except_into_pybytes(eth_state_withdrawals_root(fork, state, block), STATE_ERROR);
}
