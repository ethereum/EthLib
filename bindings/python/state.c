/* State root wrapper around the `eth_state_root` Lean export. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* The export consumes its object argument, so the caller never releases it. */

extern lean_object*
eth_state_root(
  lean_object* state
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
  return run_io_into_pybytes(eth_state_root(state), "state_root");
}
