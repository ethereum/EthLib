/* Python wrappers of the IDENTITY precompile exports.
 *
 * Each wrapper checks its Python arguments.
 *
 * It then calls the Lean export and turns the result into a Python value. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_identity(
  lean_object* data,
  uint64_t gas
);

extern uint64_t
eth_identity_gas_cost(
  lean_object* data
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_identity(
  PyObject* self,
  PyObject* args
) {
  PyObject *data_obj, *gas_obj;
  if (!PyArg_ParseTuple(args, "OO", &data_obj, &gas_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* The gas is a non-negative integer below 2^64.
   *
   * Other values raise OverflowError, and a non-integer raises TypeError. */
  uint64_t gas = (uint64_t) PyLong_AsUnsignedLongLong(gas_obj);
  if (PyErr_Occurred()) return NULL;

  /* The export takes ownership of its argument. */
  lean_object* res = eth_identity(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)),
    gas);
  return run_io_into_pybytes(res, "identity");
}

PyObject*
py_identity_gas_cost(
  PyObject* self,
  PyObject* args
) {
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "O", &data_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* Python bytes are shorter than 2^63, so the price fits in a `UInt64`. */
  uint64_t cost = eth_identity_gas_cost(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)));
  return PyLong_FromUnsignedLongLong((unsigned long long) cost);
}
