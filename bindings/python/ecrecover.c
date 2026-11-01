/* Python wrapper of the ECRECOVER export. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_ecrecover(
  lean_object* data,
  uint64_t gas
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_ecrecover(
  PyObject* self,
  PyObject* args
) {
  PyObject *data_obj, *gas_obj;
  if (!PyArg_ParseTuple(args, "OO", &data_obj, &gas_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* The gas is a non-negative integer below 2^64. */
  uint64_t gas = (uint64_t) PyLong_AsUnsignedLongLong(gas_obj);
  if (PyErr_Occurred()) return NULL;

  lean_object* res = eth_ecrecover(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)),
    gas);
  return run_io_into_pybytes(res, "ecrecover");
}
