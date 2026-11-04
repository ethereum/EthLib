/* Python wrappers of the MODEXP exports.
 *
 * Each wrapper checks its Python arguments.
 *
 * It then calls the Lean export and turns the result into a Python value. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_modexp(
  lean_object* data,
  uint64_t gas
);

extern lean_object*
eth_modexp_gas_cost(
  lean_object* data
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_modexp(
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

  lean_object* res = eth_modexp(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)),
    gas);
  return except_into_pybytes(res, MODEXP_ERROR);
}

PyObject*
py_modexp_gas_cost(
  PyObject* self,
  PyObject* args
) {
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "O", &data_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  lean_object* res = eth_modexp_gas_cost(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)));
  /* The price is at most 528449536, so it always fits in a `UInt64`. */
  return except_into_pyint(res, MODEXP_ERROR);
}
