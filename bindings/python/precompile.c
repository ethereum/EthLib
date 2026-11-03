/* Python wrapper of the export that runs any precompile by address.
 *
 * It checks its Python arguments.
 *
 * It then calls the Lean export and turns the result into Python bytes. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_precompile_run(
  uint64_t address,
  lean_object* data,
  uint64_t gas
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_precompile_run(
  PyObject* self,
  PyObject* args
) {
  PyObject *address_obj, *data_obj, *gas_obj;
  if (!PyArg_ParseTuple(args, "OOO", &address_obj, &data_obj, &gas_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* The address and the gas are non-negative integers below 2^64. */
  uint64_t address = (uint64_t) PyLong_AsUnsignedLongLong(address_obj);
  if (PyErr_Occurred()) return NULL;
  uint64_t gas = (uint64_t) PyLong_AsUnsignedLongLong(gas_obj);
  if (PyErr_Occurred()) return NULL;

  /* The export takes ownership of its argument. */
  lean_object* res = eth_precompile_run(
    address,
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)),
    gas);
  return run_io_into_pybytes(res, "precompile");
}
