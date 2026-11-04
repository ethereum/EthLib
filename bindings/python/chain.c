/* Python wrapper of the export of the active fork of mainnet. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_mainnet_active_fork(
  uint64_t number,
  uint64_t timestamp
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_mainnet_active_fork(
  PyObject* self,
  PyObject* args
) {
  PyObject *number_obj, *timestamp_obj;
  if (!PyArg_ParseTuple(args, "OO", &number_obj, &timestamp_obj)) return NULL;
  /* The block number and the timestamp are non-negative integers below 2^64. */
  uint64_t number = (uint64_t) PyLong_AsUnsignedLongLong(number_obj);
  if (PyErr_Occurred()) return NULL;
  uint64_t timestamp = (uint64_t) PyLong_AsUnsignedLongLong(timestamp_obj);
  if (PyErr_Occurred()) return NULL;
  /* The export is total: the name of the fork, or no bytes when no fork is active. */
  return pybytes_of_bytearray(eth_mainnet_active_fork(number, timestamp));
}
