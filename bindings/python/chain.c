/* Python wrappers of the exports of the active fork of mainnet, of Hoodi and of a configured chain. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_mainnet_active_fork(
  uint64_t number,
  uint64_t timestamp
);

extern lean_object*
eth_hoodi_active_fork(
  uint64_t number,
  uint64_t timestamp
);

extern lean_object*
eth_active_fork(
  lean_object* config,
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

PyObject*
py_hoodi_active_fork(
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
  return pybytes_of_bytearray(eth_hoodi_active_fork(number, timestamp));
}

PyObject*
py_active_fork(
  PyObject* self,
  PyObject* args
) {
  const char* config;
  Py_ssize_t config_len;
  PyObject *number_obj, *timestamp_obj;
  if (!PyArg_ParseTuple(args, "y#OO", &config, &config_len, &number_obj, &timestamp_obj)) {
    return NULL;
  }
  /* The block number and the timestamp are non-negative integers below 2^64. */
  uint64_t number = (uint64_t) PyLong_AsUnsignedLongLong(number_obj);
  if (PyErr_Occurred()) return NULL;
  uint64_t timestamp = (uint64_t) PyLong_AsUnsignedLongLong(timestamp_obj);
  if (PyErr_Occurred()) return NULL;
  /* The configuration is JSON text in UTF-8; the name of the fork, or no bytes, comes back. */
  return except_into_pybytes(
    eth_active_fork(mk_bytearray((const uint8_t*) config, (size_t) config_len), number, timestamp),
    CHAIN_ERROR);
}
