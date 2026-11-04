/* Python wrappers of the exports that run any precompile, and give its price, at a fork.
 *
 * Each wrapper checks its Python arguments.
 *
 * It then calls the Lean export and turns the result into Python bytes. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_precompile_run(
  lean_object* fork,
  uint64_t address,
  lean_object* data,
  uint64_t gas
);

extern lean_object*
eth_precompile_price(
  lean_object* fork,
  uint64_t address,
  lean_object* data
);

/* ---- Helpers ---------------------------------------------------------- */

/* Read a fork name, an address and call data.
 *
 * It returns 0 with an exception set when an argument has the wrong type or range.
 * On success, the caller owns `*fork` and `*data`. */
static int
parse_fork_address_data(
  PyObject* fork_obj,
  PyObject* address_obj,
  PyObject* data_obj,
  lean_object** fork,
  uint64_t* address,
  lean_object** data
) {
  if (!PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "fork must be str");
    return 0;
  }
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return 0;
  }
  /* The address is a non-negative integer below 2^64. */
  *address = (uint64_t) PyLong_AsUnsignedLongLong(address_obj);
  if (PyErr_Occurred()) return 0;
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &len);
  if (!utf8) return 0;
  *fork = mk_bytearray((const uint8_t*) utf8, (size_t) len);
  *data = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                       (size_t) PyBytes_GET_SIZE(data_obj));
  return 1;
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_precompile_run(
  PyObject* self,
  PyObject* args
) {
  PyObject *fork_obj, *address_obj, *data_obj, *gas_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &fork_obj, &address_obj, &data_obj, &gas_obj)) return NULL;
  /* The gas is a non-negative integer below 2^64, read before any Lean object exists. */
  uint64_t gas = (uint64_t) PyLong_AsUnsignedLongLong(gas_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object *fork, *data;
  uint64_t address;
  if (!parse_fork_address_data(fork_obj, address_obj, data_obj, &fork, &address, &data)) return NULL;

  /* The export takes ownership of its arguments. */
  lean_object* res = eth_precompile_run(fork, address, data, gas);
  return except_into_pybytes(res, PRECOMPILE_ERROR);
}

PyObject*
py_precompile_price(
  PyObject* self,
  PyObject* args
) {
  PyObject *fork_obj, *address_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOO", &fork_obj, &address_obj, &data_obj)) return NULL;
  lean_object *fork, *data;
  uint64_t address;
  if (!parse_fork_address_data(fork_obj, address_obj, data_obj, &fork, &address, &data)) return NULL;

  /* The export takes ownership of its arguments. */
  lean_object* res = eth_precompile_price(fork, address, data);
  return except_into_pybytes(res, PRECOMPILE_ERROR);
}
