/* Python wrappers of the Ethash exports.
 *
 * A number crosses the boundary as its big-endian bytes, and a cache as its 64-byte items.
 * The Python package converts both. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object* eth_ethash_cache_size(lean_object*);
extern lean_object* eth_ethash_dataset_size(lean_object*);
extern lean_object* eth_ethash_seed(lean_object*);
extern lean_object* eth_ethash_cache(lean_object*);
extern lean_object* eth_ethash_dataset_item(lean_object*, lean_object*);

/* The largest number of arguments of an Ethash export. */
#define ETHASH_MAX_ARGS 2

/* ---- Helpers ---------------------------------------------------------- */

/* Read exactly `n` `bytes` arguments as Lean byte arrays.
 *
 * It returns 0 with a TypeError set when the argument count or a type is wrong. */
static int
parse_bytes_args(
  PyObject* args,
  Py_ssize_t n,
  lean_object** out
) {
  if (PyTuple_GET_SIZE(args) != n) {
    PyErr_Format(PyExc_TypeError, "expected %zd arguments", n);
    return 0;
  }
  for (Py_ssize_t i = 0; i < n; i++) {
    if (!PyBytes_Check(PyTuple_GET_ITEM(args, i))) {
      PyErr_SetString(PyExc_TypeError, "every argument must be bytes");
      return 0;
    }
  }
  /* Build the arrays only once every argument is checked, so none leaks on an error. */
  for (Py_ssize_t i = 0; i < n; i++) {
    PyObject* item = PyTuple_GET_ITEM(args, i);
    out[i] = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(item),
                          (size_t) PyBytes_GET_SIZE(item));
  }
  return 1;
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_ethash_cache_size(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[ETHASH_MAX_ARGS];
  if (!parse_bytes_args(args, 1, a)) return NULL;
  return pybytes_of_bytearray(eth_ethash_cache_size(a[0]));
}

PyObject*
py_ethash_dataset_size(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[ETHASH_MAX_ARGS];
  if (!parse_bytes_args(args, 1, a)) return NULL;
  return pybytes_of_bytearray(eth_ethash_dataset_size(a[0]));
}

PyObject*
py_ethash_seed(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[ETHASH_MAX_ARGS];
  if (!parse_bytes_args(args, 1, a)) return NULL;
  return pybytes_of_bytearray(eth_ethash_seed(a[0]));
}

PyObject*
py_ethash_cache(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[ETHASH_MAX_ARGS];
  if (!parse_bytes_args(args, 1, a)) return NULL;
  return pybytes_of_bytearray(eth_ethash_cache(a[0]));
}

PyObject*
py_ethash_dataset_item(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[ETHASH_MAX_ARGS];
  if (!parse_bytes_args(args, 2, a)) return NULL;
  return except_into_pybytes(eth_ethash_dataset_item(a[0], a[1]), ETHASH_ERROR);
}
