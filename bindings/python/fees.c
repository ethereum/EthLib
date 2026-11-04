/* Python wrappers of the base fee and blob base fee exports.
 *
 * A number crosses the boundary as its big-endian bytes, and a fork as its name in UTF-8.
 * The Python package converts both. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object* eth_fees_base_fee_per_gas(lean_object*, lean_object*, lean_object*);
extern lean_object* eth_fees_fake_exponential(lean_object*, lean_object*, lean_object*);
extern lean_object* eth_fees_base_fee_per_blob_gas(lean_object*, lean_object*);
extern lean_object* eth_fees_excess_blob_gas(
  lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* eth_fees_blob_data_fee(lean_object*, lean_object*, lean_object*);

/* The largest number of arguments of a fee export. */
#define FEES_MAX_ARGS 4

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
py_fees_base_fee_per_gas(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[FEES_MAX_ARGS];
  if (!parse_bytes_args(args, 3, a)) return NULL;
  return pybytes_of_bytearray(eth_fees_base_fee_per_gas(a[0], a[1], a[2]));
}

PyObject*
py_fees_fake_exponential(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[FEES_MAX_ARGS];
  if (!parse_bytes_args(args, 3, a)) return NULL;
  return pybytes_of_bytearray(eth_fees_fake_exponential(a[0], a[1], a[2]));
}

PyObject*
py_fees_base_fee_per_blob_gas(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[FEES_MAX_ARGS];
  if (!parse_bytes_args(args, 2, a)) return NULL;
  return except_into_pybytes(eth_fees_base_fee_per_blob_gas(a[0], a[1]), FEES_ERROR);
}

PyObject*
py_fees_excess_blob_gas(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[FEES_MAX_ARGS];
  if (!parse_bytes_args(args, 4, a)) return NULL;
  return except_into_pybytes(eth_fees_excess_blob_gas(a[0], a[1], a[2], a[3]), FEES_ERROR);
}

PyObject*
py_fees_blob_data_fee(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[FEES_MAX_ARGS];
  if (!parse_bytes_args(args, 3, a)) return NULL;
  return except_into_pybytes(eth_fees_blob_data_fee(a[0], a[1], a[2]), FEES_ERROR);
}
