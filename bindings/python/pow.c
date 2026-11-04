/* Python wrappers of the proof-of-work exports.
 *
 * A number crosses the boundary as its big-endian bytes, and a fork as its name in UTF-8.
 * The Python package converts both. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object* eth_pow_block_difficulty(
  lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* eth_pow_seal_hash(lean_object*, lean_object*);
extern lean_object* eth_pow_check(lean_object*, lean_object*);

/* The largest number of arguments of a proof-of-work export: those of the difficulty. */
#define POW_MAX_ARGS 6

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
py_pow_block_difficulty(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[POW_MAX_ARGS];
  if (!parse_bytes_args(args, 6, a)) return NULL;
  return except_into_pybytes(
    eth_pow_block_difficulty(a[0], a[1], a[2], a[3], a[4], a[5]), BLOCK_ERROR);
}

PyObject*
py_pow_seal_hash(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[POW_MAX_ARGS];
  if (!parse_bytes_args(args, 2, a)) return NULL;
  return except_into_pybytes(eth_pow_seal_hash(a[0], a[1]), BLOCK_ERROR);
}

PyObject*
py_pow_check(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[POW_MAX_ARGS];
  if (!parse_bytes_args(args, 2, a)) return NULL;
  return except_into_pybool(eth_pow_check(a[0], a[1]), BLOCK_ERROR);
}
