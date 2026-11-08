/* Python wrappers of the proof-of-work exports.
 *
 * The difficulty takes and returns typed values, which the generic converter passes.
 * The other exports take a fork as its name in UTF-8, and a header or a block in RLP. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object* eth_pow_block_difficulty(lean_object*);
extern lean_object* eth_pow_seal_hash(lean_object*, lean_object*);
extern lean_object* eth_pow_check(lean_object*, lean_object*);
extern lean_object* eth_pow_validate_ommers(lean_object*, lean_object*, lean_object*, uint8_t);

/* The largest number of `bytes` arguments of a proof-of-work export: those of a header. */
#define POW_MAX_ARGS 2

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
  return call_pyvalue_export(eth_pow_block_difficulty, args, 6, BLOCK_ERROR);
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

PyObject*
py_pow_validate_ommers(
  PyObject* self,
  PyObject* args
) {
  PyObject *forks_obj, *recent_obj, *block_obj;
  int check_seal;
  if (!PyArg_ParseTuple(args, "OOOp", &forks_obj, &recent_obj, &block_obj, &check_seal)) {
    return NULL;
  }
  if (!PyBytes_Check(forks_obj) || !PyBytes_Check(recent_obj) || !PyBytes_Check(block_obj)) {
    PyErr_SetString(PyExc_TypeError, "forks, recent and block must be bytes");
    return NULL;
  }
  lean_object* forks = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(forks_obj), (size_t) PyBytes_GET_SIZE(forks_obj));
  lean_object* recent = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(recent_obj), (size_t) PyBytes_GET_SIZE(recent_obj));
  lean_object* block = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(block_obj), (size_t) PyBytes_GET_SIZE(block_obj));
  return except_into_pybool(
    eth_pow_validate_ommers(forks, recent, block, (uint8_t) check_seal), BLOCK_ERROR);
}
