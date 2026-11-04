/* Python wrappers of the proof-of-work exports.
 *
 * A number crosses the boundary as its big-endian bytes, and a fork as its name in UTF-8.
 * The Python package converts both. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object* eth_pow_block_difficulty(
  lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);

/* The number of arguments of the difficulty export. */
#define DIFFICULTY_ARGS 6

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_pow_block_difficulty(
  PyObject* self,
  PyObject* args
) {
  if (PyTuple_GET_SIZE(args) != DIFFICULTY_ARGS) {
    PyErr_Format(PyExc_TypeError, "expected %d arguments", DIFFICULTY_ARGS);
    return NULL;
  }
  for (Py_ssize_t i = 0; i < DIFFICULTY_ARGS; i++) {
    if (!PyBytes_Check(PyTuple_GET_ITEM(args, i))) {
      PyErr_SetString(PyExc_TypeError, "every argument must be bytes");
      return NULL;
    }
  }
  /* Build the arrays only once every argument is checked, so none leaks on an error. */
  lean_object* a[DIFFICULTY_ARGS];
  for (Py_ssize_t i = 0; i < DIFFICULTY_ARGS; i++) {
    PyObject* item = PyTuple_GET_ITEM(args, i);
    a[i] = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(item),
                        (size_t) PyBytes_GET_SIZE(item));
  }
  return except_into_pybytes(
    eth_pow_block_difficulty(a[0], a[1], a[2], a[3], a[4], a[5]), BLOCK_ERROR);
}
