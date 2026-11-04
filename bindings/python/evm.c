/* Python wrappers of the EVM word and memory price exports.
 *
 * Words and numbers cross the boundary as big-endian bytes, which the Python package converts. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object* eth_evm_word_op(uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* eth_evm_memory_gas_cost(lean_object*);
extern lean_object* eth_evm_extend_memory_cost(lean_object*, lean_object*);
extern lean_object* eth_evm_extend_memory_expand_by(lean_object*, lean_object*);

/* The largest number of `bytes` arguments of an EVM export. */
#define EVM_MAX_ARGS 3

/* ---- Helpers ---------------------------------------------------------- */

/* Read the `bytes` arguments from position `first` on as Lean byte arrays.
 *
 * It returns 0 with a TypeError set when an argument count or type is wrong. */
static int
parse_bytes_args(
  PyObject* args,
  Py_ssize_t first,
  Py_ssize_t n,
  lean_object** out
) {
  if (PyTuple_GET_SIZE(args) != first + n) {
    PyErr_Format(PyExc_TypeError, "expected %zd arguments", first + n);
    return 0;
  }
  for (Py_ssize_t i = 0; i < n; i++) {
    if (!PyBytes_Check(PyTuple_GET_ITEM(args, first + i))) {
      PyErr_SetString(PyExc_TypeError, "every word, size and range list must be bytes");
      return 0;
    }
  }
  /* Build the arrays only once every argument is checked, so none leaks on an error. */
  for (Py_ssize_t i = 0; i < n; i++) {
    PyObject* item = PyTuple_GET_ITEM(args, first + i);
    out[i] = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(item),
                          (size_t) PyBytes_GET_SIZE(item));
  }
  return 1;
}

/* Check that the `bytes` argument at `index`, if it is `bytes`, has a length that is a
 * multiple of `unit`, and exactly `unit` when `exact` is set.
 *
 * It returns 0 with a ValueError set otherwise.
 * It runs before any array is built, so a failed check leaks nothing. */
static int
check_length(
  PyObject* args,
  Py_ssize_t index,
  Py_ssize_t unit,
  int exact,
  const char* what
) {
  if (index >= PyTuple_GET_SIZE(args)) return 1;
  PyObject* item = PyTuple_GET_ITEM(args, index);
  if (!PyBytes_Check(item)) return 1;
  Py_ssize_t len = PyBytes_GET_SIZE(item);
  if (exact ? len != unit : len % unit != 0) {
    PyErr_Format(PyExc_ValueError, "%s", what);
    return 0;
  }
  return 1;
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_evm_word_op(
  PyObject* self,
  PyObject* args
) {
  if (PyTuple_GET_SIZE(args) < 1) {
    PyErr_SetString(PyExc_TypeError, "expected an opcode");
    return NULL;
  }
  /* The opcode is one byte. */
  unsigned long opcode = PyLong_AsUnsignedLong(PyTuple_GET_ITEM(args, 0));
  if (PyErr_Occurred()) return NULL;
  if (opcode > 0xff) {
    PyErr_SetString(PyExc_ValueError, "the opcode must be below 256");
    return NULL;
  }
  /* Each operand is one word. */
  for (Py_ssize_t i = 1; i <= 3; i++) {
    if (!check_length(args, i, 32, 1, "each operand must be 32 bytes")) return NULL;
  }
  lean_object* a[EVM_MAX_ARGS];
  if (!parse_bytes_args(args, 1, 3, a)) return NULL;
  return except_into_pybytes(eth_evm_word_op((uint8_t) opcode, a[0], a[1], a[2]), EVM_ERROR);
}

PyObject*
py_evm_memory_gas_cost(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[EVM_MAX_ARGS];
  if (!parse_bytes_args(args, 0, 1, a)) return NULL;
  return pybytes_of_bytearray(eth_evm_memory_gas_cost(a[0]));
}

PyObject*
py_evm_extend_memory_cost(
  PyObject* self,
  PyObject* args
) {
  /* Each range is a start word and a size word. */
  if (!check_length(args, 1, 64, 0, "the ranges must be a whole number of 64-byte pairs")) {
    return NULL;
  }
  lean_object* a[EVM_MAX_ARGS];
  if (!parse_bytes_args(args, 0, 2, a)) return NULL;
  return pybytes_of_bytearray(eth_evm_extend_memory_cost(a[0], a[1]));
}

PyObject*
py_evm_extend_memory_expand_by(
  PyObject* self,
  PyObject* args
) {
  /* Each range is a start word and a size word. */
  if (!check_length(args, 1, 64, 0, "the ranges must be a whole number of 64-byte pairs")) {
    return NULL;
  }
  lean_object* a[EVM_MAX_ARGS];
  if (!parse_bytes_args(args, 0, 2, a)) return NULL;
  return pybytes_of_bytearray(eth_evm_extend_memory_expand_by(a[0], a[1]));
}
