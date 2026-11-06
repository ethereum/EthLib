/* Python wrappers of the EVM word, memory price and contract address exports.
 *
 * Words and numbers cross the boundary as big-endian bytes, which the Python package converts.
 * Lean checks the length of each argument, so these wrappers check only the types. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object* eth_evm_word_op(uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* eth_evm_immediate_depths(uint8_t, uint8_t);
extern lean_object* eth_evm_memory_gas_cost(lean_object*);
extern lean_object* eth_evm_extend_memory_cost(lean_object*, lean_object*);
extern lean_object* eth_evm_extend_memory_expand_by(lean_object*, lean_object*);
extern lean_object* eth_evm_create_address(lean_object*, lean_object*);
extern lean_object* eth_evm_create2_address(lean_object*, lean_object*, lean_object*);

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
    PyErr_SetString(PyExc_OverflowError, "the opcode must be below 256");
    return NULL;
  }
  lean_object* a[EVM_MAX_ARGS];
  if (!parse_bytes_args(args, 1, 3, a)) return NULL;
  return except_into_pybytes(eth_evm_word_op((uint8_t) opcode, a[0], a[1], a[2]), EVM_ERROR);
}

PyObject*
py_evm_immediate_depths(
  PyObject* self,
  PyObject* args
) {
  unsigned long opcode, immediate;
  if (!PyArg_ParseTuple(args, "kk", &opcode, &immediate)) return NULL;
  /* The opcode and its immediate are one byte each. */
  if (opcode > 0xff || immediate > 0xff) {
    PyErr_SetString(PyExc_OverflowError, "the opcode and the immediate must be below 256");
    return NULL;
  }
  return except_into_pybytes(eth_evm_immediate_depths((uint8_t) opcode, (uint8_t) immediate),
                             EVM_ERROR);
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
  lean_object* a[EVM_MAX_ARGS];
  if (!parse_bytes_args(args, 0, 2, a)) return NULL;
  return except_into_pybytes(eth_evm_extend_memory_cost(a[0], a[1]), EVM_ERROR);
}

PyObject*
py_evm_extend_memory_expand_by(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[EVM_MAX_ARGS];
  if (!parse_bytes_args(args, 0, 2, a)) return NULL;
  return except_into_pybytes(eth_evm_extend_memory_expand_by(a[0], a[1]), EVM_ERROR);
}

PyObject*
py_evm_create_address(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[EVM_MAX_ARGS];
  if (!parse_bytes_args(args, 0, 2, a)) return NULL;
  return except_into_pybytes(eth_evm_create_address(a[0], a[1]), EVM_ERROR);
}

PyObject*
py_evm_create2_address(
  PyObject* self,
  PyObject* args
) {
  lean_object* a[EVM_MAX_ARGS];
  if (!parse_bytes_args(args, 0, 3, a)) return NULL;
  return except_into_pybytes(eth_evm_create2_address(a[0], a[1], a[2]), EVM_ERROR);
}
