/* Block and header wrappers around the `eth_block_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_block_header_hash(
  lean_object* fork,
  lean_object* header
);

extern lean_object*
eth_block_reencode(
  lean_object* fork,
  lean_object* block
);

extern lean_object*
eth_receipt_reencode(
  lean_object* fork,
  lean_object* receipt
);

extern lean_object*
eth_receipt_logs_bloom(
  lean_object* fork,
  lean_object* receipt
);

/* ---- Wrappers --------------------------------------------------------- */

/* Read a fork name and RLP bytes, as Lean byte arrays.
 *
 * It returns 0 with a TypeError set when an argument has the wrong type. */
static int
parse_fork_and_bytes(
  PyObject* args,
  const char* name,
  lean_object** fork,
  lean_object** data
) {
  PyObject* fork_obj;
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "OO", &fork_obj, &data_obj)) return 0;
  if (!PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "fork must be str");
    return 0;
  }
  if (!PyBytes_Check(data_obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", name);
    return 0;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &len);
  if (!utf8) return 0;
  *fork = mk_bytearray((const uint8_t*) utf8, len);
  *data = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj), PyBytes_GET_SIZE(data_obj));
  return 1;
}

PyObject*
py_block_header_hash(
  PyObject* self,
  PyObject* args
) {
  lean_object* fork;
  lean_object* header;
  if (!parse_fork_and_bytes(args, "header", &fork, &header)) return NULL;
  return except_into_pybytes(eth_block_header_hash(fork, header), BLOCK_ERROR);
}

PyObject*
py_block_reencode(
  PyObject* self,
  PyObject* args
) {
  lean_object* fork;
  lean_object* block;
  if (!parse_fork_and_bytes(args, "block", &fork, &block)) return NULL;
  return except_into_pybytes(eth_block_reencode(fork, block), BLOCK_ERROR);
}

PyObject*
py_receipt_reencode(
  PyObject* self,
  PyObject* args
) {
  lean_object* fork;
  lean_object* receipt;
  if (!parse_fork_and_bytes(args, "receipt", &fork, &receipt)) return NULL;
  return except_into_pybytes(eth_receipt_reencode(fork, receipt), BLOCK_ERROR);
}

PyObject*
py_receipt_logs_bloom(
  PyObject* self,
  PyObject* args
) {
  lean_object* fork;
  lean_object* receipt;
  if (!parse_fork_and_bytes(args, "receipt", &fork, &receipt)) return NULL;
  return except_into_pybytes(eth_receipt_logs_bloom(fork, receipt), BLOCK_ERROR);
}
