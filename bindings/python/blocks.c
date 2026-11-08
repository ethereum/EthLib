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
eth_block_transactions_root(
  lean_object* fork,
  lean_object* block
);

extern lean_object*
eth_block_withdrawals_root(
  lean_object* fork,
  lean_object* block
);

extern lean_object*
eth_block_deposit_requests(
  lean_object* logs
);

extern lean_object*
eth_block_requests_hash(
  lean_object* requests
);

extern lean_object*
eth_block_access_list_hash(
  lean_object* block_access_list
);

extern lean_object*
eth_block_access_list_check(
  lean_object* block_access_list,
  uint64_t gas_limit
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

extern lean_object*
eth_block_make_receipts(
  lean_object* fork,
  lean_object* results
);

extern lean_object*
eth_block_validate_size(
  lean_object* fork,
  lean_object* block
);

extern lean_object*
eth_state_transition(
  lean_object* config,
  lean_object* state,
  lean_object* recent,
  lean_object* fork,
  lean_object* block,
  uint8_t check_seal
);

extern lean_object*
eth_genesis_block(
  lean_object* args
);

extern lean_object*
eth_block_validate_header(
  lean_object* args
);

extern lean_object*
eth_block_check_header(
  lean_object* args
);

extern lean_object*
eth_block_dao_extra_data_valid(
  uint64_t dao_block,
  lean_object* fork,
  lean_object* header
);

/* ---- Wrappers --------------------------------------------------------- */

/* A fork name as a Lean byte array, or NULL with a TypeError set. */
static lean_object*
parse_fork(
  PyObject* obj
) {
  if (!PyUnicode_Check(obj)) {
    PyErr_SetString(PyExc_TypeError, "fork must be str");
    return NULL;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(obj, &len);
  if (!utf8) return NULL;
  return mk_bytearray((const uint8_t*) utf8, len);
}

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
py_block_transactions_root(
  PyObject* self,
  PyObject* args
) {
  lean_object* fork;
  lean_object* block;
  if (!parse_fork_and_bytes(args, "block", &fork, &block)) return NULL;
  return except_into_pybytes(eth_block_transactions_root(fork, block), BLOCK_ERROR);
}

PyObject*
py_block_withdrawals_root(
  PyObject* self,
  PyObject* args
) {
  lean_object* fork;
  lean_object* block;
  if (!parse_fork_and_bytes(args, "block", &fork, &block)) return NULL;
  return except_into_pybytes(eth_block_withdrawals_root(fork, block), BLOCK_ERROR);
}

/* Read one bytes argument as a Lean byte array, or NULL with a TypeError set. */
static lean_object*
parse_one_bytes(
  PyObject* args,
  const char* name
) {
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "O", &obj)) return NULL;
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", name);
    return NULL;
  }
  return mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj));
}

PyObject*
py_block_deposit_requests(
  PyObject* self,
  PyObject* args
) {
  lean_object* logs = parse_one_bytes(args, "logs");
  if (!logs) return NULL;
  return except_into_pybytes(eth_block_deposit_requests(logs), BLOCK_ERROR);
}

PyObject*
py_block_requests_hash(
  PyObject* self,
  PyObject* args
) {
  lean_object* requests = parse_one_bytes(args, "requests");
  if (!requests) return NULL;
  return except_into_pybytes(eth_block_requests_hash(requests), BLOCK_ERROR);
}

PyObject*
py_block_access_list_hash(
  PyObject* self,
  PyObject* args
) {
  lean_object* bal = parse_one_bytes(args, "block_access_list");
  if (!bal) return NULL;
  return except_into_pybytes(eth_block_access_list_hash(bal), BLOCK_ERROR);
}

PyObject*
py_block_access_list_check(
  PyObject* self,
  PyObject* args
) {
  PyObject *bal_obj, *gas_obj;
  if (!PyArg_ParseTuple(args, "OO", &bal_obj, &gas_obj)) return NULL;
  if (!PyBytes_Check(bal_obj)) {
    PyErr_SetString(PyExc_TypeError, "block_access_list must be bytes");
    return NULL;
  }
  uint64_t gas_limit;
  if (parse_uint64(gas_obj, "gas_limit", &gas_limit)) return NULL;
  lean_object* bal =
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(bal_obj), PyBytes_GET_SIZE(bal_obj));
  return except_into_pybool(eth_block_access_list_check(bal, gas_limit), BLOCK_ERROR);
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

PyObject*
py_block_make_receipts(
  PyObject* self,
  PyObject* args
) {
  lean_object* fork;
  lean_object* results;
  if (!parse_fork_and_bytes(args, "results", &fork, &results)) return NULL;
  return except_into_pybytes(eth_block_make_receipts(fork, results), BLOCK_ERROR);
}

PyObject*
py_block_validate_size(
  PyObject* self,
  PyObject* args
) {
  lean_object* fork;
  lean_object* block;
  if (!parse_fork_and_bytes(args, "block", &fork, &block)) return NULL;
  return except_into_pybool(eth_block_validate_size(fork, block), BLOCK_ERROR);
}

PyObject*
py_block_validate_header(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_block_validate_header, args, 5, BLOCK_ERROR);
}

PyObject*
py_block_check_header(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_block_check_header, args, 5, BLOCK_ERROR);
}

PyObject*
py_block_dao_extra_data_valid(
  PyObject* self,
  PyObject* args
) {
  PyObject *dao_block_obj, *fork_obj, *header_obj;
  if (!PyArg_ParseTuple(args, "OOO", &dao_block_obj, &fork_obj, &header_obj)) return NULL;
  uint64_t dao_block;
  if (parse_uint64(dao_block_obj, "dao_block", &dao_block)) return NULL;
  if (!PyBytes_Check(header_obj)) {
    PyErr_SetString(PyExc_TypeError, "header must be bytes");
    return NULL;
  }
  lean_object* fork = parse_fork(fork_obj);
  if (!fork) return NULL;
  lean_object* header =
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(header_obj), PyBytes_GET_SIZE(header_obj));
  return except_into_pybool(eth_block_dao_extra_data_valid(dao_block, fork, header), BLOCK_ERROR);
}

PyObject*
py_state_transition(
  PyObject* self,
  PyObject* args
) {
  const char *config, *state, *recent, *block;
  Py_ssize_t config_len, state_len, recent_len, block_len;
  PyObject* fork_obj;
  int check_seal;
  if (!PyArg_ParseTuple(args, "y#y#y#Oy#p", &config, &config_len, &state, &state_len, &recent,
                        &recent_len, &fork_obj, &block, &block_len, &check_seal)) {
    return NULL;
  }
  lean_object* fork = parse_fork(fork_obj);
  if (!fork) return NULL;
  return except_into_pybytes(
    eth_state_transition(
      mk_bytearray((const uint8_t*) config, (size_t) config_len),
      mk_bytearray((const uint8_t*) state, (size_t) state_len),
      mk_bytearray((const uint8_t*) recent, (size_t) recent_len), fork,
      mk_bytearray((const uint8_t*) block, (size_t) block_len), (uint8_t) check_seal),
    BLOCK_ERROR);
}

PyObject*
py_genesis_block(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_genesis_block, args, 3, BLOCK_ERROR);
}
