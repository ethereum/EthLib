/* eth capability wrappers around the `eth_*` Lean exports of the eth messages. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_message_decode(
  uint64_t version,
  uint64_t id,
  lean_object* data
);

extern lean_object*
eth_check_status(
  uint64_t version,
  lean_object* schedule,
  uint64_t number,
  uint64_t timestamp,
  lean_object* data
);

extern lean_object*
eth_check_headers(
  uint64_t version,
  lean_object* request,
  lean_object* response
);

extern lean_object*
eth_check_pooled(
  uint64_t version,
  lean_object* request,
  lean_object* response
);

extern lean_object*
eth_wire_hash(
  lean_object* tx
);

extern lean_object*
eth_receipts_match(
  uint64_t version,
  lean_object* fork,
  lean_object* root,
  lean_object* receipts
);

extern lean_object*
eth_access_lists_answer(
  uint64_t version,
  lean_object* request,
  lean_object* response,
  lean_object* expected
);

/* ---- Wrappers --------------------------------------------------------- */

/* Copy the Python `bytes` object `obj` into a Lean `ByteArray`, or set a TypeError naming it. */
static int
parse_bytes(
  PyObject* obj,
  const char* name,
  lean_object** out
) {
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", name);
    return 1;
  }
  *out = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), (size_t) PyBytes_GET_SIZE(obj));
  return 0;
}

PyObject*
py_eth_message_decode(
  PyObject* self,
  PyObject* args
) {
  PyObject *version_obj, *id_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOO", &version_obj, &id_obj, &data_obj)) return NULL;
  uint64_t version, id;
  if (parse_uint64(version_obj, "version", &version)) return NULL;
  if (parse_uint64(id_obj, "id", &id)) return NULL;
  lean_object* data;
  if (parse_bytes(data_obj, "data", &data)) return NULL;
  return except_into_pybytes(eth_message_decode(version, id, data), ETH_WIRE_ERROR);
}

PyObject*
py_eth_check_status(
  PyObject* self,
  PyObject* args
) {
  PyObject *version_obj, *schedule_obj, *number_obj, *timestamp_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOOOO", &version_obj, &schedule_obj, &number_obj, &timestamp_obj,
      &data_obj))
    return NULL;
  uint64_t version, number, timestamp;
  if (parse_uint64(version_obj, "version", &version)) return NULL;
  if (parse_uint64(number_obj, "number", &number)) return NULL;
  if (parse_uint64(timestamp_obj, "timestamp", &timestamp)) return NULL;
  lean_object *schedule, *data;
  if (parse_bytes(schedule_obj, "schedule", &schedule)) return NULL;
  if (parse_bytes(data_obj, "data", &data)) { lean_dec(schedule); return NULL; }
  return except_into_pybool(
    eth_check_status(version, schedule, number, timestamp, data), ETH_WIRE_ERROR);
}

PyObject*
py_eth_check_headers(
  PyObject* self,
  PyObject* args
) {
  PyObject *version_obj, *request_obj, *response_obj;
  if (!PyArg_ParseTuple(args, "OOO", &version_obj, &request_obj, &response_obj)) return NULL;
  uint64_t version;
  if (parse_uint64(version_obj, "version", &version)) return NULL;
  lean_object *request, *response;
  if (parse_bytes(request_obj, "request", &request)) return NULL;
  if (parse_bytes(response_obj, "response", &response)) { lean_dec(request); return NULL; }
  return except_into_pybool(eth_check_headers(version, request, response), ETH_WIRE_ERROR);
}

PyObject*
py_eth_check_pooled(
  PyObject* self,
  PyObject* args
) {
  PyObject *version_obj, *request_obj, *response_obj;
  if (!PyArg_ParseTuple(args, "OOO", &version_obj, &request_obj, &response_obj)) return NULL;
  uint64_t version;
  if (parse_uint64(version_obj, "version", &version)) return NULL;
  lean_object *request, *response;
  if (parse_bytes(request_obj, "request", &request)) return NULL;
  if (parse_bytes(response_obj, "response", &response)) { lean_dec(request); return NULL; }
  return except_into_pybool(eth_check_pooled(version, request, response), ETH_WIRE_ERROR);
}

PyObject*
py_eth_wire_hash(
  PyObject* self,
  PyObject* args
) {
  PyObject* tx_obj;
  if (!PyArg_ParseTuple(args, "O", &tx_obj)) return NULL;
  lean_object* tx;
  if (parse_bytes(tx_obj, "tx", &tx)) return NULL;
  return except_into_pybytes(eth_wire_hash(tx), ETH_WIRE_ERROR);
}

PyObject*
py_eth_receipts_match(
  PyObject* self,
  PyObject* args
) {
  PyObject *version_obj, *fork_obj, *root_obj, *receipts_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &version_obj, &fork_obj, &root_obj, &receipts_obj))
    return NULL;
  uint64_t version;
  if (parse_uint64(version_obj, "version", &version)) return NULL;
  if (!PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "fork must be str");
    return NULL;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &len);
  if (!utf8) return NULL;
  lean_object *root, *receipts;
  if (parse_bytes(root_obj, "receipts_root", &root)) return NULL;
  if (parse_bytes(receipts_obj, "receipts", &receipts)) { lean_dec(root); return NULL; }
  lean_object* fork = mk_bytearray((const uint8_t*) utf8, (size_t) len);
  return except_into_pybool(
    eth_receipts_match(version, fork, root, receipts), ETH_WIRE_ERROR);
}

PyObject*
py_eth_access_lists_answer(
  PyObject* self,
  PyObject* args
) {
  PyObject *version_obj, *request_obj, *response_obj, *expected_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &version_obj, &request_obj, &response_obj, &expected_obj))
    return NULL;
  uint64_t version;
  if (parse_uint64(version_obj, "version", &version)) return NULL;
  Py_ssize_t n;
  uint8_t* hashes = pack_bytes_sequence(expected_obj, 32, &n, "access list hash");
  if (!hashes) return NULL;
  lean_object *request, *response;
  if (parse_bytes(request_obj, "request", &request)) { PyMem_Free(hashes); return NULL; }
  if (parse_bytes(response_obj, "response", &response)) {
    lean_dec(request);
    PyMem_Free(hashes);
    return NULL;
  }
  lean_object* expected = mk_bytearray_array(hashes, n, 32);
  PyMem_Free(hashes);
  return except_into_pybool(
    eth_access_lists_answer(version, request, response, expected), ETH_WIRE_ERROR);
}
