/* snap capability wrappers around the `eth_snap_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_snap_message_decode(
  uint64_t version,
  uint64_t id,
  lean_object* data
);

extern lean_object*
eth_snap_codes_answer(
  uint64_t version,
  lean_object* request,
  lean_object* response
);

extern lean_object*
eth_snap_access_lists_answer(
  lean_object* request,
  lean_object* response,
  lean_object* expected
);

extern lean_object*
eth_snap_full_account(
  lean_object* slim
);

extern lean_object*
eth_snap_verify_account_range(
  lean_object* args
);

extern lean_object*
eth_snap_verify_storage_ranges(
  lean_object* args
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
py_snap_message_decode(
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
  return except_into_pybytes(eth_snap_message_decode(version, id, data), SNAP_ERROR);
}

PyObject*
py_snap_codes_answer(
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
  return except_into_pybool(eth_snap_codes_answer(version, request, response), SNAP_ERROR);
}

PyObject*
py_snap_access_lists_answer(
  PyObject* self,
  PyObject* args
) {
  PyObject *request_obj, *response_obj, *expected_obj;
  if (!PyArg_ParseTuple(args, "OOO", &request_obj, &response_obj, &expected_obj)) return NULL;
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
    eth_snap_access_lists_answer(request, response, expected), SNAP_ERROR);
}

PyObject*
py_snap_full_account(
  PyObject* self,
  PyObject* args
) {
  PyObject* slim_obj;
  if (!PyArg_ParseTuple(args, "O", &slim_obj)) return NULL;
  lean_object* slim;
  if (parse_bytes(slim_obj, "slim", &slim)) return NULL;
  return except_into_pybytes(eth_snap_full_account(slim), SNAP_ERROR);
}

PyObject*
py_snap_verify_account_range(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_snap_verify_account_range, args, 4, SNAP_ERROR);
}

PyObject*
py_snap_verify_storage_ranges(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_snap_verify_storage_ranges, args, 4, SNAP_ERROR);
}
