/* Req/resp encoding wrappers around the `eth_reqresp_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_reqresp_max_compressed_len(
  uint64_t n
);

extern lean_object*
eth_reqresp_max_payload_size(
  lean_object* fork
);

extern lean_object*
eth_reqresp_decode_payload(
  lean_object* fork,
  uint64_t type_bound,
  lean_object* data
);

extern lean_object*
eth_reqresp_decode_response_chunk(
  lean_object* fork,
  uint64_t context_bytes,
  uint64_t type_bound,
  lean_object* data
);

/* ---- Wrappers --------------------------------------------------------- */

/* The bytes of a `bytes` argument, or NULL with a TypeError set. */
static lean_object*
parse_data(
  PyObject* obj
) {
  if (!PyBytes_Check(obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  return mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj));
}

/* The UTF-8 bytes of a fork name, or NULL with a TypeError set. */
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

PyObject*
py_reqresp_max_payload_size(
  PyObject* self,
  PyObject* args
) {
  PyObject* fork_obj;
  if (!PyArg_ParseTuple(args, "O", &fork_obj)) return NULL;
  lean_object* fork = parse_fork(fork_obj);
  if (!fork) return NULL;
  return except_into_pyint(eth_reqresp_max_payload_size(fork), REQRESP_ERROR);
}

PyObject*
py_reqresp_max_compressed_len(
  PyObject* self,
  PyObject* args
) {
  PyObject* n_obj;
  if (!PyArg_ParseTuple(args, "O", &n_obj)) return NULL;
  uint64_t n;
  if (parse_uint64(n_obj, "n", &n)) return NULL;
  return except_into_pyint(eth_reqresp_max_compressed_len(n), REQRESP_ERROR);
}

PyObject*
py_reqresp_decode_payload(
  PyObject* self,
  PyObject* args
) {
  PyObject *fork_obj, *bound_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOO", &fork_obj, &bound_obj, &data_obj)) return NULL;
  uint64_t type_bound;
  if (parse_uint64(bound_obj, "type_bound", &type_bound)) return NULL;
  lean_object* data = parse_data(data_obj);
  if (!data) return NULL;
  lean_object* fork = parse_fork(fork_obj);
  if (!fork) { lean_dec(data); return NULL; }
  return except_into_pybytes(
    eth_reqresp_decode_payload(fork, type_bound, data), REQRESP_ERROR);
}

PyObject*
py_reqresp_decode_response_chunk(
  PyObject* self,
  PyObject* args
) {
  PyObject *fork_obj, *context_obj, *bound_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &fork_obj, &context_obj, &bound_obj, &data_obj)) {
    return NULL;
  }
  uint64_t context_bytes, type_bound;
  if (parse_uint64(context_obj, "context_bytes", &context_bytes)) return NULL;
  if (parse_uint64(bound_obj, "type_bound", &type_bound)) return NULL;
  lean_object* data = parse_data(data_obj);
  if (!data) return NULL;
  lean_object* fork = parse_fork(fork_obj);
  if (!fork) { lean_dec(data); return NULL; }
  return except_into_pybytes(
    eth_reqresp_decode_response_chunk(fork, context_bytes, type_bound, data), REQRESP_ERROR);
}
