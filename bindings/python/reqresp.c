/* Req/resp encoding wrappers around the `eth_reqresp_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_reqresp_max_compressed_len(
  uint64_t n
);

extern lean_object*
eth_reqresp_decode_payload(
  uint64_t type_min,
  uint64_t type_bound,
  lean_object* data
);

extern lean_object*
eth_reqresp_decode_response_chunk(
  uint64_t context_bytes,
  uint64_t type_min,
  uint64_t type_bound,
  lean_object* data
);

extern lean_object*
eth_reqresp_encode_payload(
  lean_object* data
);

extern lean_object*
eth_reqresp_encode_response_chunk(
  uint8_t code,
  lean_object* context,
  lean_object* payload
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
  PyObject *min_obj, *bound_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOO", &min_obj, &bound_obj, &data_obj)) return NULL;
  uint64_t type_min, type_bound;
  if (parse_uint64(min_obj, "type_min", &type_min)) return NULL;
  if (parse_uint64(bound_obj, "type_bound", &type_bound)) return NULL;
  lean_object* data = parse_data(data_obj);
  if (!data) return NULL;
  return except_into_pybytes(
    eth_reqresp_decode_payload(type_min, type_bound, data), REQRESP_ERROR);
}

PyObject*
py_reqresp_decode_response_chunk(
  PyObject* self,
  PyObject* args
) {
  PyObject *context_obj, *min_obj, *bound_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &context_obj, &min_obj, &bound_obj, &data_obj)) return NULL;
  uint64_t context_bytes, type_min, type_bound;
  if (parse_uint64(context_obj, "context_bytes", &context_bytes)) return NULL;
  if (parse_uint64(min_obj, "type_min", &type_min)) return NULL;
  if (parse_uint64(bound_obj, "type_bound", &type_bound)) return NULL;
  lean_object* data = parse_data(data_obj);
  if (!data) return NULL;
  return except_into_pybytes(
    eth_reqresp_decode_response_chunk(context_bytes, type_min, type_bound, data), REQRESP_ERROR);
}

PyObject*
py_reqresp_encode_payload(
  PyObject* self,
  PyObject* args
) {
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "O", &data_obj)) return NULL;
  lean_object* data = parse_data(data_obj);
  if (!data) return NULL;
  return except_into_pybytes(eth_reqresp_encode_payload(data), REQRESP_ERROR);
}

PyObject*
py_reqresp_encode_response_chunk(
  PyObject* self,
  PyObject* args
) {
  PyObject *code_obj, *context_obj, *payload_obj;
  if (!PyArg_ParseTuple(args, "OOO", &code_obj, &context_obj, &payload_obj)) return NULL;
  if (!PyLong_Check(code_obj)) {
    PyErr_SetString(PyExc_TypeError, "code must be int");
    return NULL;
  }
  int overflow;
  long code = PyLong_AsLongAndOverflow(code_obj, &overflow);
  if (code == -1 && PyErr_Occurred()) return NULL;
  if (overflow || code < 0 || code > 255) {
    PyErr_SetString(PyExc_OverflowError, "code must be in [0, 256)");
    return NULL;
  }
  if (!PyBytes_Check(context_obj) || !PyBytes_Check(payload_obj)) {
    PyErr_SetString(PyExc_TypeError, "context and payload must be bytes");
    return NULL;
  }
  lean_object* context = parse_data(context_obj);
  if (!context) return NULL;
  lean_object* payload = parse_data(payload_obj);
  if (!payload) {
    lean_dec(context);
    return NULL;
  }
  return except_into_pybytes(
    eth_reqresp_encode_response_chunk((uint8_t) code, context, payload), REQRESP_ERROR);
}
