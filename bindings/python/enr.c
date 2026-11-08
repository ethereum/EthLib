/* Ethereum Node Record wrappers around the `eth_enr_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_enr_from_text(
  lean_object* text
);

extern lean_object*
eth_enr_seq(
  lean_object* record
);

extern lean_object*
eth_enr_verify_v4(
  lean_object* record
);

extern lean_object*
eth_enr_node_id(
  lean_object* record
);

extern lean_object*
eth_enr_sign_v4(
  lean_object* secret_key,
  lean_object* record
);

extern lean_object*
eth_enr_make_record_v4(
  lean_object* secret_key,
  uint64_t seq,
  lean_object* pairs
);

extern lean_object*
eth_enr_consensus_entries(
  lean_object* args
);

extern lean_object*
eth_enr_eth_fork_id(
  lean_object* args
);

/* ---- Wrappers --------------------------------------------------------- */

/* The bytes of a `bytes` argument, or NULL with a TypeError set. */
static lean_object*
parse_record_arg(
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
py_enr_from_text(
  PyObject* self,
  PyObject* args
) {
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "O", &obj)) return NULL;
  if (!PyUnicode_Check(obj)) {
    PyErr_SetString(PyExc_TypeError, "text must be str");
    return NULL;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(obj, &len);
  if (!utf8) return NULL;
  /* Python gives valid UTF-8, which the export reads as a Lean string. */
  lean_object* res = eth_enr_from_text(lean_mk_string_from_bytes(utf8, (size_t) len));
  return except_into_pybytes(res, ENR_ERROR);
}

PyObject*
py_enr_seq(
  PyObject* self,
  PyObject* args
) {
  lean_object* record = parse_record_arg(args, "record");
  if (!record) return NULL;
  return except_into_pyint(eth_enr_seq(record), ENR_ERROR);
}

PyObject*
py_enr_verify_v4(
  PyObject* self,
  PyObject* args
) {
  lean_object* record = parse_record_arg(args, "record");
  if (!record) return NULL;
  return except_into_pybool(eth_enr_verify_v4(record), ENR_ERROR);
}

PyObject*
py_enr_node_id(
  PyObject* self,
  PyObject* args
) {
  lean_object* record = parse_record_arg(args, "record");
  if (!record) return NULL;
  return except_into_pybytes(eth_enr_node_id(record), ENR_ERROR);
}

PyObject*
py_enr_sign_v4(
  PyObject* self,
  PyObject* args
) {
  PyObject* key;
  PyObject* record;
  if (!PyArg_ParseTuple(args, "OO", &key, &record)) return NULL;
  if (!PyBytes_Check(key)) {
    PyErr_SetString(PyExc_TypeError, "secret_key must be bytes");
    return NULL;
  }
  if (!PyBytes_Check(record)) {
    PyErr_SetString(PyExc_TypeError, "record must be bytes");
    return NULL;
  }
  lean_object* res = eth_enr_sign_v4(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(key), PyBytes_GET_SIZE(key)),
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(record), PyBytes_GET_SIZE(record)));
  return except_into_pybytes(res, ENR_ERROR);
}

PyObject*
py_enr_make_record_v4(
  PyObject* self,
  PyObject* args
) {
  PyObject *key_obj, *seq_obj, *pairs_obj;
  if (!PyArg_ParseTuple(args, "OOO", &key_obj, &seq_obj, &pairs_obj)) return NULL;
  uint64_t seq;
  if (parse_uint64(seq_obj, "seq", &seq)) return NULL;
  if (!PyBytes_Check(key_obj)) {
    PyErr_SetString(PyExc_TypeError, "secret_key must be bytes");
    return NULL;
  }
  if (!PyBytes_Check(pairs_obj)) {
    PyErr_SetString(PyExc_TypeError, "pairs must be bytes");
    return NULL;
  }
  lean_object* key = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(key_obj), PyBytes_GET_SIZE(key_obj));
  lean_object* pairs = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(pairs_obj), PyBytes_GET_SIZE(pairs_obj));
  return except_into_pybytes(eth_enr_make_record_v4(key, seq, pairs), ENR_ERROR);
}

PyObject*
py_enr_consensus_entries(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_enr_consensus_entries, args, 3, ENR_ERROR);
}

PyObject*
py_enr_eth_fork_id(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_enr_eth_fork_id, args, 1, ENR_ERROR);
}
