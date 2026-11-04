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
eth_enr_consensus_entries(
  lean_object* fork,
  lean_object* record
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
  lean_object* res = eth_enr_from_text(mk_bytearray((const uint8_t*) utf8, len));
  return run_io_into_pybytes(res, "enr from_text");
}

PyObject*
py_enr_seq(
  PyObject* self,
  PyObject* args
) {
  lean_object* record = parse_record_arg(args, "record");
  if (!record) return NULL;
  return run_io_into_pyint(eth_enr_seq(record), "enr seq");
}

PyObject*
py_enr_verify_v4(
  PyObject* self,
  PyObject* args
) {
  lean_object* record = parse_record_arg(args, "record");
  if (!record) return NULL;
  return run_io_into_pybool(eth_enr_verify_v4(record), "enr verify_v4");
}

PyObject*
py_enr_node_id(
  PyObject* self,
  PyObject* args
) {
  lean_object* record = parse_record_arg(args, "record");
  if (!record) return NULL;
  return run_io_into_pybytes(eth_enr_node_id(record), "enr node_id");
}

PyObject*
py_enr_consensus_entries(
  PyObject* self,
  PyObject* args
) {
  PyObject *fork_obj, *record_obj;
  if (!PyArg_ParseTuple(args, "OO", &fork_obj, &record_obj)) return NULL;
  if (!PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "fork must be str");
    return NULL;
  }
  if (!PyBytes_Check(record_obj)) {
    PyErr_SetString(PyExc_TypeError, "record must be bytes");
    return NULL;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &len);
  if (!utf8) return NULL;
  lean_object* fork = mk_bytearray((const uint8_t*) utf8, len);
  lean_object* record = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(record_obj), PyBytes_GET_SIZE(record_obj));
  return run_io_into_pybytes(eth_enr_consensus_entries(fork, record), "enr consensus_entries");
}
