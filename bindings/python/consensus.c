/* Consensus-layer wrappers around the `eth_consensus_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_consensus_preset(
  lean_object* name
);

extern lean_object*
eth_consensus_config(
  lean_object* name
);

extern lean_object*
eth_consensus_parameters(
  lean_object* name,
  lean_object* fork
);

extern lean_object*
eth_consensus_get_custody_groups(
  lean_object* name,
  lean_object* node_id,
  uint64_t count
);

extern lean_object*
eth_consensus_compute_columns_for_custody_group(
  lean_object* name,
  uint64_t group
);

/* ---- Wrappers --------------------------------------------------------- */

/* The UTF-8 bytes of a `str` argument, or NULL with a TypeError set. */
static lean_object*
str_arg(
  PyObject* obj,
  const char* name
) {
  if (!PyUnicode_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be str", name);
    return NULL;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(obj, &len);
  if (!utf8) return NULL;
  return mk_bytearray((const uint8_t*) utf8, len);
}

PyObject*
py_consensus_preset(
  PyObject* self,
  PyObject* args
) {
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "O", &obj)) return NULL;
  lean_object* name = str_arg(obj, "name");
  if (!name) return NULL;
  return except_into_pybytes(eth_consensus_preset(name), CONSENSUS_ERROR);
}

PyObject*
py_consensus_config(
  PyObject* self,
  PyObject* args
) {
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "O", &obj)) return NULL;
  lean_object* name = str_arg(obj, "name");
  if (!name) return NULL;
  return except_into_pybytes(eth_consensus_config(name), CONSENSUS_ERROR);
}

PyObject*
py_consensus_parameters(
  PyObject* self,
  PyObject* args
) {
  PyObject* name_obj;
  PyObject* fork_obj;
  if (!PyArg_ParseTuple(args, "OO", &name_obj, &fork_obj)) return NULL;
  lean_object* name = str_arg(name_obj, "preset");
  if (!name) return NULL;
  lean_object* fork = str_arg(fork_obj, "fork");
  if (!fork) {
    lean_dec(name);
    return NULL;
  }
  return except_into_pybytes(eth_consensus_parameters(name, fork), CONSENSUS_ERROR);
}

PyObject*
py_consensus_get_custody_groups(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *count_obj;
  const uint8_t* node_id;
  Py_ssize_t node_id_len;
  if (!PyArg_ParseTuple(args, "Oy#O", &name_obj, &node_id, &node_id_len, &count_obj)) return NULL;
  /* A count outside [0, 2^64) raises OverflowError. */
  unsigned long long count = PyLong_AsUnsignedLongLong(count_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  lean_object* id = mk_bytearray(node_id, node_id_len);
  return except_into_pybytes(
    eth_consensus_get_custody_groups(name, id, (uint64_t) count), CONSENSUS_ERROR);
}

PyObject*
py_consensus_compute_columns_for_custody_group(
  PyObject* self,
  PyObject* args
) {
  PyObject *name_obj, *group_obj;
  if (!PyArg_ParseTuple(args, "OO", &name_obj, &group_obj)) return NULL;
  /* A group outside [0, 2^64) raises OverflowError. */
  unsigned long long group = PyLong_AsUnsignedLongLong(group_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object* name = str_arg(name_obj, "name");
  if (!name) return NULL;
  return except_into_pybytes(
    eth_consensus_compute_columns_for_custody_group(name, (uint64_t) group), CONSENSUS_ERROR);
}
