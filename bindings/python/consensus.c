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
