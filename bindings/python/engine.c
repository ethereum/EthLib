/* Python wrappers of the Engine API exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_engine_new_payload(
  lean_object* config,
  lean_object* request
);

extern lean_object*
eth_engine_new_payload_on_chain(
  lean_object* config,
  lean_object* state,
  lean_object* recent,
  lean_object* request
);

extern lean_object*
eth_engine_forkchoice_updated(
  lean_object* tree,
  lean_object* finalized,
  lean_object* request
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_engine_new_payload(
  PyObject* self,
  PyObject* args
) {
  PyObject *config, *request;
  if (!PyArg_ParseTuple(args, "OO", &config, &request)) return NULL;
  /* Both arguments are JSON text in UTF-8, as bytes. */
  if (!PyBytes_Check(config) || !PyBytes_Check(request)) {
    PyErr_SetString(PyExc_TypeError, "config and request must be bytes");
    return NULL;
  }
  lean_object* config_obj =
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(config), PyBytes_GET_SIZE(config));
  lean_object* request_obj =
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(request), PyBytes_GET_SIZE(request));
  return except_into_pybytes(eth_engine_new_payload(config_obj, request_obj), ENGINE_ERROR);
}

PyObject*
py_engine_forkchoice_updated(
  PyObject* self,
  PyObject* args
) {
  PyObject *tree, *finalized, *request;
  if (!PyArg_ParseTuple(args, "OOO", &tree, &finalized, &request)) return NULL;
  /* The three arguments are JSON text in UTF-8, as bytes. */
  if (!PyBytes_Check(tree) || !PyBytes_Check(finalized) || !PyBytes_Check(request)) {
    PyErr_SetString(PyExc_TypeError, "tree, finalized and request must be bytes");
    return NULL;
  }
  lean_object* tree_obj =
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(tree), PyBytes_GET_SIZE(tree));
  lean_object* finalized_obj =
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(finalized), PyBytes_GET_SIZE(finalized));
  lean_object* request_obj =
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(request), PyBytes_GET_SIZE(request));
  return except_into_pybytes(
    eth_engine_forkchoice_updated(tree_obj, finalized_obj, request_obj), ENGINE_ERROR);
}

PyObject*
py_engine_new_payload_on_chain(
  PyObject* self,
  PyObject* args
) {
  const char *config, *state, *recent, *request;
  Py_ssize_t config_len, state_len, recent_len, request_len;
  if (!PyArg_ParseTuple(args, "y#y#y#y#", &config, &config_len, &state, &state_len, &recent,
                        &recent_len, &request, &request_len)) {
    return NULL;
  }
  return except_into_pybytes(
    eth_engine_new_payload_on_chain(
      mk_bytearray((const uint8_t*) config, (size_t) config_len),
      mk_bytearray((const uint8_t*) state, (size_t) state_len),
      mk_bytearray((const uint8_t*) recent, (size_t) recent_len),
      mk_bytearray((const uint8_t*) request, (size_t) request_len)),
    ENGINE_ERROR);
}
