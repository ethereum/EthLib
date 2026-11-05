/* Python wrappers of the Engine API exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_engine_new_payload(
  lean_object* config,
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
