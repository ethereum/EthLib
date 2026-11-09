/* Python wrappers of the Engine API exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_engine_new_payload(
  lean_object* args
);

extern lean_object*
eth_engine_new_payload_on_chain(
  lean_object* args
);

extern lean_object*
eth_engine_forkchoice_updated(
  lean_object* args
);

extern lean_object* eth_engine_jwt_build(lean_object* args);
extern lean_object* eth_engine_jwt_check(lean_object* args);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_engine_new_payload(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_new_payload, args, 2, ENGINE_ERROR);
}

PyObject*
py_engine_forkchoice_updated(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_forkchoice_updated, args, 3, ENGINE_ERROR);
}

PyObject*
py_engine_new_payload_on_chain(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_new_payload_on_chain, args, 4, ENGINE_ERROR);
}

PyObject*
py_engine_jwt_build(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_jwt_build, args, 2, JWT_ERROR);
}

PyObject*
py_engine_jwt_check(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_jwt_check, args, 3, JWT_ERROR);
}
