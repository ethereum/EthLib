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
eth_engine_build_payload(
  lean_object* args
);

extern lean_object*
eth_engine_forkchoice_updated(
  lean_object* args
);

extern lean_object*
eth_engine_get_blobs(
  lean_object* args
);

extern lean_object*
eth_engine_get_payload_bodies(
  lean_object* args
);

extern lean_object* eth_engine_jwt_build(lean_object* args);
extern lean_object* eth_engine_jwt_check(lean_object* args);

extern lean_object* eth_engine_get_payload(lean_object* args);
extern lean_object* eth_engine_rewrite_params(lean_object* args);
extern lean_object* eth_engine_read_payload_status(lean_object* args);
extern lean_object* eth_engine_read_forkchoice_response(lean_object* args);
extern lean_object* eth_engine_read_get_payload_result(lean_object* args);
extern lean_object* eth_engine_read_payload_bodies_result(lean_object* args);
extern lean_object* eth_engine_read_get_blobs_result(lean_object* args);
extern lean_object* eth_engine_exchange_transition_configuration(lean_object* args);
extern lean_object* eth_engine_exchange_capabilities(lean_object* args);
extern lean_object* eth_engine_get_client_version(lean_object* args);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_engine_new_payload(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_new_payload, args, 2, ENGINE_ERROR);
}

PyObject*
py_engine_build_payload(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_build_payload, args, 9, ENGINE_ERROR);
}

PyObject*
py_engine_forkchoice_updated(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_forkchoice_updated, args, 5, ENGINE_ERROR);
}

PyObject*
py_engine_get_blobs(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_get_blobs, args, 5, ENGINE_ERROR);
}

PyObject*
py_engine_get_payload_bodies(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_get_payload_bodies, args, 4, ENGINE_ERROR);
}

PyObject*
py_engine_new_payload_on_chain(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_new_payload_on_chain, args, 6, ENGINE_ERROR);
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

PyObject*
py_engine_get_payload(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_get_payload, args, 3, ENGINE_ERROR);
}

PyObject*
py_engine_rewrite_params(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_rewrite_params, args, 2, ENGINE_ERROR);
}

PyObject*
py_engine_read_payload_status(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_read_payload_status, args, 1, ENGINE_ERROR);
}

PyObject*
py_engine_read_forkchoice_response(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_read_forkchoice_response, args, 1, ENGINE_ERROR);
}

PyObject*
py_engine_read_get_payload_result(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_read_get_payload_result, args, 3, ENGINE_ERROR);
}

PyObject*
py_engine_read_payload_bodies_result(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_read_payload_bodies_result, args, 2, ENGINE_ERROR);
}

PyObject*
py_engine_read_get_blobs_result(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_read_get_blobs_result, args, 2, ENGINE_ERROR);
}

PyObject*
py_engine_exchange_transition_configuration(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_exchange_transition_configuration, args, 4, ENGINE_ERROR);
}

PyObject*
py_engine_exchange_capabilities(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_exchange_capabilities, args, 1, ENGINE_ERROR);
}

PyObject*
py_engine_get_client_version(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_engine_get_client_version, args, 5, ENGINE_ERROR);
}
