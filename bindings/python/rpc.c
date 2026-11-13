/* Python wrappers of the parameter readers and the error codes of the execution JSON-RPC API. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_rpc_read_param(
  lean_object* args
);

extern lean_object*
eth_rpc_error_groups(
  lean_object* args
);

extern lean_object*
eth_rpc_pruned_history_unavailable(
  lean_object* args
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_rpc_read_param(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_rpc_read_param, args, 2, RPC_ERROR);
}

PyObject*
py_rpc_error_groups(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_rpc_error_groups, args, 0, RPC_ERROR);
}

PyObject*
py_rpc_pruned_history_unavailable(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_rpc_pruned_history_unavailable, args, 0, RPC_ERROR);
}
