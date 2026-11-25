/* Python wrappers of the exports of chain configurations: active forks and blob schedules. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_chain_config(
  lean_object* args
);

extern lean_object*
eth_active_fork(
  lean_object* args
);

extern lean_object*
eth_execution_blob_schedule(
  lean_object* args
);

extern lean_object*
eth_write_execution_config(
  lean_object* args
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_chain_config(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_chain_config, args, 1, CHAIN_ERROR);
}

PyObject*
py_active_fork(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_active_fork, args, 3, CHAIN_ERROR);
}

PyObject*
py_execution_blob_schedule(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_execution_blob_schedule, args, 4, CHAIN_ERROR);
}

PyObject*
py_write_execution_config(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_write_execution_config, args, 1, CHAIN_ERROR);
}
