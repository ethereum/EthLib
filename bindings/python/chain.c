/* Python wrappers of the exports of the active fork of mainnet, of Hoodi and of a configured chain. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_mainnet_active_fork(
  lean_object* args
);

extern lean_object*
eth_hoodi_active_fork(
  lean_object* args
);

extern lean_object*
eth_active_fork(
  lean_object* args
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_mainnet_active_fork(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_mainnet_active_fork, args, 2, CHAIN_ERROR);
}

PyObject*
py_hoodi_active_fork(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_hoodi_active_fork, args, 2, CHAIN_ERROR);
}

PyObject*
py_active_fork(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_active_fork, args, 3, CHAIN_ERROR);
}
