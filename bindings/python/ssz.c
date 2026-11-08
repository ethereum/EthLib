/* SSZ wrappers around the `eth_ssz_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export takes the tuple of its arguments as one typed value. */

extern lean_object*
eth_ssz_serialize(
  lean_object* args
);

extern lean_object*
eth_ssz_deserialize(
  lean_object* args
);

extern lean_object*
eth_ssz_hash_tree_root(
  lean_object* args
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_ssz_serialize(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ssz_serialize, args, 2, SSZ_ERROR);
}

PyObject*
py_ssz_deserialize(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ssz_deserialize, args, 2, SSZ_ERROR);
}

PyObject*
py_ssz_hash_tree_root(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ssz_hash_tree_root, args, 2, SSZ_ERROR);
}
