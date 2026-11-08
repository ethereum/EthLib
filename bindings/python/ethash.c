/* Python wrappers of the Ethash exports.
 *
 * Their arguments and results are typed values, which the generic converter passes. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export takes the tuple of the arguments as one value, and consumes it. */

extern lean_object* eth_ethash_cache_size(lean_object*);
extern lean_object* eth_ethash_dataset_size(lean_object*);
extern lean_object* eth_ethash_seed(lean_object*);
extern lean_object* eth_ethash_cache(lean_object*);
extern lean_object* eth_ethash_dataset_item(lean_object*);
extern lean_object* eth_ethash_hashimoto_light(lean_object*);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_ethash_cache_size(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ethash_cache_size, args, 1, ETHASH_ERROR);
}

PyObject*
py_ethash_dataset_size(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ethash_dataset_size, args, 1, ETHASH_ERROR);
}

PyObject*
py_ethash_seed(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ethash_seed, args, 1, ETHASH_ERROR);
}

PyObject*
py_ethash_cache(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ethash_cache, args, 1, ETHASH_ERROR);
}

PyObject*
py_ethash_dataset_item(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ethash_dataset_item, args, 2, ETHASH_ERROR);
}

PyObject*
py_ethash_hashimoto_light(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ethash_hashimoto_light, args, 4, ETHASH_ERROR);
}
