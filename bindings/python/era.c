/* Era wrappers around the `eth_era_*` Lean exports. */
#include "wrappers.h"

extern lean_object* eth_era_decode(lean_object* args);

PyObject*
py_era_decode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_era_decode, args, 3, ERA_ERROR);
}
