/* Era1 wrappers around the `eth_era1_*` Lean exports. */
#include "wrappers.h"

extern lean_object* eth_era1_decode(lean_object* args);

PyObject*
py_era1_decode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_era1_decode, args, 1, ERA1_ERROR);
}
