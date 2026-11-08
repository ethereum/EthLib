/* Python wrappers of the CRC-32C exports.
 *
 * They take and return typed values, which the generic converter passes. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_crc32c(
  lean_object* args
);

extern lean_object*
eth_crc32c_number(
  lean_object* args
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_crc32c(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_crc32c, args, 1, BINDING_ERROR);
}

PyObject*
py_crc32c_number(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_crc32c_number, args, 1, BINDING_ERROR);
}
