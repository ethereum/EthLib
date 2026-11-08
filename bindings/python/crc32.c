/* Python wrappers of the CRC-32 exports.
 *
 * They take and return typed values, which the generic converter passes. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_crc32(
  lean_object* args
);

extern lean_object*
eth_crc32_number(
  lean_object* args
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_crc32(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_crc32, args, 1, BINDING_ERROR);
}

PyObject*
py_crc32_number(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_crc32_number, args, 1, BINDING_ERROR);
}
