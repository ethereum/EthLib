/* Typed wrappers of RFC 7748 X25519. */
#include "wrappers.h"

extern lean_object* eth_x25519(lean_object* args);
extern lean_object* eth_x25519_public_key(lean_object* args);

PyObject*
py_x25519(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_x25519, args, 2, X25519_ERROR);
}

PyObject*
py_x25519_public_key(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_x25519_public_key, args, 1, X25519_ERROR);
}
