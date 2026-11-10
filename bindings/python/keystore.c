/* Python wrappers of the ERC-2335 keystore exports. */
#include "wrappers.h"

extern lean_object* eth_keystore_nfkd(lean_object* args);
extern lean_object* eth_keystore_password(lean_object* args);
extern lean_object* eth_keystore_decrypt(lean_object* args);

PyObject*
py_keystore_nfkd(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_keystore_nfkd, args, 1, KEYSTORE_ERROR);
}

PyObject*
py_keystore_password(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_keystore_password, args, 1, KEYSTORE_ERROR);
}

PyObject*
py_keystore_decrypt(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_keystore_decrypt, args, 4, KEYSTORE_ERROR);
}
