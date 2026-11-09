/* Typed wrappers of RFC 7748 X25519 and RFC 8439 ChaCha20-Poly1305. */
#include "wrappers.h"

extern lean_object* eth_x25519(lean_object* args);
extern lean_object* eth_x25519_public_key(lean_object* args);
extern lean_object* eth_chacha20_quarter_round(lean_object* args);
extern lean_object* eth_chacha20_quarter_round_state(lean_object* args);
extern lean_object* eth_chacha20_block(lean_object* args);
extern lean_object* eth_chacha20_crypt(lean_object* args);
extern lean_object* eth_poly1305(lean_object* args);
extern lean_object* eth_poly1305_key(lean_object* args);
extern lean_object* eth_chacha20_poly1305_encrypt(lean_object* args);
extern lean_object* eth_chacha20_poly1305_decrypt(lean_object* args);

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

PyObject*
py_chacha20_quarter_round(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_chacha20_quarter_round, args, 4, CHACHAPOLY_ERROR);
}

PyObject*
py_chacha20_quarter_round_state(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_chacha20_quarter_round_state, args, 5, CHACHAPOLY_ERROR);
}

PyObject*
py_chacha20_block(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_chacha20_block, args, 3, CHACHAPOLY_ERROR);
}

PyObject*
py_chacha20_crypt(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_chacha20_crypt, args, 4, CHACHAPOLY_ERROR);
}

PyObject*
py_poly1305(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_poly1305, args, 2, CHACHAPOLY_ERROR);
}

PyObject*
py_poly1305_key(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_poly1305_key, args, 2, CHACHAPOLY_ERROR);
}

PyObject*
py_chacha20_poly1305_encrypt(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_chacha20_poly1305_encrypt, args, 4, CHACHAPOLY_ERROR);
}

PyObject*
py_chacha20_poly1305_decrypt(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_chacha20_poly1305_decrypt, args, 5, CHACHAPOLY_ERROR);
}
