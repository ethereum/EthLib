/* Typed wrappers of Noise XX and the libp2p identity profile. */
#include "wrappers.h"

extern lean_object* eth_noise_initialize(lean_object* args);
extern lean_object* eth_noise_write_message(lean_object* args);
extern lean_object* eth_noise_read_message(lean_object* args);
extern lean_object* eth_noise_transport(lean_object* args);
extern lean_object* eth_noise_cipher_encrypt(lean_object* args);
extern lean_object* eth_noise_cipher_decrypt(lean_object* args);
extern lean_object* eth_noise_frame(lean_object* args);
extern lean_object* eth_noise_unframe(lean_object* args);
extern lean_object* eth_noise_libp2p_initialize(lean_object* args);
extern lean_object* eth_noise_libp2p_write(lean_object* args);
extern lean_object* eth_noise_libp2p_read(lean_object* args);
extern lean_object* eth_noise_libp2p_complete(lean_object* args);

PyObject*
py_noise_initialize(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_initialize, args, 4, NOISE_ERROR);
}

PyObject*
py_noise_write_message(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_write_message, args, 2, NOISE_ERROR);
}

PyObject*
py_noise_read_message(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_read_message, args, 2, NOISE_ERROR);
}

PyObject*
py_noise_transport(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_transport, args, 1, NOISE_ERROR);
}

PyObject*
py_noise_cipher_encrypt(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_cipher_encrypt, args, 3, NOISE_ERROR);
}

PyObject*
py_noise_cipher_decrypt(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_cipher_decrypt, args, 3, NOISE_ERROR);
}

PyObject*
py_noise_frame(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_frame, args, 1, NOISE_ERROR);
}

PyObject*
py_noise_unframe(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_unframe, args, 1, NOISE_ERROR);
}

PyObject*
py_noise_libp2p_initialize(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_libp2p_initialize, args, 3, NOISE_ERROR);
}

PyObject*
py_noise_libp2p_write(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_libp2p_write, args, 3, NOISE_ERROR);
}

PyObject*
py_noise_libp2p_read(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_libp2p_read, args, 2, NOISE_ERROR);
}

PyObject*
py_noise_libp2p_complete(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_noise_libp2p_complete, args, 1, NOISE_ERROR);
}
