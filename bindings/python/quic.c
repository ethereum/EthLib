/* Python wrappers of the QUIC exports. */
#include "wrappers.h"

extern lean_object* eth_quic_varint_encode(lean_object* args);
extern lean_object* eth_quic_varint_decode(lean_object* args);

PyObject*
py_quic_varint_encode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_varint_encode, args, 1, QUIC_VARINT_ERROR);
}

PyObject*
py_quic_varint_decode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_varint_decode, args, 1, QUIC_VARINT_ERROR);
}

extern lean_object* eth_quic_initial_secrets(lean_object* args);

PyObject*
py_quic_initial_secrets(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_initial_secrets, args, 1, TLS13_ERROR);
}

extern lean_object* eth_quic_packet_keys(lean_object* args);

PyObject*
py_quic_packet_keys(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_packet_keys, args, 2, TLS13_ERROR);
}

extern lean_object* eth_quic_tls_key_schedule(lean_object* args);

PyObject*
py_quic_tls_key_schedule(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_tls_key_schedule, args, 3, TLS13_ERROR);
}

extern lean_object* eth_quic_tls_derive_secret(lean_object* args);

PyObject*
py_quic_tls_derive_secret(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_tls_derive_secret, args, 3, TLS13_ERROR);
}

extern lean_object* eth_quic_tls_finished(lean_object* args);

PyObject*
py_quic_tls_finished(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_tls_finished, args, 2, TLS13_ERROR);
}
