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

extern lean_object* eth_quic_header_encode(lean_object* args);

PyObject*
py_quic_header_encode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_header_encode, args, 1, QUIC_ERROR);
}

extern lean_object* eth_quic_header_decode(lean_object* args);

PyObject*
py_quic_header_decode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_header_decode, args, 2, QUIC_ERROR);
}

extern lean_object* eth_quic_frame_encode(lean_object* args);

PyObject*
py_quic_frame_encode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_frame_encode, args, 1, QUIC_ERROR);
}

extern lean_object* eth_quic_frame_decode(lean_object* args);

PyObject*
py_quic_frame_decode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_frame_decode, args, 2, QUIC_ERROR);
}

extern lean_object* eth_quic_packet_number_encode(lean_object* args);

PyObject*
py_quic_packet_number_encode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_packet_number_encode, args, 2, QUIC_ERROR);
}

extern lean_object* eth_quic_packet_number_decode(lean_object* args);

PyObject*
py_quic_packet_number_decode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_packet_number_decode, args, 3, QUIC_ERROR);
}

extern lean_object* eth_quic_protect(lean_object* args);

PyObject*
py_quic_protect(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_protect, args, 6, QUIC_PROTECTION_ERROR);
}

extern lean_object* eth_quic_unprotect(lean_object* args);

PyObject*
py_quic_unprotect(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_unprotect, args, 5, QUIC_PROTECTION_ERROR);
}

extern lean_object* eth_quic_retry_tag(lean_object* args);

PyObject*
py_quic_retry_tag(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_quic_retry_tag, args, 2, QUIC_PROTECTION_ERROR);
}
