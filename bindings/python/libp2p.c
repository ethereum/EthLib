/* Typed wrappers of the libp2p framing and secp256k1 peer ID exports. */
#include "wrappers.h"

extern lean_object* eth_uvarint_encode(lean_object* args);
extern lean_object* eth_uvarint_decode(lean_object* args);
extern lean_object* eth_multistream_encode(lean_object* args);
extern lean_object* eth_multistream_decode(lean_object* args);
extern lean_object* eth_mplex_encode(lean_object* args);
extern lean_object* eth_mplex_decode(lean_object* args);
extern lean_object* eth_yamux_encode(lean_object* args);
extern lean_object* eth_yamux_decode(lean_object* args);
extern lean_object* eth_libp2p_public_key(lean_object* args);
extern lean_object* eth_libp2p_peer_id(lean_object* args);
extern lean_object* eth_libp2p_decode_peer_id(lean_object* args);

PyObject*
py_uvarint_encode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_uvarint_encode, args, 1, UVARINT_ERROR);
}

PyObject*
py_uvarint_decode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_uvarint_decode, args, 1, UVARINT_ERROR);
}

PyObject*
py_multistream_encode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_multistream_encode, args, 1, MULTISTREAM_ERROR);
}

PyObject*
py_multistream_decode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_multistream_decode, args, 1, MULTISTREAM_ERROR);
}

PyObject*
py_mplex_encode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_mplex_encode, args, 1, MPLEX_ERROR);
}

PyObject*
py_mplex_decode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_mplex_decode, args, 1, MPLEX_ERROR);
}

PyObject*
py_yamux_encode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_yamux_encode, args, 1, YAMUX_ERROR);
}

PyObject*
py_yamux_decode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_yamux_decode, args, 1, YAMUX_ERROR);
}

PyObject*
py_libp2p_public_key(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_libp2p_public_key, args, 1, LIBP2P_IDENTITY_ERROR);
}

PyObject*
py_libp2p_peer_id(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_libp2p_peer_id, args, 1, LIBP2P_IDENTITY_ERROR);
}

PyObject*
py_libp2p_decode_peer_id(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_libp2p_decode_peer_id, args, 1, LIBP2P_IDENTITY_ERROR);
}
