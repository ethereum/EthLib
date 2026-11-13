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
