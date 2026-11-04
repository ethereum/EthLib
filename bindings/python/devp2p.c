/* devp2p wrappers around the `eth_devp2p_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_devp2p_decode_message(
  uint8_t snappy,
  lean_object* frame_data
);

extern lean_object*
eth_devp2p_encode_message(
  uint8_t snappy,
  lean_object* plain
);

/* ---- Wrappers --------------------------------------------------------- */

/* Parse `(snappy: bool, data: bytes)`, or return NULL with a TypeError set. */
static lean_object*
parse_snappy_and_bytes(
  PyObject* args,
  uint8_t* snappy
) {
  int flag;
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "pO", &flag, &obj)) return NULL;
  if (!PyBytes_Check(obj)) {
    PyErr_SetString(PyExc_TypeError, "frame data must be bytes");
    return NULL;
  }
  *snappy = (uint8_t) flag;
  return mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj));
}

PyObject*
py_devp2p_decode_message(
  PyObject* self,
  PyObject* args
) {
  uint8_t snappy;
  lean_object* data = parse_snappy_and_bytes(args, &snappy);
  if (!data) return NULL;
  return except_into_pybytes(eth_devp2p_decode_message(snappy, data), DEVP2P_ERROR);
}

PyObject*
py_devp2p_encode_message(
  PyObject* self,
  PyObject* args
) {
  uint8_t snappy;
  lean_object* data = parse_snappy_and_bytes(args, &snappy);
  if (!data) return NULL;
  return except_into_pybytes(eth_devp2p_encode_message(snappy, data), DEVP2P_ERROR);
}
