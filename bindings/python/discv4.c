/* discv4 wrappers around the `eth_discv4_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_discv4_decode(
  lean_object* packet
);

extern lean_object*
eth_discv4_encode(
  lean_object* key,
  lean_object* plain
);

extern lean_object*
eth_discv4_record_signed_by(
  lean_object* sender,
  lean_object* record
);

/* ---- Wrappers --------------------------------------------------------- */

/* Copy the Python `bytes` object `obj` into a Lean `ByteArray`, or set a TypeError naming it. */
static int
parse_bytes(
  PyObject* obj,
  const char* name,
  lean_object** out
) {
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", name);
    return 1;
  }
  *out = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), (size_t) PyBytes_GET_SIZE(obj));
  return 0;
}

PyObject*
py_discv4_decode(
  PyObject* self,
  PyObject* args
) {
  PyObject* packet_obj;
  if (!PyArg_ParseTuple(args, "O", &packet_obj)) return NULL;
  lean_object* packet;
  if (parse_bytes(packet_obj, "packet", &packet)) return NULL;
  return except_into_pybytes(eth_discv4_decode(packet), DISCV4_ERROR);
}

PyObject*
py_discv4_encode(
  PyObject* self,
  PyObject* args
) {
  PyObject *key_obj, *plain_obj;
  if (!PyArg_ParseTuple(args, "OO", &key_obj, &plain_obj)) return NULL;
  lean_object *key, *plain;
  if (parse_bytes(key_obj, "key", &key)) return NULL;
  if (parse_bytes(plain_obj, "content", &plain)) { lean_dec(key); return NULL; }
  return except_into_pybytes(eth_discv4_encode(key, plain), DISCV4_ERROR);
}

PyObject*
py_discv4_record_signed_by(
  PyObject* self,
  PyObject* args
) {
  PyObject *sender_obj, *record_obj;
  if (!PyArg_ParseTuple(args, "OO", &sender_obj, &record_obj)) return NULL;
  lean_object *sender, *record;
  if (parse_bytes(sender_obj, "sender", &sender)) return NULL;
  if (parse_bytes(record_obj, "record", &record)) { lean_dec(sender); return NULL; }
  return except_into_pybool(eth_discv4_record_signed_by(sender, record), DISCV4_ERROR);
}
