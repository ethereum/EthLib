/* Gossip wrappers around the `eth_gossip_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_gossip_message_id(
  lean_object* args
);

extern lean_object*
eth_gossip_decode_payload(
  uint64_t type_bound,
  lean_object* data
);

/* ---- Wrappers --------------------------------------------------------- */

/* The bytes of a `bytes` object, or NULL with a TypeError set. */
static lean_object*
bytes_arg(
  PyObject* obj,
  const char* name
) {
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", name);
    return NULL;
  }
  return mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj));
}

PyObject*
py_gossip_message_id(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_gossip_message_id, args, 3, GOSSIP_ERROR);
}

PyObject*
py_gossip_decode_payload(
  PyObject* self,
  PyObject* args
) {
  PyObject *bound_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OO", &bound_obj, &data_obj)) return NULL;
  uint64_t type_bound;
  if (parse_uint64(bound_obj, "type_bound", &type_bound)) return NULL;
  lean_object* data = bytes_arg(data_obj, "data");
  if (!data) return NULL;
  return except_into_pybytes(eth_gossip_decode_payload(type_bound, data), GOSSIP_ERROR);
}
