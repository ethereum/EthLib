/* Gossip wrappers around the `eth_gossip_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_gossip_message_id_phase0(
  lean_object* data
);

extern lean_object*
eth_gossip_message_id_altair(
  lean_object* topic,
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
py_gossip_message_id_phase0(
  PyObject* self,
  PyObject* args
) {
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "O", &data_obj)) return NULL;
  lean_object* data = bytes_arg(data_obj, "data");
  if (!data) return NULL;
  return run_io_into_pybytes(eth_gossip_message_id_phase0(data), "gossip message_id");
}

PyObject*
py_gossip_message_id_altair(
  PyObject* self,
  PyObject* args
) {
  PyObject* topic_obj;
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "OO", &topic_obj, &data_obj)) return NULL;
  /* Check both arguments before building either, so a failure leaks nothing. */
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  lean_object* topic = bytes_arg(topic_obj, "topic");
  if (!topic) return NULL;
  lean_object* data = bytes_arg(data_obj, "data");
  return run_io_into_pybytes(eth_gossip_message_id_altair(topic, data), "gossip message_id");
}
