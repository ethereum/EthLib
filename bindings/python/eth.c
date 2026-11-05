/* eth capability wrappers around the `eth_message_decode` and `eth_check_status` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_message_decode(
  uint64_t version,
  uint64_t id,
  lean_object* data
);

extern lean_object*
eth_check_status(
  uint64_t version,
  lean_object* schedule,
  uint64_t number,
  uint64_t timestamp,
  lean_object* data
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
py_eth_message_decode(
  PyObject* self,
  PyObject* args
) {
  PyObject *version_obj, *id_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOO", &version_obj, &id_obj, &data_obj)) return NULL;
  uint64_t version, id;
  if (parse_uint64(version_obj, "version", &version)) return NULL;
  if (parse_uint64(id_obj, "id", &id)) return NULL;
  lean_object* data;
  if (parse_bytes(data_obj, "data", &data)) return NULL;
  return except_into_pybytes(eth_message_decode(version, id, data), ETH_WIRE_ERROR);
}

PyObject*
py_eth_check_status(
  PyObject* self,
  PyObject* args
) {
  PyObject *version_obj, *schedule_obj, *number_obj, *timestamp_obj, *data_obj;
  if (!PyArg_ParseTuple(args, "OOOOO", &version_obj, &schedule_obj, &number_obj, &timestamp_obj,
      &data_obj))
    return NULL;
  uint64_t version, number, timestamp;
  if (parse_uint64(version_obj, "version", &version)) return NULL;
  if (parse_uint64(number_obj, "number", &number)) return NULL;
  if (parse_uint64(timestamp_obj, "timestamp", &timestamp)) return NULL;
  lean_object *schedule, *data;
  if (parse_bytes(schedule_obj, "schedule", &schedule)) return NULL;
  if (parse_bytes(data_obj, "data", &data)) { lean_dec(schedule); return NULL; }
  return except_into_pybool(
    eth_check_status(version, schedule, number, timestamp, data), ETH_WIRE_ERROR);
}
