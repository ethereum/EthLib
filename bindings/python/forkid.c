/* Fork identifier wrappers around the `eth_fork_id*` and `eth_mainnet_fork_id` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_fork_id(
  lean_object* args
);

extern lean_object*
eth_mainnet_fork_id(
  lean_object* args
);

extern lean_object*
eth_fork_id_validate(
  lean_object* schedule,
  uint64_t number,
  uint64_t timestamp,
  lean_object* remote
);

extern lean_object*
eth_fork_id_schedule(
  lean_object* args
);

extern lean_object*
eth_fork_id_encode(
  lean_object* args
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
py_fork_id(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_fork_id, args, 3, FORK_ID_ERROR);
}

PyObject*
py_mainnet_fork_id(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_mainnet_fork_id, args, 2, FORK_ID_ERROR);
}

PyObject*
py_fork_id_validate(
  PyObject* self,
  PyObject* args
) {
  PyObject *schedule_obj, *number_obj, *timestamp_obj, *remote_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &schedule_obj, &number_obj, &timestamp_obj, &remote_obj))
    return NULL;
  uint64_t number, timestamp;
  if (parse_uint64(number_obj, "number", &number)) return NULL;
  if (parse_uint64(timestamp_obj, "timestamp", &timestamp)) return NULL;
  lean_object *schedule, *remote;
  if (parse_bytes(schedule_obj, "schedule", &schedule)) return NULL;
  if (parse_bytes(remote_obj, "remote", &remote)) { lean_dec(schedule); return NULL; }
  return except_into_pybool(
    eth_fork_id_validate(schedule, number, timestamp, remote), FORK_ID_ERROR);
}

PyObject*
py_fork_id_schedule(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_fork_id_schedule, args, 4, FORK_ID_ERROR);
}

PyObject*
py_fork_id_encode(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_fork_id_encode, args, 2, FORK_ID_ERROR);
}
