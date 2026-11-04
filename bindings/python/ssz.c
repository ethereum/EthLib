/* SSZ wrappers around the `eth_ssz_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_ssz_serialize(
  lean_object* type,
  lean_object* value
);

extern lean_object*
eth_ssz_deserialize(
  lean_object* type,
  lean_object* data
);

/* ---- Wrappers --------------------------------------------------------- */

/* Parse two `bytes` arguments, or return -1 with a TypeError set.
 *
 * Both are checked before either is copied, so a failure leaks nothing. */
static int
parse_two_bytes(
  PyObject* args,
  const char* first_name,
  const char* second_name,
  lean_object** first,
  lean_object** second
) {
  PyObject* first_obj;
  PyObject* second_obj;
  if (!PyArg_ParseTuple(args, "OO", &first_obj, &second_obj)) return -1;
  if (!PyBytes_Check(first_obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", first_name);
    return -1;
  }
  if (!PyBytes_Check(second_obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", second_name);
    return -1;
  }
  *first = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(first_obj), PyBytes_GET_SIZE(first_obj));
  *second = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(second_obj), PyBytes_GET_SIZE(second_obj));
  return 0;
}

PyObject*
py_ssz_serialize(
  PyObject* self,
  PyObject* args
) {
  lean_object* type;
  lean_object* value;
  if (parse_two_bytes(args, "type", "value", &type, &value)) return NULL;
  return except_into_pybytes(eth_ssz_serialize(type, value), SSZ_ERROR);
}

PyObject*
py_ssz_deserialize(
  PyObject* self,
  PyObject* args
) {
  lean_object* type;
  lean_object* data;
  if (parse_two_bytes(args, "type", "data", &type, &data)) return NULL;
  return except_into_pybytes(eth_ssz_deserialize(type, data), SSZ_ERROR);
}
