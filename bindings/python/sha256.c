/* Python wrapper of the SHA-256 export.
 *
 * The wrapper checks its Python argument.
 *
 * It then calls the Lean export and turns the result into a Python value. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_sha256(
  lean_object* data
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_sha256(
  PyObject* self,
  PyObject* args
) {
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "O", &data_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* The export is total, so its result is the ByteArray itself,
   * not an `IO` result to unwrap. */
  lean_object* res = eth_sha256(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)));
  PyObject* out = PyBytes_FromStringAndSize(
    (const char*) lean_sarray_cptr(res),
    (Py_ssize_t) lean_sarray_size(res));
  /* The wrapper owns the result, so it frees it after the copy. */
  lean_dec(res);
  return out;
}
