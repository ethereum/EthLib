/* Python wrapper of the SHA-256 export. */
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
  /* Take exactly one argument, and only `bytes`. */
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "O", &data_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* Copy the message into a Lean ByteArray.
   * The export takes ownership of it and frees it. */
  lean_object* res = eth_sha256(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)));
  /* The export is total, so its result is the digest itself, not an `IO` result. */
  PyObject* out = PyBytes_FromStringAndSize(
    (const char*) lean_sarray_cptr(res),
    (Py_ssize_t) lean_sarray_size(res));
  /* The wrapper owns the digest, so it frees it after the copy.
   * On a failed copy, the result is NULL with a Python error already set. */
  lean_dec(res);
  return out;
}
