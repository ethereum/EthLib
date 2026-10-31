/* Python wrapper of the RIPEMD-160 precompile export.
 *
 * It checks its Python argument.
 *
 * It then calls the Lean export and turns the result into a Python value. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_ripemd160(
  lean_object* data
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_ripemd160(
  PyObject* self,
  PyObject* args
) {
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "O", &data_obj)) return NULL;
  if (!PyBytes_Check(data_obj)) {
    PyErr_SetString(PyExc_TypeError, "data must be bytes");
    return NULL;
  }
  /* The export takes ownership of its argument. */
  lean_object* res = eth_ripemd160(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(data_obj),
                 (size_t) PyBytes_GET_SIZE(data_obj)));
  PyObject* out = PyBytes_FromStringAndSize(
    (const char*) lean_sarray_cptr(res), (Py_ssize_t) lean_sarray_size(res));
  lean_dec(res);
  return out;
}
