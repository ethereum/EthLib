/* RLP wrappers around the `eth_rlp_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_rlp_encode(
  lean_object* item
);

extern lean_object*
eth_rlp_decode(
  lean_object* data
);

extern lean_object*
eth_rlp_decode_as(
  lean_object* kind,
  lean_object* data
);

/* ---- Items ------------------------------------------------------------ */

/* An item is a byte string (constructor 0) or a list of items (constructor 1).
 *
 * Each constructor holds one object field.
 *
 * A Lean list is the scalar 0 when empty, and otherwise a cell (constructor 1) of a head and a tail. */

/* The Lean item of a Python `bytes` or list of items, or NULL with an exception set. */
static lean_object*
item_of_py(
  PyObject* obj
) {
  if (PyBytes_Check(obj)) {
    lean_object* item = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(item, 0,
      mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj)));
    return item;
  }
  if (!PyList_Check(obj)) {
    PyErr_SetString(PyExc_TypeError, "an RLP item must be bytes or a list of items");
    return NULL;
  }
  if (Py_EnterRecursiveCall(" while converting an RLP item")) return NULL;
  /* Build the list from its last element, so each cell takes the list after it. */
  lean_object* list = lean_box(0);
  for (Py_ssize_t i = PyList_GET_SIZE(obj); i > 0; i--) {
    lean_object* child = item_of_py(PyList_GET_ITEM(obj, i - 1));
    if (!child) {
      lean_dec(list);
      Py_LeaveRecursiveCall();
      return NULL;
    }
    lean_object* cell = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cell, 0, child);
    lean_ctor_set(cell, 1, list);
    list = cell;
  }
  Py_LeaveRecursiveCall();
  lean_object* item = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(item, 0, list);
  return item;
}

/* The Python form of a borrowed Lean item, or NULL with an exception set. */
static PyObject*
py_of_item(
  lean_object* item
) {
  if (lean_obj_tag(item) == 0) {
    lean_object* data = lean_ctor_get(item, 0);
    return PyBytes_FromStringAndSize(
      (const char*) lean_sarray_cptr(data), (Py_ssize_t) lean_sarray_size(data));
  }
  if (Py_EnterRecursiveCall(" while converting an RLP item")) return NULL;
  PyObject* out = PyList_New(0);
  for (lean_object* cell = lean_ctor_get(item, 0); out && !lean_is_scalar(cell);
       cell = lean_ctor_get(cell, 1)) {
    PyObject* child = py_of_item(lean_ctor_get(cell, 0));
    if (!child || PyList_Append(out, child) < 0) Py_CLEAR(out);
    Py_XDECREF(child);
  }
  Py_LeaveRecursiveCall();
  return out;
}

/* The item of a successful result as its Python form, or NULL with an RlpError set. */
static PyObject*
except_into_pyitem(
  lean_object* result
) {
  if (lean_obj_tag(result) == 0) {
    raise_lean_error(result, RLP_ERROR);
    return NULL;
  }
  PyObject* out = py_of_item(lean_ctor_get(result, 0));
  lean_dec(result);
  return out;
}

/* The bytes of a `bytes` object, or NULL with a TypeError set. */
static lean_object*
bytes_of_py(
  PyObject* obj,
  const char* name
) {
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", name);
    return NULL;
  }
  return mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), PyBytes_GET_SIZE(obj));
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_rlp_encode(
  PyObject* self,
  PyObject* args
) {
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "O", &obj)) return NULL;
  lean_object* item = item_of_py(obj);
  if (!item) return NULL;
  return except_into_pybytes(eth_rlp_encode(item), RLP_ERROR);
}

PyObject*
py_rlp_decode(
  PyObject* self,
  PyObject* args
) {
  PyObject* obj;
  if (!PyArg_ParseTuple(args, "O", &obj)) return NULL;
  lean_object* data = bytes_of_py(obj, "data");
  if (!data) return NULL;
  return except_into_pyitem(eth_rlp_decode(data));
}

PyObject*
py_rlp_decode_as(
  PyObject* self,
  PyObject* args
) {
  PyObject* kind_obj;
  PyObject* data_obj;
  if (!PyArg_ParseTuple(args, "OO", &kind_obj, &data_obj)) return NULL;
  if (!PyUnicode_Check(kind_obj)) {
    PyErr_SetString(PyExc_TypeError, "kind must be str");
    return NULL;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(kind_obj, &len);
  if (!utf8) return NULL;
  lean_object* data = bytes_of_py(data_obj, "data");
  if (!data) return NULL;
  lean_object* kind = mk_bytearray((const uint8_t*) utf8, len);
  return except_into_pyitem(eth_rlp_decode_as(kind, data));
}
