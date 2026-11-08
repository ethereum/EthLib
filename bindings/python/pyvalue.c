/*
 * The converter between Python objects and the Lean values of `EthLib.Exports.PyValue`.
 *
 * No export has code here, except the echo export that tests the converter.
 *
 * Each constructor of the Lean type has at most one field, and that field is an object.
 * A constructor without a field is the boxed index of the constructor.
 * Another constructor is an object whose tag is that index.
 *
 * Python passes `None`, `bool`, `int`, `bytes`, `str`, `list`, `tuple` and `dict` with `str` keys.
 * A value of another type raises `TypeError`.
 * Too many parts or bytes, a negative or too large `int`, or deep nesting raise `ValueError`.
 * A failure inside a result becomes an instance of the error class of the method.
 */
#include "wrappers.h"

/* The constructors of `PyValue`, in their order of declaration. */
enum {
  PV_NONE,
  PV_FALSE,
  PV_TRUE,
  PV_INT,
  PV_BYTES,
  PV_STR,
  PV_LIST,
  PV_TUPLE,
  PV_DICT,
  PV_FAILURE,
};

/* The deepest nesting that Python may pass.
 *
 * Lean reads a value by recursion, so the bound also keeps its stack small. */
#define PV_MAX_DEPTH 64

/* The widest `int` that Python may pass, in bits.
 *
 * Lean reads the digits of a large `int` one by one, in time quadratic in their number.
 * The bound keeps that time short. */
#define PV_MAX_INT_BITS 65536

extern lean_object* eth_pyvalue_nat_to_hex(lean_object* n);
extern lean_object* eth_pyvalue_nat_of_hex(lean_object* digits);
extern lean_object* eth_pyvalue_echo(lean_object* args);

/* The most parts that one call may pass, counting each value inside a container.
 *
 * A container that appears twice is converted twice.
 * So a few shared lists can stand for very many parts.
 * The bound keeps the time and the memory of a conversion bounded and linear in its size.
 * It admits every value of the `ssz_generic` vectors of consensus-spec-tests. */
#define PV_MAX_PARTS (1 << 22)

/* The most bytes that one call may pass, over its `bytes`, its `str` and its large `int`.
 *
 * The same `bytes` passed twice counts twice, since Lean holds two copies. */
#define PV_MAX_BYTES ((size_t) 1 << 29)

/* The state of one conversion from Python: the parts and the bytes it may still convert. */
typedef struct {
  size_t parts_left;
  size_t bytes_left;
} pv_budget;

/* Take a number of bytes from the budget, or set `ValueError` and return 0. */
static int
take_bytes(
  pv_budget* budget,
  size_t n
) {
  if (n > budget->bytes_left) {
    PyErr_Format(PyExc_ValueError, "cannot pass more than %zu bytes to Lean in one call",
      PV_MAX_BYTES);
    return 0;
  }
  budget->bytes_left -= n;
  return 1;
}

static lean_object* of_py(PyObject* obj, int depth, pv_budget* budget);

/* A boxed constructor with one object field. */
static lean_object*
pv_ctor(
  unsigned tag,
  lean_object* field
) {
  lean_object* out = lean_alloc_ctor(tag, 1, 0);
  lean_ctor_set(out, 0, field);
  return out;
}

/* The Lean `Nat` of a Python `int` that is not negative, or NULL with an exception set. */
static lean_object*
nat_of_py(
  PyObject* obj,
  pv_budget* budget
) {
  int overflow;
  long long small = PyLong_AsLongLongAndOverflow(obj, &overflow);
  if (small == -1 && !overflow && PyErr_Occurred()) return NULL;
  if (overflow < 0 || (!overflow && small < 0)) {
    PyErr_SetString(PyExc_ValueError, "cannot pass a negative int to Lean");
    return NULL;
  }
  if (!overflow) return lean_uint64_to_nat((uint64_t) small);
  /* The method of `int` itself, so that a subclass cannot change the width it reports. */
  PyObject* bits = PyObject_CallMethod((PyObject*) &PyLong_Type, "bit_length", "O", obj);
  if (!bits) return NULL;
  long width = PyLong_AsLong(bits);
  Py_DECREF(bits);
  if (width == -1 && PyErr_Occurred()) return NULL;
  if (width > PV_MAX_INT_BITS) {
    PyErr_Format(PyExc_ValueError, "cannot pass an int of more than %d bits to Lean",
      PV_MAX_INT_BITS);
    return NULL;
  }
  if (!take_bytes(budget, (size_t) (width + 7) / 8)) return NULL;
  /* Base 16 has no limit on the number of digits, unlike the decimal text of an int. */
  PyObject* text = PyNumber_ToBase(obj, 16);
  if (!text) return NULL;
  Py_ssize_t len;
  const char* digits = PyUnicode_AsUTF8AndSize(text, &len);
  if (!digits) {
    Py_DECREF(text);
    return NULL;
  }
  /* The text starts with `0x`. */
  lean_object* out = eth_pyvalue_nat_of_hex(lean_mk_string_from_bytes(digits + 2, (size_t) len - 2));
  Py_DECREF(text);
  return out;
}

/* The Lean array of the items of a tuple, or NULL with an exception set. */
static lean_object*
items_of_py(
  PyObject* tuple,
  int depth,
  pv_budget* budget
) {
  Py_ssize_t n = PyTuple_GET_SIZE(tuple);
  lean_object* out = lean_alloc_array(0, (size_t) n);
  for (Py_ssize_t i = 0; i < n; i++) {
    lean_object* item = of_py(PyTuple_GET_ITEM(tuple, i), depth + 1, budget);
    if (!item) {
      lean_dec(out);
      return NULL;
    }
    out = lean_array_push(out, item);
  }
  return out;
}

/* The Lean array of the entries of a dict, or NULL with an exception set. */
static lean_object*
entries_of_py(
  PyObject* dict,
  int depth,
  pv_budget* budget
) {
  /* The pairs come from the storage of the dict, never from methods that a subclass overrides.
   *
   * The list keeps them fixed if the conversion of a value runs Python code. */
  PyObject* pairs = PyDict_Items(dict);
  if (!pairs) return NULL;
  Py_ssize_t n = PyList_GET_SIZE(pairs);
  lean_object* out = lean_alloc_array(0, (size_t) n);
  for (Py_ssize_t i = 0; i < n; i++) {
    PyObject* pair = PyList_GET_ITEM(pairs, i);
    PyObject* key = PyTuple_GET_ITEM(pair, 0);
    if (!PyUnicode_Check(key)) {
      PyErr_Format(PyExc_TypeError, "cannot pass a dict key of type %s to Lean",
        Py_TYPE(key)->tp_name);
      goto fail;
    }
    Py_ssize_t len;
    const char* utf8 = PyUnicode_AsUTF8AndSize(key, &len);
    if (!utf8 || !take_bytes(budget, (size_t) len)) goto fail;
    lean_object* item = of_py(PyTuple_GET_ITEM(pair, 1), depth + 1, budget);
    if (!item) goto fail;
    lean_object* entry = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(entry, 0, lean_mk_string_from_bytes(utf8, (size_t) len));
    lean_ctor_set(entry, 1, item);
    out = lean_array_push(out, entry);
  }
  Py_DECREF(pairs);
  return out;
fail:
  Py_DECREF(pairs);
  lean_dec(out);
  return NULL;
}

/* The Lean value of a Python object, or NULL with an exception set. */
static lean_object*
of_py(
  PyObject* obj,
  int depth,
  pv_budget* budget
) {
  if (depth > PV_MAX_DEPTH) {
    PyErr_Format(PyExc_ValueError, "cannot pass a value nested deeper than %d to Lean",
      PV_MAX_DEPTH);
    return NULL;
  }
  if (budget->parts_left == 0) {
    PyErr_Format(PyExc_ValueError, "cannot pass more than %d parts to Lean in one call",
      PV_MAX_PARTS);
    return NULL;
  }
  budget->parts_left--;
  if (obj == Py_None) return lean_box(PV_NONE);
  if (obj == Py_False) return lean_box(PV_FALSE);
  if (obj == Py_True) return lean_box(PV_TRUE);
  if (PyLong_Check(obj)) {
    lean_object* n = nat_of_py(obj, budget);
    return n ? pv_ctor(PV_INT, n) : NULL;
  }
  if (PyBytes_Check(obj)) {
    if (!take_bytes(budget, (size_t) PyBytes_GET_SIZE(obj))) return NULL;
    return pv_ctor(PV_BYTES,
      mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), (size_t) PyBytes_GET_SIZE(obj)));
  }
  if (PyUnicode_Check(obj)) {
    Py_ssize_t len;
    const char* utf8 = PyUnicode_AsUTF8AndSize(obj, &len);
    if (!utf8 || !take_bytes(budget, (size_t) len)) return NULL;
    return pv_ctor(PV_STR, lean_mk_string_from_bytes(utf8, (size_t) len));
  }
  if (PyTuple_Check(obj)) {
    lean_object* items = items_of_py(obj, depth, budget);
    return items ? pv_ctor(PV_TUPLE, items) : NULL;
  }
  if (PyList_Check(obj)) {
    /* A copy keeps the items fixed if the conversion of an item runs Python code. */
    PyObject* copy = PyList_AsTuple(obj);
    if (!copy) return NULL;
    lean_object* items = items_of_py(copy, depth, budget);
    Py_DECREF(copy);
    return items ? pv_ctor(PV_LIST, items) : NULL;
  }
  if (PyDict_Check(obj)) {
    lean_object* entries = entries_of_py(obj, depth, budget);
    return entries ? pv_ctor(PV_DICT, entries) : NULL;
  }
  PyErr_Format(PyExc_TypeError, "cannot pass a value of type %s to Lean", Py_TYPE(obj)->tp_name);
  return NULL;
}

lean_object*
pyvalue_of_py(
  PyObject* obj
) {
  pv_budget budget = {PV_MAX_PARTS, PV_MAX_BYTES};
  return of_py(obj, 0, &budget);
}

static PyObject* to_py(b_lean_obj_arg value, PyObject* error_class);

/* The Python `int` of a Lean `Nat`. */
static PyObject*
int_to_py(
  b_lean_obj_arg n
) {
  if (lean_is_scalar(n)) return PyLong_FromSize_t(lean_unbox(n));
  lean_inc(n);
  lean_object* text = eth_pyvalue_nat_to_hex(n);
  PyObject* out = PyLong_FromString(lean_string_cstr(text), NULL, 16);
  lean_dec(text);
  return out;
}

/* The Python `list` or `tuple` of a Lean array of values. */
static PyObject*
items_to_py(
  b_lean_obj_arg items,
  PyObject* error_class,
  int tuple
) {
  size_t n = lean_array_size(items);
  /* The items are built first, so no Python code ever sees a container with empty slots. */
  PyObject** built = PyMem_New(PyObject*, n ? n : 1);
  if (!built) return PyErr_NoMemory();
  size_t done = 0;
  PyObject* out = NULL;
  for (; done < n; done++) {
    built[done] = to_py(lean_array_get_core(items, done), error_class);
    if (!built[done]) goto end;
  }
  out = tuple ? PyTuple_New((Py_ssize_t) n) : PyList_New((Py_ssize_t) n);
  if (!out) goto end;
  for (size_t i = 0; i < n; i++) {
    if (tuple) PyTuple_SET_ITEM(out, (Py_ssize_t) i, built[i]);
    else PyList_SET_ITEM(out, (Py_ssize_t) i, built[i]);
  }
  /* The container now owns every item. */
  done = 0;
end:
  for (size_t i = 0; i < done; i++) Py_DECREF(built[i]);
  PyMem_Free(built);
  return out;
}

/* The Python `dict` of a Lean array of entries, which must not repeat a key. */
static PyObject*
entries_to_py(
  b_lean_obj_arg entries,
  PyObject* error_class
) {
  PyObject* out = PyDict_New();
  if (!out) return NULL;
  size_t n = lean_array_size(entries);
  for (size_t i = 0; i < n; i++) {
    lean_object* pair = lean_array_get_core(entries, i);
    lean_object* key = lean_ctor_get(pair, 0);
    PyObject* k = PyUnicode_FromStringAndSize(lean_string_cstr(key),
      (Py_ssize_t) lean_string_size(key) - 1);
    PyObject* v = k ? to_py(lean_ctor_get(pair, 1), error_class) : NULL;
    int failed = !v || PyDict_SetItem(out, k, v) < 0;
    Py_XDECREF(k);
    Py_XDECREF(v);
    /* A repeated key would drop a value, so two Lean values could reach Python as one. */
    if (!failed && PyDict_GET_SIZE(out) != (Py_ssize_t) (i + 1)) {
      PyErr_SetString(PyExc_RuntimeError, "Lean returned a dict with a repeated key");
      failed = 1;
    }
    if (failed) {
      Py_DECREF(out);
      return NULL;
    }
  }
  return out;
}

/* An instance of the error class, from the code and the message of a failure. */
static PyObject*
failure_to_py(
  b_lean_obj_arg pair,
  PyObject* error_class
) {
  uint32_t code = lean_unbox_uint32(lean_ctor_get(pair, 0));
  lean_object* message = lean_ctor_get(pair, 1);
  return PyObject_CallFunction(error_class, "Is#", (unsigned int) code,
    lean_string_cstr(message), (Py_ssize_t) lean_string_size(message) - 1);
}

/* The Python object of a borrowed Lean value, or NULL with an exception set. */
static PyObject*
to_py(
  b_lean_obj_arg value,
  PyObject* error_class
) {
  if (Py_EnterRecursiveCall(" while converting a Lean value")) return NULL;
  PyObject* out = NULL;
  switch (lean_obj_tag(value)) {
    case PV_NONE: out = Py_NewRef(Py_None); break;
    case PV_FALSE: out = Py_NewRef(Py_False); break;
    case PV_TRUE: out = Py_NewRef(Py_True); break;
    case PV_INT: out = int_to_py(lean_ctor_get(value, 0)); break;
    case PV_BYTES: {
      lean_object* data = lean_ctor_get(value, 0);
      out = PyBytes_FromStringAndSize((const char*) lean_sarray_cptr(data),
        (Py_ssize_t) lean_sarray_size(data));
      break;
    }
    case PV_STR: {
      lean_object* s = lean_ctor_get(value, 0);
      out = PyUnicode_FromStringAndSize(lean_string_cstr(s), (Py_ssize_t) lean_string_size(s) - 1);
      break;
    }
    case PV_LIST: out = items_to_py(lean_ctor_get(value, 0), error_class, 0); break;
    case PV_TUPLE: out = items_to_py(lean_ctor_get(value, 0), error_class, 1); break;
    case PV_DICT: out = entries_to_py(lean_ctor_get(value, 0), error_class); break;
    case PV_FAILURE: out = failure_to_py(lean_ctor_get(value, 0), error_class); break;
    default:
      PyErr_Format(PyExc_RuntimeError, "Lean returned a value with tag %u",
        lean_obj_tag(value));
  }
  Py_LeaveRecursiveCall();
  return out;
}

PyObject*
except_into_pyvalue(
  lean_object* result,
  PyObject* error_class
) {
  if (lean_obj_tag(result) == 0) {
    raise_lean_error(result, error_class);
    return NULL;
  }
  PyObject* out = to_py(lean_ctor_get(result, 0), error_class);
  lean_dec(result);
  return out;
}

PyObject*
call_pyvalue_export(
  lean_object* (*export)(lean_object*),
  PyObject* args,
  Py_ssize_t arity,
  PyObject* error_class
) {
  if (PyTuple_GET_SIZE(args) != arity) {
    PyErr_Format(PyExc_TypeError, "expected %zd argument%s", arity, arity == 1 ? "" : "s");
    return NULL;
  }
  /* The tuple of the arguments is not a level of nesting, so each argument starts at depth 0. */
  pv_budget budget = {PV_MAX_PARTS, PV_MAX_BYTES};
  lean_object* value = of_py(args, -1, &budget);
  if (!value) return NULL;
  return except_into_pyvalue(export(value), error_class);
}

PyObject*
py_pyvalue_echo(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_pyvalue_echo, args, 1, BINDING_ERROR);
}
