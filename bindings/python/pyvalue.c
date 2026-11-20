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
 * Lean reads and writes the digits of a large `int` by halves, in time about d log d for d digits.
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

/* The budgets and last converted dictionary key for one call. */
typedef struct {
  size_t parts_left;
  size_t bytes_left;
  PyObject* last_key;
  lean_object* last_key_text;
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

/* CPython has already supplied valid UTF-8 and knows the character count. */
static lean_object*
unicode_to_lean(
  PyObject* text,
  const char* utf8,
  Py_ssize_t len
) {
  return lean_mk_string_unchecked(utf8, (size_t) len, (size_t) PyUnicode_GET_LENGTH(text));
}

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
  lean_object* out = lean_alloc_array((size_t) n, (size_t) n);
  for (Py_ssize_t i = 0; i < n; i++) {
    lean_object* item = of_py(PyTuple_GET_ITEM(tuple, i), depth + 1, budget);
    if (!item) {
      /* Release only the slots filled so far. */
      lean_array_set_size(out, (size_t) i);
      lean_dec(out);
      return NULL;
    }
    lean_array_set_core(out, (size_t) i, item);
  }
  return out;
}

/* One key and value from the snapshot of a dict. */
static lean_object*
entry_of_py(
  PyObject* key,
  PyObject* value,
  int depth,
  pv_budget* budget
) {
  if (!PyUnicode_Check(key)) {
    PyErr_Format(PyExc_TypeError, "cannot pass a dict key of type %s to Lean",
      Py_TYPE(key)->tp_name);
    return NULL;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(key, &len);
  if (!utf8 || !take_bytes(budget, (size_t) len)) return NULL;
  lean_object* item = of_py(value, depth + 1, budget);
  if (!item) return NULL;
  lean_object* text;
  if (key == budget->last_key) {
    text = budget->last_key_text;
    lean_inc(text);
  } else {
    text = unicode_to_lean(key, utf8, len);
    /* Only exact strings can be released without running user code. */
    if (PyUnicode_CheckExact(key)) {
      if (budget->last_key_text) lean_dec(budget->last_key_text);
      Py_XSETREF(budget->last_key, Py_NewRef(key));
      budget->last_key_text = text;
      lean_inc(text);
    }
  }
  lean_object* entry = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(entry, 0, text);
  lean_ctor_set(entry, 1, item);
  return entry;
}

/* Borrow the one entry of a dict while the caller holds its lock. */
static int
single_entry(
  PyObject* dict,
  PyObject** key,
  PyObject** value
) {
  Py_ssize_t pos = 0;
  return PyDict_GET_SIZE(dict) == 1 && PyDict_Next(dict, &pos, key, value);
}

/* The Lean array of the entries of a dict, or NULL with an exception set. */
static lean_object*
entries_of_py(
  PyObject* dict,
  int depth,
  pv_budget* budget
) {
  /* A one-entry dict needs only two owned references for its snapshot. */
  PyObject* key = NULL;
  PyObject* value = NULL;
#ifdef Py_GIL_DISABLED
  Py_BEGIN_CRITICAL_SECTION(dict);
#endif
  if (single_entry(dict, &key, &value)) {
    Py_INCREF(key);
    Py_INCREF(value);
  }
#ifdef Py_GIL_DISABLED
  Py_END_CRITICAL_SECTION();
#endif
  if (key) {
    lean_object* entry = entry_of_py(key, value, depth, budget);
    Py_DECREF(value);
    Py_DECREF(key);
    if (!entry) return NULL;
    lean_object* out = lean_alloc_array(1, 1);
    lean_array_set_core(out, 0, entry);
    return out;
  }

  /* The pairs come from the storage of the dict, never from methods that a subclass overrides.
   *
   * The list keeps them fixed if the conversion of a value runs Python code. */
  PyObject* pairs = PyDict_Items(dict);
  if (!pairs) return NULL;
  Py_ssize_t n = PyList_GET_SIZE(pairs);
  lean_object* out = lean_alloc_array(0, (size_t) n);
  for (Py_ssize_t i = 0; i < n; i++) {
    PyObject* pair = PyList_GET_ITEM(pairs, i);
    lean_object* entry = entry_of_py(PyTuple_GET_ITEM(pair, 0), PyTuple_GET_ITEM(pair, 1),
      depth, budget);
    if (!entry) goto fail;
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
    return pv_ctor(PV_STR, unicode_to_lean(obj, utf8, len));
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

static void
release_budget(
  pv_budget* budget
) {
  Py_XDECREF(budget->last_key);
  if (budget->last_key_text) lean_dec(budget->last_key_text);
}

static lean_object*
of_py_bounded(
  PyObject* obj,
  int depth
) {
  pv_budget budget = {.parts_left = PV_MAX_PARTS, .bytes_left = PV_MAX_BYTES};
  lean_object* value = of_py(obj, depth, &budget);
  release_budget(&budget);
  return value;
}

lean_object*
pyvalue_of_py(
  PyObject* obj
) {
  return of_py_bounded(obj, 0);
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
  lean_object* value = of_py_bounded(args, -1);
  if (!value) return NULL;
  return except_into_pyvalue(export(value), error_class);
}

/* A short sequence does not amortize a separate snapshot and packed allocation. */
#define PV_MIN_BATCH 32

/* A fallback can hold the packed data alongside the expanded entries. */
#define PV_MAX_BATCH_BYTES ((size_t) 8 << 20)

/* The outer entry can be probed without keeping a reference to either borrowed object. */
static int
batch_sequence(
  PyObject* dict,
  PyObject** owned_key,
  PyObject** owned_items
) {
  if (!PyDict_CheckExact(dict)) return 0;
  int match = 0;
  PyObject* key;
  PyObject* items;
#ifdef Py_GIL_DISABLED
  Py_BEGIN_CRITICAL_SECTION(dict);
#endif
  if (single_entry(dict, &key, &items) && PyUnicode_CheckExact(key) &&
      PyUnicode_IS_ASCII(key)) {
    Py_ssize_t count = 0;
    if (PyList_CheckExact(items)) count = PyList_Size(items);
    if (PyTuple_CheckExact(items)) count = PyTuple_GET_SIZE(items);
    if (count >= PV_MIN_BATCH) {
      match = 1;
      if (owned_key) {
        *owned_key = Py_NewRef(key);
        *owned_items = Py_NewRef(items);
      }
    }
  }
#ifdef Py_GIL_DISABLED
  Py_END_CRITICAL_SECTION();
#endif
  return match;
}

/* Read a cell with an exact ASCII key and an immutable payload.
 * A free-threaded build retains the payload before it releases the lock.
 * Under the GIL, the packing loops borrow it and run no Python callbacks. */
static PyObject*
batch_cell(
  PyObject* dict,
  PyObject** common_key,
  int allow_bytes,
  int allow_nats
) {
  if (!PyDict_CheckExact(dict)) return NULL;
  PyObject* key;
  PyObject* value;
  PyObject* data = NULL;
#ifdef Py_GIL_DISABLED
  Py_BEGIN_CRITICAL_SECTION(dict);
#endif
  if (single_entry(dict, &key, &value) &&
      ((allow_bytes && PyBytes_CheckExact(value)) || (allow_nats && PyLong_CheckExact(value))) &&
      (*common_key ? key == *common_key : PyUnicode_CheckExact(key) && PyUnicode_IS_ASCII(key))) {
    if (!*common_key) *common_key = Py_NewRef(key);
#ifdef Py_GIL_DISABLED
    data = Py_NewRef(value);
#else
    data = value;
#endif
  }
#ifdef Py_GIL_DISABLED
  Py_END_CRITICAL_SECTION();
#endif
  return data;
}

static void
release_batch_cell(
  PyObject* value
) {
#ifdef Py_GIL_DISABLED
  Py_XDECREF(value);
#else
  (void) value;
#endif
}

/* Pack bytes after reading each immutable payload. */
static lean_object*
pack_byte_cells(
  PyObject* items,
  PyObject* first,
  PyObject** item_key,
  size_t count,
  size_t width
) {
  lean_object* result = NULL;
  PyObject** cells = PyMem_New(PyObject*, count);
  if (!cells) return NULL;
  cells[0] = first;
  size_t filled = 1;
  while (filled < count) {
    PyObject* data = batch_cell(PyTuple_GET_ITEM(items, (Py_ssize_t) filled), item_key, 1, 0);
    if (!data) goto end;
    cells[filled++] = data;
    if ((size_t) PyBytes_GET_SIZE(data) != width) goto end;
  }
  size_t len = count * width;
  result = lean_alloc_sarray(1, len, len);
  uint8_t* dest = lean_sarray_cptr(result);
  for (size_t i = 0; i < count; i++)
    memcpy(dest + i * width, PyBytes_AS_STRING(cells[i]), width);
end:
  for (size_t i = 1; i < filled; i++) release_batch_cell(cells[i]);
  PyMem_Free(cells);
  return result;
}

/* Use the int conversion that takes no bytes from the ordinary budget. */
static int
small_nat(
  PyObject* value,
  uint64_t* out
) {
  int overflow;
  long long small = PyLong_AsLongLongAndOverflow(value, &overflow);
  if (overflow || small < 0) return 0;
  *out = (uint64_t) small;
  return 1;
}

static lean_object*
pack_nat_cells(
  PyObject* items,
  PyObject* first,
  PyObject** item_key,
  size_t count
) {
  uint64_t small;
  if (count > PV_MAX_BATCH_BYTES / sizeof(lean_object*) || !small_nat(first, &small))
    return NULL;
  lean_object* result = lean_alloc_array(count, count);
  lean_array_set_core(result, 0, lean_uint64_to_nat(small));
  size_t filled = 1;
  while (filled < count) {
    PyObject* data = batch_cell(PyTuple_GET_ITEM(items, (Py_ssize_t) filled), item_key, 0, 1);
    if (!data) break;
    int fits = small_nat(data, &small);
    release_batch_cell(data);
    if (!fits) break;
    lean_array_set_core(result, filled++, lean_uint64_to_nat(small));
  }
  if (filled == count) return result;
  /* The slots past the converted prefix hold no references. */
  lean_array_set_size(result, filled);
  lean_dec(result);
  return NULL;
}

/* Speculatively pack entries with a shared key inside the ordinary conversion budget. */
static lean_object*
try_batch(
  PyObject* obj,
  const pv_budget* budget,
  int allow_bytes,
  int allow_nats,
  size_t max_byte_width,
  int* packed_nats
) {
  PyObject* outer_key;
  PyObject* sequence;
  if (!batch_sequence(obj, &outer_key, &sequence)) return NULL;
  PyObject* items = NULL;
  PyObject* item_key = NULL;
  PyObject* first = NULL;
  lean_object* result = NULL;
  size_t outer_len = (size_t) PyUnicode_GET_LENGTH(outer_key);
  if (outer_len > budget->bytes_left || PV_MAX_DEPTH < 3 || budget->parts_left < 2) goto end;
  items = PyTuple_CheckExact(sequence) ? Py_NewRef(sequence) : PyList_AsTuple(sequence);
  if (!items) goto end;
  size_t count = (size_t) PyTuple_GET_SIZE(items);
  /* The outer dict and sequence take two parts, as do each inner dict and its payload. */
  if (count < PV_MIN_BATCH || count > (budget->parts_left - 2) / 2) goto end;
  first = batch_cell(PyTuple_GET_ITEM(items, 0), &item_key, allow_bytes, allow_nats);
  if (!first) goto end;
  *packed_nats = PyLong_CheckExact(first);
  size_t width = *packed_nats ? 0 : (size_t) PyBytes_GET_SIZE(first);
  if (width > max_byte_width) goto end;
  size_t item_len = (size_t) PyUnicode_GET_LENGTH(item_key);
  /* Each occurrence of the key and its bytes counts against the byte budget. */
  size_t per_cell = (budget->bytes_left - outer_len) / count;
  if (item_len > per_cell || width > per_cell - item_len ||
      width > PV_MAX_BATCH_BYTES / count) goto end;
  const char* outer_utf8 = PyUnicode_AsUTF8(outer_key);
  const char* item_utf8 = PyUnicode_AsUTF8(item_key);
  if (!outer_utf8 || !item_utf8) goto end;
  lean_object* data = *packed_nats ? pack_nat_cells(items, first, &item_key, count) :
    pack_byte_cells(items, first, &item_key, count, width);
  if (!data) goto end;
  result = lean_alloc_ctor(0, *packed_nats ? 3 : 5, 0);
  lean_ctor_set(result, 0, unicode_to_lean(outer_key, outer_utf8, (Py_ssize_t) outer_len));
  lean_ctor_set(result, 1, unicode_to_lean(item_key, item_utf8, (Py_ssize_t) item_len));
  if (*packed_nats) {
    lean_ctor_set(result, 2, data);
  } else {
    lean_ctor_set(result, 2, lean_usize_to_nat(count));
    lean_ctor_set(result, 3, lean_usize_to_nat(width));
    lean_ctor_set(result, 4, data);
  }
end:
  release_batch_cell(first);
  Py_XDECREF(item_key);
  Py_XDECREF(items);
  Py_DECREF(sequence);
  Py_DECREF(outer_key);
  /* The uncompressed conversion gives the original error in conversion order. */
  if (!result && PyErr_Occurred()) PyErr_Clear();
  return result;
}

PyObject*
call_pyvalue_export_batch(
  lean_object* (*export)(lean_object*),
  lean_object* (*bytes_batch_export)(lean_object*),
  lean_object* (*nat_batch_export)(lean_object*),
  size_t max_byte_width,
  PyObject* args,
  PyObject* error_class
) {
  if (PyTuple_GET_SIZE(args) != 2) return call_pyvalue_export(export, args, 2, error_class);
  PyObject* value = PyTuple_GET_ITEM(args, 1);
  if (!batch_sequence(value, NULL, NULL)) return call_pyvalue_export(export, args, 2, error_class);

  /* The argument tuple takes one part and each argument starts at depth zero. */
  pv_budget budget = {.parts_left = PV_MAX_PARTS - 1, .bytes_left = PV_MAX_BYTES};
  lean_object* type = of_py(PyTuple_GET_ITEM(args, 0), 0, &budget);
  if (!type) {
    release_budget(&budget);
    return NULL;
  }
  int packed_nats;
  lean_object* batch = try_batch(value, &budget, bytes_batch_export != NULL,
    nat_batch_export != NULL, max_byte_width, &packed_nats);
  if (batch) {
    release_budget(&budget);
    lean_object* pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, type);
    lean_ctor_set(pair, 1, batch);
    lean_object* result = packed_nats ? nat_batch_export(pair) : bytes_batch_export(pair);
    return except_into_pyvalue(result, error_class);
  }

  lean_object* item = of_py(value, 0, &budget);
  release_budget(&budget);
  if (!item) {
    lean_dec(type);
    return NULL;
  }
  lean_object* tuple = lean_alloc_array(2, 2);
  lean_array_set_core(tuple, 0, type);
  lean_array_set_core(tuple, 1, item);
  return except_into_pyvalue(export(pv_ctor(PV_TUPLE, tuple)), error_class);
}

PyObject*
py_pyvalue_echo(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_pyvalue_echo, args, 1, BINDING_ERROR);
}
