/* SSZ wrappers around the `eth_ssz_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* The general exports take the arguments as one tagged tuple. */

extern lean_object*
eth_ssz_serialize(
  lean_object* args
);

extern lean_object*
eth_ssz_serialize_bytes_batch(
  lean_object* args
);

extern lean_object*
eth_ssz_serialize_nat_batch(
  lean_object* args
);

extern lean_object*
eth_ssz_serialize_record(
  lean_object* type_key,
  lean_object* value_key,
  lean_object* cells
);

extern lean_object*
eth_ssz_deserialize(
  lean_object* args
);

extern lean_object*
eth_ssz_hash_tree_root(
  lean_object* args
);

extern lean_object*
eth_ssz_hash_tree_root_bytes_batch(
  lean_object* args
);

extern lean_object*
eth_ssz_hash_tree_root_nat_batch(
  lean_object* args
);

extern lean_object*
eth_ssz_hash_tree_root_record(
  lean_object* type_key,
  lean_object* value_key,
  lean_object* cells
);

extern lean_object*
eth_ssz_generalized_index(
  lean_object* args
);

extern lean_object*
eth_ssz_merkle_proof(
  lean_object* args
);

extern lean_object*
eth_ssz_merkleize_chunks(
  lean_object* args
);

/* ---- Compact fields --------------------------------------------------- */

/* This subset stays below the ordinary converter's depth, part and byte limits. */
#define RECORD_MIN_CELLS 3
#define RECORD_MAX_CELLS 12
#define RECORD_MAX_TEXT 128
#define RECORD_MAX_BYTES (1 << 20)

typedef enum {
  RECORD_SEQUENCE,
  RECORD_NUMBER,
  RECORD_ATOM,
} record_body;

static int
record_text(PyObject* text)
{
  return PyUnicode_CheckExact(text) && PyUnicode_IS_ASCII(text) &&
    PyUnicode_GET_LENGTH(text) <= RECORD_MAX_TEXT;
}

/* Retain the key and payload of a dictionary while it cannot change. */
static int
record_entry(PyObject* dict, record_body kind, PyObject** key, PyObject** body)
{
  if (!PyDict_CheckExact(dict)) return 0;
  int match = 0;
  Py_ssize_t pos = 0;
  PyObject* k;
  PyObject* b;
#ifdef Py_GIL_DISABLED
  Py_BEGIN_CRITICAL_SECTION(dict);
#endif
  if (PyDict_GET_SIZE(dict) == 1 && PyDict_Next(dict, &pos, &k, &b) && record_text(k)) {
    match = kind == RECORD_SEQUENCE ? PyList_CheckExact(b) || PyTuple_CheckExact(b) :
      PyLong_CheckExact(b) || (kind == RECORD_ATOM && PyBytes_CheckExact(b));
    if (match) {
      *key = Py_NewRef(k);
      *body = Py_NewRef(b);
    }
  }
#ifdef Py_GIL_DISABLED
  Py_END_CRITICAL_SECTION();
#endif
  return match;
}

/* Snapshot a short sequence before reading its items. */
static PyObject*
record_sequence(PyObject* dict, PyObject** key)
{
  PyObject* body;
  if (!record_entry(dict, RECORD_SEQUENCE, key, &body)) return NULL;
  Py_ssize_t count = PyList_CheckExact(body) ? PyList_Size(body) : PyTuple_GET_SIZE(body);
  PyObject* items = NULL;
  if (count >= RECORD_MIN_CELLS && count <= RECORD_MAX_CELLS) {
    items = sequence_snapshot(body, "expected a sequence");
    if (items) {
      count = PyTuple_GET_SIZE(items);
      if (count < RECORD_MIN_CELLS || count > RECORD_MAX_CELLS) Py_CLEAR(items);
    }
  }
  Py_DECREF(body);
  if (!items) Py_DECREF(*key);
  return items;
}

static lean_object*
record_string(PyObject* text)
{
  size_t len = (size_t) PyUnicode_GET_LENGTH(text);
  return lean_mk_string_unchecked((const char*) PyUnicode_1BYTE_DATA(text), len, len);
}

/* The exact integers in this subset take no bytes from the ordinary conversion budget. */
static lean_object*
record_nat(PyObject* obj)
{
  int overflow;
  long long number = PyLong_AsLongLongAndOverflow(obj, &overflow);
  if (overflow || number < 0) return NULL;
  return lean_uint64_to_nat((uint64_t) number);
}

/* A borrowed Lean key from the preceding cell and its owned Python key. */
typedef struct {
  PyObject* key;
  lean_object* text;
} record_key;

static lean_object*
record_cell_key(PyObject* key, record_key* previous)
{
  if (key == previous->key) {
    Py_DECREF(key);
    lean_inc(previous->text);
  } else {
    Py_XSETREF(previous->key, key);
    previous->text = record_string(key);
  }
  return previous->text;
}

/* The type cells start with two scalar placeholders for the value fields. */
static lean_object*
record_types(PyObject* items)
{
  size_t count = (size_t) PyTuple_GET_SIZE(items);
  lean_object* cells = lean_alloc_array(count, count);
  record_key previous = {0};
  size_t i = 0;
  for (; i < count; i++) {
    PyObject* pair = PyTuple_GET_ITEM(items, (Py_ssize_t) i);
    if (!PyTuple_CheckExact(pair) || PyTuple_GET_SIZE(pair) != 2) break;
    PyObject* name = PyTuple_GET_ITEM(pair, 0);
    PyObject* key;
    PyObject* body;
    if (!record_text(name) || !record_entry(PyTuple_GET_ITEM(pair, 1), RECORD_NUMBER, &key, &body))
      break;
    lean_object* width = record_nat(body);
    Py_DECREF(body);
    if (!width) {
      Py_DECREF(key);
      break;
    }
    lean_object* cell = lean_alloc_ctor(0, 5, 0);
    lean_ctor_set(cell, 0, record_string(name));
    lean_ctor_set(cell, 1, record_cell_key(key, &previous));
    lean_ctor_set(cell, 2, width);
    lean_ctor_set(cell, 3, lean_box(0));
    lean_ctor_set(cell, 4, lean_box(0));
    lean_array_set_core(cells, i, cell);
  }
  Py_XDECREF(previous.key);
  if (i == count) return cells;
  lean_array_set_size(cells, i);
  lean_dec(cells);
  return NULL;
}

/* Add each value cell to the type cell at the same position. */
static int
record_values(PyObject* items, lean_object* cells)
{
  size_t count = (size_t) PyTuple_GET_SIZE(items);
  if (count != lean_array_size(cells)) return 0;
  record_key previous = {0};
  size_t i = 0;
  for (; i < count; i++) {
    PyObject* key;
    PyObject* body;
    if (!record_entry(PyTuple_GET_ITEM(items, (Py_ssize_t) i), RECORD_ATOM, &key, &body)) break;
    int bytes = PyBytes_CheckExact(body);
    lean_object* data = NULL;
    if (!bytes) {
      data = record_nat(body);
    } else if (PyBytes_GET_SIZE(body) <= RECORD_MAX_BYTES) {
      data = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(body), (size_t) PyBytes_GET_SIZE(body));
    }
    Py_DECREF(body);
    if (!data) {
      Py_DECREF(key);
      break;
    }
    lean_object* payload = lean_alloc_ctor(bytes ? 1 : 0, 1, 0);
    lean_ctor_set(payload, 0, data);
    lean_object* cell = lean_array_get_core(cells, i);
    lean_ctor_set(cell, 3, record_cell_key(key, &previous));
    lean_ctor_set(cell, 4, payload);
  }
  Py_XDECREF(previous.key);
  return i == count;
}

/* A miss leaves the original arguments for the general converter. */
static PyObject*
try_record(PyObject* args, lean_object* (*export)(lean_object*, lean_object*, lean_object*))
{
  if (PyTuple_GET_SIZE(args) != 2) return NULL;
  PyObject* type_key;
  PyObject* types = record_sequence(PyTuple_GET_ITEM(args, 0), &type_key);
  if (!types) return NULL;
  lean_object* cells = record_types(types);
  Py_DECREF(types);
  if (!cells) {
    Py_DECREF(type_key);
    return NULL;
  }
  lean_object* type_tag = record_string(type_key);
  Py_DECREF(type_key);
  PyObject* value_key;
  PyObject* values = record_sequence(PyTuple_GET_ITEM(args, 1), &value_key);
  lean_object* value_tag = NULL;
  if (values) {
    if (record_values(values, cells)) value_tag = record_string(value_key);
    Py_DECREF(values);
    Py_DECREF(value_key);
  }
  if (value_tag) return except_into_pybytes(export(type_tag, value_tag, cells), SSZ_ERROR);
  lean_dec(type_tag);
  lean_dec(cells);
  return NULL;
}

/* ---- Wrappers --------------------------------------------------------- */

/* Limit the cost of a speculative copy when rooting a sequence of byte strings. */
#define SSZ_ROOT_BATCH_MAX_WIDTH ((size_t) 64)

PyObject*
py_ssz_serialize(
  PyObject* self,
  PyObject* args
) {
  PyObject* record = try_record(args, eth_ssz_serialize_record);
  if (record || PyErr_Occurred()) return record;
  return call_pyvalue_export_batch(eth_ssz_serialize, eth_ssz_serialize_bytes_batch,
    eth_ssz_serialize_nat_batch, SIZE_MAX, args, SSZ_ERROR);
}

PyObject*
py_ssz_deserialize(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ssz_deserialize, args, 2, SSZ_ERROR);
}

PyObject*
py_ssz_hash_tree_root(
  PyObject* self,
  PyObject* args
) {
  PyObject* record = try_record(args, eth_ssz_hash_tree_root_record);
  if (record || PyErr_Occurred()) return record;
  return call_pyvalue_export_batch(eth_ssz_hash_tree_root, eth_ssz_hash_tree_root_bytes_batch,
    eth_ssz_hash_tree_root_nat_batch, SSZ_ROOT_BATCH_MAX_WIDTH, args, SSZ_ERROR);
}

PyObject*
py_ssz_generalized_index(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ssz_generalized_index, args, 2, SSZ_ERROR);
}

PyObject*
py_ssz_merkle_proof(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ssz_merkle_proof, args, 3, SSZ_ERROR);
}

PyObject*
py_ssz_merkleize_chunks(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_ssz_merkleize_chunks, args, 2, SSZ_ERROR);
}
