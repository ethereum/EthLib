/* Python wrappers of the VRF tree exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

extern lean_object*
eth_vrf_verify(
  lean_object* root,
  uint64_t index,
  lean_object* opening
);

extern lean_object*
eth_vrf_secret(
  lean_object* seed,
  uint32_t index
);

extern lean_object*
eth_vrf_evaluate(
  lean_object* seed,
  uint32_t index
);

extern lean_object*
eth_vrf_mix(
  lean_object* output,
  lean_object* randomness
);

/* The size of a seed, of a root, of an output and of the randomness of a mix. */
#define VRF_HASH_SIZE 32

/* ---- Local helpers ---------------------------------------------------- */

/* Read a Python int in [0, max]; returns 0 on success. */
static int
parse_index(
  PyObject* obj,
  unsigned long long max,
  unsigned long long* out
) {
  if (!PyLong_Check(obj)) {
    PyErr_SetString(PyExc_TypeError, "index: expected int");
    return 1;
  }
  unsigned long long v = PyLong_AsUnsignedLongLong(obj);
  if (v == (unsigned long long) -1 && PyErr_Occurred()) return 1;
  if (v > max) {
    PyErr_Format(PyExc_OverflowError, "index: must be at most %llu, got %llu", max, v);
    return 1;
  }
  *out = v;
  return 0;
}

/* Read a 32-byte seed and an index below 2^32; returns 0 on success. */
static int
parse_seed_index(
  PyObject* args,
  const uint8_t** seed,
  uint32_t* index
) {
  PyObject *seed_obj, *index_obj;
  if (!PyArg_ParseTuple(args, "OO", &seed_obj, &index_obj)) return 1;
  *seed = parse_bytes_of_size(seed_obj, VRF_HASH_SIZE, "seed");
  if (!*seed) return 1;
  unsigned long long v;
  if (parse_index(index_obj, UINT32_MAX, &v)) return 1;
  *index = (uint32_t) v;
  return 0;
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_vrf_verify(
  PyObject* self,
  PyObject* args
) {
  /* Any byte strings and any index below 2^64: verification rejects the malformed ones. */
  PyObject *root_obj, *index_obj, *opening_obj;
  if (!PyArg_ParseTuple(args, "OOO", &root_obj, &index_obj, &opening_obj)) return NULL;
  if (!PyBytes_Check(root_obj) || !PyBytes_Check(opening_obj)) {
    PyErr_SetString(PyExc_TypeError, "root and opening must be bytes");
    return NULL;
  }
  unsigned long long index;
  if (parse_index(index_obj, UINT64_MAX, &index)) return NULL;
  lean_object* res = eth_vrf_verify(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(root_obj),
                 (size_t) PyBytes_GET_SIZE(root_obj)),
    (uint64_t) index,
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(opening_obj),
                 (size_t) PyBytes_GET_SIZE(opening_obj)));
  /* The export is total: the output, or no bytes when verification rejects. */
  size_t n = lean_sarray_size(res);
  PyObject* out = n == 0
    ? (Py_INCREF(Py_None), Py_None)
    : PyBytes_FromStringAndSize((const char*) lean_sarray_cptr(res), (Py_ssize_t) n);
  lean_dec(res);
  return out;
}

PyObject*
py_vrf_secret(
  PyObject* self,
  PyObject* args
) {
  const uint8_t* seed;
  uint32_t index;
  if (parse_seed_index(args, &seed, &index)) return NULL;
  return except_into_pybytes(eth_vrf_secret(mk_bytearray(seed, VRF_HASH_SIZE), index), VRF_ERROR);
}

PyObject*
py_vrf_evaluate(
  PyObject* self,
  PyObject* args
) {
  const uint8_t* seed;
  uint32_t index;
  if (parse_seed_index(args, &seed, &index)) return NULL;
  return except_into_pybytes(eth_vrf_evaluate(mk_bytearray(seed, VRF_HASH_SIZE), index), VRF_ERROR);
}

PyObject*
py_vrf_mix(
  PyObject* self,
  PyObject* args
) {
  PyObject *output_obj, *randomness_obj;
  if (!PyArg_ParseTuple(args, "OO", &output_obj, &randomness_obj)) return NULL;
  const uint8_t* output = parse_bytes_of_size(output_obj, VRF_HASH_SIZE, "output");
  if (!output) return NULL;
  const uint8_t* randomness = parse_bytes_of_size(randomness_obj, VRF_HASH_SIZE, "randomness");
  if (!randomness) return NULL;
  return except_into_pybytes(
    eth_vrf_mix(mk_bytearray(output, VRF_HASH_SIZE), mk_bytearray(randomness, VRF_HASH_SIZE)),
    VRF_ERROR);
}
