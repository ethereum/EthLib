/* Python wrappers of the Merkle Patricia trie exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_trie_root(
  uint8_t secured,
  lean_object* pairs
);

extern lean_object*
eth_trie_verify_proof(
  lean_object* root,
  uint8_t secured,
  lean_object* key,
  lean_object* proof
);

extern lean_object*
eth_trie_hex_prefix(
  lean_object* args
);

extern lean_object*
eth_trie_verify_account_proof(
  lean_object* args
);

/* ---- Local helpers ---------------------------------------------------- */

/* A Lean ByteArray copy of a Python `bytes`, or NULL with a TypeError set. */
static lean_object*
bytes_arg(
  PyObject* obj,
  const char* name
) {
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", name);
    return NULL;
  }
  return mk_bytearray((const uint8_t*) PyBytes_AS_STRING(obj), (size_t) PyBytes_GET_SIZE(obj));
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_trie_root(
  PyObject* self,
  PyObject* args
) {
  /* Whether the keys are hashed, and the RLP list of the pairs. */
  int secured;
  PyObject* pairs_obj;
  if (!PyArg_ParseTuple(args, "pO", &secured, &pairs_obj)) return NULL;
  lean_object* pairs = bytes_arg(pairs_obj, "pairs");
  if (!pairs) return NULL;
  return except_into_pybytes(eth_trie_root((uint8_t) secured, pairs), TRIE_ERROR);
}

PyObject*
py_trie_verify_proof(
  PyObject* self,
  PyObject* args
) {
  /* The root, whether the keys are hashed, the key, and the RLP list of the nodes. */
  PyObject *root_obj, *key_obj, *proof_obj;
  int secured;
  if (!PyArg_ParseTuple(args, "OpOO", &root_obj, &secured, &key_obj, &proof_obj)) return NULL;
  if (!PyBytes_Check(root_obj) || !PyBytes_Check(key_obj) || !PyBytes_Check(proof_obj)) {
    PyErr_SetString(PyExc_TypeError, "root, key and proof must be bytes");
    return NULL;
  }
  lean_object* res = eth_trie_verify_proof(
    bytes_arg(root_obj, "root"), (uint8_t) secured,
    bytes_arg(key_obj, "key"), bytes_arg(proof_obj, "proof"));
  /* No bytes means that the key is not set, since no value is empty. */
  PyObject* value = except_into_pybytes(res, TRIE_ERROR);
  if (value && PyBytes_GET_SIZE(value) == 0) {
    Py_DECREF(value);
    Py_RETURN_NONE;
  }
  return value;
}

PyObject*
py_trie_hex_prefix(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_trie_hex_prefix, args, 2, TRIE_ERROR);
}

PyObject*
py_trie_verify_account_proof(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_trie_verify_account_proof, args, 2, TRIE_ERROR);
}
