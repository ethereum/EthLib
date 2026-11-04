/* Python wrappers of the HMAC-SHA-256, HKDF and Concatenation KDF exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_hmac_sha256(
  lean_object* key,
  lean_object* message
);

extern lean_object*
eth_hkdf_sha256(
  lean_object* salt,
  lean_object* ikm,
  lean_object* info,
  uint64_t length
);

extern lean_object*
eth_concat_kdf_sha256(
  lean_object* z,
  lean_object* fixed_info,
  uint64_t length
);

/* ---- Helpers ---------------------------------------------------------- */

/* Copy a `bytes` argument into a Lean ByteArray, or raise `TypeError` and return 1. */
static int
parse_bytes(
  PyObject* obj,
  const char* name,
  lean_object** out
) {
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", name);
    return 1;
  }
  *out = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(obj), (size_t) PyBytes_GET_SIZE(obj));
  return 0;
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_hmac_sha256(
  PyObject* self,
  PyObject* args
) {
  PyObject *key_obj, *msg_obj;
  if (!PyArg_ParseTuple(args, "OO", &key_obj, &msg_obj)) return NULL;
  lean_object *key, *msg;
  if (parse_bytes(key_obj, "key", &key)) return NULL;
  if (parse_bytes(msg_obj, "message", &msg)) { lean_dec(key); return NULL; }
  /* The export is total, so its result is the tag itself, not an `IO` result. */
  lean_object* res = eth_hmac_sha256(key, msg);
  PyObject* out = PyBytes_FromStringAndSize(
    (const char*) lean_sarray_cptr(res),
    (Py_ssize_t) lean_sarray_size(res));
  /* The wrapper owns the tag, so it frees it after the copy. */
  lean_dec(res);
  return out;
}

PyObject*
py_hkdf_sha256(
  PyObject* self,
  PyObject* args
) {
  PyObject *salt_obj, *ikm_obj, *info_obj, *length_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &salt_obj, &ikm_obj, &info_obj, &length_obj)) return NULL;
  /* A length outside [0, 2^64) raises OverflowError; Lean rejects one above 255 * 32. */
  unsigned long long length = PyLong_AsUnsignedLongLong(length_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object *salt, *ikm, *info;
  if (parse_bytes(salt_obj, "salt", &salt)) return NULL;
  if (parse_bytes(ikm_obj, "ikm", &ikm)) { lean_dec(salt); return NULL; }
  if (parse_bytes(info_obj, "info", &info)) { lean_dec(salt); lean_dec(ikm); return NULL; }
  return except_into_pybytes(
    eth_hkdf_sha256(salt, ikm, info, (uint64_t) length), HKDF_ERROR);
}

PyObject*
py_concat_kdf_sha256(
  PyObject* self,
  PyObject* args
) {
  PyObject *z_obj, *info_obj, *length_obj;
  if (!PyArg_ParseTuple(args, "OOO", &z_obj, &info_obj, &length_obj)) return NULL;
  /* A length outside [0, 2^64) raises OverflowError. */
  unsigned long long length = PyLong_AsUnsignedLongLong(length_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object *z, *info;
  if (parse_bytes(z_obj, "z", &z)) return NULL;
  if (parse_bytes(info_obj, "fixed_info", &info)) { lean_dec(z); return NULL; }
  return except_into_pybytes(
    eth_concat_kdf_sha256(z, info, (uint64_t) length), CONCAT_KDF_ERROR);
}
