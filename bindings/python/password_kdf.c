/* Python wrappers of PBKDF2 and the scrypt steps of RFC 7914. */
#include "wrappers.h"

/* Each export consumes its object arguments. */
extern lean_object* eth_pbkdf2_sha256(
  lean_object* password, lean_object* salt, uint64_t iterations, uint64_t length);
extern lean_object* eth_salsa208(lean_object* block);
extern lean_object* eth_scrypt_block_mix(lean_object* block, uint64_t r);
extern lean_object* eth_scrypt_romix(lean_object* block, uint64_t n, uint64_t r);
extern lean_object* eth_scrypt(
  lean_object* password, lean_object* salt, uint64_t n, uint64_t r, uint64_t p, uint64_t length);

static int
parse_bytes(PyObject* obj, const char* name, lean_object** out) {
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s must be bytes", name);
    return 1;
  }
  *out = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(obj), (size_t) PyBytes_GET_SIZE(obj));
  return 0;
}

PyObject*
py_pbkdf2_sha256(
  PyObject* self,
  PyObject* args
) {
  PyObject *password_obj, *salt_obj, *iterations_obj, *length_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &password_obj, &salt_obj, &iterations_obj, &length_obj))
    return NULL;
  uint64_t iterations = PyLong_AsUnsignedLongLong(iterations_obj);
  if (PyErr_Occurred()) return NULL;
  uint64_t length = PyLong_AsUnsignedLongLong(length_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object *password, *salt;
  if (parse_bytes(password_obj, "password", &password)) return NULL;
  if (parse_bytes(salt_obj, "salt", &salt)) { lean_dec(password); return NULL; }
  return except_into_pybytes(
    eth_pbkdf2_sha256(password, salt, iterations, length), PBKDF2_ERROR);
}

PyObject*
py_salsa208(
  PyObject* self,
  PyObject* args
) {
  PyObject* block_obj;
  if (!PyArg_ParseTuple(args, "O", &block_obj)) return NULL;
  lean_object* block;
  if (parse_bytes(block_obj, "block", &block)) return NULL;
  return except_into_pybytes(eth_salsa208(block), SCRYPT_ERROR);
}

PyObject*
py_scrypt_block_mix(
  PyObject* self,
  PyObject* args
) {
  PyObject *block_obj, *r_obj;
  if (!PyArg_ParseTuple(args, "OO", &block_obj, &r_obj)) return NULL;
  uint64_t r = PyLong_AsUnsignedLongLong(r_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object* block;
  if (parse_bytes(block_obj, "block", &block)) return NULL;
  return except_into_pybytes(eth_scrypt_block_mix(block, r), SCRYPT_ERROR);
}

PyObject*
py_scrypt_romix(
  PyObject* self,
  PyObject* args
) {
  PyObject *block_obj, *n_obj, *r_obj;
  if (!PyArg_ParseTuple(args, "OOO", &block_obj, &n_obj, &r_obj)) return NULL;
  uint64_t n = PyLong_AsUnsignedLongLong(n_obj);
  if (PyErr_Occurred()) return NULL;
  uint64_t r = PyLong_AsUnsignedLongLong(r_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object* block;
  if (parse_bytes(block_obj, "block", &block)) return NULL;
  return except_into_pybytes(eth_scrypt_romix(block, n, r), SCRYPT_ERROR);
}

PyObject*
py_scrypt(
  PyObject* self,
  PyObject* args
) {
  PyObject *password_obj, *salt_obj, *n_obj, *r_obj, *p_obj, *length_obj;
  if (!PyArg_ParseTuple(args, "OOOOOO", &password_obj, &salt_obj,
      &n_obj, &r_obj, &p_obj, &length_obj)) return NULL;
  uint64_t n = PyLong_AsUnsignedLongLong(n_obj);
  if (PyErr_Occurred()) return NULL;
  uint64_t r = PyLong_AsUnsignedLongLong(r_obj);
  if (PyErr_Occurred()) return NULL;
  uint64_t p = PyLong_AsUnsignedLongLong(p_obj);
  if (PyErr_Occurred()) return NULL;
  uint64_t length = PyLong_AsUnsignedLongLong(length_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object *password, *salt;
  if (parse_bytes(password_obj, "password", &password)) return NULL;
  if (parse_bytes(salt_obj, "salt", &salt)) { lean_dec(password); return NULL; }
  return except_into_pybytes(eth_scrypt(password, salt, n, r, p, length), SCRYPT_ERROR);
}
