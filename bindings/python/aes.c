/* Python wrappers of the AES, CTR and GCM exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object* eth_aes_encrypt_block(lean_object* key, lean_object* block);
extern lean_object* eth_aes_decrypt_block(lean_object* key, lean_object* block);
extern lean_object* eth_aes_ctr(lean_object* key, lean_object* counter, lean_object* data);
extern lean_object* eth_aes_gcm_encrypt(
  lean_object* key, lean_object* iv, lean_object* plaintext, lean_object* aad,
  uint64_t tag_length);
extern lean_object* eth_aes_gcm_decrypt(
  lean_object* key, lean_object* iv, lean_object* ciphertext, lean_object* aad,
  lean_object* tag, uint64_t tag_length);

/* ---- Helpers ---------------------------------------------------------- */

/* Copy `count` `bytes` arguments into Lean ByteArrays.
 * On a non-`bytes` argument, free the copies made so far, raise `TypeError` and return 1. */
static int
parse_all_bytes(
  PyObject** objs,
  const char** names,
  lean_object** out,
  int count
) {
  for (int i = 0; i < count; i++) {
    if (!PyBytes_Check(objs[i])) {
      for (int j = 0; j < i; j++) lean_dec(out[j]);
      PyErr_Format(PyExc_TypeError, "%s must be bytes", names[i]);
      return 1;
    }
    out[i] = mk_bytearray(
      (const uint8_t*) PyBytes_AS_STRING(objs[i]), (size_t) PyBytes_GET_SIZE(objs[i]));
  }
  return 0;
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_aes_encrypt_block(
  PyObject* self,
  PyObject* args
) {
  PyObject* objs[2];
  const char* names[2] = {"key", "block"};
  lean_object* in[2];
  if (!PyArg_ParseTuple(args, "OO", &objs[0], &objs[1])) return NULL;
  if (parse_all_bytes(objs, names, in, 2)) return NULL;
  return except_into_pybytes(eth_aes_encrypt_block(in[0], in[1]), AES_ERROR);
}

PyObject*
py_aes_decrypt_block(
  PyObject* self,
  PyObject* args
) {
  PyObject* objs[2];
  const char* names[2] = {"key", "block"};
  lean_object* in[2];
  if (!PyArg_ParseTuple(args, "OO", &objs[0], &objs[1])) return NULL;
  if (parse_all_bytes(objs, names, in, 2)) return NULL;
  return except_into_pybytes(eth_aes_decrypt_block(in[0], in[1]), AES_ERROR);
}

PyObject*
py_aes_ctr(
  PyObject* self,
  PyObject* args
) {
  PyObject* objs[3];
  const char* names[3] = {"key", "initial_counter", "data"};
  lean_object* in[3];
  if (!PyArg_ParseTuple(args, "OOO", &objs[0], &objs[1], &objs[2])) return NULL;
  if (parse_all_bytes(objs, names, in, 3)) return NULL;
  return except_into_pybytes(eth_aes_ctr(in[0], in[1], in[2]), AES_ERROR);
}

PyObject*
py_aes_gcm_encrypt(
  PyObject* self,
  PyObject* args
) {
  PyObject* objs[4];
  const char* names[4] = {"key", "iv", "plaintext", "aad"};
  lean_object* in[4];
  PyObject* tag_length_obj;
  uint64_t tag_length;
  if (!PyArg_ParseTuple(args, "OOOOO", &objs[0], &objs[1], &objs[2], &objs[3], &tag_length_obj))
    return NULL;
  /* Read the length first, so a bad length leaves no Lean object to free. */
  if (parse_uint64(tag_length_obj, "tag_length", &tag_length)) return NULL;
  if (parse_all_bytes(objs, names, in, 4)) return NULL;
  return except_into_pybytes(
    eth_aes_gcm_encrypt(in[0], in[1], in[2], in[3], tag_length), AES_ERROR);
}

PyObject*
py_aes_gcm_decrypt(
  PyObject* self,
  PyObject* args
) {
  PyObject* objs[5];
  const char* names[5] = {"key", "iv", "ciphertext", "aad", "tag"};
  lean_object* in[5];
  PyObject* tag_length_obj;
  uint64_t tag_length;
  if (!PyArg_ParseTuple(args, "OOOOOO", &objs[0], &objs[1], &objs[2], &objs[3], &objs[4],
                        &tag_length_obj))
    return NULL;
  /* Read the length first, so a bad length leaves no Lean object to free. */
  if (parse_uint64(tag_length_obj, "tag_length", &tag_length)) return NULL;
  if (parse_all_bytes(objs, names, in, 5)) return NULL;
  return except_into_pybytes(
    eth_aes_gcm_decrypt(in[0], in[1], in[2], in[3], in[4], tag_length), AES_ERROR);
}
