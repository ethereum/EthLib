/* Python wrappers of the proof-of-work exports.
 *
 * The ommer check takes its forks and its blocks in RLP form.
 * The other exports take typed values, which the converter passes. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object* eth_pow_block_difficulty(lean_object*);
extern lean_object* eth_pow_chain_forks(lean_object*);
extern lean_object* eth_pow_seal_hash(lean_object*);
extern lean_object* eth_pow_check(lean_object*);
extern lean_object* eth_pow_validate_ommers(lean_object*, lean_object*, lean_object*, uint8_t);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_pow_block_difficulty(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_pow_block_difficulty, args, 6, BLOCK_ERROR);
}

PyObject*
py_pow_chain_forks(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_pow_chain_forks, args, 1, BLOCK_ERROR);
}

PyObject*
py_pow_seal_hash(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_pow_seal_hash, args, 2, BLOCK_ERROR);
}

PyObject*
py_pow_check(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_pow_check, args, 2, BLOCK_ERROR);
}

PyObject*
py_pow_validate_ommers(
  PyObject* self,
  PyObject* args
) {
  PyObject *forks_obj, *recent_obj, *block_obj;
  int check_seal;
  if (!PyArg_ParseTuple(args, "OOOp", &forks_obj, &recent_obj, &block_obj, &check_seal)) {
    return NULL;
  }
  if (!PyBytes_Check(forks_obj) || !PyBytes_Check(recent_obj) || !PyBytes_Check(block_obj)) {
    PyErr_SetString(PyExc_TypeError, "forks, recent and block must be bytes");
    return NULL;
  }
  lean_object* forks = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(forks_obj), (size_t) PyBytes_GET_SIZE(forks_obj));
  lean_object* recent = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(recent_obj), (size_t) PyBytes_GET_SIZE(recent_obj));
  lean_object* block = mk_bytearray(
    (const uint8_t*) PyBytes_AS_STRING(block_obj), (size_t) PyBytes_GET_SIZE(block_obj));
  return except_into_pybool(
    eth_pow_validate_ommers(forks, recent, block, (uint8_t) check_seal), BLOCK_ERROR);
}
