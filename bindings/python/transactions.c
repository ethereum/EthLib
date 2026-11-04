/* Transaction wrappers around the `eth_tx_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_tx_type(
  lean_object* fork,
  lean_object* tx
);

extern lean_object*
eth_tx_hash(
  lean_object* fork,
  lean_object* tx
);

extern lean_object*
eth_tx_network_check(
  lean_object* fork,
  lean_object* network
);

extern lean_object*
eth_tx_recover_sender(
  lean_object* fork,
  lean_object* tx
);

extern lean_object*
eth_tx_intrinsic_gas(
  lean_object* fork,
  lean_object* tx
);

extern lean_object*
eth_tx_check(
  lean_object* fork,
  uint64_t chain_id,
  lean_object* tx
);

/* ---- Wrappers --------------------------------------------------------- */

/* Read a fork name and the bytes of a transaction, as Lean byte arrays.
 *
 * It returns 0 with a TypeError set when an argument has the wrong type. */
static int
parse_fork_and_tx(
  PyObject* fork_obj,
  PyObject* tx_obj,
  lean_object** fork,
  lean_object** tx
) {
  if (!PyUnicode_Check(fork_obj)) {
    PyErr_SetString(PyExc_TypeError, "fork must be str");
    return 0;
  }
  if (!PyBytes_Check(tx_obj)) {
    PyErr_SetString(PyExc_TypeError, "tx must be bytes");
    return 0;
  }
  Py_ssize_t len;
  const char* utf8 = PyUnicode_AsUTF8AndSize(fork_obj, &len);
  if (!utf8) return 0;
  *fork = mk_bytearray((const uint8_t*) utf8, len);
  *tx = mk_bytearray((const uint8_t*) PyBytes_AS_STRING(tx_obj), PyBytes_GET_SIZE(tx_obj));
  return 1;
}

/* Read the two arguments `(fork, tx)`. */
static int
parse_args(
  PyObject* args,
  lean_object** fork,
  lean_object** tx
) {
  PyObject *fork_obj, *tx_obj;
  if (!PyArg_ParseTuple(args, "OO", &fork_obj, &tx_obj)) return 0;
  return parse_fork_and_tx(fork_obj, tx_obj, fork, tx);
}

PyObject*
py_tx_type(
  PyObject* self,
  PyObject* args
) {
  lean_object *fork, *tx;
  if (!parse_args(args, &fork, &tx)) return NULL;
  return except_into_pyint(eth_tx_type(fork, tx), TRANSACTION_ERROR);
}

PyObject*
py_tx_hash(
  PyObject* self,
  PyObject* args
) {
  lean_object *fork, *tx;
  if (!parse_args(args, &fork, &tx)) return NULL;
  return except_into_pybytes(eth_tx_hash(fork, tx), TRANSACTION_ERROR);
}

PyObject*
py_tx_recover_sender(
  PyObject* self,
  PyObject* args
) {
  lean_object *fork, *tx;
  if (!parse_args(args, &fork, &tx)) return NULL;
  return except_into_pybytes(eth_tx_recover_sender(fork, tx), TRANSACTION_ERROR);
}

PyObject*
py_tx_intrinsic_gas(
  PyObject* self,
  PyObject* args
) {
  lean_object *fork, *tx;
  if (!parse_args(args, &fork, &tx)) return NULL;
  return except_into_pyint(eth_tx_intrinsic_gas(fork, tx), TRANSACTION_ERROR);
}

PyObject*
py_tx_check(
  PyObject* self,
  PyObject* args
) {
  PyObject *fork_obj, *chain_obj, *tx_obj;
  if (!PyArg_ParseTuple(args, "OOO", &fork_obj, &chain_obj, &tx_obj)) return NULL;
  /* The chain is a non-negative integer below 2^64. */
  uint64_t chain_id = (uint64_t) PyLong_AsUnsignedLongLong(chain_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object *fork, *tx;
  if (!parse_fork_and_tx(fork_obj, tx_obj, &fork, &tx)) return NULL;
  return except_into_pybytes(eth_tx_check(fork, chain_id, tx), TRANSACTION_ERROR);
}

PyObject*
py_tx_network_check(
  PyObject* self,
  PyObject* args
) {
  lean_object *fork, *network;
  if (!parse_args(args, &fork, &network)) return NULL;
  return except_into_pybytes(eth_tx_network_check(fork, network), TRANSACTION_ERROR);
}
