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

extern lean_object*
eth_tx_check_in_block(
  lean_object* fork,
  uint64_t chain_id,
  lean_object* tx,
  lean_object* state,
  lean_object* gas_limit,
  lean_object* gas_used,
  lean_object* blob_gas_used,
  lean_object* base_fee,
  lean_object* excess_blob_gas
);

extern lean_object*
eth_tx_settle(
  lean_object* fork,
  lean_object* tx,
  lean_object* base_fee,
  lean_object* gas_left,
  lean_object* refund_counter
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
py_tx_check_in_block(
  PyObject* self,
  PyObject* args
) {
  PyObject *fork_obj, *chain_obj, *tx_obj;
  const char* data[6];
  Py_ssize_t len[6];
  if (!PyArg_ParseTuple(args, "OOOy#y#y#y#y#y#", &fork_obj, &chain_obj, &tx_obj,
                        &data[0], &len[0], &data[1], &len[1], &data[2], &len[2],
                        &data[3], &len[3], &data[4], &len[4], &data[5], &len[5])) {
    return NULL;
  }
  /* The chain is a non-negative integer below 2^64. */
  uint64_t chain_id = (uint64_t) PyLong_AsUnsignedLongLong(chain_obj);
  if (PyErr_Occurred()) return NULL;
  lean_object *fork, *tx;
  if (!parse_fork_and_tx(fork_obj, tx_obj, &fork, &tx)) return NULL;
  lean_object* arg[6];
  for (int i = 0; i < 6; i++) {
    arg[i] = mk_bytearray((const uint8_t*) data[i], (size_t) len[i]);
  }
  return except_into_pybytes(
    eth_tx_check_in_block(fork, chain_id, tx, arg[0], arg[1], arg[2], arg[3], arg[4], arg[5]),
    TRANSACTION_ERROR);
}

PyObject*
py_tx_settle(
  PyObject* self,
  PyObject* args
) {
  PyObject *fork_obj, *tx_obj;
  const char *base_fee, *gas_left, *refund_counter;
  Py_ssize_t base_fee_len, gas_left_len, refund_counter_len;
  if (!PyArg_ParseTuple(args, "OOy#y#y#", &fork_obj, &tx_obj, &base_fee, &base_fee_len,
                        &gas_left, &gas_left_len, &refund_counter, &refund_counter_len)) {
    return NULL;
  }
  lean_object *fork, *tx;
  if (!parse_fork_and_tx(fork_obj, tx_obj, &fork, &tx)) return NULL;
  return except_into_pybytes(
    eth_tx_settle(fork, tx,
                  mk_bytearray((const uint8_t*) base_fee, (size_t) base_fee_len),
                  mk_bytearray((const uint8_t*) gas_left, (size_t) gas_left_len),
                  mk_bytearray((const uint8_t*) refund_counter, (size_t) refund_counter_len)),
    TRANSACTION_ERROR);
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
