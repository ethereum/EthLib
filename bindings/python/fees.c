/* Python wrappers of the base fee and blob base fee exports.
 *
 * They take and return typed values, which the generic converter passes. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export takes the tuple of the arguments as one value, and consumes it. */

extern lean_object* eth_fees_base_fee_per_gas(lean_object*);
extern lean_object* eth_fees_fake_exponential(lean_object*);
extern lean_object* eth_fees_base_fee_per_blob_gas(lean_object*);
extern lean_object* eth_fees_excess_blob_gas(lean_object*);
extern lean_object* eth_fees_blob_data_fee(lean_object*);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_fees_base_fee_per_gas(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_fees_base_fee_per_gas, args, 3, FEES_ERROR);
}

PyObject*
py_fees_fake_exponential(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_fees_fake_exponential, args, 3, FEES_ERROR);
}

PyObject*
py_fees_base_fee_per_blob_gas(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_fees_base_fee_per_blob_gas, args, 2, FEES_ERROR);
}

PyObject*
py_fees_excess_blob_gas(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_fees_excess_blob_gas, args, 4, FEES_ERROR);
}

PyObject*
py_fees_blob_data_fee(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_fees_blob_data_fee, args, 3, FEES_ERROR);
}
