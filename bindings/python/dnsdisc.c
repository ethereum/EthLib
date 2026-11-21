/* DNS node list wrappers around the `eth_dnsdisc_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_dnsdisc_parse_entry(
  lean_object* args
);

extern lean_object*
eth_dnsdisc_subdomain(
  lean_object* args
);

extern lean_object*
eth_dnsdisc_verify_root(
  lean_object* args
);

extern lean_object*
eth_dnsdisc_parse_url(
  lean_object* args
);

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_dnsdisc_parse_entry(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_dnsdisc_parse_entry, args, 1, DNSDISC_ERROR);
}

PyObject*
py_dnsdisc_subdomain(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_dnsdisc_subdomain, args, 1, DNSDISC_ERROR);
}

PyObject*
py_dnsdisc_verify_root(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_dnsdisc_verify_root, args, 2, DNSDISC_ERROR);
}

PyObject*
py_dnsdisc_parse_url(
  PyObject* self,
  PyObject* args
) {
  return call_pyvalue_export(eth_dnsdisc_parse_url, args, 1, DNSDISC_ERROR);
}
