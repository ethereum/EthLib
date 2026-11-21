module

public import EthLib.Base.Exports.PyValue
public import EthLib.Cryptography.Hash.Tls13

/-!
# Exports: TLS 1.3 labelled HKDF

The C exports of `HkdfLabel` and HKDF-Expand-Label, RFC 8446 §7.1, for the Python bindings.

A rejected field returns the code and the message of its error.

The secret is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

public section

namespace EthLib.Cryptography.Hash.Tls13.Exports

open EthLib.Exports (Result PyValue pyExport ExportError toResult)

/-- An error reaches Python with its code, and its message names the error. -/
instance : ExportError Error where
  code := Error.code
  message := reprStr

/-- The HkdfLabel of RFC 8446 §7.1, for a label without its `tls13 ` prefix. -/
@[export eth_tls13_hkdf_label]
def labelExport (args : PyValue) : Result PyValue :=
  pyExport (fun (label, context, length) => toResult none (hkdfLabel label context length)) args

/-- Expand a SHA-256 secret with a TLS 1.3 label and context, RFC 8446 §7.1. -/
@[export eth_tls13_expand_label]
def expandExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret, label, context, length) =>
    toResult none ((expandLabel secret label context length).map Base.packBytes)) args

end EthLib.Cryptography.Hash.Tls13.Exports
