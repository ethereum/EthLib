module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Hash.Tls13

/-!
# Exports: TLS 1.3 labelled HKDF

The C exports of `HkdfLabel` and HKDF-Expand-Label, RFC 8446 §7.1, for the Python bindings.

A rejected field returns the code and the message of its error.

The secret is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

public section

namespace EthLib.Cryptography.Hash.Tls13.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- The code and the message of a TLS 1.3 derivation error. -/
def ofExcept {α : Type} (r : Except Error α) : Result α :=
  r.mapError fun e => (e.code, reprStr e)

/-- The HkdfLabel of RFC 8446 §7.1, for a label without its `tls13 ` prefix. -/
@[export eth_tls13_hkdf_label]
def labelExport (args : PyValue) : Result PyValue :=
  pyExport (fun (label, context, length) => ofExcept (hkdfLabel label context length)) args

/-- Expand a SHA-256 secret with a TLS 1.3 label and context, RFC 8446 §7.1. -/
@[export eth_tls13_expand_label]
def expandExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret, label, context, length) =>
    ofExcept ((expandLabel secret label context length).map Base.packBytes)) args

end EthLib.Cryptography.Hash.Tls13.Exports
