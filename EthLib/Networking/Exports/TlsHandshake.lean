module

public import EthLib.Base.Exports.Fin
public import EthLib.Networking.Exports.Quic
public import EthLib.Networking.Exports.TlsCertificate
public import EthLib.Networking.Quic.Tls.Handshake

/-!
# Exports of the libp2p QUIC certificate handshake

Every caller supplies an algorithm policy and the private inputs of one handshake.

The returned messages carry their QUIC encryption levels.

Error codes are the QUIC transport errors of RFC 9000 §20.1 and the alert codes of RFC 9001 §4.8.

An argument that Lean cannot read fails with code 0, which is not a QUIC error to forward.
-/

public section

namespace EthLib.Networking.Quic.Tls.Handshake.Exports

open EthLib.Exports (ExportError Result PyValue pyExport toResult ToPy FromPy PlainPy LawfulPy
  fromPy)
open scoped EthLib.Exports.FinAsInt

derive_py KeySchedule
derive_py_laws KeySchedule
derive_py Transcript
derive_py_laws Transcript
derive_py Level
derive_py_laws Level
derive_py FlightMessage
derive_py_laws FlightMessage
derive_py Policy
derive_py_laws Policy
derive_py EphemeralKey
derive_py_laws EphemeralKey
derive_py Config
derive_py_laws Config
derive_py Phase
derive_py_laws Phase
derive_py Retry
derive_py_laws Retry
derive_py Negotiated
derive_py_laws Negotiated
derive_py State
derive_py_laws State
derive_py Completion
derive_py_laws Completion
derive_py Step
derive_py_laws Step

/-- A failed TLS transition reaches Python with its QUIC error code, and the printed error. -/
instance : ExportError Error where
  code := Error.code
  message := reprStr

/-- Start a client certificate handshake under an explicit policy, RFC 8446 §4.1.2. -/
@[export eth_quic_tls_client_start]
def clientStartExport (args : PyValue) : Result PyValue :=
  pyExport (fun (config : Config) => toResult "TLS handshake rejected" (clientStart config)) args

/-- Start a server certificate handshake under an explicit policy. -/
@[export eth_quic_tls_server_start]
def serverStartExport (args : PyValue) : Result PyValue :=
  pyExport (fun (config : Config) => toResult "TLS handshake rejected" (serverStart config)) args

/-- Process one complete server message and check the intended peer ID at authentication. -/
@[export eth_quic_tls_client_step]
def clientStepExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((config, expected, state, message) :
      Config × ByteArray × State × FlightMessage) =>
    toResult "TLS handshake rejected" (clientStep config expected state message)) args

/-- Process one complete client message and require libp2p client authentication. -/
@[export eth_quic_tls_server_step]
def serverStepExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((config, state, message) : Config × State × FlightMessage) =>
    toResult "TLS handshake rejected" (serverStep config state message)) args

end EthLib.Networking.Quic.Tls.Handshake.Exports
