module

public import EthLib.Base.Exports.Fin
public import EthLib.Networking.Exports.Quic
public import EthLib.Networking.Exports.TlsCertificate
public import EthLib.Networking.Quic.Tls.Handshake

/-!
# Exports of the libp2p QUIC certificate handshake

Every caller supplies an algorithm policy and the private inputs of one handshake.

The returned messages carry their QUIC encryption levels.

Error codes are the QUIC connection errors of RFC 9001 §4.8.
-/

public section

namespace EthLib.Networking.Quic.Tls.Handshake.Exports

open EthLib.Exports (Result PyValue pyExport ToPy FromPy PlainPy LawfulPy fromPy)
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

/-- Report a failed TLS transition with its QUIC connection error code. -/
def stepResult {α : Type} (value : Except Error α) : Result α :=
  value.mapError fun e => (e.code, s!"TLS handshake rejected: {reprStr e}")

/-- Start a client certificate handshake under an explicit policy, RFC 8446 §4.1.2. -/
@[export eth_quic_tls_client_start]
def clientStartExport (args : PyValue) : Result PyValue :=
  pyExport (fun (config : Config) => stepResult (clientStart config)) args

/-- Start a server certificate handshake under an explicit policy, RFC 8446 §4.1.2. -/
@[export eth_quic_tls_server_start]
def serverStartExport (args : PyValue) : Result PyValue :=
  pyExport (fun (config : Config) => stepResult (serverStart config)) args

/-- Process one complete server message and check the intended peer ID at authentication. -/
@[export eth_quic_tls_client_step]
def clientStepExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((config, expected, state, message) :
      Config × ByteArray × State × FlightMessage) =>
    stepResult (clientStep config expected state message)) args

/-- Process one complete client message and require libp2p client authentication. -/
@[export eth_quic_tls_server_step]
def serverStepExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((config, state, message) : Config × State × FlightMessage) =>
    stepResult (serverStep config state message)) args

end EthLib.Networking.Quic.Tls.Handshake.Exports
