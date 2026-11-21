module

public import EthLib.Execution.Exports.Network
public import EthLib.Execution.Exports.Snap
public import EthLib.Execution.Proofs.Network.Message
import all EthLib.Execution.Exports.Network
import all EthLib.Execution.Exports.Snap

/-!
# Proofs: the decoding exports of the eth and snap messages

Once the version and the message read, each export returns its data.

That data is what encoding the decoded message gives.
-/

@[expose] public section

namespace EthLib.Execution.Network.Exports

/-- Once the version and the message read, the eth export returns the data. -/
theorem decodeExport_eq_ok {version id : UInt64} {data : ByteArray} {v : EthVersion}
    {m : Message} (hv : readVersion version = .ok v)
    (hm : Message.decode v id.toNat data = .ok m) :
    decodeExport version id data = .ok data := by
  simp [decodeExport, hv, hm, bind, Except.bind, Except.mapError, pure, Except.pure]

/-- The data that the eth export returns is the encoding of the decoded message. -/
theorem decodeExport_eq_encode {version id : UInt64} {data : ByteArray} {v : EthVersion}
    {m : Message} (hv : readVersion version = .ok v)
    (hm : Message.decode v id.toNat data = .ok m) :
    decodeExport version id data = m.encode.mapError fun e => (e.code, ethMessage e) := by
  simp [decodeExport_eq_ok hv hm, Message.encode_of_decode hm, Except.mapError]

end EthLib.Execution.Network.Exports

namespace EthLib.Execution.Network.Snap.Exports

/-- Once the version and the message read, the snap export returns the data. -/
theorem decodeExport_eq_ok {version id : UInt64} {data : ByteArray} {v : SnapVersion}
    {m : SnapMessage} (hv : readVersion version = .ok v)
    (hm : SnapMessage.decode v id.toNat data = .ok m) :
    decodeExport version id data = .ok data := by
  simp [decodeExport, run, hv, hm, bind, Except.bind, Except.mapError, pure, Except.pure]

/-- The data that the snap export returns is the encoding of the decoded message. -/
theorem decodeExport_eq_encode {version id : UInt64} {data : ByteArray} {v : SnapVersion}
    {m : SnapMessage} (hv : readVersion version = .ok v)
    (hm : SnapMessage.decode v id.toNat data = .ok m) :
    decodeExport version id data = run m.encode := by
  simp [decodeExport_eq_ok hv hm, SnapMessage.encode_of_decode hm, run, Except.mapError]

end EthLib.Execution.Network.Snap.Exports
