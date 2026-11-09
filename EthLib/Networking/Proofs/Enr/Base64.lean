module

public import EthLib.Base.Proofs.Base64
public import EthLib.Networking.Enr.Base64

/-!
# Base64 proof names retained for ENR users

The shared base64url proofs are in `EthLib.Base.Base64`.
-/

public section

namespace EthLib.Networking.Enr.Base64

export EthLib.Base.Base64 (decodeSextet_encodeSextet readSextet_encodeSextet
  decodeList_encodeList decode_encode encodeSextet_of_decodeSextet encodeSextet_of_readSextet
  encodeList_decodeList encode_decode)

end EthLib.Networking.Enr.Base64
