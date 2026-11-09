module

public import EthLib.Base.Base64

/-!
# Base64 names retained for ENR users

The shared base64url implementation is in `EthLib.Base.Base64`.
-/

public section

namespace EthLib.Networking.Enr.Base64

export EthLib.Base.Base64 (Base64Error encodeSextet decodeSextet encodeList readSextet decodeList
  encode decode)

namespace Base64Error

export EthLib.Base.Base64.Base64Error (invalidChar invalidLength nonZeroPadBits)

end Base64Error

end EthLib.Networking.Enr.Base64
