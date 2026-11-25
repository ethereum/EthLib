module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Cryptography.Proofs.HashSig
public import EthLib.Base.Proofs.ByteOrder
public import EthLib.Cryptography.Xmss.Types

/-!
# Proofs: leanXMSS types

Properties of the fixed-size byte objects.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

export EthLib.Base (size_packBytes readBytes_packBytes packBytes_injective)

/-! ## The two layers -/

/-- The bottom layer is layer 0. -/
@[simp] theorem Layer.toNat_bottom : Layer.bottom.toNat = 0 :=
  rfl

/-- The top layer is layer 1. -/
@[simp] theorem Layer.toNat_top : Layer.top.toNat = 1 :=
  rfl

end EthLib.Cryptography.Xmss
