module

public import EthLib.Cryptography.Secp256k1.Address
public import EthLib.Cryptography.Secp256k1.Recovery
public import EthLib.Execution.Transactions.Envelope

/-!
# `Transactions.Signature`

The hash that the sender signs, and the sender that a signature names.

A transaction carries a secp256k1 signature `(r, s)` and a recovery id, the parity of `y` of `R`.

The sender is the address of the public key that the signature recovers.

Appendix F of the Yellow Paper, Shanghai version, defines the recovery.

Source: [`Paper.tex` at `efc5f9a`][yp].

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Secp256k1

/-! ## The signing hashes -/

/-- The Keccak-256 hash of the encoding of a list of items. -/
def hashItems (items : List Item) : Except RlpError Hash32 := do
  -- Yellow Paper, Appendix F: `h(T) = KEC(RLP(L_X(T)))` for `T_x = 0`.
  return Cryptography.Hash.Keccak.keccak256 (← encode (.list items))

/-- The Keccak-256 hash of a type byte, then the encoding of a list of items. -/
def hashTypedItems (type : UInt8) (items : List Item) : Except RlpError Hash32 := do
  -- Yellow Paper, Appendix F: `h(T) = KEC(T_x · RLP(L_X(T)))` for a typed transaction.
  return Cryptography.Hash.Keccak.keccak256 (typedBytes type (← encode (.list items)))

/-- The six fields of a legacy transaction that every legacy signature covers. -/
def LegacyTransaction.signedItems (tx : LegacyTransaction) : List Item :=
  -- `(T_n, T_p, T_g, T_t, T_v, p)`, where `p = T_i` if `T_t = ∅`, else `p = T_d`.
  [Codec.toItem tx.nonce, Codec.toItem tx.gasPrice, Codec.toItem tx.gas, Codec.toItem tx.to,
    Codec.toItem tx.value, Codec.toItem tx.data]

/-- The hash of a legacy transaction that signs no chain: the hash of its six fields. -/
def signingHashPre155 (tx : LegacyTransaction) : Except RlpError Hash32 :=
  -- `L_X(T) = (T_n, T_p, T_g, T_t, T_v, p)` for `T_w` in `{27, 28}`.
  hashItems tx.signedItems

/-- The hash of a legacy transaction that signs the chain `chainId`.

[EIP-155](https://eips.ethereum.org/EIPS/eip-155#specification) appends the chain, 0 and 0. -/
def signingHash155 (tx : LegacyTransaction) (chainId : U256) : Except RlpError Hash32 :=
  -- `L_X(T) = (T_n, T_p, T_g, T_t, T_v, p, beta, (), ())` for `T_w` in `{2beta + 35, 2beta + 36}`.
  --
  -- The scalar 0 and the empty string `()` both encode as the byte `0x80`.
  hashItems
    (tx.signedItems ++ [Codec.toItem chainId, Codec.toItem (0 : Nat), Codec.toItem (0 : Nat)])

/-- The hash of a transaction of type 1: its type, then its fields before the signature.

[EIP-2930](https://eips.ethereum.org/EIPS/eip-2930#specification) defines it. -/
def signingHash2930 (tx : AccessListTransaction) : Except RlpError Hash32 :=
  -- `L_X(T) = (T_c, T_n, T_p, T_g, T_t, T_v, p, T_A)` for `T_x = 1`.
  hashTypedItems 1 [Codec.toItem tx.chainId, Codec.toItem tx.nonce, Codec.toItem tx.gasPrice,
    Codec.toItem tx.gas, Codec.toItem tx.to, Codec.toItem tx.value, Codec.toItem tx.data,
    Codec.toItem tx.accessList]

/-- The hash of a transaction of type 2: its type, then its fields before the signature.

[EIP-1559](https://eips.ethereum.org/EIPS/eip-1559#specification) defines it. -/
def signingHash1559 (tx : FeeMarketTransaction) : Except RlpError Hash32 :=
  -- `L_X(T) = (T_c, T_n, T_f, T_m, T_g, T_t, T_v, p, T_A)` for `T_x = 2`.
  hashTypedItems 2 [Codec.toItem tx.chainId, Codec.toItem tx.nonce,
    Codec.toItem tx.maxPriorityFeePerGas, Codec.toItem tx.maxFeePerGas, Codec.toItem tx.gas,
    Codec.toItem tx.to, Codec.toItem tx.value, Codec.toItem tx.data, Codec.toItem tx.accessList]

/-- The hash of a transaction of type 3: its type, then its fields before the signature.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#signature) defines it. -/
def signingHash4844 (tx : BlobTransaction) : Except RlpError Hash32 :=
  -- EIP-4844: `h(T) = KEC(3 · RLP(L_X(T)))`, with `L_X(T)` of `T_x = 2`.
  --
  -- That list is followed by the maximum fee per blob gas and the versioned hashes.
  hashTypedItems 3 [Codec.toItem tx.chainId, Codec.toItem tx.nonce,
    Codec.toItem tx.maxPriorityFeePerGas, Codec.toItem tx.maxFeePerGas, Codec.toItem tx.gas,
    Codec.toItem tx.to, Codec.toItem tx.value, Codec.toItem tx.data, Codec.toItem tx.accessList,
    Codec.toItem tx.maxFeePerBlobGas, Codec.toItem tx.blobVersionedHashes]

/-- The hash of a transaction of type 4: its type, then its fields before the signature.

[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702#set-code-transaction) defines it. -/
def signingHash7702 (tx : SetCodeTransaction) : Except RlpError Hash32 :=
  -- EIP-7702: `h(T) = KEC(4 · RLP(L_X(T)))`, with `L_X(T)` of `T_x = 2`.
  --
  -- That list is followed by the authorization list.
  --
  -- The EIP signs its whole payload, which holds `T_y, T_r, T_s`; here those three are left out.
  hashTypedItems 4 [Codec.toItem tx.chainId, Codec.toItem tx.nonce,
    Codec.toItem tx.maxPriorityFeePerGas, Codec.toItem tx.maxFeePerGas, Codec.toItem tx.gas,
    Codec.toItem tx.to, Codec.toItem tx.value, Codec.toItem tx.data, Codec.toItem tx.accessList,
    Codec.toItem tx.authorizations]

/-! ## The recovery id and the chain -/

/-- The chain and the recovery id that the `v` of a legacy transaction holds at `fork`.

A `v` of 27 or 28 is the recovery id plus 27, and signs no chain.

From Spurious Dragon, `v = 35 + 2 c + y` signs the chain `c` with the recovery id `y`.

[EIP-155](https://eips.ethereum.org/EIPS/eip-155#specification) adds that form.

A chain of 2^64 or more is invalid.

No EIP fixes that bound, and EIP-2294, which is Stagnant, only suggests one.

Any other `v` is invalid. -/
def legacyRecovery (fork : Fork) (v : U256) : Except TransactionError (Option U256 × Fin 2) :=
  -- Yellow Paper, Appendix F: `v = T_w - 27` for `T_w` in `{27, 28}`.
  if v.toNat = 27 then .ok (none, 0)
  else if v.toNat = 28 then .ok (none, 1)
  -- From Spurious Dragon, by EIP-155: `T_w = 2beta + 35 + v` (Yellow Paper, §4.2).
  --
  -- Here `beta` is read from `T_w` as `(T_w - 35) / 2`, and `v = (T_w - 35) mod 2` (Appendix F).
  --
  -- The source checks `T_w` against the chain of the network; that check is made elsewhere.
  --
  -- The bound `beta < 2^64` is EthLib's own.
  else if fork ≥ .spuriousDragon then
    if 35 ≤ v.toNat ∧ (v.toNat - 35) / 2 < 2 ^ 64 then
      .ok (some (BitVec.ofNat 256 ((v.toNat - 35) / 2)), Fin.ofNat 2 ((v.toNat - 35) % 2))
    else .error .invalidSignature
  else .error .invalidSignature

/-- The recovery id of a typed transaction: its parity, which must be 0 or 1. -/
def parityRecovery (yParity : U256) : Except TransactionError (Fin 2) :=
  -- Yellow Paper, Appendix F: `v = T_y` for `T_x` in `{1, 2}`, and EIP-4844 and EIP-7702 keep it.
  --
  -- The signature is invalid unless `v` is in `{0, 1}`.
  if yParity.toNat = 0 then .ok 0
  else if yParity.toNat = 1 then .ok 1
  else .error .invalidSignature

/-- The chain of a transaction at `fork`, or none for a legacy transaction that signs no chain. -/
def Transaction.chainId (fork : Fork) : Transaction → Except TransactionError (Option U256)
  -- `beta` of a legacy `T_w`, and `T_c` of a typed transaction.
  | .legacy tx => Prod.fst <$> legacyRecovery fork tx.v
  | .accessList tx => .ok (some (.ofNat 256 tx.chainId.toNat))
  | .feeMarket tx => .ok (some (.ofNat 256 tx.chainId.toNat))
  | .blob tx => .ok (some (.ofNat 256 tx.chainId.toNat))
  | .setCode tx => .ok (some (.ofNat 256 tx.chainId.toNat))

/-- The first integer of the signature of a transaction. -/
def Transaction.r : Transaction → U256
  | .legacy tx => tx.r
  | .accessList tx => tx.r
  | .feeMarket tx => tx.r
  | .blob tx => tx.r
  | .setCode tx => tx.r

/-- The second integer of the signature of a transaction. -/
def Transaction.s : Transaction → U256
  | .legacy tx => tx.s
  | .accessList tx => tx.s
  | .feeMarket tx => tx.s
  | .blob tx => tx.s
  | .setCode tx => tx.s

/-- The hash that the sender of a transaction signs at `fork`, and the recovery id. -/
def signingInput (fork : Fork) : Transaction → Except TransactionError (Hash32 × Fin 2)
  | .legacy tx => do
    let (chain, id) ← legacyRecovery fork tx.v
    -- `L_X(T)` has six items for `T_w` in `{27, 28}`, and nine, with `beta`, otherwise.
    let hash ← (match chain with
      | none => signingHashPre155 tx
      | some c => signingHash155 tx c).mapError .encoding
    return (hash, id)
  -- `h(T)` and `v = T_y`, as for `T_x` in `{1, 2}`, for each typed transaction.
  | .accessList tx => do
    return (← (signingHash2930 tx).mapError .encoding, ← parityRecovery tx.yParity)
  | .feeMarket tx => do
    return (← (signingHash1559 tx).mapError .encoding, ← parityRecovery tx.yParity)
  | .blob tx => do
    return (← (signingHash4844 tx).mapError .encoding, ← parityRecovery tx.yParity)
  | .setCode tx => do
    return (← (signingHash7702 tx).mapError .encoding, ← parityRecovery tx.yParity)

/-! ## The sender -/

/-- Whether `s` is a valid second integer of a transaction signature at `fork`.

It lies in `[1, n - 1]`, and from Homestead it is at most `n / 2`.

[EIP-2][eip-2] adds that bound, so each signature has one form.

[eip-2]: https://eips.ethereum.org/EIPS/eip-2#specification -/
def validS (fork : Fork) (s : Nat) : Bool :=
  -- Yellow Paper, Appendix F: `0 < s < secp256k1n / 2 + 1`, by EIP-2 from Homestead.
  if fork ≥ .homestead then 0 < s && Ecdsa.isLowS s
  -- Before Homestead, as EIP-2 states: `0 < s < secp256k1n`.
  else 0 < s && s < Fn.modulus

/-- The sender of a transaction at `fork`: the address of the key that its signature recovers.

`r` lies in `[1, n - 1]`, and `s` must pass the rule of its fork. -/
def recoverSender (fork : Fork) (tx : Transaction) : Except TransactionError Address :=
  -- Yellow Paper, Appendix F: the signature is invalid unless `0 < r < secp256k1n`.
  --
  -- And unless `s` passes the bound of its fork.
  if 0 < tx.r.toNat ∧ tx.r.toNat < Fn.modulus ∧ validS fork tx.s.toNat then do
    -- `h(T)` and `v`, which must be in `{0, 1}`.
    let (hash, id) ← signingInput fork tx
    -- `S(T) = B_96..255(KEC(ECDSARECOVER(h(T), v, T_r, T_s)))`.
    match Ecdsa.recover hash tx.r.toNat tx.s.toNat id with
    | .ok (.affine x y) => return address x y
    -- A recovery that fails, or gives the point at infinity, leaves the signature invalid.
    | _ => .error .invalidSignature
  else .error .invalidSignature

end EthLib.Execution.Transactions
