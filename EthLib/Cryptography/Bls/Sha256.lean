/-!
# `Sha256`

A direct transcription of FIPS 180-4 §6.2 (SHA-256). Used by BLS
hash-to-curve (`expand_message_xmd`) and KZG's Fiat-Shamir challenges;
neither needs constant-time, so this is written for clarity.
-/

namespace EthLib.Cryptography.Bls.Sha256

/-! ## 32-bit primitives -/

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] private def shr (x : UInt32) (n : UInt32) : UInt32 := x >>> n

@[inline] private def ch  (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)
@[inline] private def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

@[inline] private def bigSigma0 (x : UInt32) : UInt32 := rotr x 2  ^^^ rotr x 13 ^^^ rotr x 22
@[inline] private def bigSigma1 (x : UInt32) : UInt32 := rotr x 6  ^^^ rotr x 11 ^^^ rotr x 25
@[inline] private def smallSigma0 (x : UInt32) : UInt32 := rotr x 7  ^^^ rotr x 18 ^^^ shr x 3
@[inline] private def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ shr x 10

/-! ## Round constants -/

private def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/-! ## Padding -/

private def padded (msg : ByteArray) : ByteArray := Id.run do
  let len      := msg.size
  let bitLen   : UInt64 := UInt64.ofNat (len * 8)
  let after80  := len + 1
  let padZeros := (56 + 64 - (after80 % 64)) % 64
  let total    := after80 + padZeros + 8
  let mut buf := ByteArray.mk (Array.replicate total 0)
  for i in [:len] do buf := buf.set! i msg[i]!
  buf := buf.set! len 0x80
  -- 64-bit big-endian length at the very end.
  for i in [:8] do
    let shift := UInt64.ofNat ((7 - i) * 8)
    buf := buf.set! (total - 8 + i) (UInt8.ofNat (bitLen >>> shift |>.toNat))
  return buf

/-! ## Compression function over a 64-byte block -/

private def big32 (b : ByteArray) (off : Nat) : UInt32 :=
  (UInt32.ofNat b[off]!.toNat <<< 24)
  ||| (UInt32.ofNat b[off + 1]!.toNat <<< 16)
  ||| (UInt32.ofNat b[off + 2]!.toNat <<< 8)
  ||| UInt32.ofNat b[off + 3]!.toNat

private def compressBlock (H : Array UInt32) (buf : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  -- Schedule W[0..63].
  let mut W : Array UInt32 := Array.replicate 64 0
  for t in [:16] do W := W.set! t (big32 buf (off + 4*t))
  for t in [16:64] do
    let s0 := smallSigma0 W[t - 15]!
    let s1 := smallSigma1 W[t - 2]!
    W := W.set! t (W[t - 16]! + s0 + W[t - 7]! + s1)
  let mut a := H[0]!
  let mut b := H[1]!
  let mut c := H[2]!
  let mut d := H[3]!
  let mut e := H[4]!
  let mut f := H[5]!
  let mut g := H[6]!
  let mut h := H[7]!
  for t in [:64] do
    let T1 := h + bigSigma1 e + ch e f g + K[t]! + W[t]!
    let T2 := bigSigma0 a + maj a b c
    h := g; g := f; f := e; e := d + T1
    d := c; c := b; b := a; a := T1 + T2
  return #[H[0]! + a, H[1]! + b, H[2]! + c, H[3]! + d,
           H[4]! + e, H[5]! + f, H[6]! + g, H[7]! + h]

/-! ## Top-level driver -/

/-- SHA-256 of an arbitrary-length `ByteArray`. -/
def hash (msg : ByteArray) : ByteArray := Id.run do
  -- Initial hash value (FIPS 180-4 §5.3.3).
  let mut H : Array UInt32 := #[
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]
  let buf := padded msg
  for off in [0 : buf.size : 64] do
    H := compressBlock H buf off
  -- Pack the 8 words big-endian into a 32-byte output.
  let mut out := ByteArray.mk (Array.replicate 32 0)
  for i in [:8] do
    let h := H[i]!
    out := out.set! (4*i)     (UInt8.ofNat ((h >>> 24).toNat))
    out := out.set! (4*i + 1) (UInt8.ofNat ((h >>> 16).toNat &&& 0xff))
    out := out.set! (4*i + 2) (UInt8.ofNat ((h >>>  8).toNat &&& 0xff))
    out := out.set! (4*i + 3) (UInt8.ofNat (h.toNat &&& 0xff))
  return out

end EthLib.Cryptography.Bls.Sha256

namespace EthLib.Cryptography.Bls

/-- SHA-256 of an arbitrary-length `ByteArray`. -/
@[inline] def sha256 (data : ByteArray) : ByteArray := Sha256.hash data

end EthLib.Cryptography.Bls
