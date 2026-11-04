module

public import EthLib.Networking.Rlpx.Handshake

/-!
# `Networking.Rlpx.Frame`

The frames of RLPx and their MAC, from the sections "Framing" and "MAC" of [`rlpx.md`][rlpx].

[rlpx]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#framing

A frame is the header ciphertext and its MAC, then the frame ciphertext and its MAC.

Each part is 16 bytes, except the frame ciphertext, which is a multiple of 16 bytes.

Each direction of a connection has one cipher stream and one Keccak-256 MAC state.

The sender and the receiver of a direction hold the same state, and each frame moves it on.
-/

@[expose] public section

namespace EthLib.Networking.Rlpx

open EthLib.Cryptography
open EthLib.Cryptography.Hash.Keccak

/-- Every way a frame can be rejected. -/
inductive FrameError where
  /-- The frame data had `size` bytes, more than a 24-bit size can give. -/
  | tooLarge (size : Nat)
  /-- The input ended after `available` bytes, before the `needed` bytes of the frame. -/
  | tooShort (needed available : Nat)
  /-- The header MAC did not match. -/
  | headerMacMismatch
  /-- The frame MAC did not match. -/
  | frameMacMismatch
deriving DecidableEq, Repr

/-- The size of a header, of a MAC and of a cipher block. -/
def BLOCK_SIZE : Nat := 16

/--
The header data `[capability-id, context-id]`: the RLP list `[0, 0]`.

`rlpx.md` fixes both integers at zero.
-/
def HEADER_DATA : List UInt8 := [0xc2, 0x80, 0x80]

/-- The state of one direction of a connection. -/
structure FrameState where
  /-- `aes-secret`, the AES-256 key of the cipher stream. -/
  aesKey : Aes.Key .aes256
  /-- The next counter block of the cipher stream. -/
  counter : Aes.Block
  /-- `mac-secret`, the AES-256 key of the MAC. -/
  macKey : Aes.Key .aes256
  /-- The Keccak-256 state of the MAC. -/
  mac : Hasher

/-- `keccak256.digest(mac)[:16]`, the first 16 bytes of the digest of a MAC state. -/
def macDigest (h : Hasher) : Aes.Block :=
  Vector.ofFn fun i => h.digest[i.val]

/--
The seed `aes(mac-secret, keccak256.digest(mac)[:16]) ^ value` of a MAC update.

`aes` here is the AES-256 forward cipher on one block.
-/
def macSeed (macKey : Aes.Key .aes256) (h : Hasher) (value : List UInt8) : ByteArray :=
  ⟨(List.zipWith (· ^^^ ·) (Aes.ciph .aes256 macKey (macDigest h)).toList value).toArray⟩

/-- The MAC state after it absorbs the seed of `value`. -/
def macStep (macKey : Aes.Key .aes256) (h : Hasher) (value : List UInt8) : Hasher :=
  h.absorb (macSeed macKey h value)

/-- The MAC state after the frame ciphertext and the seed of its digest. -/
def frameMacStep (macKey : Aes.Key .aes256) (h : Hasher) (frameCt : ByteArray) : Hasher :=
  let h := h.absorb frameCt
  macStep macKey h (macDigest h).toList

/--
Data XORed with the cipher stream of AES-256 in counter mode, from the counter block `counter`.

The key is the 32-byte `aes-secret`, and one stream runs on across the frames of a direction.
-/
def crypt (aesKey : Aes.Key .aes256) (counter : Aes.Block) (data : ByteArray) : ByteArray :=
  Aes.ctr (Aes.ciph .aes256 aesKey) 128 counter data

/-- The counter block `n` blocks later. -/
def advance (n : Nat) (counter : Aes.Block) : Aes.Block :=
  Nat.repeat (Aes.inc 128) n counter

/-- The size of `size` bytes zero-filled to a multiple of 16. -/
def paddedSize (size : Nat) : Nat := (size + 15) / 16 * 16

/-- The header: `frame-size` in 3 big-endian bytes, the header data, then zeros, 16 bytes. -/
def header (size : Nat) : ByteArray :=
  ⟨#[(size / 65536 % 256).toUInt8, (size / 256 % 256).toUInt8, (size % 256).toUInt8] ++
    HEADER_DATA.toArray ++ Array.replicate 10 0⟩

/-- The frame size that the first 3 bytes of a header give. -/
def readSize (header : List UInt8) : Nat :=
  (header.take 3).foldl (fun acc b => 256 * acc + b.toNat) 0

/-- A MAC state as the 16 bytes of its MAC. -/
def macBytes (h : Hasher) : ByteArray := ⟨(macDigest h).toArray⟩

/--
The frame of `frameData`, and the state of the direction after it.

The header MAC covers the header ciphertext, and the frame MAC covers the frame ciphertext.
-/
def writeFrame (st : FrameState) (frameData : ByteArray) :
    Except FrameError (ByteArray × FrameState) :=
  let size := frameData.size
  if 2 ^ 24 ≤ size then .error (.tooLarge size)
  else
    let headerCt := crypt st.aesKey st.counter (header size)
    let h1 := macStep st.macKey st.mac headerCt.data.toList
    let counter := advance 1 st.counter
    let padded := frameData ++ ⟨Array.replicate (paddedSize size - size) 0⟩
    let frameCt := crypt st.aesKey counter padded
    let h2 := frameMacStep st.macKey h1 frameCt
    .ok (headerCt ++ macBytes h1 ++ frameCt ++ macBytes h2,
      { st with counter := advance (paddedSize size / BLOCK_SIZE) counter, mac := h2 })

/--
The data of the frame at the start of `input`, the state after it, and the bytes after it.

Each MAC is checked before the part it covers is decrypted, as `rlpx.md` asks.

The reader ignores the header data.
-/
def readFrame (st : FrameState) (input : ByteArray) :
    Except FrameError (ByteArray × FrameState × ByteArray) :=
  let bytes := input.data.toList
  if bytes.length < 2 * BLOCK_SIZE then .error (.tooShort (2 * BLOCK_SIZE) bytes.length)
  else
    let headerCt := bytes.take BLOCK_SIZE
    let h1 := macStep st.macKey st.mac headerCt
    if (bytes.drop BLOCK_SIZE).take BLOCK_SIZE ≠ (macDigest h1).toList then
      .error .headerMacMismatch
    else
      let size := readSize (crypt st.aesKey st.counter ⟨headerCt.toArray⟩).data.toList
      let n := paddedSize size
      let needed := 2 * BLOCK_SIZE + n + BLOCK_SIZE
      if bytes.length < needed then .error (.tooShort needed bytes.length)
      else
        let frameCt : ByteArray := ⟨((bytes.drop (2 * BLOCK_SIZE)).take n).toArray⟩
        let h2 := frameMacStep st.macKey h1 frameCt
        if (bytes.drop (2 * BLOCK_SIZE + n)).take BLOCK_SIZE ≠ (macDigest h2).toList then
          .error .frameMacMismatch
        else
          let counter := advance 1 st.counter
          let data := (crypt st.aesKey counter frameCt).data.toList.take size
          .ok (⟨data.toArray⟩, { st with counter := advance (n / BLOCK_SIZE) counter, mac := h2 },
            ⟨(bytes.drop needed).toArray⟩)

/--
The sending direction of a session, from its secrets.

`rlpx.md` does not fix the first counter block, and EthLib takes the zero block.

Both directions start with the same key and the same counter, so they use the same keystream.

Who knows the plaintext of one direction can then decrypt the other at the same positions.

`rlpx.md` lists this weakness in its section "Known Issues in the current version".
-/
def Secrets.egress (s : Secrets) : FrameState :=
  ⟨⟨s.aesSecret.toArray, by simp [Aes.KeySize.Nk]⟩, Vector.replicate 16 0,
    ⟨s.macSecret.toArray, by simp [Aes.KeySize.Nk]⟩, s.egressMac⟩

/-- The receiving direction of a session, from its secrets. -/
def Secrets.ingress (s : Secrets) : FrameState :=
  ⟨⟨s.aesSecret.toArray, by simp [Aes.KeySize.Nk]⟩, Vector.replicate 16 0,
    ⟨s.macSecret.toArray, by simp [Aes.KeySize.Nk]⟩, s.ingressMac⟩

end EthLib.Networking.Rlpx
