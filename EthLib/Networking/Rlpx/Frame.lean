module

public import EthLib.Networking.Rlpx.Handshake
public import EthLib.Base.ByteOrder

/-!
# `Networking.Rlpx.Frame`

The frames of RLPx and their MAC, from the sections "Framing" and "MAC" of [`rlpx.md`][rlpx].

[rlpx]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/rlpx.md#framing

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

/-- The stable code of an error, for the C exports.

ECIES and the handshake share the codes up to 200, so frames take the codes from 201. -/
def FrameError.code : FrameError → UInt32
  | .tooLarge _ => 201
  | .tooShort _ _ => 202
  | .headerMacMismatch => 203
  | .frameMacMismatch => 204

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
  mac : Hasher256

/-- `keccak256.digest(mac)[:16]`, the first 16 bytes of the digest of a MAC state. -/
def macDigest (h : Hasher256) : Aes.Block :=
  -- The first 16 of the 32 bytes of the digest.
  Vector.ofFn fun i => h.digest[i.val]

/-- The seed of a MAC update, from the section MAC of `rlpx.md`. -/
def macSeed (macKey : Aes.Key .aes256) (h : Hasher256) (value : List UInt8) : ByteArray :=
  -- `aes(mac-secret, keccak256.digest(mac)[:16]) ^ value`, where every caller passes 16 bytes.
  --
  -- `rlpx.md` writes `aes` with no key size: `mac-secret` has 32 bytes, so EthLib takes AES-256.
  --
  -- EthLib reads `aes` here as the forward cipher on one block, since its input is one block.
  ⟨(List.zipWith (· ^^^ ·) (Aes.ciph .aes256 macKey (macDigest h)).toList value).toArray⟩

/-- The MAC state after it absorbs the seed of `value`. -/
def macStep (macKey : Aes.Key .aes256) (h : Hasher256) (value : List UInt8) : Hasher256 :=
  -- `mac = keccak256.update(mac, seed)`, for `header-mac-seed` and `frame-mac-seed` alike.
  h.absorb (macSeed macKey h value)

/-- The MAC state after the frame ciphertext and the seed of its digest. -/
def frameMacStep (macKey : Aes.Key .aes256) (h : Hasher256) (frameCt : ByteArray) : Hasher256 :=
  -- `egress-mac = keccak256.update(egress-mac, frame-ciphertext)`.
  let h := h.absorb frameCt
  -- `frame-mac-seed = aes(mac-secret, keccak256.digest(egress-mac)[:16]) ^ D`.
  --
  -- Here `D = keccak256.digest(egress-mac)[:16]`.
  --
  -- Then `egress-mac = keccak256.update(egress-mac, frame-mac-seed)`.
  macStep macKey h (macDigest h).toList

/--
Data XORed with the cipher stream of AES-256 in counter mode, from the counter block `counter`.

One stream runs on across the frames of a direction.
-/
def crypt (aesKey : Aes.Key .aes256) (counter : Aes.Block) (data : ByteArray) : ByteArray :=
  -- `aes(aes-secret, data)`: `rlpx.md` names CTR mode only in Known Issues, with no key size.
  --
  -- `aes-secret` has 32 bytes, so EthLib takes AES-256 in counter mode.
  --
  -- Each next counter block is the one before plus one, modulo `2^128` (SP 800-38A, Appendix B.1).
  Aes.ctr (Aes.ciph .aes256 aesKey) 128 counter data

/-- The counter block `n` blocks later. -/
def advance (n : Nat) (counter : Aes.Block) : Aes.Block :=
  -- Each 16-byte block of the stream adds one to the counter block, modulo `2^128`.
  Nat.repeat (Aes.inc 128) n counter

/-- The size of `size` bytes zero-filled to a multiple of 16. -/
def paddedSize (size : Nat) : Nat := (size + 15) / 16 * 16

/-- The header of a frame of `size` bytes, in 16 bytes. -/
def header (size : Nat) : ByteArray :=
  -- `header = frame-size || header-data || header-padding`.
  --
  -- `frame-size` is a 24-bit big-endian integer, in 3 bytes (section Message Encoding).
  --
  -- `header-data` is the 3 bytes of `[0, 0]`, and `header-padding` is 10 zeros up to 16 bytes.
  ⟨(Base.ByteOrder.toBE 3 size).toArray ++ HEADER_DATA.toArray ++ Array.replicate 10 0⟩

/-- The frame size that the first 3 bytes of a header give. -/
def readSize (header : List UInt8) : Nat :=
  -- `frame-size`: the first 3 bytes of the header, a 24-bit big-endian integer.
  Base.ByteOrder.ofBE (header.take 3)

/-- A MAC state as the 16 bytes of its MAC. -/
def macBytes (h : Hasher256) : ByteArray := ⟨(macDigest h).toArray⟩

/-- The frame of `frameData`, and the state of the direction after it. -/
def writeFrame (st : FrameState) (frameData : ByteArray) :
    Except FrameError (ByteArray × FrameState) :=
  let size := frameData.size
  -- `frame-size` is a 24-bit integer, so frame data of `2^24` bytes or more fails.
  if 2 ^ 24 ≤ size then .error (.tooLarge size)
  else
    -- `header-ciphertext = aes(aes-secret, header)`, one block of the stream.
    let headerCt := crypt st.aesKey st.counter (header size)
    -- `header-mac-seed = aes(mac-secret, keccak256.digest(egress-mac)[:16]) ^ header-ciphertext`.
    --
    -- Then `egress-mac = keccak256.update(egress-mac, header-mac-seed)`.
    let h1 := macStep st.macKey st.mac headerCt.data.toList
    -- The frame ciphertext goes on from the block after the header.
    let counter := advance 1 st.counter
    -- `frame-padding = zero-fill frame-data to 16-byte boundary`.
    let padded := frameData ++ ⟨Array.replicate (paddedSize size - size) 0⟩
    -- `frame-ciphertext = aes(aes-secret, frame-data || frame-padding)`.
    let frameCt := crypt st.aesKey counter padded
    -- The steps of `frame-mac`, from the state after the header.
    let h2 := frameMacStep st.macKey h1 frameCt
    -- `frame = header-ciphertext || header-mac || frame-ciphertext || frame-mac`.
    --
    -- Each MAC is `keccak256.digest(egress-mac)[:16]` after its update.
    .ok (headerCt ++ macBytes h1 ++ frameCt ++ macBytes h2,
      -- The stream moves past the blocks of the frame ciphertext.
      { st with counter := advance (paddedSize size / BLOCK_SIZE) counter, mac := h2 })

/-- The data of the frame at offset `pos` of `input`, the state after it, and the offset after it.

The offsets let a stream of frames be read without copying what is left of it. -/
def readFrameAt (st : FrameState) (input : ByteArray) (pos : Nat) :
    Except FrameError (ByteArray × FrameState × Nat) :=
  -- Each part is cut at its offset from `pos`, so a frame costs its own size, not the input's.
  let left := input.size - pos
  -- The header ciphertext and the header MAC take 16 bytes each.
  if left < 2 * BLOCK_SIZE then .error (.tooShort (2 * BLOCK_SIZE) left)
  else
    let headerCt := (input.extract pos (pos + BLOCK_SIZE)).data.toList
    -- `ingress-mac` is updated in the same way as `egress-mac`, from `header-ciphertext`.
    let h1 := macStep st.macKey st.mac headerCt
    -- The digest is compared to `header-mac`, before `header-ciphertext` is decrypted.
    if (input.extract (pos + BLOCK_SIZE) (pos + 2 * BLOCK_SIZE)).data.toList ≠
        (macDigest h1).toList then
      .error .headerMacMismatch
    else
      -- `frame-size` from the decrypted header.
      --
      -- EthLib ignores the header data and padding; the two fields are unused (Known Issues).
      let size := readSize (crypt st.aesKey st.counter ⟨headerCt.toArray⟩).data.toList
      -- The frame ciphertext holds `frame-size` bytes zero-filled to a 16-byte boundary.
      let n := paddedSize size
      -- Then comes the 16-byte `frame-mac`.
      let needed := 2 * BLOCK_SIZE + n + BLOCK_SIZE
      if left < needed then .error (.tooShort needed left)
      else
        let frameCt := input.extract (pos + 2 * BLOCK_SIZE) (pos + 2 * BLOCK_SIZE + n)
        -- `ingress-mac` takes the steps of `frame-mac`, as `egress-mac` does.
        let h2 := frameMacStep st.macKey h1 frameCt
        -- The digest is compared to `frame-mac`, before `frame-ciphertext` is decrypted.
        if (input.extract (pos + 2 * BLOCK_SIZE + n) (pos + needed)).data.toList ≠
            (macDigest h2).toList then
          .error .frameMacMismatch
        else
          -- The frame ciphertext starts at the block after the header.
          let counter := advance 1 st.counter
          -- `frame-data || frame-padding`, then the padding is dropped.
          let data := (crypt st.aesKey counter frameCt).data.toList.take size
          -- The stream moves past the blocks of the frame ciphertext.
          .ok (⟨data.toArray⟩, { st with counter := advance (n / BLOCK_SIZE) counter, mac := h2 },
            pos + needed)

/-- The data of the frame at the start of `input`, the state after it, and the bytes after it. -/
def readFrame (st : FrameState) (input : ByteArray) :
    Except FrameError (ByteArray × FrameState × ByteArray) := do
  let (data, st, next) ← readFrameAt st input 0
  -- The bytes after the frame, from the offset where it ends.
  return (data, st, input.extract next input.size)

/--
The sending direction of a session, from its secrets.

Both directions start with the same key and the same counter, so they use the same keystream.

Who knows the plaintext of one direction can then decrypt the other at the same positions.

`rlpx.md` lists this weakness in its section "Known Issues in the current version".
-/
def Secrets.egress (s : Secrets) : FrameState :=
  -- The keys `aes-secret` and `mac-secret`, and `egress-mac`.
  --
  -- `rlpx.md` does not fix the first counter block, and EthLib takes the zero block.
  ⟨⟨s.aesSecret.toArray, by simp [Aes.KeySize.Nk]⟩, Vector.replicate 16 0,
    ⟨s.macSecret.toArray, by simp [Aes.KeySize.Nk]⟩, s.egressMac⟩

/-- The receiving direction of a session, from its secrets. -/
def Secrets.ingress (s : Secrets) : FrameState :=
  -- The keys `aes-secret` and `mac-secret`, and `ingress-mac`.
  --
  -- `rlpx.md` does not fix the first counter block, and EthLib takes the zero block.
  ⟨⟨s.aesSecret.toArray, by simp [Aes.KeySize.Nk]⟩, Vector.replicate 16 0,
    ⟨s.macSecret.toArray, by simp [Aes.KeySize.Nk]⟩, s.ingressMac⟩

end EthLib.Networking.Rlpx
