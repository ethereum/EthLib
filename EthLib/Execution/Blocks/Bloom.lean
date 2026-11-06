module

public import EthLib.Base.BigEndian
public import EthLib.Base.Bytes
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Blocks.Log

/-!
# `Blocks.Bloom`

The logs Bloom filter: 2048 bits that summarize the addresses and topics of some logs.

Each entry, an address or a topic, sets three bits.

They are the first three 16-bit words of its Keccak-256 hash, each taken modulo 2048.

The filter is the OR of the bits of every entry.

So a reader can skip a block whose filter lacks a bit of the entry it looks for.

The filter is written as 256 bytes, big-endian, so bit `k` is bit `2047 - k` from the first byte.

Section 4.4.1 of the Yellow Paper, Shanghai version, defines it: [`Paper.tex`][yp].

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)

namespace Bloom

/-- The three bits that an entry sets: three 16-bit words of its hash, each modulo 2048. -/
def bits (entry : ByteArray) : List Nat :=
  let h := keccak256 entry
  let byte (i : Fin 6) : Nat :=
    (h[i.val]'(by have := i.isLt; unfold Cryptography.Hash.Keccak.DIGEST_LEN; omega)).toNat
  [(byte 0 * 256 + byte 1) % 2048, (byte 2 * 256 + byte 3) % 2048, (byte 4 * 256 + byte 5) % 2048]

/-- The filter of one entry: its three bits set. -/
def ofEntry (entry : ByteArray) : BitVec 2048 :=
  (bits entry).foldr (fun k acc => BitVec.twoPow 2048 k ||| acc) 0

/-- The entries of a log: its address, then each of its topics. -/
def entries (log : Log) : List ByteArray :=
  ⟨log.address.toArray⟩ :: log.topics.map fun t => ⟨t.toArray⟩

/-- The filter of some logs: the OR of the filters of all their entries. -/
def ofLogs (logs : List Log) : BitVec 2048 :=
  ((logs.flatMap entries).map ofEntry).foldr (· ||| ·) 0

/-- The 256 bytes of a filter, the most significant byte first. -/
def toBytes (bloom : BitVec 2048) : Bytes256 :=
  ⟨(natToBytes 256 bloom.toNat).toArray, by simp [natToBytes_length]⟩

/-- Whether a filter has every bit of an entry.

A false answer shows that no log of the filter has the entry. -/
def mayContain (bloom : BitVec 2048) (entry : ByteArray) : Bool :=
  (bits entry).all bloom.getLsbD

end Bloom

/-- The 256 bytes of the logs Bloom filter of some logs. -/
def logsBloom (logs : List Log) : Bytes256 := Bloom.toBytes (Bloom.ofLogs logs)

end EthLib.Execution.Blocks
