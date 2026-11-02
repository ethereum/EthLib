import EthLib.Proofs

open EthLib.Cryptography.Hash

-- The Keccak team ShortMsgKAT_256, Len = 0, transferred through the
-- independently defined bit sponge rather than numerical bit execution.
example : (KeccakBits.keccak256 ByteArray.empty).toArray =
    (Keccak.hexBytes "C5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470").data := by
  rw [← KeccakBits.keccak256_eq]
  exact Keccak.keccak256_empty

example : (KeccakBits.keccak256 (Keccak.hexBytes "CC")).toArray =
    (Keccak.hexBytes "EEAD6DBFC7340A56CAEDC044696A168870549A6A7F6F56961E84A54BD9970B8A").data := by
  rw [← KeccakBits.keccak256_eq]
  exact Keccak.keccak256_len8

example (a : KeccakBits.State) (n : Nat) :
    KeccakBits.round (n + 255) a = KeccakBits.round n a :=
  KeccakBits.round_periodic n a

example (a : KeccakBits.State) (n : Nat) :
    KeccakBits.outputByte a (n + 200) = KeccakBits.outputByte a n :=
  KeccakBits.outputByte_periodic a n

example (a : KeccakBits.State) : KeccakBits.ofLanes (KeccakBits.toLanes a) = a :=
  KeccakBits.ofLanes_toLanes a
