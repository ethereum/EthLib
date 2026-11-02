import EthLib.Cryptography

open EthLib.Cryptography.Hash

-- The first and last bits of an empty message's padded block are set.
/-- info: (1088, true, true) -/
#guard_msgs in
#eval let bits := KeccakBits.padded ByteArray.empty
      (bits.length, bits[0]!, bits[1087]!)

example (msg : ByteArray) : (KeccakBits.padded msg).length % 1088 = 0 :=
  KeccakBits.padded_size_multiple msg

-- Pack bit positions 0 and 7 in an explicitly defined state.
/-- info: true -/
#guard_msgs in
#eval KeccakBits.outputByte (fun _ _ z => z.val == 0 || z.val == 7) 0 == 0x81
