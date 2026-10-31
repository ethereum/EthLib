module

public import EthLib.Networking.Snappy.Block

/-!
# `Networking.Proofs.Snappy.Block`

Properties of Snappy block decompression, and the known answers of the
format description.

Decompression has no round trip to prove: the block format admits many
encodings of one byte string, and compression is out of scope. What a
reader can rely on instead is that a block which decompresses at all
yields exactly the number of bytes it declared, and that every malformed
shape the format allows is rejected by name.

The known answers below are blocks built by hand from
`format_description.txt`, one per element type. Their outputs come from the
reference implementation, not from the definitions here.

Everything is checked by the kernel: each known answer reduces by `rfl`.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.Block

open EthLib.Networking.Snappy

/-! ## A copy writes exactly as many bytes as it claims -/

/-- A successful copy of `n` bytes lengthens the output by `n`. -/
theorem copyBytes_length {out out' : List UInt8} {offset n : Nat}
    (h : copyBytes out offset n = .ok out') : out'.length = out.length + n := by
  induction n generalizing out with
  | zero => rw [copyBytes] at h; cases h; simp
  | succ n ih =>
      rw [copyBytes] at h
      split at h
      · exact absurd h (by simp)
      · have := ih h
        simp only [List.length_cons] at this
        omega

/-! ## A block yields the length it declared

The final check in `decompressList` is what makes this hold, and stating
it is what lets a caller size a buffer from the preamble.
-/

/-- A block that decompresses yields exactly as many bytes as its preamble
declared. -/
theorem decompressList_length_eq_declared {bs out : List UInt8}
    (h : decompressList bs = .ok out) :
    ∃ rest, readPreamble bs = .ok (out.length, rest) := by
  rw [decompressList] at h
  split at h
  · exact absurd h (by simp)
  · rename_i declared rest hpre
    split at h
    · exact absurd h (by simp)
    · rename_i mid hmid
      split at h
      · rename_i hlen
        refine ⟨rest, ?_⟩
        cases h
        rw [hpre, List.length_reverse, beq_iff_eq.mp hlen]
      · exact absurd h (by simp)

/-! ## Known answers

Each block is built by hand from `format_description.txt`; each expected
output is what the reference implementation produces for it.
-/

/-- A literal whose length rides in the tag. -/
example : decompressList [0x02, 0x04, 0x41, 0x42] = .ok [0x41, 0x42] := rfl

/-- A copy with a one-byte offset. -/
example : decompressList [0x05, 0x00, 0x41, 0x01, 0x01] =
    .ok [0x41, 0x41, 0x41, 0x41, 0x41] := rfl

/-- A copy with a two-byte offset. -/
example : decompressList [0x08, 0x0c, 0x41, 0x42, 0x43, 0x44, 0x0e, 0x04, 0x00] =
    .ok [0x41, 0x42, 0x43, 0x44, 0x41, 0x42, 0x43, 0x44] := rfl

/-- A copy with a four-byte offset. -/
example : decompressList [0x08, 0x0c, 0x41, 0x42, 0x43, 0x44, 0x0f, 0x04, 0x00, 0x00, 0x00] =
    .ok [0x41, 0x42, 0x43, 0x44, 0x41, 0x42, 0x43, 0x44] := rfl

/-- An overlapping copy: a run of one byte, where the copy re-reads the
bytes it has just written. -/
example : decompressList [0x0b, 0x00, 0x41, 0x19, 0x01] =
    .ok [0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41] := rfl

/-- An empty block: a preamble of zero and no elements. -/
example : decompressList [0x00] = .ok [] := rfl

/-- A preamble that is not minimally encoded. Snappy has no minimality
rule, and the reference implementation accepts this, so a decoder that
reused the consensus layer's varint would wrongly reject it. -/
example : decompressList [0x81, 0x00, 0x00, 0x41] = .ok [0x41] := rfl

/-! ## Rejected inputs

One per error the format allows.
-/

/-- No bytes at all. -/
example : decompressList [] = .error .preambleTruncated := rfl

/-- A preamble whose continuation bit is set on its last byte. -/
example : decompressList [0x80] = .error .preambleTruncated := rfl

/-- A preamble that does not end within five bytes. -/
example : decompressList [0x80, 0x80, 0x80, 0x80, 0x80, 0x00] =
    .error .preambleTooLong := rfl

/-- A preamble declaring more than `2 ^ 32 - 1` bytes. -/
example : decompressList [0x80, 0x80, 0x80, 0x80, 0x10] =
    .error (.preambleTooLarge 4294967296) := rfl

/-- A literal running past the end of the input. -/
example : decompressList [0x05, 0x08, 0x41] = .error .literalPastEnd := rfl

/-- A copy whose offset bytes run past the end of the input. -/
example : decompressList [0x05, 0x00, 0x41, 0x0e] = .error .copyPastEnd := rfl

/-- A copy offset of zero, which names no byte. -/
example : decompressList [0x05, 0x00, 0x41, 0x01, 0x00] =
    .error .copyOffsetZero := rfl

/-- A copy offset reaching before the start of the output. -/
example : decompressList [0x05, 0x00, 0x41, 0x01, 0x05] =
    .error (.copyOffsetTooLarge 5) := rfl

/-- An output shorter than the preamble declared. -/
example : decompressList [0x02, 0x00, 0x41] = .error (.lengthMismatch 2 1) := rfl

/-- An output longer than the preamble declared. -/
example : decompressList [0x01, 0x04, 0x41, 0x42] = .error (.lengthMismatch 1 2) := rfl

end EthLib.Networking.Proofs.Snappy.Block
