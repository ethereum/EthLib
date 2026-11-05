module

public import EthLib.Execution.Evm.Op

/-!
# Proofs: `Evm.Op`

Each opcode has its own byte, and the decoder gives the opcode of each byte back.

A byte decodes at a fork exactly when its opcode exists at that fork.

Each opcode that a fork after Frontier adds has the byte and the fork that its EIP gives.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Op

open EthLib.Base (Fork)

/-- The decoder gives the opcode of each byte back. -/
theorem decode_toByte (op : Op) : decode op.toByte = some op := by
  cases op <;> first | decide | (rename_i n; revert n; decide)

/-- Two opcodes have two different bytes. -/
theorem toByte_injective : Function.Injective toByte := fun a b h =>
  Option.some.inj (by rw [← decode_toByte a, h, decode_toByte])

/-- The decoder gives an opcode only for its byte. -/
theorem toByte_of_decode {byte : UInt8} {op : Op} (h : decode byte = some op) :
    op.toByte = byte := by
  -- Check each of the 256 bytes.
  have all : ∀ n : Fin 256,
      (decode (UInt8.ofNat n)).all (fun op => op.toByte == UInt8.ofNat n) = true := by
    set_option maxRecDepth 4096 in decide
  have := all ⟨byte.toNat, byte.toNat_lt⟩
  simp only [UInt8.ofNat_toNat, h, Option.all_some, beq_iff_eq] at this
  exact this

/-- A byte decodes at a fork exactly to the opcode of that byte, when the fork has the opcode. -/
theorem ofByte_eq_some_iff {fork : Fork} {byte : UInt8} {op : Op} :
    ofByte fork byte = some op ↔ op.toByte = byte ∧ op.since ≤ fork := by
  unfold ofByte
  rw [Option.filter_eq_some_iff]
  constructor
  · rintro ⟨h, le⟩
    exact ⟨toByte_of_decode h, by simpa using le⟩
  · rintro ⟨rfl, le⟩
    exact ⟨decode_toByte op, by simpa using le⟩

/-- The opcodes that forks after Frontier add: the byte and the fork of each one, from its EIP. -/
def addedOpcodes : List (UInt8 × Fork) :=
  [ -- DELEGATECALL, EIP-7
    (0xf4, .homestead),
    -- RETURNDATASIZE and RETURNDATACOPY, EIP-211
    (0x3d, .byzantium), (0x3e, .byzantium),
    -- STATICCALL, EIP-214
    (0xfa, .byzantium),
    -- REVERT, EIP-140
    (0xfd, .byzantium),
    -- SHL, SHR and SAR, EIP-145
    (0x1b, .constantinople), (0x1c, .constantinople), (0x1d, .constantinople),
    -- EXTCODEHASH, EIP-1052
    (0x3f, .constantinople),
    -- CREATE2, EIP-1014
    (0xf5, .constantinople),
    -- CHAINID, EIP-1344
    (0x46, .istanbul),
    -- SELFBALANCE, EIP-1884
    (0x47, .istanbul),
    -- BASEFEE, EIP-3198
    (0x48, .london),
    -- PUSH0, EIP-3855
    (0x5f, .shapella),
    -- BLOBHASH, EIP-4844
    (0x49, .dencun),
    -- BLOBBASEFEE, EIP-7516
    (0x4a, .dencun),
    -- TLOAD and TSTORE, EIP-1153
    (0x5c, .dencun), (0x5d, .dencun),
    -- MCOPY, EIP-5656
    (0x5e, .dencun),
    -- CLZ, EIP-7939
    (0x1e, .fusaka),
    -- SLOTNUM, EIP-7843
    (0x4b, .glamsterdam),
    -- DUPN, SWAPN and EXCHANGE, EIP-8024
    (0xe6, .glamsterdam), (0xe7, .glamsterdam), (0xe8, .glamsterdam)]

/-- Each opcode is from the fork that its EIP gives, or from Frontier when it has no such EIP. -/
theorem since_eq_addedOpcodes (op : Op) :
    op.since = (addedOpcodes.lookup op.toByte).getD .frontier := by
  cases op <;> first | decide | (rename_i n; revert n; decide)

/-- The byte `0x4b` is SLOTNUM from Glamsterdam, and no opcode before. -/
theorem ofByte_slotnum (fork : Fork) :
    ofByte fork 0x4b = if .glamsterdam ≤ fork then some .slotnum else none := by
  have hd : decode 0x4b = some .slotnum := rfl
  unfold ofByte
  rw [hd]
  split <;> simp_all [since, Option.filter]

end EthLib.Execution.Evm.Op
