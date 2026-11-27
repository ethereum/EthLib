module

public import EthLib.Execution.Proofs.Evm.Machine.JumpDest
public import EthLib.Execution.Evm.Instructions.StackOnly
import EthLib.Execution.Proofs.Evm.Machine.Memory

/-!
# Proofs: a code stored as one natural number

A proof about a code needs facts about its bytes.

These are its size, the byte at a position, the data of a PUSH and its valid jump destinations.

On a literal array, such a fact costs time that grows with the position.

Past a few hundred bytes, it runs out of the default limits.

Here a code is stored as one natural number, the big-endian number of its bytes.

A position is a valid jump destination when a walk along the opcodes from 0 reaches it.

Its byte must also be JUMPDEST.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.NatCode

open EthLib.Base (byteAtOrZero ByteOrder.ofBE)

/-- The byte at index `i` of the code of `size` bytes stored in `n`, or 0 past its end.

The first byte of the code is the highest byte of `n`. -/
def natByte (n size i : Nat) : UInt8 :=
  -- The byte is one shift of `n`.
  --
  -- The kernel and tactics such as `simp` and `decide` compute it on big numbers in one step.
  --
  -- So a fact about one byte costs about the same at every position.
  if i < size then UInt8.ofNat (n >>> (8 * (size - 1 - i))) else 0

/-- The code of `size` bytes stored in `n`, the big-endian number of its bytes.

A number above `256 ^ size` keeps only its lowest `size` bytes. -/
def ofNat (n size : Nat) : ByteArray := ⟨Array.ofFn (n := size) fun i => natByte n size i.val⟩

/-- The number of a code given as words of 32 bytes, the first word highest.

A code of tens of kilobytes is written this way, one word per line. -/
def ofWords (words : List Nat) : Nat :=
  -- The elaborator reads a list of numbers cheaply, where a sum of powers of 256 runs out of time.
  --
  -- Each word is below `2 ^ 256`.
  --
  -- When the size is not a multiple of 32, zero bytes in front of the first word fill it.
  --
  -- The code is then the lowest `size` bytes of the number.
  words.foldl (fun acc w => acc * 2 ^ 256 + w) 0

/-! ## The bytes -/

/-- The code stored in a number has the size it is given. -/
theorem size_ofNat (n size : Nat) : (ofNat n size).size = size := by
  simp [ofNat, ByteArray.size]

/-- A byte inside the code is the byte of the number at that index. -/
theorem getElem_ofNat (n size i : Nat) (h : i < (ofNat n size).size) :
    (ofNat n size)[i] = natByte n size i :=
  show (Array.ofFn (n := size) fun i => natByte n size i.val)[i]'(by
    simpa [ofNat, ByteArray.size] using h) = _ from Array.getElem_ofFn ..

/-- The byte at any index, 0 past the end, is the byte of the number at that index. -/
theorem byteAtOrZero_ofNat (n size i : Nat) : byteAtOrZero (ofNat n size) i = natByte n size i := by
  unfold byteAtOrZero
  split
  · exact getElem_ofNat n size i _
  · rename_i h
    rw [size_ofNat] at h
    simp [natByte, h]

/-- The `k` bytes of data after `pc`, inside the code, are a shift and a remainder of the number.

The last of them sits `size - 1 - (pc + k)` bytes above the lowest byte of the number. -/
theorem pushData_ofNat (n size pc k : Nat) (h : pc + k < size) :
    pushData (ofNat n size) pc k =
      BitVec.ofNat 256 (n >>> (8 * (size - 1 - (pc + k))) % 256 ^ k) := by
  unfold pushData
  rw [bufferRead_eq]
  congr 1
  induction k with
  | zero => simp [EthLib.Base.ByteOrder.ofBE_eq_foldl, Nat.mod_one]
  | succ k ih =>
    rw [List.range_succ, List.map_append, EthLib.Base.ByteOrder.ofBE_eq_foldl, List.foldl_append,
      ← EthLib.Base.ByteOrder.ofBE_eq_foldl, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, byteAtOrZero_ofNat,
      natByte, show pc + 1 + k < size by omega, ↓reduceIte, UInt8.toNat_ofNat']
    -- The data before the last byte is the number shifted one byte further.
    have hs : 8 * (size - 1 - (pc + k)) = 8 * (size - 1 - (pc + 1 + k)) + 8 := by omega
    rw [hs, Nat.shiftRight_add, show pc + (k + 1) = pc + 1 + k by omega]
    generalize n >>> (8 * (size - 1 - (pc + 1 + k))) = m
    rw [Nat.shiftRight_eq_div_pow, show 2 ^ 8 = 256 from rfl,
      show 256 ^ (k + 1) = 256 * 256 ^ k from Nat.pow_succ', Nat.mod_mul]
    omega

/-! ## Jump destinations -/

/-- The position of the opcode after the one at `pc`, past the data of a PUSH1 to PUSH32. -/
def nextPc (n size pc : Nat) : Nat :=
  pc + 1 + if 0x60 ≤ (natByte n size pc).toNat ∧ (natByte n size pc).toNat ≤ 0x7f then
    (natByte n size pc).toNat - 0x5f else 0

/-- The opcode after the one at `pc` sits where the number puts it. -/
theorem nextOpcode_ofNat (n size pc : Nat) : nextOpcode (ofNat n size) pc = nextPc n size pc := by
  rw [nextOpcode_eq, byteAtOrZero_ofNat, nextPc]

/-- Whether the opcodes from `pc` reach `target`, in at most `fuel` opcodes.

The walk stops with false once it passes the target.

It reads each byte the same way.

It takes at most one step per opcode before the target.

The kernel checks it with `decide +kernel`. -/
def walk (n size : Nat) : (fuel pc target : Nat) → Bool
  | 0, _, _ => false
  | fuel + 1, pc, target =>
    if pc = target then true
    else if pc < target then walk n size fuel (nextPc n size pc) target else false

/-- A target inside the code that the walk from `pc` reaches is an opcode boundary from `pc`. -/
theorem boundaryFrom_of_walk (n size target : Nat) (ht : target < size) :
    ∀ (fuel pc : Nat), walk n size fuel pc target = true →
      BoundaryFrom (ofNat n size) pc target
  | 0, _, h => by simp [walk] at h
  | fuel + 1, pc, h => by
    have hs : target < (ofNat n size).size := by rw [size_ofNat]; exact ht
    unfold walk at h
    split at h
    · subst_vars
      exact .here hs
    · split at h
      · refine .step (by omega) ?_
        rw [nextOpcode_ofNat]
        exact boundaryFrom_of_walk n size target ht fuel _ h
      · simp at h

/-- A JUMPDEST in the code that the walk from 0 reaches is a valid jump destination. -/
theorem valid_of_walk {n size d : Nat} (hw : walk n size size 0 d = true)
    (hb : natByte n size d = 0x5b) :
    isValidJumpDest (validJumpDestinations (ofNat n size)) d = true := by
  -- Past the end of the code the byte is 0, so a JUMPDEST lies inside it.
  have ht : d < size := Nat.lt_of_not_le fun h => by
    simp [natByte, Nat.not_lt.mpr h] at hb
  exact isValidJumpDest_iff_boundaryFrom.mpr
    ⟨boundaryFrom_of_walk n size d ht _ _ hw, by rw [byteAtOrZero_ofNat, hb]; rfl⟩

/-- A position whose byte is not JUMPDEST is not a valid jump destination. -/
theorem not_valid_of_natByte {n size d : Nat} (hb : natByte n size d ≠ 0x5b) :
    isValidJumpDest (validJumpDestinations (ofNat n size)) d = false := by
  cases h : isValidJumpDest (validJumpDestinations (ofNat n size)) d with
  | false => rfl
  | true => exact absurd (by rw [← byteAtOrZero_ofNat]; exact byteAtOrZero_of_isValidJumpDest h) hb

/-! ## The jump destinations from one walk -/

/-- The JUMPDEST positions that the opcodes from `pc` reach in at most `fuel` opcodes. -/
def destsFrom (n size : Nat) : (fuel pc : Nat) → List Nat
  | 0, _ => []
  | fuel + 1, pc =>
    -- The walk stops at the end of the code, and lists each JUMPDEST that it meets.
    if pc < size then
      if natByte n size pc = 0x5b then pc :: destsFrom n size fuel (nextPc n size pc)
      else destsFrom n size fuel (nextPc n size pc)
    else []

/-- The valid jump destinations of the code, from one walk along its opcodes.

A proof evaluates the walk once, then reads each destination in the list. -/
def jumpDests (n size : Nat) : List Nat := destsFrom n size size 0

/-- A position listed by the walk from `pc` is a JUMPDEST at an opcode boundary from `pc`. -/
theorem boundaryFrom_of_mem_destsFrom {n size d : Nat} :
    ∀ {fuel pc : Nat}, d ∈ destsFrom n size fuel pc →
      BoundaryFrom (ofNat n size) pc d ∧ natByte n size d = 0x5b
  | 0, _, h => by simp [destsFrom] at h
  | fuel + 1, pc, h => by
    have hs : pc < size → pc < (ofNat n size).size := fun h => by rw [size_ofNat]; exact h
    unfold destsFrom at h
    split at h
    · rename_i hpc
      have step : d ∈ destsFrom n size fuel (nextPc n size pc) →
          BoundaryFrom (ofNat n size) (nextPc n size pc) d ∧ natByte n size d = 0x5b :=
        boundaryFrom_of_mem_destsFrom
      split at h
      · rename_i hb
        rcases List.mem_cons.mp h with rfl | h'
        · exact ⟨.here (hs hpc), hb⟩
        · obtain ⟨hbd, hbyte⟩ := step h'
          exact ⟨.step (hs hpc) (by rw [nextOpcode_ofNat]; exact hbd), hbyte⟩
      · obtain ⟨hbd, hbyte⟩ := step h
        exact ⟨.step (hs hpc) (by rw [nextOpcode_ofNat]; exact hbd), hbyte⟩
    · simp at h

/-- A JUMPDEST at an opcode boundary from `pc` is listed by the walk from `pc`.

The walk needs at least one opcode of fuel for each byte from `pc` to the end. -/
theorem mem_destsFrom_of_boundaryFrom {n size d pc : Nat} (h : BoundaryFrom (ofNat n size) pc d) :
    ∀ {fuel : Nat}, size - pc ≤ fuel → natByte n size d = 0x5b → d ∈ destsFrom n size fuel pc := by
  induction h with
  | here hlt =>
    intro fuel hf hb
    rw [size_ofNat] at hlt
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [destsFrom, hlt, hb]
  | @step start _ hlt _ ih =>
    intro fuel hf hb
    rw [size_ofNat] at hlt
    rw [nextOpcode_ofNat] at ih
    -- Each opcode moves the walk forward by at least one byte.
    have hnext : start < nextPc n size start := by
      unfold nextPc
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hmem := ih (fuel := fuel) (by omega) hb
    simp only [destsFrom, hlt, ↓reduceIte]
    split
    · exact List.mem_cons_of_mem _ hmem
    · exact hmem

/-- A position is a valid jump destination exactly when the walk along the opcodes lists it. -/
theorem isValidJumpDest_ofNat_iff {n size d : Nat} :
    isValidJumpDest (validJumpDestinations (ofNat n size)) d = true ↔ d ∈ jumpDests n size := by
  rw [isValidJumpDest_iff_boundaryFrom, byteAtOrZero_ofNat]
  constructor
  · rintro ⟨hbd, hb⟩
    exact mem_destsFrom_of_boundaryFrom hbd (by omega) hb
  · intro h
    obtain ⟨hbd, hb⟩ := boundaryFrom_of_mem_destsFrom h
    exact ⟨hbd, hb⟩

/-- The `w` bits of a number from bit `s` depend only on its bits below bit `W`.

It holds when `s + w ≤ W`. -/
theorem shiftRight_mod_two_pow (n s w W : Nat) (h : s + w ≤ W) :
    (n >>> s) % 2 ^ w = ((n % 2 ^ W) >>> s) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < w
  · simp [hi, show s + i < W by omega]
  · simp [hi]

end EthLib.Execution.Evm.Logic.NatCode
