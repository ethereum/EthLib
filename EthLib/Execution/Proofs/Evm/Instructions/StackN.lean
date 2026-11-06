module

public import EthLib.Execution.Evm.Instructions.StackN
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Instructions.StackN`

The immediate byte of DUPN and SWAPN encodes exactly the depths from 17 to 235, one byte each.

The immediate byte of EXCHANGE encodes exactly the pairs `n < m` with `1 ≤ n` and `n + m ≤ 30`.

So each decoder is a bijection from the bytes it accepts onto its depths, inverse to its encoder.

SWAPN and EXCHANGE keep the items of the stack and only reorder them.

DUPN pushes a copy of the item at its depth.

Each of the three instructions fails first when it cannot pay its gas.

It then fails with an invalid parameter when its immediate byte encodes no depth or pair.

Last, it fails when the stack has no item at a depth, or when DUPN pushes onto a full stack.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

/-! ## The decoders -/

/-- A property of every byte follows from the property of each number below 256. -/
private theorem forall_byte {P : UInt8 → Prop} (h : ∀ n, n < 256 → P (UInt8.ofNat n))
    (x : UInt8) : P x := by
  simpa using h x.toNat x.toNat_lt

/-- Whether a byte that decodes to a depth is the encoding of that depth, in its range. -/
private def singleRoundTrips (x : UInt8) : Bool :=
  match decodeSingle x with
  | some n => encodeSingle n == x && 17 ≤ n && n ≤ 235
  | none => true

private theorem singleRoundTrips_all :
    (List.range 256).all (fun n => singleRoundTrips (UInt8.ofNat n)) = true := by
  decide +kernel

/-- A byte that decodes to a depth is the encoding of that depth, from 17 to 235. -/
theorem encodeSingle_of_decodeSingle {x : UInt8} {n : Nat} (h : decodeSingle x = some n) :
    encodeSingle n = x ∧ 17 ≤ n ∧ n ≤ 235 := by
  have hx : singleRoundTrips x = true := forall_byte (P := fun x => singleRoundTrips x = true)
    (fun k hk => List.all_eq_true.mp singleRoundTrips_all k (List.mem_range.mpr hk)) x
  simpa [singleRoundTrips, h, and_assoc] using hx

private theorem decodeSingle_encodeSingle_all :
    (List.range 236).all (fun n => n < 17 || decodeSingle (encodeSingle n) == some n) = true := by
  decide +kernel

/-- Each depth from 17 to 235 has an encoding, which decodes back to it. -/
theorem decodeSingle_encodeSingle {n : Nat} (h₁ : 17 ≤ n) (h₂ : n ≤ 235) :
    decodeSingle (encodeSingle n) = some n := by
  have := List.all_eq_true.mp decodeSingle_encodeSingle_all n (List.mem_range.mpr (by omega))
  simpa [show ¬n < 17 by omega] using this

/-- Exactly the bytes from 91 to 127 encode no depth. -/
theorem decodeSingle_eq_none_iff {x : UInt8} :
    decodeSingle x = none ↔ 90 < x.toNat ∧ x.toNat < 128 := by
  unfold decodeSingle
  split <;> simp_all

/-- Whether a byte that decodes to a pair is the encoding of that pair, in its range. -/
private def pairRoundTrips (x : UInt8) : Bool :=
  match decodePair x with
  | some (n, m) => encodePair n m == x && 1 ≤ n && n < m && n + m ≤ 30
  | none => true

private theorem pairRoundTrips_all :
    (List.range 256).all (fun n => pairRoundTrips (UInt8.ofNat n)) = true := by
  decide +kernel

/-- A byte that decodes to a pair encodes that pair, with `1 ≤ n < m` and `n + m ≤ 30`. -/
theorem encodePair_of_decodePair {x : UInt8} {n m : Nat} (h : decodePair x = some (n, m)) :
    encodePair n m = x ∧ 1 ≤ n ∧ n < m ∧ n + m ≤ 30 := by
  have hx : pairRoundTrips x = true := forall_byte (P := fun x => pairRoundTrips x = true)
    (fun k hk => List.all_eq_true.mp pairRoundTrips_all k (List.mem_range.mpr hk)) x
  simpa [pairRoundTrips, h, and_assoc] using hx

private theorem decodePair_encodePair_all :
    (List.range 31).all (fun m => (List.range m).all fun n =>
      n < 1 || 30 < n + m || decodePair (encodePair n m) == some (n, m)) = true := by
  decide +kernel

/-- Each pair `n < m` with `1 ≤ n` and `n + m ≤ 30` has an encoding, which decodes back to it. -/
theorem decodePair_encodePair {n m : Nat} (h₁ : 1 ≤ n) (h₂ : n < m) (h₃ : n + m ≤ 30) :
    decodePair (encodePair n m) = some (n, m) := by
  have := List.all_eq_true.mp
    (List.all_eq_true.mp decodePair_encodePair_all m (List.mem_range.mpr (by omega)))
    n (List.mem_range.mpr h₂)
  simpa [show ¬n < 1 by omega, show ¬30 < n + m by omega] using this

/-- Exactly the bytes from 82 to 127 encode no pair. -/
theorem decodePair_eq_none_iff {x : UInt8} :
    decodePair x = none ↔ 81 < x.toNat ∧ x.toNat < 128 := by
  unfold decodePair
  split
  · simp_all
  · refine ⟨fun h => ?_, fun h => absurd h ‹_›⟩
    simp only at h
    split at h <;> simp at h

/-! ## The stack -/

/-- Exchanging two items keeps the items of the stack, in another order. -/
theorem exchangeItems_perm {stack stack' : Stack} {i j : Nat}
    (h : exchangeItems stack i j = some stack') : stack'.val.Perm stack.val := by
  unfold exchangeItems at h
  split at h
  · rename_i a b ha hb
    cases h
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hb
    exact List.set_set_perm hi hj
  · cases h

/-- Exchanging two items succeeds exactly when the stack has an item at both depths. -/
theorem exchangeItems_isSome {stack : Stack} {i j : Nat} :
    (exchangeItems stack i j).isSome ↔ i < stack.val.length ∧ j < stack.val.length := by
  unfold exchangeItems
  split
  · rename_i ha hb
    simp [(List.getElem?_eq_some_iff.mp ha).1, (List.getElem?_eq_some_iff.mp hb).1]
  · rename_i hne
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    intro hi hj
    exact hne _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- SWAPN keeps the items of the stack, in another order. -/
theorem swapnStep_perm {evm after : Evm fork Meter} (h : swapnStep evm = .ok after) :
    after.stack.val.Perm evm.stack.val := by
  obtain ⟨paid, h1, h⟩ := Base.bind_ok_iff.mp h
  have hstack : paid.stack = evm.stack := by
    obtain ⟨_, -, rfl⟩ := chargeGas_eq_ok_iff_charge.mp h1
    rfl
  split at h
  · split at h
    · cases h
      rename_i hx
      exact hstack ▸ exchangeItems_perm hx
    · cases h
  · cases h

/-- EXCHANGE keeps the items of the stack, in another order. -/
theorem exchangeStep_perm {evm after : Evm fork Meter} (h : exchangeStep evm = .ok after) :
    after.stack.val.Perm evm.stack.val := by
  obtain ⟨paid, h1, h⟩ := Base.bind_ok_iff.mp h
  have hstack : paid.stack = evm.stack := by
    obtain ⟨_, -, rfl⟩ := chargeGas_eq_ok_iff_charge.mp h1
    rfl
  split at h
  · split at h
    · cases h
      rename_i hx
      exact hstack ▸ exchangeItems_perm hx
    · cases h
  · cases h

/-- SWAPN and EXCHANGE keep the number of items of the stack. -/
theorem swapnStep_length {evm after : Evm fork Meter} (h : swapnStep evm = .ok after) :
    after.stack.val.length = evm.stack.val.length :=
  (swapnStep_perm h).length_eq

/-- EXCHANGE keeps the number of items of the stack. -/
theorem exchangeStep_length {evm after : Evm fork Meter} (h : exchangeStep evm = .ok after) :
    after.stack.val.length = evm.stack.val.length :=
  (exchangeStep_perm h).length_eq

/-- DUPN at depth `n` pushes a copy of the item at depth `n`, counted from 1 at the top. -/
theorem dupnStep_stack {evm after : Evm fork Meter} {n : Nat}
    (hn : decodeSingle (immediateByte evm.code evm.pc) = some n)
    (h : dupnStep evm = .ok after) :
    ∃ x, evm.stack.val[n - 1]? = some x ∧ after.stack.val = x :: evm.stack.val := by
  obtain ⟨paid, h1, h⟩ := Base.bind_ok_iff.mp h
  have hpaid : paid = { evm with gas := paid.gas } := by
    obtain ⟨_, -, rfl⟩ := chargeGas_eq_ok_iff_charge.mp h1
    rfl
  rw [hpaid] at h
  simp only [hn] at h
  split at h
  · cases h
  · rename_i x hx
    obtain ⟨pushed, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    refine ⟨x, hx, ?_⟩
    simp only [pushWord, Stack.push, bind, Except.bind] at h2
    split at h2
    · cases h2
    · rename_i v hv
      cases h2
      split at hv
      · cases hv
      · cases hv
        rfl

/-- DUPN keeps the message, the state and the substate. -/
theorem dupnStep_sameContext {evm after : Evm fork Meter} (h : dupnStep evm = .ok after) :
    SameContext evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
    · obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact ((chargeGas_sameContext h1).trans (pushWord_sameContext h2)).advance _
  · cases h

/-- SWAPN keeps the message, the state and the substate. -/
theorem swapnStep_sameContext {evm after : Evm fork Meter} (h : swapnStep evm = .ok after) :
    SameContext evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
      have := chargeGas_sameContext h1
      exact ⟨this.message, this.state, this.substate⟩
    · cases h
  · cases h

/-- EXCHANGE keeps the message, the state and the substate. -/
theorem exchangeStep_sameContext {evm after : Evm fork Meter} (h : exchangeStep evm = .ok after) :
    SameContext evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
      have := chargeGas_sameContext h1
      exact ⟨this.message, this.state, this.substate⟩
    · cases h
  · cases h

/-- DUPN keeps memory. -/
theorem memory_dupnStep {evm after : Evm fork Meter} (h : dupnStep evm = .ok after) :
    after.memory = evm.memory := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
    · obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      cases h
      simp only [advance, memory_pushWord h2, memory_chargeGas h1]
  · cases h

/-- SWAPN keeps memory. -/
theorem memory_swapnStep {evm after : Evm fork Meter} (h : swapnStep evm = .ok after) :
    after.memory = evm.memory := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
      simp only [advance, memory_chargeGas h1]
    · cases h
  · cases h

/-- EXCHANGE keeps memory. -/
theorem memory_exchangeStep {evm after : Evm fork Meter} (h : exchangeStep evm = .ok after) :
    after.memory = evm.memory := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · split at h
    · cases h
      simp only [advance, memory_chargeGas h1]
    · cases h
  · cases h

/-! ## The order of the failures -/

/-- DUPN fails first when the meter cannot pay its 3 gas, whatever its immediate byte and stack.

It fails with the error of the charge. -/
theorem dupnStep_of_charge_eq_error {evm : Evm fork Meter} {e : EvmError}
    (hc : GasMeter.charge evm.gas OPCODE_DUPN = .error e) : dupnStep evm = .error e := by
  simp [dupnStep, chargeGas, hc, bind, Except.bind]

/-- SWAPN fails first when the meter cannot pay its 3 gas, whatever its immediate byte and stack.

It fails with the error of the charge. -/
theorem swapnStep_of_charge_eq_error {evm : Evm fork Meter} {e : EvmError}
    (hc : GasMeter.charge evm.gas OPCODE_SWAPN = .error e) : swapnStep evm = .error e := by
  simp [swapnStep, chargeGas, hc, bind, Except.bind]

/-- EXCHANGE fails first when the meter cannot pay its 3 gas, whatever its immediate byte and stack.

It fails with the error of the charge. -/
theorem exchangeStep_of_charge_eq_error {evm : Evm fork Meter} {e : EvmError}
    (hc : GasMeter.charge evm.gas OPCODE_EXCHANGE = .error e) : exchangeStep evm = .error e := by
  simp [exchangeStep, chargeGas, hc, bind, Except.bind]

/-- After DUPN pays its gas, it fails in exactly three cases, which it checks in this order.

Its immediate byte encodes no depth, and the error is an invalid parameter.

Or the byte encodes a depth `n`, and the stack has fewer than `n` items, so it underflows.

Or the stack has at least `n` items but is full, so the push overflows it. -/
theorem dupnStep_eq_error_iff {evm : Evm fork Meter} {g : Meter} {e : EvmError}
    (hc : GasMeter.charge evm.gas OPCODE_DUPN = .ok g) :
    dupnStep evm = .error e ↔
      (decodeSingle (immediateByte evm.code evm.pc) = none ∧ e = .invalidParameter) ∨
      ∃ n, decodeSingle (immediateByte evm.code evm.pc) = some n ∧
        ((evm.stack.val.length < n ∧ e = .stackUnderflow) ∨
          (n ≤ evm.stack.val.length ∧ evm.stack.val.length = STACK_LIMIT ∧
            e = .stackOverflow)) := by
  simp only [dupnStep, chargeGas, hc, bind, Except.bind, pure, Except.pure]
  cases hd : decodeSingle (immediateByte evm.code evm.pc) with
  | none => simp [eq_comm]
  | some n =>
    have h17 := (encodeSingle_of_decodeSingle hd).2.1
    simp only [reduceCtorEq, false_and, false_or, Option.some.injEq, exists_eq_left']
    cases hx : evm.stack.val[n - 1]? with
    | none =>
      have : evm.stack.val.length < n := by
        have := List.getElem?_eq_none_iff.mp hx; omega
      simp [this, eq_comm, Nat.not_le_of_lt this]
    | some x =>
      have : n ≤ evm.stack.val.length := by
        have := (List.getElem?_eq_some_iff.mp hx).1; omega
      by_cases hl : evm.stack.val.length = STACK_LIMIT
      · rw [hl] at this
        simp [pushWord, Stack.push, hl, bind, Except.bind, Nat.not_lt_of_le this, this, eq_comm]
      · simp [pushWord, Stack.push, hl, bind, Except.bind, pure, Except.pure,
          Nat.not_lt_of_le this]

/-- After SWAPN pays its gas, it fails in exactly two cases, which it checks in this order.

Its immediate byte encodes no depth, and the error is an invalid parameter.

Or the byte encodes a depth `n`, and the stack has at most `n` items, so it underflows. -/
theorem swapnStep_eq_error_iff {evm : Evm fork Meter} {g : Meter} {e : EvmError}
    (hc : GasMeter.charge evm.gas OPCODE_SWAPN = .ok g) :
    swapnStep evm = .error e ↔
      (decodeSingle (immediateByte evm.code evm.pc) = none ∧ e = .invalidParameter) ∨
      ∃ n, decodeSingle (immediateByte evm.code evm.pc) = some n ∧
        evm.stack.val.length ≤ n ∧ e = .stackUnderflow := by
  simp only [swapnStep, chargeGas, hc, bind, Except.bind, pure, Except.pure]
  cases hd : decodeSingle (immediateByte evm.code evm.pc) with
  | none => simp [eq_comm]
  | some n =>
    have h17 := (encodeSingle_of_decodeSingle hd).2.1
    simp only [reduceCtorEq, false_and, false_or, Option.some.injEq, exists_eq_left']
    have hs := exchangeItems_isSome (stack := evm.stack) (i := 0) (j := n)
    cases hx : exchangeItems evm.stack 0 n with
    | none =>
      simp only [hx, Option.isSome_none, Bool.false_eq_true, false_iff, not_and] at hs
      have : evm.stack.val.length ≤ n := Nat.not_lt.mp fun hlt => hs (by omega) hlt
      simp [this, eq_comm]
    | some s =>
      simp only [hx, Option.isSome_some, true_iff] at hs
      simp [Nat.not_le_of_lt hs.2]

/-- After EXCHANGE pays its gas, it fails in exactly two cases, which it checks in this order.

Its immediate byte encodes no pair, and the error is an invalid parameter.

Or the byte encodes a pair `n < m`, and the stack has at most `m` items, so it underflows. -/
theorem exchangeStep_eq_error_iff {evm : Evm fork Meter} {g : Meter} {e : EvmError}
    (hc : GasMeter.charge evm.gas OPCODE_EXCHANGE = .ok g) :
    exchangeStep evm = .error e ↔
      (decodePair (immediateByte evm.code evm.pc) = none ∧ e = .invalidParameter) ∨
      ∃ n m, decodePair (immediateByte evm.code evm.pc) = some (n, m) ∧
        evm.stack.val.length ≤ m ∧ e = .stackUnderflow := by
  simp only [exchangeStep, chargeGas, hc, bind, Except.bind, pure, Except.pure]
  cases hd : decodePair (immediateByte evm.code evm.pc) with
  | none => simp [eq_comm]
  | some p =>
    obtain ⟨n, m⟩ := p
    have hnm := (encodePair_of_decodePair hd).2.2.1
    simp only [reduceCtorEq, false_and, false_or, Option.some.injEq, Prod.mk.injEq]
    have hs := exchangeItems_isSome (stack := evm.stack) (i := n) (j := m)
    cases hx : exchangeItems evm.stack n m with
    | none =>
      simp only [hx, Option.isSome_none, Bool.false_eq_true, false_iff, not_and] at hs
      have : evm.stack.val.length ≤ m := Nat.not_lt.mp fun hlt => hs (by omega) hlt
      simp only [Except.error.injEq, eq_comm (a := EvmError.stackUnderflow)]
      exact ⟨fun h => ⟨n, m, ⟨rfl, rfl⟩, this, h⟩, fun ⟨_, _, _, _, h⟩ => h⟩
    | some s =>
      simp only [hx, Option.isSome_some, true_iff] at hs
      simp [Nat.not_le_of_lt hs.2]

/-- With one counter of gas, DUPN fails out of gas when it has less than 3 gas. -/
theorem dupnStep_of_gas_lt {evm : Evm fork Nat} (h : evm.gas < OPCODE_DUPN) :
    dupnStep evm = .error .outOfGas :=
  dupnStep_of_charge_eq_error (by simp [GasMeter.charge, h])

/-- With one counter of gas, SWAPN fails out of gas when it has less than 3 gas. -/
theorem swapnStep_of_gas_lt {evm : Evm fork Nat} (h : evm.gas < OPCODE_SWAPN) :
    swapnStep evm = .error .outOfGas :=
  swapnStep_of_charge_eq_error (by simp [GasMeter.charge, h])

/-- With one counter of gas, EXCHANGE fails out of gas when it has less than 3 gas. -/
theorem exchangeStep_of_gas_lt {evm : Evm fork Nat} (h : evm.gas < OPCODE_EXCHANGE) :
    exchangeStep evm = .error .outOfGas :=
  exchangeStep_of_charge_eq_error (by simp [GasMeter.charge, h])

end EthLib.Execution.Evm
