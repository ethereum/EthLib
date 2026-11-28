module

public import EthLib.Execution.Proofs.Evm.OpTables.Follows
public import EthLib.Execution.Proofs.Evm.Machine.Stack

/-!
# Proofs: the words, the gas and the code of the parts of an instruction

Each part of an instruction takes and leaves words on the stack, pays gas and keeps the code.

Parts in sequence add their prices, and their words where the second takes what the first leaves.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A change of frame that takes `takes` words, leaves `leaves` words and pays at least `price`.

It keeps the code and its valid jump destinations. -/
structure Moves (takes leaves price : Nat) (before after : Evm fork Meter) : Prop where
  /-- The stack holds the words that the change takes. -/
  enough : takes ≤ before.stack.val.length
  /-- The change takes its words and leaves its words. -/
  stack : after.stack.val.length + takes = before.stack.val.length + leaves
  /-- The change pays at least its price. -/
  gas : GasMeter.gasHeld after.gas + price ≤ GasMeter.gasHeld before.gas
  /-- The change keeps the code. -/
  code : after.code = before.code
  /-- The change keeps the valid jump destinations. -/
  jumps : after.validJumpDestinations = before.validJumpDestinations

namespace Moves

/-- A change that keeps the stack, the gas, the code and the destinations moves nothing. -/
theorem of_eq {before after : Evm fork Meter} (stack : after.stack = before.stack)
    (gas : after.gas = before.gas) (code : after.code = before.code)
    (jumps : after.validJumpDestinations = before.validJumpDestinations) :
    Moves 0 0 0 before after :=
  ⟨Nat.zero_le _, by rw [stack], by rw [gas]; omega, code, jumps⟩

/-- A change that keeps the height of the stack, the gas, the code and the destinations. -/
theorem of_length {before after : Evm fork Meter}
    (stack : after.stack.val.length = before.stack.val.length) (gas : after.gas = before.gas)
    (code : after.code = before.code)
    (jumps : after.validJumpDestinations = before.validJumpDestinations) :
    Moves 0 0 0 before after :=
  ⟨Nat.zero_le _, by rw [stack], by rw [gas]; omega, code, jumps⟩

/-- A change that pays at least `n`, and takes and leaves the words given. -/
theorem of_pays {before after : Evm fork Meter} {t l n : Nat} (paid : Pays n before after)
    (enough : t ≤ before.stack.val.length)
    (stack : after.stack.val.length + t = before.stack.val.length + l)
    (code : after.code = before.code)
    (jumps : after.validJumpDestinations = before.validJumpDestinations) :
    Moves t l n before after :=
  ⟨enough, stack, paid.gasHeld, code, jumps⟩

/-- Every frame moves nothing to itself. -/
theorem refl (evm : Evm fork Meter) : Moves 0 0 0 evm evm :=
  of_eq rfl rfl rfl rfl

/-- Two changes in a row: the second takes first the words that the first leaves. -/
theorem trans {a b c : Evm fork Meter} {t₁ l₁ p₁ t₂ l₂ p₂ : Nat} (hab : Moves t₁ l₁ p₁ a b)
    (hbc : Moves t₂ l₂ p₂ b c) : Moves (t₁ + (t₂ - l₁)) (l₂ + (l₁ - t₂)) (p₁ + p₂) a c := by
  have := hab.enough
  have := hab.stack
  have := hbc.enough
  have := hbc.stack
  have := hab.gas
  have := hbc.gas
  exact ⟨by omega, by omega, by omega, hbc.code.trans hab.code, hbc.jumps.trans hab.jumps⟩

/-- The same change, with any lower price. -/
theorem weaken {a b : Evm fork Meter} {t l p t' l' p' : Nat} (h : Moves t l p a b)
    (ht : t = t' := by omega) (hl : l = l' := by omega) (hp : p' ≤ p := by omega) :
    Moves t' l' p' a b := by
  subst ht hl
  have := h.gas
  exact ⟨h.enough, h.stack, by omega, h.code, h.jumps⟩

/-- A change also takes and leaves `k` more words below its own, when the stack holds them. -/
theorem deepen {a b : Evm fork Meter} {t l p : Nat} (h : Moves t l p a b) (k : Nat)
    (hk : t + k ≤ a.stack.val.length) : Moves (t + k) (l + k) p a b :=
  ⟨hk, by have := h.stack; omega, h.gas, h.code, h.jumps⟩

/-- A change followed by one that keeps the stack, the gas and the code. -/
theorem keep {a b c : Evm fork Meter} {t l p : Nat} (h : Moves t l p a b)
    (stack : c.stack = b.stack) (gas : c.gas = b.gas) (code : c.code = b.code)
    (jumps : c.validJumpDestinations = b.validJumpDestinations) : Moves t l p a c :=
  (h.trans (of_eq stack gas code jumps)).weaken

/-- A change that takes, leaves and pays as the tables say follows them. -/
theorem toFollows {a b : Evm fork Meter} {t l p : Nat} (h : Moves t l p a b) :
    FollowsTables t l p a b :=
  ⟨h.enough, h.code, h.jumps, .inl ⟨h.stack, h.gas⟩⟩

/-- A change followed by one that keeps the stack, the gas and the code follows the tables. -/
theorem follows {a b c : Evm fork Meter} {t l p : Nat} (h : Moves t l p a b)
    (stack : c.stack = b.stack) (gas : c.gas = b.gas) (code : c.code = b.code)
    (jumps : c.validJumpDestinations = b.validJumpDestinations) : FollowsTables t l p a c :=
  (h.keep stack gas code jumps).toFollows

end Moves

/-- A step that has taken its words, then halts without an abort, follows the tables. -/
theorem FollowsTables.halt {a b : Evm fork Meter} {t l p t' p' : Nat} (h : Moves t' 0 p' a b)
    (enough : t ≤ t') {e : EvmError} (he : e.aborts = false) :
    FollowsTables t l p a (exceptionalHalt b e) := by
  have := h.stack
  exact ⟨Nat.le_trans enough h.enough, h.code, h.jumps, .inr ⟨b, e, he, h.code, by omega, rfl⟩⟩

/-! ## The parts -/

/-- A pop takes one word. -/
theorem popWord_moves {evm after : Evm fork Meter} {x : U256}
    (h : popWord evm = .ok (x, after)) : Moves 1 0 0 evm after := by
  have paid := popWord_pays h
  obtain ⟨⟨y, st⟩, hp, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have := Stack.pop_eq_ok_iff.mp hp
  exact .of_pays paid (by simp [this]) (by simp [this]) rfl rfl

/-- A push leaves one word. -/
theorem pushWord_moves {evm after : Evm fork Meter} {x : U256}
    (h : pushWord evm x = .ok after) : Moves 0 1 0 evm after := by
  have paid := pushWord_pays h
  obtain ⟨st, hp, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact .of_pays paid (Nat.zero_le _) (by simp [(Stack.push_eq_ok_iff.mp hp).2]) rfl rfl

/-- A move of the program counter moves nothing. -/
theorem advance_moves (evm : Evm fork Meter) (n : Nat) : Moves 0 0 0 evm (advance evm n) :=
  .of_eq rfl rfl rfl rfl

/-- An access to an address moves nothing. -/
theorem accessAddress_moves (evm : Evm fork Meter) (address : Address) :
    Moves 0 0 0 evm (accessAddress evm address).2 := by
  unfold accessAddress
  split <;> exact .of_eq rfl rfl rfl rfl

/-- An access to a slot moves nothing. -/
theorem accessStorageKey_moves (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    Moves 0 0 0 evm (accessStorageKey evm address key).2 := by
  unfold accessStorageKey
  split <;> exact .of_eq rfl rfl rfl rfl

/-- A record of a read moves nothing. -/
theorem recordAccountRead_moves (evm : Evm fork Meter) (address : Address) :
    Moves 0 0 0 evm (recordAccountRead evm address) :=
  .of_eq rfl rfl rfl rfl

/-- A record of a read of a slot moves nothing. -/
theorem recordStorageRead_moves (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    Moves 0 0 0 evm (recordStorageRead evm address key) :=
  .of_eq rfl rfl rfl rfl

variable [LawfulGasMeter Meter]

/-- A charge of `amount` pays `amount`. -/
theorem chargeGas_moves {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeGas evm amount = .ok after) : Moves 0 0 amount evm after := by
  have paid := chargeGas_pays h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact .of_pays paid (Nat.zero_le _) rfl rfl rfl

/-- A charge of state gas pays nothing. -/
theorem chargeStateGas_moves {evm after : Evm fork Meter} {amount : Nat}
    (h : chargeStateGas evm amount = .ok after) : Moves 0 0 0 evm after := by
  have paid := chargeStateGas_pays h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact .of_pays paid (Nat.zero_le _) rfl rfl rfl

/-- A refill of state gas pays nothing. -/
theorem refillStateGas_moves (evm : Evm fork Meter) (amount : Nat) :
    Moves 0 0 0 evm (refillStateGas evm amount) :=
  .of_pays (refillStateGas_pays evm amount) (Nat.zero_le _) rfl rfl rfl

/-- A frame that passes on its reservoir pays nothing. -/
theorem drain_moves (evm : Evm fork Meter) :
    Moves 0 0 0 evm { evm with gas := GasMeter.drain evm.gas } :=
  .of_pays (Pays.of_eq rfl rfl).drain (Nat.zero_le _) rfl rfl rfl

/-- A charge of a price and of the growth of memory pays at least the price. -/
theorem chargeGasAndMemory_moves {evm after : Evm fork Meter} {cost : Nat}
    {ranges : List (U256 × U256)} (h : chargeGasAndMemory evm cost ranges = .ok after) :
    Moves 0 0 cost evm after := by
  have paid := chargeGasAndMemory_pays h
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have m := chargeGas_moves h1
  exact .of_pays paid (Nat.zero_le _) m.stack m.code m.jumps

/-! ## The shapes of the simple instructions -/

/-- An instruction that reads the frame leaves a word and pays at least its price. -/
theorem readFrame_moves {cost : Nat} {value : Evm fork Meter → U256} {evm after : Evm fork Meter}
    (h : readFrame cost value evm = .ok after) : Moves 0 1 cost evm after := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((chargeGas_moves h1).trans (pushWord_moves h2)).trans (advance_moves _ _)).weaken

/-- An instruction that reads a number leaves a word and pays at least its price. -/
theorem readNumber_moves {cost : Nat} {value : Evm fork Meter → Nat} {evm after : Evm fork Meter}
    (h : readNumber cost value evm = .ok after) : Moves 0 1 cost evm after := by
  unfold readNumber at h
  split at h
  · exact readFrame_moves h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h

/-- An instruction with one operand takes one word and leaves one. -/
theorem unaryOp_moves {cost : Nat} {f : U256 → U256} {evm after : Evm fork Meter}
    (h : unaryOp cost f evm = .ok after) : Moves 1 1 cost evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_moves h1).trans (chargeGas_moves h2)).trans (pushWord_moves h3)).trans
    (advance_moves _ _)).weaken

/-- An instruction with two operands takes two words and leaves one. -/
theorem binaryOp_moves {cost : Nat} {f : U256 → U256 → U256} {evm after : Evm fork Meter}
    (h : binaryOp cost f evm = .ok after) : Moves 2 1 cost evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((((popWord_moves h1).trans (popWord_moves h2)).trans (chargeGas_moves h3)).trans
    (pushWord_moves h4)).trans (advance_moves _ _)).weaken

/-- An instruction with three operands takes three words and leaves one. -/
theorem ternaryOp_moves {cost : Nat} {f : U256 → U256 → U256 → U256} {evm after : Evm fork Meter}
    (h : ternaryOp cost f evm = .ok after) : Moves 3 1 cost evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((((popWord_moves h1).trans (popWord_moves h2)).trans (popWord_moves h3)).trans
    (chargeGas_moves h4)).trans (pushWord_moves h5)).trans (advance_moves _ _)).weaken

end EthLib.Execution.Evm
