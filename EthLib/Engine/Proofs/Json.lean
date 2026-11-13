module

public import EthLib.Engine.Json
public import EthLib.Serialization.Proofs.JsonRpc
public import EthLib.Execution.Proofs.Rpc.Json
public import EthLib.Base.Except
public import EthLib.Base.Proofs.Fork

/-!
# Proofs: the JSON decoders of the Engine API

A shared reader, run as an Engine decoding, returns what the reader returns.

A reader that rejects its input becomes an invalid parameter, for the same reason.

A decoded payload has version 1, 2 or 3 of the structure.

It holds the withdrawals exactly from version 2.

It holds the two blob gas fields exactly in version 3.

A payload of version 4 decodes only when its object holds exactly the fields of that version.

Its access list and its slot must then decode.

The rest must decode as a payload of an earlier version.

A field from a fork decodes exactly when it is present from that fork on and absent before.

A field decodes from an option exactly when reading the field back gives that option.
-/

public section

namespace EthLib.Engine.Json

open EthLib.Base
open EthLib.Serialization.JsonRpc

/-- A failure with an invalid parameter is that error, never a value. -/
@[simp] theorem invalid_eq {α : Type} (reason : String) :
    (invalid reason : Decode α) = .error (.invalidParams reason) := rfl

/-- A shared reader returns a value as a decoding exactly when it returns it alone. -/
@[simp] theorem liftM_eq_ok_iff {α : Type} {r : Read α} {a : α} :
    (liftM r : Decode α) = .ok a ↔ r = .ok a := by
  cases r <;> simp [liftM, monadLift, MonadLift.monadLift, lift, Except.mapError]

/-- A shared reader that rejects its input fails as a decoding with an invalid parameter. -/
@[simp] theorem liftM_error {α : Type} (reason : String) :
    (liftM (.error reason : Read α) : Decode α) = .error (.invalidParams reason) := rfl

/-- A value that a shared reader returns is what the decoding returns. -/
@[simp] theorem liftM_ok {α : Type} (a : α) : (liftM (.ok a : Read α) : Decode α) = .ok a :=
  rfl

/-- A decoded payload has version 1, 2 or 3, and its optional fields match that version. -/
theorem shape_of_anyPayload {j : Lean.Json} {p : AnyPayload} (h : anyPayload j = .ok p) :
    (p.version = 1 ∨ p.version = 2 ∨ p.version = 3) ∧ (p.withdrawals.isSome ↔ 2 ≤ p.version) ∧
      (p.blobGasUsed.isSome ↔ 3 ≤ p.version) ∧ (p.excessBlobGas.isSome ↔ 3 ≤ p.version) := by
  unfold anyPayload at h
  -- Inline the steps that the decoder shares between its branches.
  dsimp only at h
  -- Split each step of the decoder: a failing step contradicts the success, and a read value stays.
  repeat' (first
    | (simp only [invalid_eq] at h; cases h; done)
    | (obtain ⟨_, step, h⟩ := bind_ok_iff.mp h
       first | cases step | obtain ⟨_, -, rfl⟩ := map_ok_iff.mp step | skip)
    | split at h)
  -- Each success fixes the version and the fields.
  all_goals (cases h; simp)

/-- A decoded payload has version 1, 2 or 3. -/
theorem version_of_anyPayload {j : Lean.Json} {p : AnyPayload} (h : anyPayload j = .ok p) :
    p.version = 1 ∨ p.version = 2 ∨ p.version = 3 :=
  (shape_of_anyPayload h).1

/-- A decoded payload holds the withdrawals exactly from version 2. -/
theorem withdrawals_isSome_iff_of_anyPayload {j : Lean.Json} {p : AnyPayload}
    (h : anyPayload j = .ok p) : p.withdrawals.isSome ↔ 2 ≤ p.version :=
  (shape_of_anyPayload h).2.1

/-- A decoded payload holds the blob gas used exactly in version 3. -/
theorem blobGasUsed_isSome_iff_of_anyPayload {j : Lean.Json} {p : AnyPayload}
    (h : anyPayload j = .ok p) : p.blobGasUsed.isSome ↔ 3 ≤ p.version :=
  (shape_of_anyPayload h).2.2.1

/-- A decoded payload holds the excess blob gas exactly in version 3. -/
theorem excessBlobGas_isSome_iff_of_anyPayload {j : Lean.Json} {p : AnyPayload}
    (h : anyPayload j = .ok p) : p.excessBlobGas.isSome ↔ 3 ≤ p.version :=
  (shape_of_anyPayload h).2.2.2

/-- A payload of version 4 decodes exactly when it has the fields of version 4 and each decodes.

Fields whose value is null count as absent.

The object without the access list and the slot must decode as a payload of version 1, 2 or 3.

The access list must decode as a byte string, and the slot as a 64-bit number. -/
theorem payloadV4_eq_ok_iff {j : Lean.Json} {p : AnyPayload} {blockAccessList : ByteArray}
    {slotNumber : UInt64} :
    payloadV4 j = .ok (p, blockAccessList, slotNumber) ↔
      ∃ fs, fields "payload" j = .ok fs ∧ hasExactly fs payloadFieldsV4 = true ∧
        anyPayload (Lean.Json.mkObj
          (fs.filter fun (name, _) => !amsterdamFields.contains name)) = .ok p ∧
        ∃ list slot, fs.lookup "blockAccessList" = some list ∧ fs.lookup "slotNumber" = some slot ∧
          bytes "blockAccessList" list = .ok blockAccessList ∧
          uint64 "slotNumber" slot = .ok slotNumber := by
  unfold payloadV4
  simp only [bind_ok_iff, liftM_eq_ok_iff]
  constructor
  · rintro ⟨fs, hfs, h⟩
    by_cases hc : hasExactly fs payloadFieldsV4 = true
    · rw [ite_eq_left hc] at h
      simp only [bind_ok_iff, liftM_eq_ok_iff, field_eq_ok_iff] at h
      obtain ⟨a, ha, l, hl, b, hb, s, hs, n, hn, hr⟩ := h
      cases hr
      exact ⟨fs, hfs, hc, ha, l, s, hl, hs, hb, hn⟩
    -- An object with other fields fails with an invalid parameter, never with a payload.
    · rw [ite_eq_right hc, bind_ok_iff] at h
      obtain ⟨_, hInvalid, -⟩ := h
      cases hInvalid
  · rintro ⟨fs, hfs, hc, ha, l, s, hl, hs, hb, hn⟩
    refine ⟨fs, hfs, ?_⟩
    rw [ite_eq_left hc]
    simp only [bind_ok_iff, liftM_eq_ok_iff, field_eq_ok_iff]
    exact ⟨p, ha, l, hl, _, hb, s, hs, _, hn, rfl⟩

/-! ## A field from a fork -/

section Since

variable {fork : Fork}

/-- A field from fork `f` decodes exactly when its presence agrees with `f ≤ fork`. -/
theorem exists_since_iff {α : Type} {f : Fork} {what : String} {o : Option α} :
    (∃ x : Since f fork α, since what o = .ok x) ↔ (o.isSome ↔ f ≤ fork) := by
  -- Each of the four cases either succeeds or fails with an invalid parameter.
  cases o <;> unfold since <;> by_cases h : f ≤ fork <;> simp [h, pure, Except.pure] <;>
    exact ⟨_, rfl⟩

/-- Reading back a decoded field from a fork gives the option it was decoded from. -/
theorem sinceValue_of_since {α : Type} {f : Fork} {what : String} {o : Option α}
    {x : Since f fork α} (h : since what o = .ok x) : sinceValue x = o := by
  -- The two cases that fail cannot give the field, and the other two give back the option.
  cases o <;> unfold since at h <;> by_cases hf : f ≤ fork <;> simp [hf, pure, Except.pure] at h
  · simp [sinceValue, hf]
  · cases h
    simp [sinceValue, hf]

/-- Decoding the value of a field from a fork gives back the field. -/
theorem since_sinceValue {α : Type} {f : Fork} {what : String} (x : Since f fork α) :
    since what (sinceValue x) = .ok x := by
  unfold sinceValue since
  by_cases hf : f ≤ fork
  · simp only [hf, dite_true, ite_true]
    exact congrArg Except.ok (Since.eq_const hf x).symm
  · simp only [hf, dite_false]
    exact congrArg Except.ok (Since.eq_of_not_le hf _ _)

/-- A field from a fork decodes from an option exactly when reading it back gives that option. -/
theorem since_eq_ok_iff {α : Type} {f : Fork} {what : String} {o : Option α}
    {x : Since f fork α} : since what o = .ok x ↔ sinceValue x = o :=
  ⟨sinceValue_of_since, fun h => h ▸ since_sinceValue x⟩

end Since

end EthLib.Engine.Json

namespace EthLib.Engine

/-- A request passes the size check exactly when it asks for at most as many items as allowed. -/
theorem checkRequestSize_eq_ok_iff (maxRequest count : Nat) :
    checkRequestSize maxRequest count = .ok () ↔ count ≤ maxRequest := by
  unfold checkRequestSize
  by_cases h : maxRequest < count
  · simp [h, throw, throwThe, MonadExceptOf.throw]
  · simp [h, pure, Except.pure]; omega

/-- A request is too large exactly when it asks for more items than the node takes. -/
theorem checkRequestSize_eq_error_iff (maxRequest count : Nat) (e : EngineError) :
    checkRequestSize maxRequest count = .error e ↔ maxRequest < count ∧ e = .tooLargeRequest := by
  unfold checkRequestSize
  by_cases h : maxRequest < count
  · simp [h, throw, throwThe, MonadExceptOf.throw, eq_comm]
  · simp [h, pure, Except.pure]

end EthLib.Engine
