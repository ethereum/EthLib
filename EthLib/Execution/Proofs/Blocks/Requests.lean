module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.Requests

/-!
# Proofs: the requests of a block

A list of requests with no data, only its type byte, leaves the requests hash unchanged.

A deposit log in the layout of the Solidity ABI gives back its five fields, in order.

The parser accepts a log exactly when it has 576 bytes and the ten words of the layout.

So an accepted log gives a request of 192 bytes.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base

/-- Two errors with one code come from one constructor. -/
theorem DepositError.code_injective (e₁ e₂ : DepositError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [DepositError.code] at h; exact absurd h (by decide))

/-! ## The requests hash -/

/-- A list with no data does not enter the requests hash. -/
theorem requestsHash_cons_of_size_le {r : ByteArray} (h : r.size ≤ 1) (requests : List ByteArray) :
    requestsHash (r :: requests) = requestsHash requests := by
  simp [requestsHash, Nat.not_lt.mpr h]

/-- Dropping the lists with no data leaves the requests hash unchanged. -/
theorem requestsHash_filter (requests : List ByteArray) :
    requestsHash (requests.filter (·.size > 1)) = requestsHash requests := by
  simp [requestsHash, List.filter_filter]

/-! ## Deposit logs -/

/-- The data of a deposit log, in the layout of the Solidity ABI.

The head gives the offset of each field.

Each field follows its 32-byte size, padded with zeros to a multiple of 32 bytes. -/
def depositEvent (pubkey : Vector UInt8 48) (credentials : Bytes32) (amount : Bytes8)
    (signature : Vector UInt8 96) (index : Bytes8) : List UInt8 :=
  natToBytes 32 160 ++ natToBytes 32 256 ++ natToBytes 32 320 ++ natToBytes 32 384
    ++ natToBytes 32 512
    ++ natToBytes 32 48 ++ pubkey.toList ++ List.replicate 16 0
    ++ natToBytes 32 32 ++ credentials.toList
    ++ natToBytes 32 8 ++ amount.toList ++ List.replicate 24 0
    ++ natToBytes 32 96 ++ signature.toList
    ++ natToBytes 32 8 ++ index.toList ++ List.replicate 24 0

/-- A deposit log in the layout of the Solidity ABI gives its five fields, one after the other. -/
theorem depositRequestOfEvent_depositEvent (pubkey : Vector UInt8 48) (credentials : Bytes32)
    (amount : Bytes8) (signature : Vector UInt8 96) (index : Bytes8) :
    depositRequestOfEvent ⟨(depositEvent pubkey credentials amount signature index).toArray⟩ =
      .ok ⟨(pubkey.toList ++ credentials.toList ++ amount.toList ++ signature.toList
        ++ index.toList).toArray⟩ := by
  simp [depositRequestOfEvent, depositEvent, DEPOSIT_EVENT_FIELDS, DEPOSIT_EVENT_LENGTH, wordAt,
    fieldAt, List.drop_append, List.take_append, natToBytes_length, List.zipIdx,
    bytesToNat_natToBytes_of_lt, List.take_of_length_le, List.drop_of_length_le]
  rfl

/-- One check succeeds exactly when its condition holds. -/
private theorem check_eq_ok {ε : Type} (c : Prop) [Decidable c] (e : ε) :
    (if c then (Except.ok () : Except ε Unit) else throw e) = .ok () ↔ c := by
  split <;> simp_all [throw, throwThe, MonadExceptOf.throw]

/-- The parser accepts the data of a log exactly when it has 576 bytes and the words of the layout.

The head gives each field its offset, and each field starts with its size.

The request is then the five fields, one after the other. -/
theorem depositRequestOfEvent_eq_ok_iff (data request : ByteArray) :
    depositRequestOfEvent data = .ok request ↔
      data.size = DEPOSIT_EVENT_LENGTH ∧
      (∀ p ∈ DEPOSIT_EVENT_FIELDS.zipIdx,
        wordAt data.data.toList (32 * p.2) = p.1.1 ∧ wordAt data.data.toList p.1.1 = p.1.2) ∧
      request = ⟨(DEPOSIT_EVENT_FIELDS.flatMap fun (offset, size) =>
        fieldAt data.data.toList offset size).toArray⟩ := by
  have hsize : data.data.toList.length = data.size := rfl
  unfold depositRequestOfEvent
  dsimp only
  rw [hsize]
  by_cases hlen : data.size = DEPOSIT_EVENT_LENGTH
  · simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte, true_and, bind_unit_ok_iff,
      forM_ok_iff, check_eq_ok, pure, Except.pure, Except.ok.injEq]
    constructor
    · rintro ⟨h1, h2, rfl⟩
      exact ⟨fun p hp => ⟨h1 p hp, h2 p hp⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨fun p hp => (h p hp).1, fun p hp => (h p hp).2, rfl⟩
  · simp [hlen, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- An accepted deposit log gives a request of 192 bytes: 48, 32, 8, 96 and 8 bytes of fields. -/
theorem size_of_depositRequestOfEvent {data request : ByteArray}
    (h : depositRequestOfEvent data = .ok request) : request.size = 192 := by
  obtain ⟨hlen, -, rfl⟩ := (depositRequestOfEvent_eq_ok_iff data request).mp h
  have hbytes : data.data.toList.length = 576 := hlen
  simp [ByteArray.size, DEPOSIT_EVENT_FIELDS, fieldAt, hbytes]

end EthLib.Execution.Blocks
