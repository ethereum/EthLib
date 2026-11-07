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

The deposit requests of a block succeed exactly when the parser accepts every deposit log.

They then hold 192 bytes for each deposit log.
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

/-- Joining byte strings onto a start adds up their sizes. -/
private theorem size_foldl_append (requests : List ByteArray) (start : ByteArray) :
    (requests.foldl (· ++ ·) start).size = start.size + (requests.map (·.size)).sum := by
  induction requests generalizing start with
  | nil => simp
  | cons r rest ih =>
    simp only [List.foldl_cons, ih, ByteArray.size_append, List.map_cons, List.sum_cons]
    omega

/-- The deposit requests of a block succeed exactly when the parser accepts every deposit log. -/
theorem depositRequests_isOk_iff (logs : List Log) :
    (∃ data, depositRequests logs = .ok data) ↔
      ∀ log ∈ logs, isDepositLog log = true →
        ∃ request, depositRequestOfEvent log.data = .ok request := by
  unfold depositRequests
  constructor
  · rintro ⟨data, h⟩ log hlog hdeposit
    obtain ⟨requests, hrequests, -⟩ := bind_ok_iff.mp h
    exact mapM_ok_of_mem hrequests log (List.mem_filter.mpr ⟨hlog, hdeposit⟩)
  · intro h
    obtain ⟨requests, hrequests⟩ := mapM_exists_ok (f := fun log => depositRequestOfEvent log.data)
      fun log hlog => h log (List.mem_filter.mp hlog).1 (List.mem_filter.mp hlog).2
    exact ⟨_, by simp only [hrequests, bind, Except.bind, pure, Except.pure]; rfl⟩

/-- The deposit requests of a block hold 192 bytes for each deposit log. -/
theorem size_of_depositRequests {logs : List Log} {data : ByteArray}
    (h : depositRequests logs = .ok data) :
    data.size = 192 * (logs.filter isDepositLog).length := by
  unfold depositRequests at h
  obtain ⟨requests, hrequests, h⟩ := bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  -- Each request has 192 bytes, and there is one request for each deposit log.
  have hsizes : requests.map (·.size) = requests.map fun _ => 192 := by
    apply List.map_congr_left
    intro r hr
    obtain ⟨log, -, hlog⟩ := mapM_ok_mem hrequests r hr
    exact size_of_depositRequestOfEvent hlog
  rw [size_foldl_append, hsizes, ← mapM_ok_length hrequests, List.map_const']
  simp [Nat.mul_comm]

end EthLib.Execution.Blocks
