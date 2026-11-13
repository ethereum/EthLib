module

public import EthLib.Base.Except
public import EthLib.Execution.Network.Session

/-!
# Proofs: the eth session

Before the peer's Status, every other message is rejected.

A Status is accepted then exactly when it passes the checks of a Status.

An accepted response removes the oldest pending request that it answers, and only that one.

A response that answers no pending request is rejected.

Receiving never changes the hashes sent, and only appends the hashes it receives.

Before both Status messages, this node sends nothing but Status.

Along any run of a session, a Transactions message sends no transaction that went out before.

Nor does it send one back to the peer it came from.

The eth requirement of snap holds exactly when some version of eth is a shared capability.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Networking.Devp2p
open EthLib.Serialization.Rlp

/-- Two byte arrays compare equal exactly when they are equal. -/
private theorem byteArray_beq_iff (a b : ByteArray) : (a == b) = true ↔ a = b := by
  show (a.data == b.data) = true ↔ a = b
  rw [beq_iff_eq, ByteArray.ext_iff]

/-- Before the peer's Status, every message other than Status is rejected. -/
theorem receiveEth_beforeStatus (s : Schedule) (number timestamp : Nat) (session : EthSession)
    (m : Message) (h : session.remoteStatus = none) (hm : ∀ st, m ≠ .status st) :
    receiveEth s number timestamp session m = .error .beforeStatus := by
  cases m <;> simp_all [receiveEth] <;> rfl

/-- Before the peer's Status, a Status is accepted exactly when it passes the checks of Status.

It then records the Status and changes nothing else. -/
theorem receiveEth_status_iff (s : Schedule) (number timestamp : Nat) (session : EthSession)
    (st : Status) (h : session.remoteStatus = none) (next : EthSession) (v : EthVerdict) :
    receiveEth s number timestamp session (.status st) = .ok (next, v) ↔
      checkStatus session.version s number timestamp st = .ok () ∧
        next = { session with remoteStatus := some st } ∧ v = .accept := by
  unfold receiveEth
  rw [h]
  simp only [bind_ok_iff, Except.mapError]
  cases checkStatus session.version s number timestamp st with
  | error e => simp
  | ok u => cases u; simp [pure, Except.pure, eq_comm]

/-- In an active session, a response either answers a pending request or is unsolicited. -/
private theorem receiveEth_active_response (s : Schedule) (number timestamp : Nat)
    (session : EthSession) (st : Status) (m : Message) (i : UInt64)
    (hs : session.remoteStatus = some st) (hi : m.responseId? = some i) :
    receiveEth s number timestamp session m =
      if session.pending.any (Message.answers · m) = true then
        (m.transactionHashes.mapError .transaction).map fun hashes =>
          ({ session with
              pending := session.pending.eraseP (Message.answers · m)
              receivedTxs := session.receivedTxs ++ hashes }, .accept)
      else .error (.unsolicited i) := by
  cases m <;> simp_all [receiveEth, Message.responseId?] <;> split <;> rfl

/-- An accepted response removes exactly one pending request, the oldest one it answers. -/
theorem receiveEth_response (s : Schedule) (number timestamp : Nat) (session next : EthSession)
    (v : EthVerdict) (m : Message) (hr : m.responseId?.isSome)
    (h : receiveEth s number timestamp session m = .ok (next, v)) :
    ∃ before q after, session.pending = before ++ q :: after ∧
      next.pending = before ++ after ∧ Message.answers q m = true ∧
      ∀ q' ∈ before, Message.answers q' m = false := by
  obtain ⟨st, hs⟩ : ∃ st, session.remoteStatus = some st := by
    cases hs : session.remoteStatus with
    | some st => exact ⟨st, rfl⟩
    | none =>
      have hm : ∀ st, m ≠ .status st := by
        rintro st rfl
        simp [Message.responseId?] at hr
      rw [receiveEth_beforeStatus s number timestamp session m hs hm] at h
      cases h
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hr
  rw [receiveEth_active_response s number timestamp session st m i hs hi] at h
  split at h
  · rename_i hany
    obtain ⟨q, hq, hqa⟩ := List.any_eq_true.mp hany
    obtain ⟨a, l1, l2, hb, hpa, hl, he⟩ := List.exists_of_eraseP (p := (Message.answers · m)) hq hqa
    cases hth : m.transactionHashes.mapError EthSessionError.transaction with
    | error e => simp [hth, Except.map] at h
    | ok hashes =>
      simp only [hth, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨l1, a, l2, hl, by simp [he], hpa, fun q' hq' => by simpa using hb q' hq'⟩
  · simp at h

/-- In an active session, a response that answers no pending request is rejected. -/
theorem receiveEth_unsolicited (s : Schedule) (number timestamp : Nat) (session : EthSession)
    (st : Status) (m : Message) (i : UInt64) (h : session.remoteStatus = some st)
    (hr : m.responseId? = some i) (hn : ∀ q ∈ session.pending, Message.answers q m = false) :
    receiveEth s number timestamp session m = .error (.unsolicited i) := by
  rw [receiveEth_active_response s number timestamp session st m i h hr]
  split
  · rename_i hany
    obtain ⟨q, hq, hqa⟩ := List.any_eq_true.mp hany
    rw [hn q hq] at hqa
    cases hqa
  · rfl

/-- One receive leaves the hashes sent alone and appends those of the message received. -/
private theorem receiveEth_txs (s : Schedule) (number timestamp : Nat) (session next : EthSession)
    (v : EthVerdict) (m : Message)
    (h : receiveEth s number timestamp session m = .ok (next, v)) :
    next.sentTxs = session.sentTxs ∧ ∃ hashes, m.transactionHashes = .ok hashes ∧
      next.receivedTxs = session.receivedTxs ++ hashes := by
  unfold receiveEth at h
  cases hs : session.remoteStatus with
  | none =>
    rw [hs] at h
    dsimp only at h
    split at h
    · rename_i st
      simp only [bind_ok_iff] at h
      obtain ⟨-, -, rfl, -⟩ := h
      simp [Message.transactionHashes, pure, Except.pure]
    · simp at h
  | some st =>
    rw [hs] at h
    dsimp only at h
    split at h
    · simp at h
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
      simp [Message.transactionHashes, pure, Except.pure]
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
      simp [Message.transactionHashes, pure, Except.pure]
    · split at h
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
        simp [Message.transactionHashes, pure, Except.pure]
      · simp at h
    · cases hth : m.transactionHashes with
      | error e =>
        split at h <;> (try split at h) <;>
          simp [hth, Except.mapError, bind_ok_iff, Functor.map, Except.map] at h
      | ok hashes =>
        split at h <;> (try split at h) <;>
          simp [hth, Except.mapError, bind_ok_iff, Functor.map, Except.map] at h <;>
          (obtain ⟨rfl, -⟩ := h; simp)

/-- A received message leaves the hashes sent alone. -/
theorem receiveEth_sentTxs (s : Schedule) (number timestamp : Nat) (session next : EthSession)
    (v : EthVerdict) (m : Message)
    (h : receiveEth s number timestamp session m = .ok (next, v)) :
    next.sentTxs = session.sentTxs :=
  (receiveEth_txs s number timestamp session next v m h).1

/-- A received message appends to the hashes received exactly those of the transactions it holds.
-/
theorem receiveEth_receivedTxs (s : Schedule) (number timestamp : Nat)
    (session next : EthSession) (v : EthVerdict) (m : Message)
    (h : receiveEth s number timestamp session m = .ok (next, v)) :
    ∃ hashes, m.transactionHashes = .ok hashes ∧
      next.receivedTxs = session.receivedTxs ++ hashes :=
  (receiveEth_txs s number timestamp session next v m h).2

/-- A sent message adds itself to the pending requests exactly when it is a request. -/
theorem sendEth_pending (session next : EthSession) (m : Message)
    (h : sendEth session m = some next) :
    next.pending = if m.isRequest then session.pending ++ [m] else session.pending := by
  cases m <;> cases hb : session.statusSent && session.remoteStatus.isSome <;>
    simp [sendEth, hb, Message.isRequest, Message.transactionHashes, Option.bind_eq_some_iff] at h ⊢
  all_goals first | (obtain ⟨_, _, _, rfl⟩ := h; rfl) | (subst h; rfl)

/-- One send records the hashes of its message as sent, and keeps the hashes received. -/
private theorem sendEth_step (session next : EthSession) (m : Message)
    (h : sendEth session m = some next) :
    next.sentTxs = session.sentTxs ++ (EthEvent.sent m).sentHashes ∧
      next.receivedTxs = session.receivedTxs := by
  cases m <;> cases hb : session.statusSent && session.remoteStatus.isSome <;>
    simp [sendEth, hb, EthEvent.sentHashes, Message.transactionHashes, Message.isRequest, pure,
      Except.pure, Except.toOption, Option.bind_eq_some_iff] at h ⊢
  all_goals first
    | (obtain ⟨_, ha, _, rfl⟩ := h; simp [ha])
    | (obtain ⟨_, ha, rfl⟩ := h; simp [ha])
    | (subst h; simp)

/-- One send of a Transactions message keeps its hashes fresh. -/
private theorem sendEth_transactions (session next : EthSession) (txs : List Item)
    (h : sendEth session (.transactions txs) = some next) :
    ∃ hashes, (Message.transactions txs).transactionHashes = .ok hashes ∧
      hashes ≠ [] ∧ hashes.Nodup ∧
      ∀ x ∈ hashes, x ∉ session.sentTxs ∧ x ∉ session.receivedTxs := by
  cases hb : session.statusSent && session.remoteStatus.isSome <;>
    simp [sendEth, hb, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, hc, -⟩ := h
  refine ⟨a, ?_, hc.1, hc.2.1, hc.2.2⟩
  simp only [Message.transactionHashes] at ha ⊢
  cases hm : List.mapM wireHash txs with
  | error e => simp [Except.toOption, hm] at ha
  | ok b => simp [Except.toOption, hm] at ha; rw [ha]

/-- Before the peer's Status, this node may send nothing but Status. -/
theorem sendEth_beforeStatus (session : EthSession) (m : Message)
    (h : session.remoteStatus = none) (hm : ∀ st, m ≠ .status st) :
    sendEth session m = none := by
  cases m <;> simp_all [sendEth]

/-- Before this node sends its own Status, it may send nothing else. -/
theorem sendEth_beforeOwnStatus (session : EthSession) (m : Message)
    (h : session.statusSent = false) (hm : ∀ st, m ≠ .status st) :
    sendEth session m = none := by
  cases m <;> simp_all [sendEth]

/-- In an active session, NewBlockHashes and NewBlock are discarded and change nothing. -/
theorem receiveEth_discard (s : Schedule) (number timestamp : Nat) (session : EthSession)
    (st : Status) (m : Message) (h : session.remoteStatus = some st)
    (hm : (∃ blocks, m = .newBlockHashes blocks) ∨ ∃ block td, m = .newBlock block td) :
    receiveEth s number timestamp session m = .ok (session, .discard) := by
  rcases hm with ⟨b, rfl⟩ | ⟨b, td, rfl⟩ <;> simp [receiveEth, h] <;> rfl

/-- In an active session, a second Status is rejected. -/
theorem receiveEth_secondStatus (s : Schedule) (number timestamp : Nat) (session : EthSession)
    (st st' : Status) (h : session.remoteStatus = some st) :
    receiveEth s number timestamp session (.status st') = .error .secondStatus := by
  simp [receiveEth, h]
  rfl

/-- One event moves a session to the next one, which a run chains. -/
private def EthSession.step (s : Schedule) (number timestamp : Nat) (session : EthSession)
    (event : EthEvent) : Option EthSession :=
  match event with
  | .sent m => sendEth session m
  | .received m => ((receiveEth s number timestamp session m).toOption).map (·.1)

/-- A run on an event followed by more events runs the rest from the session after the event. -/
private theorem run_cons (s : Schedule) (number timestamp : Nat) (session : EthSession)
    (e : EthEvent) (es : List EthEvent) :
    session.run s number timestamp (e :: es) =
      (EthSession.step s number timestamp session e).bind fun s' =>
        s'.run s number timestamp es := by
  simp only [EthSession.run, List.foldlM_cons]
  rfl

/-- A run on two lists of events runs the second from the session after the first. -/
private theorem run_append (s : Schedule) (number timestamp : Nat) (session : EthSession)
    (a b : List EthEvent) :
    session.run s number timestamp (a ++ b) =
      (session.run s number timestamp a).bind fun s1 => s1.run s number timestamp b := by
  simp only [EthSession.run, List.foldlM_append]
  rfl

/-- One event records the hashes it sends, and appends the hashes it receives. -/
private theorem step_tracks (s : Schedule) (number timestamp : Nat) (session next : EthSession)
    (event : EthEvent) (h : EthSession.step s number timestamp session event = some next) :
    next.sentTxs = session.sentTxs ++ event.sentHashes ∧
      next.receivedTxs = session.receivedTxs ++ event.receivedHashes := by
  cases event with
  | sent m =>
    obtain ⟨h1, h2⟩ := sendEth_step session next m h
    simp [EthEvent.receivedHashes, h1, h2]
  | received m =>
    simp only [EthSession.step] at h
    cases hr : receiveEth s number timestamp session m with
    | error e => simp [hr, Except.toOption] at h
    | ok r =>
      obtain ⟨next', v⟩ := r
      simp [hr, Except.toOption] at h
      subst h
      obtain ⟨hs, hashes, hh, hr2⟩ := receiveEth_txs s number timestamp session next' v m hr
      simp [EthEvent.sentHashes, EthEvent.receivedHashes, hs, hr2, hh, Except.toOption]

/-- A run records the hashes of its events, in order. -/
private theorem run_tracks (s : Schedule) (number timestamp : Nat) (events : List EthEvent) :
    ∀ (session next : EthSession), session.run s number timestamp events = some next →
      next.sentTxs = session.sentTxs ++ events.flatMap EthEvent.sentHashes ∧
        next.receivedTxs = session.receivedTxs ++ events.flatMap EthEvent.receivedHashes := by
  induction events with
  | nil =>
    intro session next h
    simp [EthSession.run] at h
    subst h
    simp
  | cons e es ih =>
    intro session next h
    rw [run_cons] at h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a1, a2⟩ := step_tracks s number timestamp session s1 e h1
    obtain ⟨b1, b2⟩ := ih s1 next h2
    simp [b1, b2, a1, a2]

/-- A run appends to the hashes sent those of each Transactions and PooledTransactions it sends.
-/
theorem run_sentTxs (s : Schedule) (number timestamp : Nat) (session next : EthSession)
    (events : List EthEvent) (h : session.run s number timestamp events = some next) :
    next.sentTxs = session.sentTxs ++ events.flatMap EthEvent.sentHashes :=
  (run_tracks s number timestamp events session next h).1

/-- Each Transactions message of a run holds at least one transaction, and none twice.

None of its transactions went to the peer before, in the run or before the run.

None came from the peer before, in the run or before the run. -/
theorem run_no_resend (s : Schedule) (number timestamp : Nat) (session next : EthSession)
    (events before after : List EthEvent) (txs : List Item)
    (h : session.run s number timestamp events = some next)
    (hev : events = before ++ .sent (.transactions txs) :: after) :
    ∃ hashes, (Message.transactions txs).transactionHashes = .ok hashes ∧
      hashes ≠ [] ∧ hashes.Nodup ∧
      ∀ x ∈ hashes, x ∉ session.sentTxs ∧ x ∉ before.flatMap EthEvent.sentHashes ∧
        x ∉ session.receivedTxs ∧ x ∉ before.flatMap EthEvent.receivedHashes := by
  subst hev
  rw [run_append] at h
  obtain ⟨s1, hr, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t1, t2⟩ := run_tracks s number timestamp before session s1 hr
  rw [run_cons] at h2
  obtain ⟨s2, h3, -⟩ := Option.bind_eq_some_iff.mp h2
  have h3 : sendEth s1 (.transactions txs) = some s2 := h3
  obtain ⟨hashes, hh, hne, hnd, hf⟩ := sendEth_transactions s1 s2 txs h3
  refine ⟨hashes, hh, hne, hnd, fun x hx => ?_⟩
  obtain ⟨c1, c2⟩ := hf x hx
  rw [t1] at c1
  rw [t2] at c2
  simp only [List.mem_append, not_or] at c1 c2
  exact ⟨c1.1, c1.2, c2.1, c2.2⟩

/-- The eth requirement of snap holds exactly when some shared capability is named eth. -/
theorem snapAllowed_iff (offsets : List (Capability × Nat)) :
    snapAllowed offsets = true ↔ ∃ c n, (c, n) ∈ offsets ∧ c.name = ETH_NAME := by
  simp only [snapAllowed, List.any_eq_true, byteArray_beq_iff]
  constructor
  · rintro ⟨⟨c, n⟩, hm, hc⟩
    exact ⟨c, n, hm, hc⟩
  · rintro ⟨c, n, hm, hc⟩
    exact ⟨(c, n), hm, hc⟩

end EthLib.Execution.Network
