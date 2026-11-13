module

public import EthLib.Networking.Libp2p.YamuxSession

/-!
# Proofs: the streams of a yamux session

- A Ping with SYN gets exactly one reply, a Ping with ACK and the same value.
- Along accepted frames from an empty session, every stream has a nonzero ID of its opener's parity.
- The data that a side sends on a stream stays within the first window and the deltas it received.
- A stream is closed iff this side sent FIN, it received FIN, and no frame on it carried RST.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.YamuxSession

open EthLib.Networking.Libp2p.Yamux

/-- Looking up an ID in a table with a first entry. -/
private theorem lookup_cons' (a : UInt32) (e : UInt32 × Stream) (t : List (UInt32 × Stream)) :
    List.lookup a (e :: t) = if a = e.1 then some e.2 else List.lookup a t := by
  by_cases h : a = e.1
  · have : (a == e.1) = true := by simpa using h
    simp [List.lookup, h]
  · have : (a == e.1) = false := by simpa using h
    simp [List.lookup, this, h]

/-- Setting a stream makes the table report that stream for its ID. -/
theorem find?_set_self (session : Session) (id : UInt32) (s : Stream) :
    (session.set id s).find? id = some s := by
  unfold Session.set Session.find?
  by_cases h : session.streams.any (·.1 = id) = true
  · simp only [h, ↓reduceIte]
    generalize session.streams = l at h
    induction l with
    | nil => simp at h
    | cons e t ih =>
      by_cases he : e.1 = id
      · rw [List.map_cons, lookup_cons']
        simp [he]
      · have he' : ¬ id = e.1 := fun h => he h.symm
        simp only [List.any_cons, he, decide_false, Bool.false_or] at h
        rw [List.map_cons, lookup_cons']
        simp only [he, he', ite_false]
        exact ih h
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    generalize session.streams = l at h
    induction l with
    | nil => simp
    | cons e t ih =>
      by_cases he : e.1 = id
      · simp [List.any_cons, he] at h
      · have he' : ¬ id = e.1 := fun h => he h.symm
        simp only [List.any_cons, he, decide_false, Bool.false_or] at h
        rw [List.cons_append, lookup_cons']
        simp only [he', ite_false]
        exact ih h

/-- Setting a stream leaves the table as it was for every other ID. -/
theorem find?_set_of_ne (session : Session) {id id' : UInt32} (s : Stream)
    (h : id' ≠ id) : (session.set id s).find? id' = session.find? id' := by
  unfold Session.set Session.find?
  by_cases hc : session.streams.any (·.1 = id) = true
  · simp only [hc, ↓reduceIte]
    clear hc
    generalize session.streams = l
    induction l with
    | nil => simp [List.lookup]
    | cons e t ih =>
      rw [List.map_cons, lookup_cons', lookup_cons']
      by_cases he : e.1 = id
      · have : ¬ id' = e.1 := fun h' => h (h'.trans he)
        simp [he, h, ih]
      · simp only [he, ite_false]
        rw [← ih]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    clear hc
    generalize session.streams = l
    induction l with
    | nil => simp [lookup_cons', List.lookup, h]
    | cons e t ih =>
      rw [List.cons_append, lookup_cons', lookup_cons']
      by_cases hk : id' = e.1 <;> simp [hk, ih]

/-- Setting a stream keeps the side of the session. -/
theorem isClient_set (session : Session) (id : UInt32) (s : Stream) :
    (session.set id s).isClient = session.isClient := rfl

/-- One Data or Window Update frame changes the flags of a stream only as its own flags say.

The flags only turn on, and each turns on only for its own side and frame flag. -/
private theorem apply_spec {remote : Bool} {id : UInt32} {s s' : Stream} {frame : Frame}
    (hkind : frame.kind = .data ∨ frame.kind = .windowUpdate)
    (h : s.apply remote id frame = .ok s') :
    s'.localOpened = s.localOpened ∧
    (s.localClosed = true → s'.localClosed = true) ∧
    (s.remoteClosed = true → s'.remoteClosed = true) ∧
    (s.localReset = true → s'.localReset = true) ∧
    (s.remoteReset = true → s'.remoteReset = true) ∧
    (s'.localClosed = true → s.localClosed = true ∨ (remote = false ∧ frame.hasFlag fin = true)) ∧
    (s'.remoteClosed = true → s.remoteClosed = true ∨ (remote = true ∧ frame.hasFlag fin = true)) ∧
    (s'.localReset = true → s.localReset = true ∨ (remote = false ∧ frame.hasFlag rst = true)) ∧
    (s'.remoteReset = true → s.remoteReset = true ∨ (remote = true ∧ frame.hasFlag rst = true)) ∧
    (remote = false → frame.hasFlag fin = true → s'.localClosed = true) ∧
    (remote = true → frame.hasFlag fin = true → s'.remoteClosed = true) ∧
    (remote = false → frame.hasFlag rst = true → s'.localReset = true) ∧
    (remote = true → frame.hasFlag rst = true → s'.remoteReset = true) ∧
    s'.sendWindow + (if remote = false ∧ frame.kind = .data then frame.length.toNat else 0) ≤
      s.sendWindow + (if remote = true ∧ frame.kind = .windowUpdate then frame.length.toNat
        else 0) := by
  unfold Stream.apply at h
  cases remote <;> by_cases hk : frame.kind = .data <;> by_cases ha : frame.hasFlag ack = true <;>
    by_cases hf : frame.hasFlag fin = true <;> by_cases hr : frame.hasFlag rst = true <;>
    simp [ha, hf, hr, hk, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h ⊢ <;>
    (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; simp_all; try omega)

/-- An accepted frame leaves the side alone.

It either leaves the streams as they were, or sets one stream that the frame names.

That stream is an existing one.

Or it is a new one that a SYN opens with the parity of its writer. -/
private theorem step_spec {remote : Bool} {session after : Session} {frame : Frame}
    (h : step remote session frame = .ok after) :
    after.isClient = session.isClient ∧
    (((frame.kind = .ping ∨ frame.kind = .goAway) ∧ ∀ i, after.find? i = session.find? i) ∨
    (∃ s, session.find? frame.streamId = some s ∧ s.localReset = true ∧ remote = true ∧
      (frame.kind = .data ∨ frame.kind = .windowUpdate) ∧ after = session) ∨
    (∃ s0 s', frame.streamId ≠ 0 ∧ (frame.kind = .data ∨ frame.kind = .windowUpdate) ∧
      (session.find? frame.streamId = some s0 ∨
        (session.find? frame.streamId = none ∧ frame.hasFlag syn = true ∧
          session.ownsId frame.streamId ≠ remote ∧ s0 = { localOpened := !remote })) ∧
      s0.remoteReset = false ∧ (remote = false → s0.localReset = false) ∧
      s0.apply remote frame.streamId frame = .ok s' ∧
      after = session.set frame.streamId s')) := by
  unfold step at h
  by_cases hd : frame.kind = .data ∨ frame.kind = .windowUpdate
  · have hm : (frame.kind = .data ∨ frame.kind = .windowUpdate) := hd
    rcases hd with hk | hk <;> simp only [hk] at h <;>
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h <;>
    repeat' split at h
    all_goals first | (cases h; done) | (cases h; simp_all; done) | skip
    all_goals
      first
      | (rename_i hid hsyn hnf hpar _ _ _ v hap
         cases h
         exact ⟨rfl, Or.inr (Or.inr ⟨{ localOpened := !remote }, v, hid, hm,
           Or.inr ⟨by simpa using hnf, hsyn, by simpa using hpar, rfl⟩, rfl,
           fun _ => rfl, hap, rfl⟩)⟩)
      | (rename_i hid _ _ s hfind _ h2 _ v hap
         cases h
         refine ⟨rfl, Or.inr (Or.inr ⟨s, v, hid, hm, Or.inl hfind, ?_, ?_, hap, rfl⟩)⟩
         · simp_all
         · simp_all)
  · have hk : frame.kind = .ping ∨ frame.kind = .goAway := by
      cases hk : frame.kind <;> simp_all
    rcases hk with hk | hk
    · simp only [hk] at h
      simp only [pure, Except.pure] at h
      cases h
      exact ⟨rfl, Or.inl ⟨Or.inl hk, fun _ => rfl⟩⟩
    · simp only [hk] at h
      simp only [pure, Except.pure] at h
      split at h <;> (cases h; exact ⟨rfl, Or.inl ⟨Or.inr hk, fun _ => rfl⟩⟩)

/-- An accepted frame leaves the send window of a stream at most its old value plus a delta.

The delta is that of a Window Update that this side receives on the stream.

The bytes of a Data frame that this side sends on the stream count against the window.

A stream that the table lacks counts as one with the first window. -/
theorem step_window {remote : Bool} {session after : Session} {frame : Frame}
    (h : step remote session frame = .ok after) (id : UInt32) :
    ((after.find? id).map Stream.sendWindow).getD initialWindow +
        (if remote = false ∧ frame.kind = .data ∧ frame.streamId = id then frame.length.toNat
          else 0) ≤
      ((session.find? id).map Stream.sendWindow).getD initialWindow +
        (if remote = true ∧ frame.kind = .windowUpdate ∧ frame.streamId = id then
          frame.length.toNat else 0) := by
  obtain ⟨_, hcase⟩ := step_spec h
  rcases hcase with ⟨hk, hsame⟩ | ⟨s, _, _, rfl, _, rfl⟩ | ⟨s0, s', _, hkind, hs0, _, _, hap, rfl⟩
  · rw [hsame]
    rcases hk with hk | hk <;> simp [hk]
  · simp
  · by_cases hid : id = frame.streamId
    · subst hid
      have hw := (apply_spec hkind hap).2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [find?_set_self]
      rcases hs0 with hf | ⟨hn, _, _, rfl⟩
      · simpa [hf] using hw
      · simpa [hn, initialWindow] using hw
    · rw [find?_set_of_ne _ _ hid]
      have : frame.streamId ≠ id := fun h => hid h.symm
      simp [this]

/-- A run of no frames returns the session. -/
theorem run_nil (session : Session) : run session [] = .ok session := rfl

/-- A run that accepts a first frame goes through the session after that frame. -/
theorem run_cons {session after : Session} {e : Bool × Frame} {t : List (Bool × Frame)}
    (h : run session (e :: t) = .ok after) :
    ∃ s1, step e.1 session e.2 = .ok s1 ∧ run s1 t = .ok after := by
  obtain ⟨remote, frame⟩ := e
  simp only [run, List.foldlM] at h
  cases hs : step remote session frame with
  | error err =>
    rw [hs] at h
    exact absurd h (by simp [bind, Except.bind])
  | ok s1 =>
    rw [hs] at h
    exact ⟨s1, rfl, h⟩

/-- An accepted frame keeps the nonzero IDs and the opener of every stream. -/
theorem step_parity {remote : Bool} {session after : Session} {frame : Frame}
    (h : step remote session frame = .ok after)
    (hinv : ∀ id s, session.find? id = some s → id ≠ 0 ∧ s.localOpened = session.ownsId id) :
    ∀ id s, after.find? id = some s → id ≠ 0 ∧ s.localOpened = after.ownsId id := by
  obtain ⟨hc, hcase⟩ := step_spec h
  have hown : ∀ id, after.ownsId id = session.ownsId id := by
    intro id; simp [Session.ownsId, hc]
  intro id s hs
  rw [hown]
  rcases hcase with ⟨_, hsame⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨s0, s', hz, _, hs0, _, _, hap, rfl⟩
  · rw [hsame] at hs; exact hinv id s hs
  · exact hinv id s hs
  · by_cases hid : id = frame.streamId
    · subst hid
      rw [find?_set_self] at hs
      cases hs
      refine ⟨hz, ?_⟩
      rw [(apply_spec ‹_› hap).1]
      rcases hs0 with hf | ⟨_, _, hp, rfl⟩
      · exact (hinv _ _ hf).2
      · cases hh : session.ownsId frame.streamId <;> cases remote <;> simp_all
    · rw [find?_set_of_ne _ _ hid] at hs
      exact hinv id s hs

/-- A run of accepted frames keeps the side of the session. -/
theorem run_isClient (events : List (Bool × Frame)) :
    ∀ {session after : Session}, run session events = .ok after →
    after.isClient = session.isClient := by
  induction events with
  | nil =>
    intro session after h
    rw [run_nil] at h
    cases h
    rfl
  | cons e t ih =>
    intro session after h
    obtain ⟨s1, hs1, ht⟩ := run_cons h
    rw [ih ht]
    exact (step_spec hs1).1

/-- A run of accepted frames keeps the nonzero IDs and the opener of every stream. -/
theorem run_parity_aux (events : List (Bool × Frame)) :
    ∀ {session after : Session}, run session events = .ok after →
    (∀ id s, session.find? id = some s → id ≠ 0 ∧ s.localOpened = session.ownsId id) →
    ∀ id s, after.find? id = some s → id ≠ 0 ∧ s.localOpened = after.ownsId id := by
  induction events with
  | nil =>
    intro session after h hinv
    rw [run_nil] at h
    cases h
    exact hinv
  | cons e t ih =>
    intro session after h hinv
    obtain ⟨s1, hs1, ht⟩ := run_cons h
    exact ih ht (step_parity hs1 hinv)

/-- A Ping with SYN changes nothing, and gets a Ping with ACK, stream 0 and the same value. -/
theorem receive_ping (session : Session) (frame : Frame) (hkind : frame.kind = .ping)
    (hsyn : frame.hasFlag syn = true) :
    receive session frame = .ok (session,
      [{ kind := .ping, flags := ack, streamId := 0, length := frame.length,
         data := .empty }]) := by
  simp [receive, step, reply, hkind, hsyn]
  rfl

/-- After accepted frames from an empty session, every stream has a nonzero ID.

Its ID has the parity of this side iff this side opened it. -/
theorem run_parity {isClient : Bool} {events : List (Bool × Frame)} {after : Session}
    (h : run { isClient } events = .ok after) {id : UInt32} {s : Stream}
    (hs : after.find? id = some s) :
    id ≠ 0 ∧ s.localOpened = ({ isClient } : Session).ownsId id := by
  have hr := run_parity_aux events h (session := { isClient }) (by
    intro id s hs
    simp [Session.find?] at hs) id s hs
  have hc : after.isClient = isClient := run_isClient events h
  simpa [Session.ownsId, hc] using hr

/-- A Data or Window Update frame on a stream. -/
def OnStream (id : UInt32) (frame : Frame) : Prop :=
  (frame.kind = .data ∨ frame.kind = .windowUpdate) ∧ frame.streamId = id

instance (id : UInt32) (frame : Frame) : Decidable (OnStream id frame) := by
  unfold OnStream; infer_instance

/-- The lengths of the Data frames that this side sends on a stream. -/
def sentData (id : UInt32) (events : List (Bool × Frame)) : Nat :=
  ((events.filter fun e => !e.1 && e.2.kind = .data && e.2.streamId = id).map
    (·.2.length.toNat)).sum

/-- The deltas of the Window Update frames that this side receives on a stream. -/
def receivedDeltas (id : UInt32) (events : List (Bool × Frame)) : Nat :=
  ((events.filter fun e => e.1 && e.2.kind = .windowUpdate && e.2.streamId = id).map
    (·.2.length.toNat)).sum

/-- The data sent by a list of events is that of the first event plus that of the rest. -/
theorem sentData_cons (id : UInt32) (e : Bool × Frame) (t : List (Bool × Frame)) :
    sentData id (e :: t) =
      (if e.1 = false ∧ e.2.kind = .data ∧ e.2.streamId = id then e.2.length.toNat else 0) +
        sentData id t := by
  obtain ⟨r, f⟩ := e
  unfold sentData
  cases r <;> by_cases hk : f.kind = .data <;> by_cases hi : f.streamId = id <;>
    simp [hk, hi]

/-- The deltas received by a list of events.

They are those of the first event plus those of the rest. -/
theorem receivedDeltas_cons (id : UInt32) (e : Bool × Frame) (t : List (Bool × Frame)) :
    receivedDeltas id (e :: t) =
      (if e.1 = true ∧ e.2.kind = .windowUpdate ∧ e.2.streamId = id then e.2.length.toNat
        else 0) + receivedDeltas id t := by
  obtain ⟨r, f⟩ := e
  unfold receivedDeltas
  cases r <;> by_cases hk : f.kind = .windowUpdate <;> by_cases hi : f.streamId = id <;>
    simp [hk, hi]

/-- Along accepted frames, the data sent plus the window left is bounded.

The bound is the window at the start plus the deltas received. -/
theorem run_window (events : List (Bool × Frame)) (id : UInt32) :
    ∀ {session after : Session}, run session events = .ok after →
    ((after.find? id).map Stream.sendWindow).getD initialWindow + sentData id events ≤
      ((session.find? id).map Stream.sendWindow).getD initialWindow +
        receivedDeltas id events := by
  induction events with
  | nil =>
    intro session after h
    rw [run_nil] at h
    cases h
    simp [sentData, receivedDeltas]
  | cons e t ih =>
    intro session after h
    obtain ⟨s1, hs1, ht⟩ := run_cons h
    have h1 := step_window hs1 id
    have h2 := ih ht
    rw [sentData_cons, receivedDeltas_cons]
    omega

/-- After accepted frames from an empty session, the data sent on a stream is within its windows.

It is at most the first window plus the deltas of the Window Updates received on the stream. -/
theorem send_window {isClient : Bool} {events : List (Bool × Frame)} {after : Session}
    (h : run { isClient } events = .ok after) (id : UInt32) :
    sentData id events ≤ initialWindow + receivedDeltas id events := by
  have h1 := run_window events id h
  simp only [Session.find?, List.lookup, Option.map_none, Option.getD_none] at h1
  omega

/-- How the flags of one stream change along one accepted frame.

The flags that are on stay on.

Each turns on only by its own frame flag from its own side.

FIN from this side, FIN from the peer and RST turn them on.

The exception is a frame from the peer that this side drops after its own reset. -/
def FlagStep (remote : Bool) (session after : Session) (frame : Frame) (id : UInt32) : Prop :=
  (∀ s, session.find? id = some s → ∃ s', after.find? id = some s' ∧
    (s.localClosed = true → s'.localClosed = true) ∧
    (s.remoteClosed = true → s'.remoteClosed = true) ∧
    (s.localReset = true → s'.localReset = true) ∧
    (s.remoteReset = true → s'.remoteReset = true)) ∧
  (∀ s', after.find? id = some s' →
    (s'.localClosed = true → (∃ s, session.find? id = some s ∧ s.localClosed = true) ∨
      (remote = false ∧ OnStream id frame ∧ frame.hasFlag fin = true)) ∧
    (s'.remoteClosed = true → (∃ s, session.find? id = some s ∧ s.remoteClosed = true) ∨
      (remote = true ∧ OnStream id frame ∧ frame.hasFlag fin = true)) ∧
    ((s'.localReset = true ∨ s'.remoteReset = true) →
      (∃ s, session.find? id = some s ∧ (s.localReset = true ∨ s.remoteReset = true)) ∨
        (OnStream id frame ∧ frame.hasFlag rst = true))) ∧
  (remote = false → OnStream id frame → frame.hasFlag fin = true →
    ∃ s', after.find? id = some s' ∧ s'.localClosed = true) ∧
  (remote = true → OnStream id frame → frame.hasFlag fin = true →
    (∃ s', after.find? id = some s' ∧ s'.remoteClosed = true) ∨
      ∃ s, session.find? id = some s ∧ s.localReset = true) ∧
  (OnStream id frame → frame.hasFlag rst = true →
    ∃ s', after.find? id = some s' ∧ (s'.localReset = true ∨ s'.remoteReset = true))

/-- A frame that does not touch a stream leaves its flags as they were. -/
theorem flagStep_of_same {remote : Bool} {session after : Session} {frame : Frame} {id : UInt32}
    (hs : after.find? id = session.find? id) (hno : ¬ OnStream id frame) :
    FlagStep remote session after frame id := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s h
    exact ⟨s, hs.trans h, fun x => x, fun x => x, fun x => x, fun x => x⟩
  · intro s' h
    rw [hs] at h
    exact ⟨fun hl => Or.inl ⟨s', h, hl⟩, fun hl => Or.inl ⟨s', h, hl⟩,
      fun hl => Or.inl ⟨s', h, hl⟩⟩
  · intro _ hon; exact absurd hon hno
  · intro _ hon; exact absurd hon hno
  · intro hon; exact absurd hon hno

/-- An accepted frame changes the flags of each stream as the frame step says. -/
theorem step_flags {remote : Bool} {session after : Session} {frame : Frame}
    (h : step remote session frame = .ok after) (id : UInt32) :
    FlagStep remote session after frame id := by
  obtain ⟨_, hcase⟩ := step_spec h
  rcases hcase with ⟨hk, hsame⟩ | ⟨s, hs, hl, hr, hkind, rfl⟩ |
      ⟨s0, s', hz, hkind, hs0, _, _, hap, rfl⟩
  · refine flagStep_of_same (hsame id) ?_
    rintro ⟨hon, _⟩
    rcases hk with hk | hk <;> rcases hon with hon | hon <;> simp_all
  · by_cases hid : id = frame.streamId
    · subst hid
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro s2 h2
        exact ⟨s2, h2, fun x => x, fun x => x, fun x => x, fun x => x⟩
      · intro s' h2
        exact ⟨fun hl => Or.inl ⟨s', h2, hl⟩, fun hl => Or.inl ⟨s', h2, hl⟩,
          fun hl => Or.inl ⟨s', h2, hl⟩⟩
      · intro hr' _; simp_all
      · intro _ _ _; exact Or.inr ⟨s, hs, hl⟩
      · intro _ _; exact ⟨s, hs, Or.inl hl⟩
    · exact flagStep_of_same rfl (fun hon => hid hon.2.symm)
  · by_cases hid : id = frame.streamId
    · subst hid
      obtain ⟨_, m1, m2, m3, m4, p1, p2, p3, p4, f1, f2, r1, r2, _⟩ := apply_spec hkind hap
      have hold : ∀ s, session.find? frame.streamId = some s → s = s0 := by
        intro s hs
        rcases hs0 with hf | ⟨hn, _⟩
        · rw [hf] at hs; exact (Option.some.inj hs).symm
        · rw [hn] at hs; cases hs
      have hfound : ∀ f : Stream → Bool, f ({ localOpened := !remote } : Stream) = false →
          f s0 = true → ∃ s, session.find? frame.streamId = some s ∧ f s = true := by
        intro f hf0 hf
        rcases hs0 with hf' | ⟨_, _, _, rfl⟩
        · exact ⟨s0, hf', hf⟩
        · rw [hf0] at hf; cases hf
      have hon : OnStream frame.streamId frame := ⟨hkind, rfl⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro s hs
        obtain rfl := hold s hs
        exact ⟨s', find?_set_self _ _ _, m1, m2, m3, m4⟩
      · intro s'' h2
        rw [find?_set_self] at h2
        obtain rfl := Option.some.inj h2
        refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
        · rcases p1 hl with h3 | h3
          · exact Or.inl (hfound (·.localClosed) rfl h3)
          · exact Or.inr ⟨h3.1, hon, h3.2⟩
        · rcases p2 hl with h3 | h3
          · exact Or.inl (hfound (·.remoteClosed) rfl h3)
          · exact Or.inr ⟨h3.1, hon, h3.2⟩
        · rcases hl with hl | hl
          · rcases p3 hl with h3 | h3
            · obtain ⟨s2, hs2, h4⟩ := hfound (·.localReset) rfl h3
              exact Or.inl ⟨s2, hs2, Or.inl h4⟩
            · exact Or.inr ⟨hon, h3.2⟩
          · rcases p4 hl with h3 | h3
            · obtain ⟨s2, hs2, h4⟩ := hfound (·.remoteReset) rfl h3
              exact Or.inl ⟨s2, hs2, Or.inr h4⟩
            · exact Or.inr ⟨hon, h3.2⟩
      · intro hr _ hf
        exact ⟨s', find?_set_self _ _ _, f1 hr hf⟩
      · intro hr _ hf
        exact Or.inl ⟨s', find?_set_self _ _ _, f2 hr hf⟩
      · intro _ hr
        refine ⟨s', find?_set_self _ _ _, ?_⟩
        cases remote
        · exact Or.inl (r1 rfl hr)
        · exact Or.inr (r2 rfl hr)
    · exact flagStep_of_same (find?_set_of_ne _ _ hid) (fun hon => hid hon.2.symm)

/-- Along accepted frames, the flags that a stream has on stay on. -/
theorem run_mono (events : List (Bool × Frame)) (id : UInt32) :
    ∀ {session after : Session}, run session events = .ok after →
    ∀ s, session.find? id = some s → ∃ s', after.find? id = some s' ∧
      (s.localClosed = true → s'.localClosed = true) ∧
      (s.remoteClosed = true → s'.remoteClosed = true) ∧
      (s.localReset = true → s'.localReset = true) ∧
      (s.remoteReset = true → s'.remoteReset = true) := by
  induction events with
  | nil =>
    intro session after h s hs
    rw [run_nil] at h
    cases h
    exact ⟨s, hs, fun x => x, fun x => x, fun x => x, fun x => x⟩
  | cons e t ih =>
    intro session after h s hs
    obtain ⟨s1, hs1, ht⟩ := run_cons h
    obtain ⟨s2, h2, a1, a2, a3, a4⟩ := (step_flags hs1 id).1 s hs
    obtain ⟨s3, h3, b1, b2, b3, b4⟩ := ih ht s2 h2
    exact ⟨s3, h3, fun x => b1 (a1 x), fun x => b2 (a2 x), fun x => b3 (a3 x),
      fun x => b4 (a4 x)⟩

/-- Along accepted frames, a flag of a stream is on only for a reason.

Either it was on at the start.

Or a frame with the matching flag, from the matching side, named the stream. -/
theorem run_prov (events : List (Bool × Frame)) (id : UInt32) :
    ∀ {session after : Session}, run session events = .ok after →
    ∀ s', after.find? id = some s' →
      (s'.localClosed = true → (∃ s, session.find? id = some s ∧ s.localClosed = true) ∨
        ∃ f, (false, f) ∈ events ∧ OnStream id f ∧ f.hasFlag fin = true) ∧
      (s'.remoteClosed = true → (∃ s, session.find? id = some s ∧ s.remoteClosed = true) ∨
        ∃ f, (true, f) ∈ events ∧ OnStream id f ∧ f.hasFlag fin = true) ∧
      ((s'.localReset = true ∨ s'.remoteReset = true) →
        (∃ s, session.find? id = some s ∧ (s.localReset = true ∨ s.remoteReset = true)) ∨
          ∃ e ∈ events, OnStream id e.2 ∧ e.2.hasFlag rst = true) := by
  induction events with
  | nil =>
    intro session after h s' hs'
    rw [run_nil] at h
    cases h
    exact ⟨fun hl => Or.inl ⟨s', hs', hl⟩, fun hl => Or.inl ⟨s', hs', hl⟩,
      fun hl => Or.inl ⟨s', hs', hl⟩⟩
  | cons e t ih =>
    intro session after h s' hs'
    obtain ⟨r, f⟩ := e
    obtain ⟨s1, hs1, ht⟩ := run_cons h
    obtain ⟨c1, c2, c3⟩ := ih ht s' hs'
    refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
    · rcases c1 hl with ⟨s2, h2, h3⟩ | ⟨f', hm, hon, hf⟩
      · rcases ((step_flags hs1 id).2.1 s2 h2).1 h3 with h4 | ⟨h4, hon, hf⟩
        · exact Or.inl h4
        · refine Or.inr ⟨f, ?_, hon, hf⟩
          simp_all
      · exact Or.inr ⟨f', List.mem_cons_of_mem _ hm, hon, hf⟩
    · rcases c2 hl with ⟨s2, h2, h3⟩ | ⟨f', hm, hon, hf⟩
      · rcases ((step_flags hs1 id).2.1 s2 h2).2.1 h3 with h4 | ⟨h4, hon, hf⟩
        · exact Or.inl h4
        · refine Or.inr ⟨f, ?_, hon, hf⟩
          simp_all
      · exact Or.inr ⟨f', List.mem_cons_of_mem _ hm, hon, hf⟩
    · rcases c3 hl with ⟨s2, h2, h3⟩ | ⟨e', hm, hon, hf⟩
      · rcases ((step_flags hs1 id).2.1 s2 h2).2.2 h3 with h4 | ⟨hon, hf⟩
        · exact Or.inl h4
        · exact Or.inr ⟨(r, f), List.mem_cons_self .., hon, hf⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ hm, hon, hf⟩

/-- A frame with RST on a stream, once accepted, leaves the stream reset. -/
theorem run_rst (events : List (Bool × Frame)) (id : UInt32) :
    ∀ {session after : Session}, run session events = .ok after →
    (∃ e ∈ events, OnStream id e.2 ∧ e.2.hasFlag rst = true) →
    ∃ s', after.find? id = some s' ∧ (s'.localReset = true ∨ s'.remoteReset = true) := by
  induction events with
  | nil => intro session after h hex; simp at hex
  | cons e t ih =>
    intro session after h hex
    obtain ⟨r, f⟩ := e
    obtain ⟨s1, hs1, ht⟩ := run_cons h
    by_cases hf : OnStream id f ∧ f.hasFlag rst = true
    · obtain ⟨s2, h2, h3⟩ := (step_flags hs1 id).2.2.2.2 hf.1 hf.2
      obtain ⟨s3, h3', b1, b2, b3, b4⟩ := run_mono t id ht s2 h2
      rcases h3 with h3 | h3
      · exact ⟨s3, h3', Or.inl (b3 h3)⟩
      · exact ⟨s3, h3', Or.inr (b4 h3)⟩
    · refine ih ht ?_
      obtain ⟨e', hm, hon, hr⟩ := hex
      rcases List.mem_cons.1 hm with rfl | hm
      · exact absurd ⟨hon, hr⟩ hf
      · exact ⟨e', hm, hon, hr⟩

/-- A frame with FIN that this side sends on a stream, once accepted, leaves it closed.

It is closed on this side. -/
theorem run_fin_sent (events : List (Bool × Frame)) (id : UInt32) :
    ∀ {session after : Session}, run session events = .ok after →
    (∃ f, (false, f) ∈ events ∧ OnStream id f ∧ f.hasFlag fin = true) →
    ∃ s', after.find? id = some s' ∧ s'.localClosed = true := by
  induction events with
  | nil => intro session after h hex; simp at hex
  | cons e t ih =>
    intro session after h hex
    obtain ⟨r, f⟩ := e
    obtain ⟨s1, hs1, ht⟩ := run_cons h
    obtain ⟨f', hm, hon, hf⟩ := hex
    by_cases hh : r = false ∧ f' = f
    · obtain ⟨rfl, rfl⟩ := hh
      obtain ⟨s2, h2, h3⟩ := (step_flags hs1 id).2.2.1 rfl hon hf
      obtain ⟨s3, h3', b1, _⟩ := run_mono t id ht s2 h2
      exact ⟨s3, h3', b1 h3⟩
    · refine ih ht ⟨f', ?_, hon, hf⟩
      rcases List.mem_cons.1 hm with h' | h'
      · simp only [Prod.mk.injEq] at h'
        exact absurd ⟨h'.1.symm, h'.2⟩ hh
      · exact h'

/-- A frame with FIN that the peer sends on a stream, once accepted, leaves it closed.

It is closed on the peer side.

This holds if no frame on this stream carries RST.

It also needs that this stream does not start reset. -/
theorem run_fin_recv (events : List (Bool × Frame)) (id : UInt32) :
    ∀ {session after : Session}, run session events = .ok after →
    (∃ f, (true, f) ∈ events ∧ OnStream id f ∧ f.hasFlag fin = true) →
    (∀ e ∈ events, OnStream id e.2 → e.2.hasFlag rst = false) →
    (∀ s, session.find? id = some s → s.localReset = false ∧ s.remoteReset = false) →
    ∃ s', after.find? id = some s' ∧ s'.remoteClosed = true := by
  induction events with
  | nil => intro session after h hex; simp at hex
  | cons e t ih =>
    intro session after h hex hno hstart
    obtain ⟨r, f⟩ := e
    obtain ⟨s1, hs1, ht⟩ := run_cons h
    obtain ⟨f', hm, hon, hf⟩ := hex
    by_cases hh : r = true ∧ f' = f
    · obtain ⟨rfl, rfl⟩ := hh
      rcases (step_flags hs1 id).2.2.2.1 rfl hon hf with ⟨s2, h2, h3⟩ | ⟨s2, h2, h3⟩
      · obtain ⟨s3, h3', _, b2, _⟩ := run_mono t id ht s2 h2
        exact ⟨s3, h3', b2 h3⟩
      · have := (hstart s2 h2).1
        simp_all
    · refine ih ht ⟨f', ?_, hon, hf⟩ (fun e' hm' => hno e' (List.mem_cons_of_mem _ hm')) ?_
      · rcases List.mem_cons.1 hm with h' | h'
        · simp only [Prod.mk.injEq] at h'
          exact absurd ⟨h'.1.symm, h'.2⟩ hh
        · exact h'
      · intro s2 h2
        rcases ((step_flags hs1 id).2.1 s2 h2).2.2 with h3
        have h4 : ¬ (s2.localReset = true ∨ s2.remoteReset = true) := by
          intro hc
          rcases h3 hc with ⟨s4, h4, h5⟩ | ⟨hon', hr'⟩
          · have := hstart s4 h4
            simp_all
          · have := hno (r, f) (List.mem_cons_self ..) hon'
            simp_all
        simp_all

/-- A stream is closed iff both sides sent FIN and neither side sent RST. -/
theorem state_eq_closed_iff (s : Stream) :
    s.state = .closed ↔ s.localReset = false ∧ s.remoteReset = false ∧
      s.localClosed = true ∧ s.remoteClosed = true := by
  unfold Stream.state
  cases h1 : s.localReset <;> cases h2 : s.remoteReset <;> cases h3 : s.localClosed <;>
    cases h4 : s.remoteClosed <;> cases s.acked <;> cases s.localOpened <;> simp

/-- The table of a new session has no stream. -/
theorem find?_empty (isClient : Bool) (id : UInt32) :
    ({ isClient } : Session).find? id = none := by
  simp [Session.find?]

/-- After accepted frames from an empty session, take a stream in the table.

It is closed iff this side sent FIN on it, it received FIN on it, and no frame on it carried RST.
-/
theorem closed_iff {isClient : Bool} {events : List (Bool × Frame)} {after : Session}
    (h : run { isClient } events = .ok after) (id : UInt32) :
    (after.find? id).map Stream.state = some .closed ↔
      (∃ f, (false, f) ∈ events ∧ OnStream id f ∧ f.hasFlag fin = true) ∧
      (∃ f, (true, f) ∈ events ∧ OnStream id f ∧ f.hasFlag fin = true) ∧
      ∀ e ∈ events, OnStream id e.2 → e.2.hasFlag rst = false := by
  have hstart := find?_empty isClient
  constructor
  · intro hmap
    obtain ⟨s', hs', hst⟩ : ∃ s', after.find? id = some s' ∧ s'.state = .closed := by
      cases hf : after.find? id with
      | none => simp [hf] at hmap
      | some s' => exact ⟨s', rfl, by simpa [hf] using hmap⟩
    obtain ⟨hlr, hrr, hlc, hrc⟩ := (state_eq_closed_iff s').1 hst
    obtain ⟨c1, c2, _⟩ := run_prov events id h s' hs'
    refine ⟨?_, ?_, ?_⟩
    · rcases c1 hlc with ⟨s, hs, _⟩ | hex
      · rw [find?_empty] at hs; cases hs
      · exact hex
    · rcases c2 hrc with ⟨s, hs, _⟩ | hex
      · rw [find?_empty] at hs; cases hs
      · exact hex
    · intro e he hon
      cases hr : e.2.hasFlag rst with
      | false => rfl
      | true =>
        obtain ⟨s'', hs'', hc⟩ := run_rst events id h ⟨e, he, hon, hr⟩
        rw [hs'] at hs''
        obtain rfl := Option.some.inj hs''
        rcases hc with hc | hc <;> simp_all
  · rintro ⟨hsent, hrecv, hno⟩
    obtain ⟨sa, hsa, hlc⟩ := run_fin_sent events id h hsent
    obtain ⟨sb, hsb, hrc⟩ := run_fin_recv events id h hrecv hno (by
      intro s hs
      rw [find?_empty] at hs; cases hs)
    rw [hsa] at hsb
    obtain rfl := Option.some.inj hsb
    have hnr : ¬ (sa.localReset = true ∨ sa.remoteReset = true) := by
      intro hc
      rcases (run_prov events id h sa hsa).2.2 hc with ⟨s, hs, _⟩ | ⟨e, he, hon, hr⟩
      · rw [find?_empty] at hs; cases hs
      · have := hno e he hon
        simp_all
    rw [hsa]
    simp only [Option.map_some, Option.some.injEq]
    exact (state_eq_closed_iff sa).2 ⟨by simp_all, by simp_all, hlc, hrc⟩

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Libp2p.Yamux.YamuxSessionError.code_injective
    (e₁ e₂ : YamuxSessionError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [YamuxSessionError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Libp2p.YamuxSession
