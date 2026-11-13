module

public import EthLib.Networking.Libp2p.MplexSession

/-!
# Proofs: the streams of an mplex connection

- A frame changes the state of its own stream only.
- Once a side has received a close or a reset on a stream, it refuses the peer's later data on it.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.MplexSession

open EthLib.Networking.Libp2p.Mplex

/-- Setting a stream makes the table report that state for it. -/
theorem find?_set_self (streams : Streams) (key : StreamKey) (s : StreamState) :
    (streams.set key s).find? key = some s := by
  unfold Streams.set
  by_cases h : streams.any (·.1 = key) = true
  · simp only [h, ↓reduceIte]
    induction streams with
    | nil => simp at h
    | cons e t ih =>
      by_cases he : e.1 = key
      · simp [Streams.find?, he]
      · simp only [List.any_cons, he, decide_false, Bool.false_or] at h
        simpa [Streams.find?, List.find?_cons, he] using ih h
  · simp only [h]
    induction streams with
    | nil => simp [Streams.find?]
    | cons e t ih =>
      by_cases he : e.1 = key
      · simp [List.any_cons, he] at h
      · simp only [List.any_cons, he, decide_false, Bool.false_or] at h
        simpa [Streams.find?, List.find?_cons, he] using ih h

/-- Setting a stream leaves every other stream as it was. -/
theorem find?_set_of_ne (streams : Streams) {key key' : StreamKey} (s : StreamState)
    (h : key' ≠ key) : (streams.set key s).find? key' = streams.find? key' := by
  unfold Streams.set
  by_cases hc : streams.any (·.1 = key) = true
  · simp only [hc]
    clear hc
    induction streams with
    | nil => simp
    | cons e t ih =>
      by_cases he : e.1 = key'
      · have : e.1 ≠ key := fun h' => h (he ▸ h' ▸ rfl)
        simp [Streams.find?, he, h]
      · by_cases hk : e.1 = key
        · simpa [Streams.find?, List.find?_cons, he, hk, Ne.symm h] using ih
        · simpa [Streams.find?, List.find?_cons, he, hk] using ih
  · simp only [hc]
    clear hc
    induction streams with
    | nil => simp [Streams.find?, Ne.symm h]
    | cons e t ih =>
      by_cases he : e.1 = key'
      · simp [Streams.find?, he]
      · simpa [Streams.find?, List.find?_cons, he] using ih

/-- An accepted frame leaves the state of every other stream unchanged.

So the two streams that share an ID, one opened by each side, never affect each other. -/
theorem step_find?_of_ne {remote : Bool} {streams after : Streams} {frame : Frame}
    {key : StreamKey} (h : step remote streams frame = .ok after)
    (hkey : key ≠ streamKey remote frame) : after.find? key = streams.find? key := by
  unfold step at h
  generalize hk : streamKey remote frame = k at h hkey
  rcases hf : frame.flag <;> rcases hs : streams.find? k with _ | st <;>
    (try (cases st <;> try (rename_i b; cases b))) <;>
    simp only [hf, hs] at h <;>
    (try split at h) <;> (try split at h) <;>
    first
    | (cases h; done)
    | (cases h; rfl)
    | (cases h; exact find?_set_of_ne _ _ hkey)

/-- The table has the stream, and the other side has closed or reset it. -/
def Blocked (k : StreamKey) (streams : Streams) : Prop :=
  ∃ st, streams.find? k = some st ∧ (st.remoteClosed || st.remoteReset) = true

/-- An accepted frame keeps a blocked stream blocked. -/
theorem blocked_step {remote : Bool} {streams after : Streams} {frame : Frame} {k : StreamKey}
    (h : step remote streams frame = .ok after) (hb : Blocked k streams) : Blocked k after := by
  by_cases hk : k = streamKey remote frame
  · obtain ⟨st, hs, hw⟩ := hb
    unfold step at h
    generalize streamKey remote frame = k' at h hk
    subst hk
    rcases hf : frame.flag <;> simp only [hf, hs] at h <;>
      (try split at h) <;> (try split at h) <;> (try split at h) <;>
      first
      | (cases h; done)
      | (cases h; exact ⟨_, hs, hw⟩)
      | (cases h; refine ⟨_, find?_set_self _ _ _, ?_⟩; simp_all)
  · obtain ⟨st, hs, hw⟩ := hb
    exact ⟨st, (step_find?_of_ne h hk).trans hs, hw⟩

/-- Any accepted run of frames keeps a blocked stream blocked. -/
theorem blocked_foldlM {k : StreamKey} (l : List (Bool × Frame)) :
    ∀ {streams after : Streams},
      l.foldlM (fun streams (e : Bool × Frame) => step e.1 streams e.2) streams = .ok after →
      Blocked k streams → Blocked k after := by
  induction l with
  | nil =>
    intro streams after h hb
    have h' : (Except.ok streams : Except MplexSessionError Streams) = .ok after := h
    cases h'
    exact hb
  | cons e t ih =>
    intro streams after h hb
    rw [List.foldlM_cons] at h
    cases hs : step e.1 streams e.2 with
    | error _ => simp [hs] at h; cases h
    | ok s' => simp [hs] at h; exact ih h (blocked_step hs hb)

/-- An accepted received close or reset leaves its stream blocked. -/
theorem blocked_of_end {streams after : Streams} {ending : Frame}
    (hend : ending.flag ∈
      [Flag.closeReceiver, Flag.closeInitiator, Flag.resetReceiver, Flag.resetInitiator])
    (h : step true streams ending = .ok after) : Blocked (streamKey true ending) after := by
  unfold step at h
  generalize streamKey true ending = k at h ⊢
  rcases hs : streams.find? k with _ | st <;>
    rcases hf : ending.flag <;> simp only [hf, hs, List.mem_cons] at h hend <;>
    (try split at h) <;> (try split at h) <;>
    first
    | (exfalso; simp at hend; done)
    | (cases h; done)
    | (cases h; refine ⟨_, find?_set_self _ _ _, ?_⟩; simp_all)

/-- After a received close or reset on a stream, a later received data frame on it is refused.

Any frames may come between, sent or received, as long as the side accepts them. -/
theorem run_receive_writeAfterClose {streams after : Streams} {pre mid : List (Bool × Frame)}
    {ending message : Frame}
    (hend : ending.flag ∈
      [Flag.closeReceiver, Flag.closeInitiator, Flag.resetReceiver, Flag.resetInitiator])
    (hmsg : message.flag = .messageReceiver ∨ message.flag = .messageInitiator)
    (hkey : streamKey true message = streamKey true ending)
    (h : run streams (pre ++ (true, ending) :: mid) = .ok after) :
    receive after message =
      .error (.writeAfterClose message.streamId (streamKey true message).2) := by
  unfold run at h
  rw [List.foldlM_append] at h
  cases h1 : List.foldlM (fun streams (e : Bool × Frame) => step e.1 streams e.2) streams pre with
  | error _ => simp [h1] at h; cases h
  | ok s1 =>
    simp only [h1, bind, Except.bind] at h
    rw [List.foldlM_cons] at h
    cases h2 : step true s1 ending with
    | error _ => simp [h2] at h; cases h
    | ok s2 =>
      simp only [h2] at h
      have hb := blocked_foldlM mid h (blocked_of_end hend h2)
      rw [← hkey] at hb
      obtain ⟨st, hs, hw⟩ := hb
      have hid : (streamKey true ending).fst = message.streamId := (congrArg Prod.fst hkey).symm
      unfold receive step
      rcases hm : message.flag <;> simp_all

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Libp2p.Mplex.MplexSessionError.code_injective
    (e₁ e₂ : MplexSessionError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [MplexSessionError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Libp2p.MplexSession
