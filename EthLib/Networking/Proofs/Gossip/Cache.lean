module

public import EthLib.Networking.Gossip.Cache

/-!
# Proofs: the gossipsub caches

- A message put into the cache is found by its ID.
- After a put and some shifts, the message is found iff fewer shifts than the history length ran.
- Take a put of an ID that the cache did not hold, then some shifts.
  The ID is told of in gossip iff fewer shifts ran than both window counts, and its topic matches.
- These two results need a history of at least one window.
- Every ID told of in gossip is found in the cache.
- An ID inserted at a time is seen until its lifetime ends, and expiry then removes that entry.
- Expiry keeps every answer at the time it runs, for the same lifetime.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Cache

open EthLib.Networking.Gossip

/-- After one shift or more, the windows are empty ones, then the old ones, cut to the length. -/
private theorem windows_iterate (c : MessageCache) {len : Nat} (hlen : 0 < len) (k : Nat) :
    (Nat.repeat (fun (c : MessageCache) => c.shift len) (k + 1) c).windows =
      (List.replicate (k + 1) [] ++ c.windows).take len := by
  induction k with
  | zero => simp [Nat.repeat, MessageCache.shift]
  | succ k ih =>
    rw [Nat.repeat, MessageCache.shift]
    simp only [ih]
    cases len with
    | zero => omega
    | succ n =>
      rw [List.replicate_succ (n := k + 1), List.cons_append]
      simp [List.take_succ_cons, List.take_take]

/-- Cutting to a count then flattening drops the empty leading windows. -/
private theorem flatten_take_replicate (W : List (List (MessageId × Message))) (k n : Nat) :
    ((List.replicate k [] ++ W).take n).flatten = (W.take (n - k)).flatten := by
  rw [List.take_append]
  simp [List.take_replicate]

/-- Every message of a prefix of the windows is a message of the windows. -/
private theorem mem_flatten_take {L : List (List (MessageId × Message))} {n : Nat}
    {p : MessageId × Message} (h : p ∈ (L.take n).flatten) : p ∈ L.flatten := by
  obtain ⟨w, hw, hp⟩ := List.mem_flatten.mp h
  exact List.mem_flatten.mpr ⟨w, List.mem_of_mem_take hw, hp⟩

/-- A put makes the current window start with the new message. -/
private theorem put_windows (cache : MessageCache) (id : MessageId) (m : Message) :
    ∃ (w : List (MessageId × Message)) (older : List (List (MessageId × Message))),
      (cache.put id m).windows = ((id, m) :: w) :: older := by
  unfold MessageCache.put
  cases cache.windows with
  | nil => exact ⟨[], [], rfl⟩
  | cons w older => exact ⟨w, older, rfl⟩

/-- A put adds the new message in front of the messages of the cache. -/
private theorem put_flatten (cache : MessageCache) (id : MessageId) (m : Message) :
    (cache.put id m).windows.flatten = (id, m) :: cache.windows.flatten := by
  unfold MessageCache.put
  cases cache.windows with
  | nil => rfl
  | cons w older => simp

/-- After some shifts, the newest windows hold the messages of the newest old windows. -/
private theorem flatten_take_iterate (c : MessageCache) {len : Nat} (hlen : 0 < len) (k n : Nat) :
    ∃ N, ((Nat.repeat (fun (c : MessageCache) => c.shift len) k c).windows.take n).flatten =
        (c.windows.take (N - k)).flatten ∧ (k < N ↔ k < n ∧ k < len) := by
  cases k with
  | zero => exact ⟨n, by simp [Nat.repeat], by omega⟩
  | succ j =>
    refine ⟨min n len, ?_, by omega⟩
    rw [windows_iterate c hlen, List.take_take, flatten_take_replicate]

/-- A message put into the cache is found by its ID. -/
theorem get_put (cache : MessageCache) (id : MessageId) (m : Message) :
    (cache.put id m).get id = some m := by
  unfold MessageCache.put
  cases h : cache.windows <;> simp [MessageCache.get]

/-- After a put and some shifts, the message is found iff fewer shifts than the history length ran.

The history length is at least one window. -/
theorem get_shift_iterate (cache : MessageCache) (id : MessageId) (m : Message) {len : Nat}
    (hlen : 0 < len) (k : Nat) :
    (Nat.repeat (fun (c : MessageCache) => c.shift len) k (cache.put id m)).get id =
      if k < len then some m else none := by
  cases k with
  | zero => simpa [Nat.repeat, hlen] using get_put cache id m
  | succ j =>
    obtain ⟨w, older, hW⟩ := put_windows cache id m
    unfold MessageCache.get
    rw [windows_iterate _ hlen, flatten_take_replicate, hW]
    by_cases hj : j + 1 < len
    · obtain ⟨r, hr⟩ : ∃ r, len - (j + 1) = r + 1 := ⟨len - (j + 1) - 1, by omega⟩
      simp [hj, hr]
    · have : len - (j + 1) = 0 := by omega
      simp [hj, this]

/-- After a put and some shifts, the ID is told of in gossip iff fewer shifts ran than either count.

The counts are the gossip count and the history length.

Its topic must match too, and the cache must not hold the ID before the put.

The history length is at least one window. -/
theorem gossipIds_shift_iterate (cache : MessageCache) (id : MessageId) (m : Message)
    {len : Nat} (hlen : 0 < len) (gossip k : Nat) (topic : String)
    (hfresh : cache.get id = none) :
    id ∈ (Nat.repeat (fun (c : MessageCache) => c.shift len) k (cache.put id m)).gossipIds
      gossip topic ↔
      k < gossip ∧ k < len ∧ m.topic = topic := by
  obtain ⟨N, hN, hiff⟩ := flatten_take_iterate (cache.put id m) hlen k gossip
  have hsub : ∀ q ∈ ((cache.put id m).windows.take (N - k)).flatten,
      q = (id, m) ∨ q ∈ cache.windows.flatten := by
    intro q hq
    have := mem_flatten_take hq
    rw [put_flatten] at this
    simpa using this
  obtain ⟨w, older, hW⟩ := put_windows cache id m
  unfold MessageCache.gossipIds
  rw [hN]
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨q, ⟨hq, hqt⟩, hid⟩
    have hk : k < N := by
      refine Nat.lt_of_not_ge fun hk => ?_
      have h0 : N - k = 0 := by omega
      rw [h0] at hq
      simp at hq
    refine ⟨(hiff.mp hk).1, (hiff.mp hk).2, ?_⟩
    rcases hsub q hq with hqm | hc
    · rw [hqm] at hqt
      exact hqt
    · have := List.lookup_eq_none_iff.mp hfresh q hc
      rw [hid] at this
      simp at this
  · rintro ⟨hk, hl, ht⟩
    have hk' : k < N := hiff.mpr ⟨hk, hl⟩
    obtain ⟨r, hr⟩ : ∃ r, N - k = r + 1 := ⟨N - k - 1, by omega⟩
    refine ⟨(id, m), ⟨?_, by simpa using ht⟩, rfl⟩
    rw [hr, hW]
    simp

/-- Every ID told of in gossip is found in the cache. -/
theorem gossipIds_subset_get (cache : MessageCache) (gossip : Nat) (topic : String)
    {id : MessageId} (h : id ∈ cache.gossipIds gossip topic) : (cache.get id).isSome := by
  unfold MessageCache.gossipIds at h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  have hq' := mem_flatten_take (List.mem_filter.mp hq).1
  unfold MessageCache.get
  rcases hl : List.lookup q.1 cache.windows.flatten with _ | _
  · have := List.lookup_eq_none_iff.mp hl q hq'
    simp at this
  · rfl

/-- An ID inserted at a time is seen at every time before its lifetime ends. -/
theorem contains_insert (cache : SeenCache) {t now ttlMs : Nat} (id : MessageId)
    (h : now < t + ttlMs) : (cache.insert t id).contains now ttlMs id = true := by
  simp [SeenCache.contains, SeenCache.insert, h]

/-- Expiry keeps every answer at the time it runs, for the same lifetime. -/
theorem contains_expire (cache : SeenCache) (now ttlMs : Nat) (id : MessageId) :
    (cache.expire now ttlMs).contains now ttlMs id = cache.contains now ttlMs id := by
  simp [SeenCache.contains, SeenCache.expire, List.any_filter]
  congr 1
  funext a
  generalize decide (now < a.snd + ttlMs) = x
  generalize decide (a.fst = id) = y
  cases x <;> cases y <;> rfl

/-- Expiry removes the entry of an ID once its lifetime has ended. -/
theorem expire_insert (cache : SeenCache) {t now ttlMs : Nat} (id : MessageId)
    (h : t + ttlMs ≤ now) : (id, t) ∉ ((cache.insert t id).expire now ttlMs).entries := by
  simp [SeenCache.insert, SeenCache.expire]
  omega

end EthLib.Networking.Proofs.Gossip.Cache
