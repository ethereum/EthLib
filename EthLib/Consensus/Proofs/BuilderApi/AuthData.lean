module

public import EthLib.Consensus.BuilderApi.AuthData

/-!
# Proofs: the default data of a builder from its URL

The compressed text of an IPv6 address reads back as that address.

So two addresses with the same compressed text are equal.

Two URLs whose hosts are IPv6 literals give the same data exactly when they name the same address.

So every spelling of an address signs the same bytes, and two different addresses never do.

More generally, two URLs that give the same data have the same host.

The default data is never empty, and each of its bytes is ASCII.
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

/-! ## Hexadecimal groups -/

/-- A hexadecimal digit reads back as its value, and is ASCII. -/
private theorem hexDigitValue?_digitChar {d : Nat} (hd : d < 16) :
    hexDigitValue? (Nat.digitChar d) = some d ∧ (Nat.digitChar d).toNat < 128 := by
  match d, hd with
  | 0, _ => rw [show Nat.digitChar 0 = '0' by simp]; decide
  | 1, _ => rw [show Nat.digitChar 1 = '1' by simp]; decide
  | 2, _ => rw [show Nat.digitChar 2 = '2' by simp]; decide
  | 3, _ => rw [show Nat.digitChar 3 = '3' by simp]; decide
  | 4, _ => rw [show Nat.digitChar 4 = '4' by simp]; decide
  | 5, _ => rw [show Nat.digitChar 5 = '5' by simp]; decide
  | 6, _ => rw [show Nat.digitChar 6 = '6' by simp]; decide
  | 7, _ => rw [show Nat.digitChar 7 = '7' by simp]; decide
  | 8, _ => rw [show Nat.digitChar 8 = '8' by simp]; decide
  | 9, _ => rw [show Nat.digitChar 9 = '9' by simp]; decide
  | 10, _ => rw [show Nat.digitChar 10 = 'a' by simp]; decide
  | 11, _ => rw [show Nat.digitChar 11 = 'b' by simp]; decide
  | 12, _ => rw [show Nat.digitChar 12 = 'c' by simp]; decide
  | 13, _ => rw [show Nat.digitChar 13 = 'd' by simp]; decide
  | 14, _ => rw [show Nat.digitChar 14 = 'e' by simp]; decide
  | 15, _ => rw [show Nat.digitChar 15 = 'f' by simp]; decide
  | _ + 16, h => omega

/-- Each digit of a number in base 16 is the character of a digit below 16. -/
private theorem exists_digitChar_of_mem_toDigits {n : Nat} {c : Char} (hc : c ∈ Nat.toDigits 16 n) :
    ∃ d < 16, c = Nat.digitChar d := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)] at hc
    split at hc
    · exact ⟨n, by omega, by simpa using hc⟩
    · simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih (n / 16) (by omega) hc
      · exact ⟨n % 16, Nat.mod_lt _ (by decide), hc⟩

/-- The digits of a number in base 16 read back as that number. -/
private theorem foldlM_toDigits (n : Nat) :
    (Nat.toDigits 16 n).foldlM (fun acc c => (acc * 16 + ·) <$> hexDigitValue? c) 0 = some n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · simp [(hexDigitValue?_digitChar ‹_›).1]
    · rw [List.foldlM_append, ih (n / 16) (by omega)]
      simp [(hexDigitValue?_digitChar (Nat.mod_lt n (by decide : 16 > 0))).1]
      omega

/-- A group in hexadecimal is not empty. -/
theorem hexGroup_ne_nil (g : UInt16) : hexGroup g ≠ [] := Nat.toDigits_ne_nil

/-- Each character of a group in hexadecimal is a hexadecimal digit and ASCII. -/
theorem mem_hexGroup {g : UInt16} {c : Char} (hc : c ∈ hexGroup g) :
    (∃ d, hexDigitValue? c = some d) ∧ c.toNat < 128 := by
  obtain ⟨d, hd, rfl⟩ := exists_digitChar_of_mem_toDigits hc
  exact ⟨⟨d, (hexDigitValue?_digitChar hd).1⟩, (hexDigitValue?_digitChar hd).2⟩

/-- A group in hexadecimal holds no colon. -/
theorem colon_not_mem_hexGroup (g : UInt16) : ':' ∉ hexGroup g := by
  intro h
  obtain ⟨⟨d, hd⟩, -⟩ := mem_hexGroup h
  rw [show hexDigitValue? _ = none by decide] at hd
  cases hd

/-- A group in hexadecimal holds no dot. -/
theorem dot_not_mem_hexGroup (g : UInt16) : '.' ∉ hexGroup g := by
  intro h
  obtain ⟨⟨d, hd⟩, -⟩ := mem_hexGroup h
  rw [show hexDigitValue? _ = none by decide] at hd
  cases hd

/-- A group in hexadecimal reads back as that group. -/
theorem parseHexGroup_hexGroup (g : UInt16) : parseHexGroup (hexGroup g) = some g := by
  have hlen : (hexGroup g).length ≤ 4 :=
    (Nat.length_toDigits_le_iff (by decide) (by decide)).2 (by simpa using g.toNat_lt)
  have hc : ¬(hexGroup g = [] ∨ 4 < (hexGroup g).length) := by
    simp only [hexGroup_ne_nil g, false_or]
    omega
  simp only [parseHexGroup, hc, ite_false]
  rw [hexGroup, foldlM_toDigits]
  simp

/-! ## Splitting at a double colon -/

/-- A character other than a colon is kept on the left of the split. -/
theorem splitDoubleColon_cons {c : Char} (hc : c ≠ ':') (t : List Char) :
    splitDoubleColon (c :: t) = (fun p => (c :: p.1, p.2)) <$> splitDoubleColon t := by
  cases t with
  | nil => simp [splitDoubleColon]
  | cons d t => simp [splitDoubleColon, hc]

/-- A colon followed by a character other than a colon is kept on the left of the split. -/
theorem splitDoubleColon_colon_cons {c : Char} (hc : c ≠ ':') (t : List Char) :
    splitDoubleColon (':' :: c :: t) =
      (fun p => (':' :: p.1, p.2)) <$> splitDoubleColon (c :: t) := by
  simp [splitDoubleColon, hc]

/-- Text without colons is kept on the left of the split. -/
theorem splitDoubleColon_append {h : List Char} (hh : ':' ∉ h) (s : List Char) :
    splitDoubleColon (h ++ s) = (fun p => (h ++ p.1, p.2)) <$> splitDoubleColon s := by
  induction h with
  | nil => simp
  | cons c h ih =>
    simp only [List.mem_cons, not_or] at hh
    rw [List.cons_append, splitDoubleColon_cons (Ne.symm hh.1), ih hh.2]
    simp [Function.comp_def]

/-- Groups in hexadecimal separated by colons start with the first group and a colon. -/
theorem joinGroups_cons_cons (g g' : UInt16) (gs : List UInt16) :
    joinGroups (g :: g' :: gs) = hexGroup g ++ ':' :: joinGroups (g' :: gs) := by
  simp [joinGroups]

/-- Groups in hexadecimal start with a character other than a colon. -/
theorem joinGroups_cons_append (g : UInt16) (gs : List UInt16) (s : List Char) :
    ∃ c t, joinGroups (g :: gs) ++ s = c :: t ∧ c ≠ ':' := by
  obtain ⟨c, t, ht⟩ := List.exists_cons_of_ne_nil (hexGroup_ne_nil g)
  refine ⟨c, ?_, ?_, ?_⟩
  · exact (joinGroups (g :: gs) ++ s).tail
  · cases gs <;> simp [joinGroups, ht]
  · intro hc
    exact colon_not_mem_hexGroup g (hc ▸ ht ▸ List.mem_cons_self)

/-- Groups in hexadecimal are kept whole on the left of the split. -/
theorem splitDoubleColon_joinGroups_append :
    ∀ (gs : List UInt16), gs ≠ [] → ∀ s, splitDoubleColon (joinGroups gs ++ s) =
      (fun p => (joinGroups gs ++ p.1, p.2)) <$> splitDoubleColon s
  | [], h, _ => absurd rfl h
  | [g], _, s => by
    simpa [joinGroups] using splitDoubleColon_append (colon_not_mem_hexGroup g) s
  | g :: g' :: gs, _, s => by
    obtain ⟨c, t, hct, hc⟩ := joinGroups_cons_append g' gs s
    rw [joinGroups_cons_cons, List.append_assoc, List.cons_append,
      splitDoubleColon_append (colon_not_mem_hexGroup g), hct, splitDoubleColon_colon_cons hc,
      ← hct, splitDoubleColon_joinGroups_append (g' :: gs) (by simp) s]
    simp [Function.comp_def]

/-- The split of compressed text is at its double colon. -/
theorem splitDoubleColon_joinGroups_colon (gs : List UInt16) (r : List Char) :
    splitDoubleColon (joinGroups gs ++ ':' :: ':' :: r) = some (joinGroups gs, r) := by
  rcases gs with _ | ⟨g, gs⟩
  · simp [joinGroups, splitDoubleColon]
  · rw [splitDoubleColon_joinGroups_append _ (by simp)]
    simp [splitDoubleColon]

/-- Groups in hexadecimal hold no double colon. -/
theorem splitDoubleColon_joinGroups (gs : List UInt16) :
    splitDoubleColon (joinGroups gs) = none := by
  rcases gs with _ | ⟨g, gs⟩
  · simp [joinGroups, splitDoubleColon]
  · have := splitDoubleColon_joinGroups_append (g :: gs) (by simp) []
    simpa [splitDoubleColon] using this

/-! ## Reading groups back -/

/-- A group in hexadecimal reads back as a field. -/
theorem parseField_hexGroup (last : Bool) (g : UInt16) :
    parseField last (hexGroup g) = some [g] := by
  have hc : ¬(last = true ∧ '.' ∈ hexGroup g) := fun h => dot_not_mem_hexGroup g h.2
  simp only [parseField, hc, ite_false, parseHexGroup_hexGroup]
  rfl

/-- Groups in hexadecimal read back as fields. -/
theorem parseFields_map_hexGroup (ipv4Tail : Bool) :
    ∀ gs : List UInt16, parseFields ipv4Tail (gs.map hexGroup) = some gs
  | [] => rfl
  | [g] => parseField_hexGroup ipv4Tail g
  | g :: g' :: gs => by
    have := parseFields_map_hexGroup ipv4Tail (g' :: gs)
    simp only [List.map_cons] at this ⊢
    rw [parseFields, parseHexGroup_hexGroup, this]
    · rfl
    · simp

/-- Groups in hexadecimal separated by colons read back as those groups. -/
theorem parseGroups_joinGroups (ipv4Tail : Bool) (gs : List UInt16) :
    parseGroups ipv4Tail (joinGroups gs) = some gs := by
  rcases gs with _ | ⟨g, gs⟩
  · simp [parseGroups, joinGroups]
  have hsplit : (joinGroups (g :: gs)).splitOn ':' = (g :: gs).map hexGroup :=
    List.splitOn_intercalate ':' (by simp [colon_not_mem_hexGroup]) (by simp)
  have hne : joinGroups (g :: gs) ≠ [] := by
    obtain ⟨c, t, h, -⟩ := joinGroups_cons_append g gs []
    simp only [List.append_nil] at h
    simp [h]
  simp only [parseGroups, hne, ite_false]
  rw [hsplit, parseFields_map_hexGroup]

/-! ## The first longest run of zero groups -/

/-- A property that holds at the start of a left fold and that each step keeps holds at its end. -/
private theorem foldl_induction {α β : Type} (P : β → Prop) (f : β → α → β)
    (hf : ∀ b a, P b → P (f b a)) : ∀ (xs : List α) (b : β), P b → P (xs.foldl f b)
  | [], _, hb => hb
  | a :: xs, b, hb => foldl_induction P f hf xs (f b a) (hf b a hb)

/-- The run that compression replaces holds at least two groups, all of them zero. -/
theorem zeroRun_spec {gs : List UInt16} {s l : Nat} (h : zeroRun gs = some (s, l)) :
    2 ≤ l ∧ l = ((gs.drop s).takeWhile (· = 0)).length := by
  unfold zeroRun at h
  refine foldl_induction (fun best => ∀ s l, best = some (s, l) →
    2 ≤ l ∧ l = ((gs.drop s).takeWhile (· = 0)).length) _ ?_ _ none (by simp) s l h
  intro best start hb s l h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨‹_ ∧ _›.1, rfl⟩
  · exact hb s l h

/-- The groups around a run of zero groups, with the run put back, are all the groups. -/
theorem take_append_replicate_append_drop {gs : List UInt16} {s l : Nat}
    (hl : l = ((gs.drop s).takeWhile (· = 0)).length) :
    gs.take s ++ List.replicate l 0 ++ gs.drop (s + l) = gs := by
  have hrep : List.replicate l 0 = (gs.drop s).takeWhile (· = 0) := by
    refine (List.eq_replicate_iff.2 ⟨hl.symm, fun b hb => ?_⟩).symm
    simpa using List.all_eq_true.1 List.all_takeWhile b hb
  have hdrop : gs.drop (s + l) = (gs.drop s).dropWhile (· = 0) := by
    rw [← List.drop_drop, hl]
    generalize gs.drop s = D
    have hD := List.takeWhile_append_dropWhile (p := fun x : UInt16 => decide (x = 0)) (l := D)
    calc List.drop (D.takeWhile (· = 0)).length D
        = List.drop (D.takeWhile (· = 0)).length (D.takeWhile (· = 0) ++ D.dropWhile (· = 0)) := by
          rw [hD]
      _ = D.dropWhile (· = 0) := List.drop_left
  rw [List.append_assoc, hrep, hdrop, List.takeWhile_append_dropWhile, List.take_append_drop]

/-- The vector of the groups of an address is that address. -/
private theorem vector_mk_eq {address : Vector UInt16 8} {gs : List UInt16}
    (h : gs = address.toList)
    (hg : gs.toArray.size = 8) : (⟨gs.toArray, hg⟩ : Vector UInt16 8) = address := by
  subst h
  rcases address with ⟨a, ha⟩
  simp [Vector.toList]

/-- The compressed text of an IPv6 address reads back as that address. -/
theorem parseIpv6_compressIpv6 (address : Vector UInt16 8) :
    parseIpv6 (compressIpv6 address) = .ok address := by
  unfold compressIpv6 parseIpv6
  simp only [String.toList_ofList]
  cases hz : zeroRun address.toList with
  | none =>
    simp only [splitDoubleColon_joinGroups, parseGroups_joinGroups]
    rw [dite_eq_left (by simp), vector_mk_eq rfl]
  | some run =>
    obtain ⟨s, l⟩ := run
    obtain ⟨hl2, hl⟩ := zeroRun_spec hz
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      splitDoubleColon_joinGroups_colon, parseGroups_joinGroups]
    have hle : l ≤ 8 - s := by
      rw [hl]
      exact Nat.le_trans (List.takeWhile_sublist _).length_le (by simp)
    have hrun := take_append_replicate_append_drop hl
    have hlen : 8 - (s + (8 - (s + l))) = l := by omega
    simp [show s ≤ 8 by omega, show s + (8 - (s + l)) ≤ 7 by omega, hlen]
    rw [dite_eq_left (by omega), vector_mk_eq (by rw [← List.append_assoc, hrun])]

/-- Two IPv6 addresses with the same compressed text are equal. -/
theorem compressIpv6_injective : Function.Injective compressIpv6 := by
  intro a b h
  have hb := parseIpv6_compressIpv6 b
  rw [← h, parseIpv6_compressIpv6] at hb
  injection hb

/-! ## The bytes of the default data -/

/-- Only an opening bracket lowercases to an opening bracket. -/
private theorem eq_of_toLower_eq_bracket {c : Char} (h : c.toLower = '[') : c = '[' := by
  unfold Char.toLower at h
  split at h
  · rename_i hc
    have := congrArg (fun c : Char => c.val.toNat) h
    simp only [UInt32.le_iff_toNat_le, ge_iff_le] at hc
    simp only [UInt32.toNat_add] at this
    have h1 : ('A' : Char).val.toNat = 65 := rfl
    have h2 : ('Z' : Char).val.toNat = 90 := rfl
    have h3 : ('a' : Char).val - ('A' : Char).val = 32 := rfl
    have h4 : ('[' : Char).val.toNat = 91 := rfl
    rw [h3, h4] at this
    rw [h1, h2] at hc
    have h5 : c.toNat = c.val.toNat := rfl
    simp at this
    omega
  · exact h

/-- A name that a URL gives as its host is not empty and does not start with a bracket. -/
theorem urlHost_name_spec {url : String} {text : String} (h : urlHost url = .ok (.name text)) :
    text.toList ≠ [] ∧ text.toList.head? ≠ some '[' := by
  unfold urlHost at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · split at h
        · simp only [bind, Except.bind, pure, Except.pure] at h
          split at h <;> cases h
        · cases h
      · cases h
    · split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
        · split at h
          · rename_i hne hall
            injection h with h
            injection h with h
            subst h
            simp only [String.toList_ofList, ne_eq, List.map_eq_nil_iff]
            refine ⟨hne, ?_⟩
            obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
            rw [hct] at hall ⊢
            intro hc
            simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hc
            have := (List.all_eq_true.1 hall) c List.mem_cons_self
            rw [eq_of_toLower_eq_bracket hc] at this
            exact absurd this (by decide)
          · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Each character of groups in hexadecimal separated by colons is ASCII. -/
theorem joinGroups_ascii : ∀ (gs : List UInt16), ∀ c ∈ joinGroups gs, c.toNat < 128
  | [], c, hc => by simp [joinGroups] at hc
  | [g], c, hc => (mem_hexGroup (by simpa [joinGroups] using hc)).2
  | g :: g' :: gs, c, hc => by
    rw [joinGroups_cons_cons] at hc
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact (mem_hexGroup hc).2
    · decide
    · exact joinGroups_ascii (g' :: gs) c hc

/-- Each character of the compressed text of an IPv6 address is ASCII. -/
theorem compressIpv6_ascii (address : Vector UInt16 8) :
    ∀ c ∈ (compressIpv6 address).toList, c.toNat < 128 := by
  intro c hc
  simp only [compressIpv6, String.toList_ofList] at hc
  split at hc
  · exact joinGroups_ascii _ c hc
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (hc | rfl | rfl) | hc
    · exact joinGroups_ascii _ c hc
    · decide
    · decide
    · exact joinGroups_ascii _ c hc

/-- Lists of ASCII characters with the same byte values are equal. -/
private theorem map_toUInt8_injective : ∀ {xs ys : List Char}, (∀ c ∈ xs, c.toNat < 128) →
    (∀ c ∈ ys, c.toNat < 128) →
    xs.map (fun c => c.toNat.toUInt8) = ys.map (fun c => c.toNat.toUInt8) → xs = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, hx, hy, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hx' := hx x List.mem_cons_self
    have hy' := hy y List.mem_cons_self
    have hxy : x.toNat = y.toNat := by
      have := congrArg UInt8.toNat h.1
      simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat'] at this
      omega
    rw [Char.toNat_inj.1 hxy, map_toUInt8_injective (fun c hc => hx c (List.mem_cons_of_mem _ hc))
      (fun c hc => hy c (List.mem_cons_of_mem _ hc)) h.2]

/-- Two lists of ASCII characters with the same bytes are equal. -/
theorem asciiBytes_injective {xs ys : List Char} (hx : ∀ c ∈ xs, c.toNat < 128)
    (hy : ∀ c ∈ ys, c.toNat < 128) (h : asciiBytes xs = asciiBytes ys) : xs = ys := by
  simp only [asciiBytes, ByteArray.mk.injEq] at h
  exact map_toUInt8_injective hx hy (by simpa using congrArg Array.toList h)

/-- The text of an IPv6 host in brackets is ASCII. -/
theorem bracketed_ascii (address : Vector UInt16 8) :
    ∀ c ∈ '[' :: (compressIpv6 address).toList ++ [']'], c.toNat < 128 := by
  intro c hc
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | hc | rfl
  · decide
  · exact compressIpv6_ascii address c hc
  · decide

/-- The default data of a URL whose host is an IPv6 literal is its bracketed compressed text. -/
theorem defaultAuthData_of_ipv6 {url : String} {address : Vector UInt16 8}
    (host : urlHost url = .ok (.ipv6 address)) :
    defaultAuthData url = .ok (asciiBytes ('[' :: (compressIpv6 address).toList ++ [']'])) := by
  have hall : ('[' :: (compressIpv6 address).toList ++ [']']).all (·.toNat < 128) = true :=
    List.all_eq_true.2 fun c hc => decide_eq_true (bracketed_ascii address c hc)
  simp only [defaultAuthData, host, bind, Except.bind, hall, ite_true, pure, Except.pure]

/-- The text of a host whose bytes are the default data. -/
private def hostText : UrlHost → List Char
  | .name text => text.toList
  | .ipv6 address => '[' :: (compressIpv6 address).toList ++ [']']

/-- The default data is the bytes of the ASCII text of the host. -/
private theorem defaultAuthData_eq_ok {url : String} {data : ByteArray}
    (h : defaultAuthData url = .ok data) :
    ∃ host, urlHost url = .ok host ∧ (∀ c ∈ hostText host, c.toNat < 128) ∧
      data = asciiBytes (hostText host) := by
  unfold defaultAuthData at h
  cases hu : urlHost url with
  | error e =>
    rw [hu] at h
    cases h
  | ok host =>
    rw [hu] at h
    have key : ∀ text : List Char,
        (if text.all (·.toNat < 128) = true then Except.ok (asciiBytes text)
          else Except.error AuthDataError.nonAscii) = Except.ok data →
        (∀ c ∈ text, c.toNat < 128) ∧ data = asciiBytes text := by
      intro text h
      split at h
      · rename_i hall
        injection h with h
        exact ⟨fun c hc => by simpa using List.all_eq_true.1 hall c hc, h.symm⟩
      · cases h
    refine ⟨host, rfl, ?_⟩
    cases host with
    | name t => exact key _ h
    | ipv6 a => exact key ('[' :: (compressIpv6 a).toList ++ [']']) h

/-- The default data is the bytes of a nonempty ASCII text. -/
theorem defaultAuthData_spec {url : String} {data : ByteArray}
    (h : defaultAuthData url = .ok data) :
    ∃ text : List Char, text ≠ [] ∧ (∀ c ∈ text, c.toNat < 128) ∧ data = asciiBytes text := by
  obtain ⟨host, hu, hascii, rfl⟩ := defaultAuthData_eq_ok h
  refine ⟨_, ?_, hascii, rfl⟩
  cases host with
  | name t => exact (urlHost_name_spec hu).1
  | ipv6 a => simp [hostText]

/-- Two URLs whose hosts are IPv6 literals give the same data exactly when the addresses match. -/
theorem defaultAuthData_eq_iff_of_ipv6 {url url' : String} {address address' : Vector UInt16 8}
    (host : urlHost url = .ok (.ipv6 address)) (host' : urlHost url' = .ok (.ipv6 address')) :
    defaultAuthData url = defaultAuthData url' ↔ address = address' := by
  rw [defaultAuthData_of_ipv6 host, defaultAuthData_of_ipv6 host']
  constructor
  · intro h
    injection h with h
    have h := asciiBytes_injective (bracketed_ascii address) (bracketed_ascii address') h
    simp only [List.cons_append, List.cons.injEq, true_and, List.append_cancel_right_eq] at h
    exact compressIpv6_injective (String.toList_inj.1 h)
  · rintro rfl
    rfl

/-- The default data, when a URL gives it, is never empty. -/
theorem defaultAuthData_nonempty {url : String} {data : ByteArray}
    (h : defaultAuthData url = .ok data) : 0 < data.size := by
  obtain ⟨text, hne, -, rfl⟩ := defaultAuthData_spec h
  simpa [asciiBytes, ByteArray.size, List.length_pos_iff] using hne

/-- Each byte of the default data is ASCII. -/
theorem defaultAuthData_ascii {url : String} {data : ByteArray}
    (h : defaultAuthData url = .ok data) : ∀ byte ∈ data.data, byte < 128 := by
  obtain ⟨text, -, hascii, rfl⟩ := defaultAuthData_spec h
  intro byte hb
  simp only [asciiBytes, List.mem_toArray, List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  have := hascii c hc
  rw [UInt8.lt_iff_toNat_lt]
  have h128 : (128 : UInt8).toNat = 128 := rfl
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', h128]
  omega

/-- Two URLs that give the same default data have the same host. -/
theorem urlHost_eq_of_defaultAuthData_eq {url url' : String} {data : ByteArray}
    (h : defaultAuthData url = .ok data) (h' : defaultAuthData url' = .ok data) :
    urlHost url = urlHost url' := by
  obtain ⟨host, hu, hascii, rfl⟩ := defaultAuthData_eq_ok h
  obtain ⟨host', hu', hascii', hdata⟩ := defaultAuthData_eq_ok h'
  have htext := asciiBytes_injective hascii hascii' hdata
  rw [hu, hu']
  congr 1
  cases host with
  | name t =>
    cases host' with
    | name t' => rw [String.toList_inj.1 htext]
    | ipv6 a' =>
      exact absurd (by simp only [hostText] at htext; rw [htext]; rfl) (urlHost_name_spec hu).2
  | ipv6 a =>
    cases host' with
    | name t' =>
      exact absurd (by simp only [hostText] at htext; rw [← htext]; rfl)
        (urlHost_name_spec hu').2
    | ipv6 a' =>
      simp only [hostText, List.cons_append, List.cons.injEq, true_and,
        List.append_cancel_right_eq] at htext
      rw [compressIpv6_injective (String.toList_inj.1 htext)]

end EthLib.Consensus.BuilderApi
