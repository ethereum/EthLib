module

public import EthLib.Engine.Jwt
public import EthLib.Base.Proofs.Base64
public import Mathlib.Tactic

/-!
# Engine JWT construction and refusal

A 32-byte secret always builds a token, since the reader reads back the builder's own JSON.

That token authenticates with its secret and issued-at time.

The clock check then accepts at every clock within 60 seconds, including both endpoints.

A token whose tag does not match its parts is refused before any JSON is read.
-/

@[expose] public section

namespace EthLib.Engine.Jwt

open EthLib.Base

private theorem encodeSextet_ne_dot (n : Nat) : Base64.encodeSextet n ≠ '.' := by
  by_cases h : n < 64
  · exact (by decide : ∀ i : Fin 64, Base64.encodeSextet i ≠ '.') ⟨n, h⟩
  · simp [Base64.encodeSextet, show ¬n < 26 by omega, show ¬n < 52 by omega,
      show ¬n < 62 by omega, show n ≠ 62 by omega]

private theorem dot_ne_encodeSextet (n : Nat) : '.' ≠ Base64.encodeSextet n :=
  Ne.symm (encodeSextet_ne_dot n)

private theorem dot_not_mem_encodeList :
    (bytes : List UInt8) → '.' ∉ Base64.encodeList bytes
  | b0 :: b1 :: b2 :: rest => by
    simp [Base64.encodeList, dot_ne_encodeSextet, dot_not_mem_encodeList rest]
  | [b0, b1] => by simp [Base64.encodeList, dot_ne_encodeSextet]
  | [b0] => by simp [Base64.encodeList, dot_ne_encodeSextet]
  | [] => by simp [Base64.encodeList]

/-- A base64url part contains no compact-form separator. -/
theorem dot_not_mem_encode (bytes : ByteArray) : '.' ∉ (Base64.encode bytes).toList := by
  simpa [Base64.encode] using dot_not_mem_encodeList bytes.data.toList

/-- Splitting a compact form recovers its parts when none contains a separator. -/
theorem parts_compact (header claims mac : String)
    (hh : '.' ∉ header.toList) (hc : '.' ∉ claims.toList) (hm : '.' ∉ mac.toList) :
    parts (compact header claims mac) = some ⟨header, claims, mac⟩ := by
  simp only [parts, compact, String.toList_append, show ".".toList = ['.'] by rfl,
    List.append_assoc, List.cons_append, List.nil_append]
  rw [List.splitOn_append_cons_self_of_not_mem hh,
    List.splitOn_append_cons_self_of_not_mem hc, List.splitOn_eq_singleton hm]
  simp

private theorem objectFields_encode (text : String) :
    objectFields (Base64.encode text.toUTF8) = Json.fields text := by
  simp [objectFields, Base64.decode_encode, String.fromUTF8?, String.fromUTF8, text.isValidUTF8]

/-- Characters a JSON string may hold without an escape. -/
private def Plain (c : Char) : Prop := c ≠ '"' ∧ c ≠ '\\' ∧ 0x20 ≤ c.toNat

private theorem string_plain (rest : List Char) :
    ∀ (s acc : List Char) (fuel : Nat), (∀ c ∈ s, Plain c) → s.length < fuel →
      Json.string fuel (s ++ '"' :: rest) acc = some (String.ofList (acc.reverse ++ s), rest)
  | [], acc, fuel + 1, _, _ => by simp [Json.string]
  | c :: s, acc, fuel + 1, h, hl => by
    obtain ⟨h1, h2, h3⟩ := h c (by simp)
    have ih := string_plain rest s (c :: acc) fuel (fun d hd => h d (by simp [hd]))
      (by simp at hl; omega)
    rw [List.cons_append, Json.string.eq_def]
    split <;> simp_all

private theorem digit_of_mem_toDigits {c : Char} {n : Nat} (h : c ∈ Nat.toDigits 10 n) :
    Json.digit c = true := by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  simp only [Char.isDigit, Json.digit, Bool.and_eq_true, decide_eq_true_eq] at this ⊢
  exact this

private theorem digitsValue_eq (l : List Char) (h : ∀ c ∈ l, Json.digit c = true) (init : Nat) :
    l.foldl (fun acc c => 10 * acc + c.toNat - '0'.toNat) init = Nat.ofDigitChars 10 l init := by
  induction l generalizing init with
  | nil => simp
  | cons c l ih =>
    have hc := h c (by simp)
    simp only [Json.digit, Bool.and_eq_true, decide_eq_true_eq] at hc
    have : '0'.toNat ≤ c.toNat := hc.1
    rw [List.foldl_cons, Nat.ofDigitChars_cons, Nat.add_sub_assoc this]
    exact ih (fun d hd => h d (by simp [hd])) _

private theorem head_toDigits_ne_zero (n : Nat) (hn : 0 < n) :
    (Nat.toDigits 10 n).head? ≠ some '0' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · simp; omega
    · rw [List.head?_append_of_ne_nil _ Nat.toDigits_ne_nil]
      exact ih (n / 10) (by omega) (by omega)

private theorem number_toDigits (n : Nat) (tail : List Char) :
    Json.number (Nat.toDigits 10 n ++ '}' :: tail) = some (⟨n, 0⟩, '}' :: tail) := by
  have hdig : ∀ c ∈ Nat.toDigits 10 n, Json.digit c = true := fun c h => digit_of_mem_toDigits h
  have hspan : (Nat.toDigits 10 n ++ '}' :: tail).span Json.digit =
      (Nat.toDigits 10 n, '}' :: tail) := by
    rw [List.span_eq_takeWhile_dropWhile, List.takeWhile_append_of_pos hdig,
      List.dropWhile_append_of_pos hdig]
    simp [Json.digit]
  obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 n = d :: ds :=
    List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
  have hminus : d ≠ '-' := by
    have := hdig d (by simp [hd])
    rintro rfl
    simp [Json.digit] at this
  have hlead : ((d :: ds).head? = some '0' && (d :: ds).length > 1) = false := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.toDigits_zero] at hd
      simp [← hd.2]
    · have := head_toDigits_ne_zero n hn
      simp_all
  have hval : Json.digitsValue (d :: ds ++ []) = n := by
    rw [List.append_nil, ← hd, Json.digitsValue, digitsValue_eq _ hdig,
      Nat.ofDigitChars_ten_toDigits]
  rw [hd] at hspan
  unfold Json.number
  rw [hd, List.cons_append]
  split
  rename_i minus rest heq
  have : (minus, rest) = (false, d :: (ds ++ '}' :: tail)) := by
    rw [← heq]
    split <;> simp_all
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  simp only [List.cons_append] at hspan
  simp only [hspan]
  simp only [List.append_nil] at hval
  simp only [List.head?_cons, Option.some.injEq, List.length_cons, Bool.and_eq_false_imp,
    decide_eq_true_eq, decide_eq_false_iff_not, not_lt] at hlead
  simpa [hval] using fun h => List.eq_nil_of_length_eq_zero (by have := hlead h; omega)

private theorem value_string (fuel : Nat) (s rest : List Char) (hs : ∀ c ∈ s, Plain c) :
    Json.value (fuel + 1) ('"' :: (s ++ '"' :: rest)) = some (.str (String.ofList s), rest) := by
  rw [Json.value]
  simp [Json.whitespace]
  rw [string_plain rest s [] _ hs (by simp)]
  simp

private theorem value_number (fuel n : Nat) (tail : List Char) :
    Json.value (fuel + 1) (Nat.toDigits 10 n ++ '}' :: tail) =
      some (.num ⟨n, 0⟩, '}' :: tail) := by
  obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 n = d :: ds :=
    List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
  have hdig := digit_of_mem_toDigits (c := d) (n := n) (by simp [hd])
  have hnum := number_toDigits n tail
  rw [hd] at hnum
  simp only [Json.digit, Bool.and_eq_true, decide_eq_true_eq] at hdig
  rw [Json.value, hd, List.cons_append, List.dropWhile_cons_of_neg (by
    simp only [Json.whitespace, Bool.or_eq_true, decide_eq_true_eq]
    rintro (((rfl | rfl) | rfl) | rfl) <;> revert hdig <;> decide)]
  split <;> simp_all

private theorem object_close (fuel : Nat) (key rest tail : List Char) (item : Json.Value)
    (acc : List (String × Json.Value)) (empty : Bool) (hk : ∀ c ∈ key, Plain c)
    (h : Json.value fuel rest = some (item, '}' :: tail)) :
    Json.object (fuel + 1) ('"' :: (key ++ '"' :: ':' :: rest)) acc empty =
      some ((String.ofList key, item) :: acc, tail) := by
  rw [Json.object]
  simp only [List.length_append, List.length_cons]
  rw [string_plain _ key [] _ hk (by omega)]
  simp [Json.whitespace, h]

private theorem object_comma (fuel : Nat) (key rest tail : List Char) (item : Json.Value)
    (acc : List (String × Json.Value)) (empty : Bool) (hk : ∀ c ∈ key, Plain c)
    (h : Json.value fuel rest = some (item, ',' :: tail)) :
    Json.object (fuel + 1) ('"' :: (key ++ '"' :: ':' :: rest)) acc empty =
      Json.object fuel (tail.dropWhile Json.whitespace) ((String.ofList key, item) :: acc)
        false := by
  rw [Json.object]
  simp only [List.length_append, List.length_cons]
  rw [string_plain _ key [] _ hk (by omega)]
  simp [Json.whitespace, h]

/-- The builder's header names HS256 and no critical extension. -/
theorem algorithm_headerPart : algorithm headerPart = .ok "HS256" := by
  have hobj : Json.object 55 ['"', 'a', 'l', 'g', '"', ':', '"', 'H', 'S', '2', '5', '6', '"', ',',
      '"', 't', 'y', 'p', '"', ':', '"', 'J', 'W', 'T', '"', '}'] [] true =
      some ([(String.ofList ['t', 'y', 'p'], .str (String.ofList ['J', 'W', 'T'])),
        (String.ofList ['a', 'l', 'g'], .str (String.ofList ['H', 'S', '2', '5', '6']))], []) :=
    (object_comma 54 ['a', 'l', 'g'] _ _ _ _ _ (by simp [Plain])
      (value_string 53 ['H', 'S', '2', '5', '6'] _ (by simp [Plain]))).trans
      (object_close 53 ['t', 'y', 'p'] _ _ _ _ _ (by simp [Plain])
        (value_string 52 ['J', 'W', 'T'] _ (by simp [Plain])))
  rw [algorithm, headerPart, objectFields_encode]
  simp only [Json.fields, String.reduceToList]
  simp [Json.whitespace]
  rw [hobj]
  simp [List.lookup]
  rfl

/-- The builder's claims read back as its integral issued-at time. -/
theorem issuedAt_claimsPart (time : Nat) :
    issuedAt headerPart (claimsPart time) = .ok ⟨time, 0⟩ := by
  have hobj (m : Nat) : Json.object (m + 2) ('"' :: 'i' :: 'a' :: 't' :: '"' :: ':' ::
      (Nat.toDigits 10 time ++ ['}'])) [] true = some ([("iat", .num ⟨time, 0⟩)], []) := by
    refine (object_close (m + 1) ['i', 'a', 't'] _ _ _ _ _ (by simp [Plain])
      (value_number m time [])).trans ?_
    simp
  rw [issuedAt, algorithm_headerPart]
  simp only [claimsPart, objectFields_encode, Json.fields, String.toList_append, Nat.toList_repr,
    String.reduceToList]
  simp [Json.whitespace]
  rw [show ∀ k : Nat, 2 * (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) + 1 = (2 * k + 15) + 2 from
    fun k => by omega, hobj]
  simp [List.lookup, bind, Except.bind]
  rfl

/-- A 32-byte secret always builds the signed compact form of the builder's two parts. -/
theorem build_eq_ok {secret : ByteArray} (hs : secret.size = 32) (time : Nat) :
    build secret time = .ok (compact headerPart (claimsPart time)
      (signature secret headerPart (claimsPart time))) := by
  simp [build, hs, issuedAt_claimsPart]
  rfl

/-- Every successful string build authenticates, with the issued-at time it was given. -/
theorem authenticate_build {secret : ByteArray} {time : Nat} {token : String}
    (hb : build secret time = .ok token) :
    authenticate secret token = .ok ⟨time, 0⟩ := by
  have hs : secret.size = 32 := by
    by_contra hs
    simp [build, hs] at hb
  rw [build_eq_ok hs] at hb
  cases hb
  rw [authenticate, ite_eq_right (by simp [hs]), signature, parts_compact headerPart
    (claimsPart time) _ (dot_not_mem_encode _) (dot_not_mem_encode _) (dot_not_mem_encode _)]
  simp [Base64.decode_encode, issuedAt_claimsPart]

/-- Integral NumericDates pass exactly within 60 seconds of the integral clock. -/
theorem within_nat_iff (time clock : Nat) :
    Json.within ⟨time, 0⟩ clock = true ↔ clock ≤ time + 60 ∧ time ≤ clock + 60 := by
  unfold Json.within
  dsimp only
  rw [ite_eq_left (by decide : (0 : Int) ≥ 0)]
  split
  · simp only [decide_eq_true_eq]
    omega
  · rw [ite_eq_right (by simp : ¬(0 : Int).toNat > (clock + 60).repr.length)]
    simp only [Int.toNat_zero, pow_zero, Int.ofNat_one, mul_one, decide_eq_true_eq]
    omega

/-- A successfully built token passes with the same secret at every clock within 60 seconds. -/
theorem check_build {secret : ByteArray} {time clock : Nat} {token : String}
    (hb : build secret time = .ok token)
    (hclock : clock ≤ time + 60 ∧ time ≤ clock + 60) : check secret token clock = true := by
  rw [check, authenticate_build hb]
  exact (within_nat_iff time clock).2 hclock

/-- A token built with a 32-byte secret passes with it at every clock within 60 seconds. -/
theorem check_build_of_size {secret : ByteArray} {time clock : Nat} (hs : secret.size = 32)
    (hclock : clock ≤ time + 60 ∧ time ≤ clock + 60) :
    check secret (compact headerPart (claimsPart time)
      (signature secret headerPart (claimsPart time))) clock = true :=
  check_build (build_eq_ok hs time) hclock

/-- An algorithm other than HS256 cannot produce an issued-at time for this profile. -/
theorem issuedAt_eq_error_of_algorithm_ne {header claims name : String}
    (ha : algorithm header = .ok name) (hn : name ≠ "HS256") :
    issuedAt header claims = .error .algorithm := by
  simp only [issuedAt, ha, bind, Except.bind, ite_eq_left hn]
  rfl

/-- A token whose tag does not decode to the HS256 tag of its parts is refused, JSON unread. -/
theorem authenticate_eq_error_of_tag_ne {secret : ByteArray} {token : String} {p : Parts}
    (hs : secret.size = 32) (hp : parts token = some p)
    (ht : Base64.decode p.signature ≠
      .ok (Cryptography.Hash.Hmac.hmac secret (signingInput p.header p.claims))) :
    authenticate secret token = .error .signature := by
  unfold authenticate
  simp only [hs, ne_eq, not_true_eq_false, ↓reduceIte, hp]
  split
  · rename_i mac h
    rw [ite_eq_left (fun e => ht (by rw [h, e]))]
    rfl
  · rfl

/-- An authenticated time is the issued-at time read from the token's own parts. -/
theorem issuedAt_of_authenticate {secret : ByteArray} {token : String} {time : Json.Number}
    {p : Parts} (hp : parts token = some p) (h : authenticate secret token = .ok time) :
    issuedAt p.header p.claims = .ok time := by
  unfold authenticate at h
  simp only [hp] at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · exact h
  · cases h

/-- A compact token whose decoded algorithm differs from HS256 is refused. -/
theorem check_eq_false_of_algorithm_ne {secret : ByteArray} {token : String} {clock : Nat}
    {p : Parts} {name : String} (hp : parts token = some p)
    (ha : algorithm p.header = .ok name) (hn : name ≠ "HS256") :
    check secret token clock = false := by
  unfold check
  split
  · rename_i time h
    have hi := issuedAt_of_authenticate hp h
    rw [issuedAt_eq_error_of_algorithm_ne ha hn] at hi
    cases hi
  · rfl

end EthLib.Engine.Jwt
