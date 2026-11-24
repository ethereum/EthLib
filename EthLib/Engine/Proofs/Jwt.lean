module

public import EthLib.Engine.Jwt
public import EthLib.Base.Proofs.Base64
public import EthLib.Base.Proofs.Json.Number
public import EthLib.Base.Proofs.Json.Text
public import Mathlib.Tactic

/-!
# Engine JWT construction, refusal and acceptance

A token built with a 32-byte secret authenticates.

The clock check accepts it at each clock at most 60 seconds from its issued-at time.

A token authenticates only as the compact form of its parts with their HS256 tag under the secret.
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

open Base.Json (after after_eq_cons after_eq_nil_iff eq_of_after_eq expect_of_after
  expect_eq_none)

/-- A string of characters that need no escape is read through its closing quotation mark. -/
private theorem string_plain {text : String} {p : text.Pos} {s rest : List Char} (fuel : Nat)
    (acc : String) (hs : ∀ c ∈ s, Json.plain c = true) (h : after p = s ++ '"' :: rest) :
    ∃ q, Json.string (fuel + 1) p acc = some (acc ++ String.ofList s, q) ∧ after q = rest := by
  -- The run without an escape is the whole string, and the quotation mark stops it.
  have stop : after (Json.plainEnd p) = '"' :: rest := by
    rw [Json.after_plainEnd, h, List.dropWhile_append_of_pos hs,
      List.dropWhile_cons_of_neg (by simp [Json.plain])]
  have piece : text.extract p (Json.plainEnd p) = String.ofList s := by
    rw [Json.extract_plainEnd, h, List.takeWhile_append_of_pos hs,
      List.takeWhile_cons_of_neg (by simp [Json.plain]), List.append_nil]
  obtain ⟨hq, get, next⟩ := after_eq_cons stop
  refine ⟨_, ?_, next⟩
  rw [Json.string]
  simp only [piece, hq, get, dite_false, ite_true]
  split
  · rename_i empty
    simp [String.isEmpty_iff.1 empty]
  · rfl

/-- The decimal digits of a natural number and a closing brace read as that number. -/
private theorem number_toDigits {text : String} {p : text.Pos} (n : Nat) (tail : List Char)
    (h : after p = Nat.toDigits 10 n ++ '}' :: tail) :
    ∃ q, Json.number p = some (⟨n, 0⟩, q) ∧ after q = '}' :: tail := by
  have brace : ∀ c ∈ ('}' :: tail).head?, Json.digit c = false := by simp [Json.digit]
  obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 n = d :: ds :=
    List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
  have hdig := Json.digit_of_mem_toDigits (c := d) (n := n) (by simp [hd])
  -- No minus sign comes first.
  have minus : Json.expect p '-' = none := by
    refine expect_eq_none ?_
    rw [h, hd]
    rintro ⟨⟩
    revert hdig
    decide
  -- The digits read as the number, and a brace follows them.
  obtain ⟨q, eq, rest⟩ := Json.digits_eq p 0 0
  rw [h, Json.takeWhile_toDigits n _ brace, Json.foldl_digitStep_toDigits] at eq
  rw [h, Json.dropWhile_toDigits n _ brace] at rest
  -- A leading zero comes only in 0 itself, which has one digit.
  have lead : (Json.expect p '0').isSome = true → (Nat.toDigits 10 n).length ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | pos
    · simp [Nat.toDigits_zero]
    · rw [expect_eq_none (by rw [h, hd]; simpa [hd] using Json.head_toDigits_ne_zero n pos)]
      simp
  have length : (Nat.toDigits 10 n).length ≠ 0 := by simp [hd]
  -- No fraction and no exponent follow.
  have dot : Json.expect q '.' = none := expect_eq_none (by simp [rest])
  have small : Json.expect q 'e' = none := expect_eq_none (by simp [rest])
  have large : Json.expect q 'E' = none := expect_eq_none (by simp [rest])
  refine ⟨q, ?_, rest⟩
  simp only [Json.number, minus, eq, dot]
  simp [small, large, length, bind, Option.bind, pure]
  exact lead

/-- Whitespace skipped before a character that is not whitespace leaves the position. -/
private theorem skipWhitespace_eq {text : String} {p : text.Pos} {c : Char} {cs : List Char}
    (h : after p = c :: cs) (hc : Json.whitespace c = false) : Json.skipWhitespace p = p :=
  eq_of_after_eq (by rw [Json.after_skipWhitespace, h, List.dropWhile_cons_of_neg (by simp [hc])])

/-- A string of characters that need no escape reads as a value. -/
private theorem value_string {text : String} {p : text.Pos} (fuel : Nat) (s rest : List Char)
    (hs : ∀ c ∈ s, Json.plain c = true) (h : after p = '"' :: (s ++ '"' :: rest)) :
    ∃ q, Json.value (fuel + 2) p = some (.str (String.ofList s), q) ∧ after q = rest := by
  obtain ⟨hp, get, next⟩ := after_eq_cons h
  obtain ⟨q, str, after_q⟩ := string_plain fuel "" hs next
  refine ⟨q, ?_, after_q⟩
  rw [Json.value, skipWhitespace_eq h (by decide)]
  simp [hp, get, str]

/-- The decimal digits of a natural number and a closing brace read as a value. -/
private theorem value_number {text : String} {p : text.Pos} (fuel n : Nat) (tail : List Char)
    (h : after p = Nat.toDigits 10 n ++ '}' :: tail) :
    ∃ q, Json.value (fuel + 1) p = some (.num ⟨n, 0⟩, q) ∧ after q = '}' :: tail := by
  obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 n = d :: ds :=
    List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
  have hdig := Json.digit_of_mem_toDigits (c := d) (n := n) (by simp [hd])
  simp only [Json.digit, Bool.and_eq_true, decide_eq_true_eq] at hdig
  have h' : after p = d :: (ds ++ '}' :: tail) := by rw [h, hd, List.cons_append]
  obtain ⟨hp, get, -⟩ := after_eq_cons h'
  obtain ⟨q, num, after_q⟩ := number_toDigits n tail h
  refine ⟨q, ?_, after_q⟩
  have white : Json.whitespace d = false := by
    simp only [Json.whitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> rintro rfl <;> revert hdig <;> decide
  rw [Json.value, skipWhitespace_eq h' white]
  have : d ≠ '"' ∧ d ≠ '{' ∧ d ≠ '[' ∧ d ≠ 't' ∧ d ≠ 'f' ∧ d ≠ 'n' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert hdig <;> decide
  simp [hp, get, this, num]

/-- A member of plain name whose value ends the object closes it. -/
private theorem object_close {text : String} {p : text.Pos} (fuel : Nat)
    (key rest tail : List Char) (item : Base.Json.Value) (acc : List (String × Base.Json.Value))
    (empty : Bool) (hk : ∀ c ∈ key, Json.plain c = true)
    (h : after p = '"' :: (key ++ '"' :: ':' :: rest))
    (hv : ∀ r : text.Pos, after r = rest →
      ∃ q, Json.value (fuel + 1) r = some (item, q) ∧ after q = '}' :: tail) :
    ∃ q, Json.object (fuel + 2) p acc empty =
        some (((String.ofList key, item) :: acc).reverse, q) ∧ after q = tail := by
  obtain ⟨hp, get, next⟩ := after_eq_cons h
  obtain ⟨q₁, str, after₁⟩ := string_plain fuel "" hk next
  obtain ⟨q₂, colon, after₂⟩ := expect_of_after after₁
  obtain ⟨q₃, val, after₃⟩ := hv q₂ after₂
  obtain ⟨hq, close, after₄⟩ := after_eq_cons after₃
  refine ⟨_, ?_, after₄⟩
  rw [Json.object]
  simp [hp, get, str, skipWhitespace_eq after₁ (by decide), colon, val,
    skipWhitespace_eq after₃ (by decide), hq, close]

/-- A member of plain name whose value a comma follows continues the object. -/
private theorem object_comma {text : String} {p : text.Pos} (fuel : Nat)
    (key rest tail : List Char) (item : Base.Json.Value) (acc : List (String × Base.Json.Value))
    (empty : Bool) (hk : ∀ c ∈ key, Json.plain c = true)
    (h : after p = '"' :: (key ++ '"' :: ':' :: rest))
    (hv : ∀ r : text.Pos, after r = rest →
      ∃ q, Json.value (fuel + 1) r = some (item, q) ∧ after q = ',' :: tail) :
    ∃ q, after q = tail.dropWhile Json.whitespace ∧ Json.object (fuel + 2) p acc empty =
        Json.object (fuel + 1) q ((String.ofList key, item) :: acc) false := by
  obtain ⟨hp, get, next⟩ := after_eq_cons h
  obtain ⟨q₁, str, after₁⟩ := string_plain fuel "" hk next
  obtain ⟨q₂, colon, after₂⟩ := expect_of_after after₁
  obtain ⟨q₃, val, after₃⟩ := hv q₂ after₂
  obtain ⟨hq, comma, after₄⟩ := after_eq_cons after₃
  refine ⟨_, by rw [Json.after_skipWhitespace, after₄], ?_⟩
  rw [Json.object]
  simp [hp, get, str, skipWhitespace_eq after₁ (by decide), colon, val,
    skipWhitespace_eq after₃ (by decide), hq, comma]

/-- An object whose first member comes right after its opening brace reads as a value. -/
private theorem value_object {text : String} {p : text.Pos} (fuel : Nat) (chars tail : List Char)
    (members : List (String × Base.Json.Value)) (h : after p = '{' :: '"' :: chars)
    (ho : ∀ r : text.Pos, after r = '"' :: chars →
      ∃ q, Json.object fuel r [] true = some (members, q) ∧ after q = tail) :
    ∃ q, Json.value (fuel + 1) p = some (.obj members, q) ∧ after q = tail := by
  obtain ⟨hp, get, next⟩ := after_eq_cons h
  obtain ⟨q, obj, after_q⟩ := ho _ next
  refine ⟨q, ?_, after_q⟩
  rw [Json.value, skipWhitespace_eq h (by decide)]
  simp [hp, get, skipWhitespace_eq next (by decide), obj]

/-- A text whose value runs to its end reads as that value. -/
private theorem read_eq {text : String} {v : Base.Json.Value}
    (h : ∃ q, Json.value (2 * text.length + 1) text.startPos = some (v, q) ∧ after q = []) :
    Json.read text = some v := by
  obtain ⟨q, val, after_q⟩ := h
  obtain rfl := (after_eq_nil_iff).1 after_q
  have rest : Json.skipWhitespace text.endPos = text.endPos :=
    eq_of_after_eq (by simp [Json.after_skipWhitespace, (after_eq_nil_iff).2 rfl])
  simp [Json.read, val, rest, bind, Option.bind]

/-- The builder's header names HS256 and no critical extension. -/
theorem algorithm_headerPart : algorithm headerPart = .ok "HS256" := by
  have text : after "{\"alg\":\"HS256\",\"typ\":\"JWT\"}".startPos = '{' :: '"' ::
      (['a', 'l', 'g'] ++ '"' :: ':' :: ('"' :: (['H', 'S', '2', '5', '6'] ++ '"' :: ',' ::
        ('"' :: (['t', 'y', 'p'] ++ '"' :: ':' :: ('"' :: (['J', 'W', 'T'] ++
          '"' :: ['}']))))))) := by
    rw [Json.after_startPos]
    simp
  have read : Json.read "{\"alg\":\"HS256\",\"typ\":\"JWT\"}" = some (.obj
      [(String.ofList ['a', 'l', 'g'], .str (String.ofList ['H', 'S', '2', '5', '6'])),
        (String.ofList ['t', 'y', 'p'], .str (String.ofList ['J', 'W', 'T']))]) := by
    have length : 2 * "{\"alg\":\"HS256\",\"typ\":\"JWT\"}".length + 1 = 54 + 1 := by
      rw [← String.length_toList]
      simp
    refine read_eq ?_
    rw [length]
    refine value_object 54 _ [] _ text fun r hr => ?_
    -- The first member, then a comma, then the last member and the closing brace.
    have first := object_comma 52 ['a', 'l', 'g']
      ('"' :: (['H', 'S', '2', '5', '6'] ++ '"' :: ',' :: '"' :: (['t', 'y', 'p'] ++ '"' :: ':' ::
        '"' :: (['J', 'W', 'T'] ++ ['"', '}']))))
      ('"' :: (['t', 'y', 'p'] ++ '"' :: ':' :: '"' :: (['J', 'W', 'T'] ++ ['"', '}'])))
      (.str (String.ofList ['H', 'S', '2', '5', '6'])) [] true (by simp [Json.plain]) hr
      fun r hr => value_string 51 ['H', 'S', '2', '5', '6'] _ (by simp [Json.plain]) hr
    obtain ⟨q, after_q, step⟩ := first
    rw [List.dropWhile_cons_of_neg (by decide)] at after_q
    obtain ⟨q', close, after_q'⟩ := object_close (p := q) 51 ['t', 'y', 'p']
      ('"' :: (['J', 'W', 'T'] ++ ['"', '}'])) [] (.str (String.ofList ['J', 'W', 'T']))
      [(String.ofList ['a', 'l', 'g'], .str (String.ofList ['H', 'S', '2', '5', '6']))] false
      (by simp [Json.plain]) after_q
      fun r hr => value_string 50 ['J', 'W', 'T'] _ (by simp [Json.plain]) hr
    exact ⟨q', by rw [step, close]; rfl, after_q'⟩
  rw [algorithm, headerPart, objectFields_encode]
  simp only [Json.fields, read]
  simp [List.lookup, Json.scalar]
  rfl

/-- The builder's claims read back as its integral issued-at time. -/
theorem issuedAt_claimsPart (time : Nat) :
    issuedAt headerPart (claimsPart time) = .ok ⟨time, 0⟩ := by
  have text : after ("{\"iat\":" ++ time.repr ++ "}").startPos = '{' :: '"' ::
      (['i', 'a', 't'] ++ '"' :: ':' :: (Nat.toDigits 10 time ++ ['}'])) := by
    rw [Json.after_startPos, String.toList_append, String.toList_append, Nat.toList_repr]
    rfl
  have length : 2 * ("{\"iat\":" ++ time.repr ++ "}").length + 1 =
      (2 * (Nat.toDigits 10 time).length + 12) + 5 := by
    rw [← String.length_toList, String.toList_append, String.toList_append, Nat.toList_repr]
    simp only [List.length_append]
    simp
    omega
  have read : Json.read ("{\"iat\":" ++ time.repr ++ "}") =
      some (.obj [("iat", .num ⟨time, 0⟩)]) := by
    refine read_eq ?_
    rw [length]
    refine value_object _ _ [] _ text fun r hr => ?_
    obtain ⟨q, close, after_q⟩ := object_close _ ['i', 'a', 't'] _ [] _ [] true
      (by simp [Json.plain]) hr fun r hr => value_number _ time [] hr
    exact ⟨q, close, after_q⟩
  rw [issuedAt, algorithm_headerPart]
  simp only [claimsPart, objectFields_encode, Json.fields, read]
  simp [List.lookup, Json.scalar, bind, Except.bind]
  rfl

/-- A 32-byte secret always builds the signed compact form of the builder's two parts. -/
theorem build_eq_ok {secret : ByteArray} (hs : secret.size = 32) (time : Nat) :
    build secret time = .ok (compact headerPart (claimsPart time)
      (signature secret headerPart (claimsPart time))) := by
  simp [build, hs, issuedAt_claimsPart]
  rfl

/-- With a 32-byte secret, the compact form signed with it passes the tag check.

This holds for parts with no separator.

Authentication then gives what reading those parts gives: an issued-at time, or its error. -/
theorem authenticate_compact {secret : ByteArray} (hs : secret.size = 32)
    {header claims : String} (hh : '.' ∉ header.toList) (hc : '.' ∉ claims.toList) :
    authenticate secret (compact header claims (signature secret header claims)) =
      issuedAt header claims := by
  rw [authenticate, ite_eq_right (by simp [hs]), signature,
    parts_compact header claims _ hh hc (dot_not_mem_encode _)]
  simp [Base64.decode_encode]

/-- Every successful string build authenticates, with the issued-at time it was given. -/
theorem authenticate_build {secret : ByteArray} {time : Nat} {token : String}
    (hb : build secret time = .ok token) :
    authenticate secret token = .ok ⟨time, 0⟩ := by
  have hs : secret.size = 32 := by
    by_contra hs
    simp [build, hs] at hb
  rw [build_eq_ok hs] at hb
  cases hb
  rw [authenticate_compact (header := headerPart) (claims := claimsPart time) hs
    (dot_not_mem_encode _) (dot_not_mem_encode _), issuedAt_claimsPart]

/-! ## The NumericDate comparison

The clock check compares a JSON number with the clock exactly, whatever its exponent.

Two theorems give it in full, one for each sign of that exponent.

For a negative exponent, the statement scales the bounds instead of dividing the date.

So the theorems prove the two shortcuts of the check correct for every input.

A test can run those shortcuts, but on a huge exponent it cannot compute the value they replace.
-/

/-- Past the digits of a bound, a power of ten overshoots it. -/
private theorem lt_ten_pow_of_length_lt {n k : Nat} (h : n.repr.length < k) : n < 10 ^ k :=
  (Nat.length_repr_le_iff (by omega)).mp (Nat.le_of_lt h)

/-- A date with a nonnegative exponent passes exactly when it is within 60 seconds of the clock.

Its value is the mantissa times that power of ten. -/
theorem within_eq_true_iff_of_nonneg {time : Json.Number} (he : 0 ≤ time.exponent)
    (clock : Nat) :
    Json.within time clock = true ↔
      (clock : Int) - 60 ≤ time.mantissa * (10 ^ time.exponent.toNat : Nat) ∧
        time.mantissa * (10 ^ time.exponent.toNat : Nat) ≤ (clock : Int) + 60 := by
  unfold Json.within
  dsimp only
  rw [ite_eq_left he]
  split
  · rename_i hm
    rw [hm]
    simp
  · split
    · rename_i hm hbig
      -- The power of ten overshoots the bound, so no multiple of it lands inside.
      have hpow : clock + 60 < 10 ^ time.exponent.toNat := lt_ten_pow_of_length_lt hbig
      have hcast : ((clock + 60 : Nat) : Int) < ((10 ^ time.exponent.toNat : Nat) : Int) := by
        exact_mod_cast hpow
      have hone : (1 : Int) ≤ time.mantissa ∨ time.mantissa ≤ -1 := by omega
      refine iff_of_false (by simp) ?_
      rintro ⟨hlo, hhi⟩
      have hP : (0 : Int) ≤ ((10 ^ time.exponent.toNat : Nat) : Int) := by positivity
      rcases hone with h1 | h1
      · have : ((10 ^ time.exponent.toNat : Nat) : Int)
            ≤ time.mantissa * ((10 ^ time.exponent.toNat : Nat) : Int) := by
          have := Int.mul_le_mul_of_nonneg_right h1 hP
          rwa [Int.one_mul] at this
        push_cast at hcast hhi this
        omega
      · have : time.mantissa * ((10 ^ time.exponent.toNat : Nat) : Int)
            ≤ -((10 ^ time.exponent.toNat : Nat) : Int) := by
          have := Int.mul_le_mul_of_nonneg_right h1 hP
          rwa [Int.neg_one_mul] at this
        push_cast at hcast hlo this
        omega
    · simp

/-- A date with a negative exponent passes exactly when the scaled bounds enclose its mantissa.

That is the exact comparison of its value with the clock, with no division. -/
theorem within_eq_true_iff_of_neg {time : Json.Number} (he : time.exponent < 0) (clock : Nat) :
    Json.within time clock = true ↔
      ((clock : Int) - 60) * ((10 ^ (-time.exponent).toNat : Nat) : Int) ≤ time.mantissa ∧
        time.mantissa ≤ ((clock : Int) + 60) * ((10 ^ (-time.exponent).toNat : Nat) : Int) := by
  unfold Json.within
  dsimp only
  rw [ite_eq_right (by omega : ¬ time.exponent ≥ 0)]
  have hS : (0 : Int) < ((10 ^ (-time.exponent).toNat : Nat) : Int) := by positivity
  split
  · -- The magnitude is below one scale, so the floor and the ceiling are known outright.
    rename_i hsmall
    have hm : time.mantissa.natAbs < 10 ^ (-time.exponent).toNat :=
      lt_ten_pow_of_length_lt hsmall
    have hmS : |time.mantissa| < ((10 ^ (-time.exponent).toNat : Nat) : Int) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hm
    rw [abs_lt] at hmS
    split
    · rename_i hz
      rw [hz]
      simp only [decide_eq_true_eq]
      constructor
      · intro h
        exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
      · intro h
        exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
    · split
      · rename_i hz hpos
        simp only [decide_eq_true_eq]
        constructor
        · intro h
          exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
        · intro h
          exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
      · rename_i hz hneg
        simp only [decide_eq_true_eq]
        have hlt : time.mantissa < 0 := by omega
        constructor
        · intro h
          exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
        · intro h
          exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
  · -- The scale divides out, so the floor is the quotient and the ceiling follows the remainder.
    simp only [decide_eq_true_eq]
    rw [Int.le_ediv_iff_mul_le hS]
    split
    · rename_i hdvd
      have : time.mantissa / ((10 ^ (-time.exponent).toNat : Nat) : Int)
          * ((10 ^ (-time.exponent).toNat : Nat) : Int) = time.mantissa :=
        Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hdvd)
      constructor
      · intro h
        refine ⟨h.1, ?_⟩
        have := (Int.mul_le_mul_iff_of_pos_right hS).mpr h.2
        omega
      · intro h
        refine ⟨h.1, ?_⟩
        exact (Int.mul_le_mul_iff_of_pos_right hS).mp (by omega)
    · rename_i hdvd
      have hne : time.mantissa ≠ ((clock : Int) + 60)
          * ((10 ^ (-time.exponent).toNat : Nat) : Int) := by
        intro heq
        rw [heq] at hdvd
        exact hdvd (Int.mul_emod_left _ _)
      constructor
      · intro h
        refine ⟨h.1, ?_⟩
        have : time.mantissa / ((10 ^ (-time.exponent).toNat : Nat) : Int) < (clock : Int) + 60 :=
          by omega
        have := (Int.ediv_lt_iff_lt_mul hS).mp this
        omega
      · intro h
        refine ⟨h.1, ?_⟩
        have hlt : time.mantissa < ((clock : Int) + 60)
            * ((10 ^ (-time.exponent).toNat : Nat) : Int) := by omega
        have := (Int.ediv_lt_iff_lt_mul hS).mpr hlt
        omega

/-- Integral NumericDates pass exactly within 60 seconds of the integral clock. -/
theorem within_nat_iff (time clock : Nat) :
    Json.within ⟨time, 0⟩ clock = true ↔ clock ≤ time + 60 ∧ time ≤ clock + 60 := by
  rw [within_eq_true_iff_of_nonneg (time := ⟨time, 0⟩) (Int.le_refl 0)]
  simp only [Int.toNat_zero, pow_zero, Int.ofNat_one, mul_one]
  omega

/-- A successfully built token passes with the same secret at every clock within 60 seconds. -/
theorem check_build {secret : ByteArray} {time clock : Nat} {token : String}
    (hb : build secret time = .ok token)
    (hclock : clock ≤ time + 60 ∧ time ≤ clock + 60) : check secret token clock = true := by
  rw [check, authenticate_build hb]
  exact (within_nat_iff time clock).2 hclock

/-- A token built with a 32-byte secret passes with it at every clock within 60 seconds.

Both endpoints of that window are included. -/
theorem check_build_of_size {secret : ByteArray} {time clock : Nat} (hs : secret.size = 32)
    (hclock : clock ≤ time + 60 ∧ time ≤ clock + 60) :
    check secret (compact headerPart (claimsPart time)
      (signature secret headerPart (claimsPart time))) clock = true :=
  check_build (build_eq_ok hs time) hclock

/-- An algorithm other than HS256 cannot produce an issued-at time for this profile. -/
theorem issuedAt_eq_error_of_algorithm_ne {header claims name : String}
    (ha : algorithm header = .ok name) (hn : name ≠ "HS256") :
    issuedAt header claims = .error (.algorithm (some name)) := by
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

/-! ## What an accepted token proves -/

/-- Rejoining the three parts that a compact token splits into gives that token back. -/
theorem compact_parts {token : String} {p : Parts} (hp : parts token = some p) :
    compact p.header p.claims p.signature = token := by
  unfold parts at hp
  split at hp
  · rename_i header claims signature hsplit
    cases hp
    have hj := List.intercalate_splitOn (xs := token.toList) (x := '.')
    rw [hsplit] at hj
    apply String.ext
    simp only [compact, String.toList_append, String.toList_ofList,
      show ".".toList = ['.'] by rfl]
    simpa [List.intercalate] using hj
  · cases hp

/-- A secret of any length other than 32 bytes authenticates no token. -/
theorem size_eq_of_authenticate {secret : ByteArray} {token : String} {time : Json.Number}
    (h : authenticate secret token = .ok time) : secret.size = 32 := by
  by_contra hs
  simp only [authenticate] at h
  split at h <;> cases h

/-- An authenticated token splits at exactly two period separators. -/
theorem exists_parts_of_authenticate {secret : ByteArray} {token : String} {time : Json.Number}
    (h : authenticate secret token = .ok time) : ∃ p, parts token = some p := by
  rcases hp : parts token with _ | p
  · simp only [authenticate, hp] at h
    split at h <;> cases h
  · exact ⟨p, rfl⟩

/-- An authenticated token's tag part decodes to the HS256 tag of its parts under the secret. -/
theorem tag_of_authenticate {secret : ByteArray} {token : String} {time : Json.Number}
    {p : Parts} (hp : parts token = some p) (h : authenticate secret token = .ok time) :
    Base64.decode p.signature =
      .ok (Cryptography.Hash.Hmac.hmac secret (signingInput p.header p.claims)) := by
  by_contra ht
  rw [authenticate_eq_error_of_tag_ne (size_eq_of_authenticate h) hp ht] at h
  cases h

/-- The tag part of an authenticated token is the base64url tag of its own header and claims.

The encoder writes back every text that the decoder accepts, so the tag part is the encoded tag. -/
theorem signature_eq_of_authenticate {secret : ByteArray} {token : String} {time : Json.Number}
    {p : Parts} (hp : parts token = some p) (h : authenticate secret token = .ok time) :
    p.signature = signature secret p.header p.claims := by
  rw [signature]
  exact (Base64.encode_decode _ _ (tag_of_authenticate hp h)).symm

/-- An authenticated token is the compact form that signing its own parts with the secret gives.

So for given parts, no other tag part authenticates under that secret.

That only a holder of the secret can compute that tag is HMAC unforgeability, not proved here. -/
theorem compact_signature_of_authenticate {secret : ByteArray} {token : String}
    {time : Json.Number} {p : Parts} (hp : parts token = some p)
    (h : authenticate secret token = .ok time) :
    token = compact p.header p.claims (signature secret p.header p.claims) := by
  rw [← signature_eq_of_authenticate hp h, compact_parts hp]

/-- The header of an authenticated token names HS256. -/
theorem algorithm_eq_of_authenticate {secret : ByteArray} {token : String} {time : Json.Number}
    {p : Parts} (hp : parts token = some p) (h : authenticate secret token = .ok time) :
    algorithm p.header = .ok "HS256" := by
  have hi := issuedAt_of_authenticate hp h
  rcases ha : algorithm p.header with e | name
  · simp [issuedAt, ha, bind, Except.bind] at hi
  · by_cases hn : name = "HS256"
    · rw [hn]
    · rw [issuedAt_eq_error_of_algorithm_ne ha hn] at hi
      cases hi

/-- The header of an authenticated token has no critical-extension field. -/
theorem crit_eq_none_of_authenticate {secret : ByteArray} {token : String} {time : Json.Number}
    {p : Parts} {fields : List (String × Json.Value)} (hp : parts token = some p)
    (h : authenticate secret token = .ok time) (hf : objectFields p.header = some fields) :
    fields.lookup "crit" = none := by
  have ha := algorithm_eq_of_authenticate hp h
  unfold algorithm at ha
  simp only [hf] at ha
  split at ha
  · cases ha
  · rename_i hc
    cases hl : fields.lookup "crit" with
    | none => rfl
    | some value => rw [hl] at hc; simp at hc

/-- A token that the clock check accepts authenticates.

Its issued-at time is within 60 seconds of the clock. -/
theorem exists_authenticate_of_check {secret : ByteArray} {token : String} {clock : Nat}
    (h : check secret token clock = true) :
    ∃ time, authenticate secret token = .ok time ∧ Json.within time clock = true := by
  unfold check at h
  split at h
  · rename_i time ht
    exact ⟨time, ht, h⟩
  · cases h

/-- The clock check accepts only the compact form of the token's parts signed with the secret. -/
theorem compact_signature_of_check {secret : ByteArray} {token : String} {clock : Nat}
    {p : Parts} (hp : parts token = some p) (h : check secret token clock = true) :
    token = compact p.header p.claims (signature secret p.header p.claims) := by
  obtain ⟨time, ha, -⟩ := exists_authenticate_of_check h
  exact compact_signature_of_authenticate hp ha

end EthLib.Engine.Jwt
