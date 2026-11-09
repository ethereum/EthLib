module

public import EthLib.Engine.Jwt
public import EthLib.Base.Proofs.Base64
public import Mathlib.Tactic

/-!
# Engine JWT construction and refusal

Every successful builder result authenticates with its secret and issued-at time.

The clock check then accepts at every clock within 60 seconds, including both endpoints.

The builder checks JSON decoding before signing, so these results need no JSON-parser hypothesis.
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

/-- Every successful string build authenticates, with the issued-at time it was given. -/
theorem authenticate_build {secret : ByteArray} {time : Nat} {token : String}
    (hb : build secret time = .ok token) :
    authenticate secret token = .ok ⟨time, 0⟩ := by
  unfold build at hb
  split at hb
  · cases hb
  rename_i hs
  dsimp only at hb
  split at hb
  · rename_i parsed hp
    split at hb
    · rename_i ht
      subst parsed
      cases hb
      simp only [authenticate, hs, ↓reduceIte,
        bind, Except.bind, pure, Except.pure,
        parts_compact _ _ _ (dot_not_mem_encode _) (dot_not_mem_encode _)
          (dot_not_mem_encode _), hp, signature, Base64.decode_encode]
    · cases hb
  · cases hb

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

/-- An algorithm other than HS256 cannot produce an issued-at time for this profile. -/
theorem issuedAt_eq_error_of_algorithm_ne {header claims name : String}
    (ha : algorithm header = .ok name) (hn : name ≠ "HS256") :
    issuedAt header claims = .error .algorithm := by
  simp only [issuedAt, ha, bind, Except.bind, ite_eq_left hn]
  rfl

/-- A compact token whose decoded algorithm differs from HS256 is refused. -/
theorem check_eq_false_of_algorithm_ne {secret : ByteArray} {token : String} {clock : Nat}
    {p : Parts} {name : String} (hp : parts token = some p)
    (ha : algorithm p.header = .ok name) (hn : name ≠ "HS256") :
    check secret token clock = false := by
  by_cases hs : secret.size = 32
  · simp [check, authenticate, hs, hp, issuedAt_eq_error_of_algorithm_ne ha hn,
      bind, Except.bind]
  · rw [check, authenticate, ite_eq_left hs]
    rfl

end EthLib.Engine.Jwt
