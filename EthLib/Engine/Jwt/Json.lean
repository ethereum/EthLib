module

public import EthLib.Base.Json

/-!
# JSON fields of a JWT

The JSON text of a token reads as one object.

Strings and numbers keep their values; the profile reads no other value.
-/

@[expose] public section

namespace EthLib.Engine.Jwt.Json

export EthLib.Base.Json (Number)

/-- The scalar values the JWT profile reads; it needs only the syntax of other JSON values. -/
inductive Value where
  | str (text : String)
  | num (value : Number)
  | other
  deriving Repr

/-- The scalar that a JSON value gives the JWT profile: a string, a number or another value. -/
def scalar : Base.Json.Value → Value
  | .str text => .str text
  | .num value => .num value
  | _ => .other

/-- Read one complete JSON object, with only whitespace after it, RFC 8259 §§2 and 4.

The fields come newest first, so a lookup finds the lexically last of duplicate names.

RFC 7515 §4 and RFC 7519 §4 allow that reading of duplicate names. -/
def fields (text : String) : Option (List (String × Value)) := do
  -- RFC 8259 §2: `JSON-text = ws value ws`, here with an object as the value.
  let .obj members ← Base.Json.read text | none
  return members.reverse.map fun (name, item) => (name, scalar item)

/-- Compare a NumericDate with an integral clock, exactly and without expanding a huge exponent. -/
def within (time : Number) (clock : Nat) : Bool :=
  -- Engine authentication, JWT claims: `iat` within +-60 seconds of the current time.
  --
  -- RFC 7519 §2: a NumericDate counts seconds and may be non-integer.
  --
  -- The test is `lo <= t <= hi` for `t = m * 10^e`, exactly.
  let lo := (clock : Int) - 60
  let hi := (clock : Int) + 60
  if time.exponent ≥ 0 then
    if time.mantissa = 0 then decide (lo ≤ 0 ∧ 0 ≤ hi)
    -- With `m` nonzero and `e` above the digit count of `hi`, `|t| >= 10^e > hi >= |lo|`.
    --
    -- So `t` is outside the interval, and `10^e` is never computed.
    else if time.exponent.toNat > (clock + 60).repr.length then false
    else
      let seconds := time.mantissa * (10 ^ time.exponent.toNat : Nat)
      decide (lo ≤ seconds ∧ seconds ≤ hi)
  else
    -- A magnitude below one has floor/ceiling known without constructing the denominator.
    let n := (-time.exponent).toNat
    let (floor, ceiling) := if n > time.mantissa.natAbs.repr.length then
      if time.mantissa = 0 then (0, 0)
      else if time.mantissa > 0 then (0, 1) else (-1, 0)
    else
      let scale : Int := (10 ^ n : Nat)
      let floor := time.mantissa / scale
      (floor, if time.mantissa % scale = 0 then floor else floor + 1)
    -- For integer bounds, `lo <= t <= hi` exactly when `lo <= floor(t)` and `ceil(t) <= hi`.
    decide (lo ≤ floor ∧ ceiling ≤ hi)

end EthLib.Engine.Jwt.Json
