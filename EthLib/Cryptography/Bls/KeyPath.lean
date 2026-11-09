module

/-!
# ERC-2334 key paths

[ERC-2334, Path][erc2334] fixes purpose `12381` and requires at least four child indices.

The parser accepts decimal indices separated by `/`, after the master node `m`.

[erc2334]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#path
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.KeyPath

/-- Invalid path text or an index outside the range of ERC-2333, The Tree Structure. -/
inductive KeyPathError where
  | invalidRoot
  | invalidIndex (segment : String)
  | indexOutOfRange (value : Nat)
  | tooShort
  | invalidPurpose (value : UInt32)
deriving DecidableEq, Repr

/-- Stable error codes for the bindings, one per constructor. -/
def KeyPathError.code : KeyPathError → UInt32
  | .invalidRoot => 1
  | .invalidIndex _ => 2
  | .indexOutOfRange _ => 3
  | .tooShort => 4
  | .invalidPurpose _ => 5

/-- The reason that parsing failed. -/
def KeyPathError.message : KeyPathError → String
  | .invalidRoot => "path must start with m"
  | .invalidIndex segment => s!"invalid path index: {segment}"
  | .indexOutOfRange value => s!"path index out of range: {value}"
  | .tooShort => "ERC-2334 path needs at least four indices"
  | .invalidPurpose value => s!"invalid path purpose: {value.toNat}"

/-- The fixed purpose of [ERC-2334, Purpose][purpose].

[purpose]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#purpose
-/
def PURPOSE : UInt32 := 12381

/-- The fields after purpose, including any deeper indices, [ERC-2334, Path][path].

[path]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#path
-/
structure Path where
  coinType : UInt32
  account : UInt32
  use : UInt32
  subpath : List UInt32 := []
deriving DecidableEq, Repr

/-- All child indices, including purpose, coin type, account, use and any deeper indices. -/
def Path.indices (path : Path) : List UInt32 :=
  PURPOSE :: path.coinType :: path.account :: path.use :: path.subpath

/-- Read ASCII decimal digits into an accumulator, rejecting any other byte. -/
def decimalValue : List UInt8 → Nat → Option Nat
  | [], value => some value
  | byte :: rest, value =>
    if 48 ≤ byte && byte ≤ 57 then
      decimalValue rest (10 * value + (byte.toNat - 48))
    else none

/-- Parse a decimal child index, rejecting apostrophes, [ERC-2334, Backwards Compatibility][compat].

[compat]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#backwards-compatibility
-/
def parseIndex (segment : String) : Except KeyPathError UInt32 := do
  let bytes := segment.toByteArray.data.toList
  if bytes.isEmpty then throw (.invalidIndex segment)
  let some value := decimalValue bytes 0 | throw (.invalidIndex segment)
  if value < 2 ^ 32 then return UInt32.ofNat value
  else throw (.indexOutOfRange value)

/-- Parse a [purpose-12381][purpose] path of at least four indices, [ERC-2334, Path][path].

Leading zeros are accepted and spaces are rejected.

[purpose]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#purpose
[path]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#path
-/
def parsePath (text : String) : Except KeyPathError Path := do
  match (text.split '/').toList.map String.Slice.copy with
  | root :: parts =>
    if root != "m" then throw .invalidRoot
    match parts with
    | purpose :: coinType :: account :: use :: subpath =>
      let purpose ← parseIndex purpose
      if purpose != PURPOSE then throw (.invalidPurpose purpose)
      return ⟨← parseIndex coinType, ← parseIndex account, ← parseIndex use,
        ← subpath.mapM parseIndex⟩
    | _ => throw .tooShort
  | [] => throw .invalidRoot

/-- Write a path with decimal indices and no spaces, [ERC-2334, Validator keys][keys].

[keys]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#validator-keys
-/
def Path.toString (path : Path) : String :=
  "m/" ++ String.intercalate "/" (path.indices.map fun index => ToString.toString index.toNat)

/-- The Ethereum withdrawal path, [ERC-2334, Validator keys][keys].

[keys]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#validator-keys
-/
def withdrawalPath (index : UInt32) : Path := ⟨3600, index, 0, []⟩

/-- The signing key is child zero of the withdrawal key, [ERC-2334, Validator keys][keys].

[keys]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#validator-keys
-/
def signingPath (index : UInt32) : Path := ⟨3600, index, 0, [0]⟩

end EthLib.Cryptography.Bls.KeyPath
