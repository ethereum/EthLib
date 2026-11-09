module

/-!
# ERC-2334 key paths

[ERC-2334, Path][path] fixes [purpose][purpose] `12381` and requires at least four child indices.

The parser accepts decimal indices separated by `/`, after the master node `m`.

ERC-2334 reads each index as an integer and sets no rule on its digits.

So the parser accepts leading zeros, and `m/012381/03600/0/0` is the path `m/12381/3600/0/0`.

It rejects spaces, as [the validator key paths][validator] are written.

That is EthLib's choice, since the notation of ERC-2334, Path, puts spaces around `/`.

It rejects the apostrophe of a hardened index, as [Backwards Compatibility][compat] requires.

Indices lie below 2^32, as in [ERC-2333, The Tree Structure][tree].

The links pin ERC-2334 and ERC-2333 at the commit that the Python vectors read.

[path]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#path
[purpose]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#purpose
[validator]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#validator-keys
[compat]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2334.md#backwards-compatibility
[tree]: https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#the-tree-structure
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

/-- Stable error codes for the bindings, one per constructor.

The codes start at 101, since the path errors share their Python class with the BLS errors. -/
def KeyPathError.code : KeyPathError → UInt32
  | .invalidRoot => 101
  | .invalidIndex _ => 102
  | .indexOutOfRange _ => 103
  | .tooShort => 104
  | .invalidPurpose _ => 105

/-- The reason that parsing failed. -/
def KeyPathError.message : KeyPathError → String
  | .invalidRoot => "path must start with m"
  | .invalidIndex segment => s!"invalid path index: {segment}"
  | .indexOutOfRange value => s!"path index out of range: {value}"
  | .tooShort => "ERC-2334 path needs at least four indices"
  | .invalidPurpose value => s!"invalid path purpose: {value.toNat}"

/-- The fixed purpose of ERC-2334, Purpose. -/
def PURPOSE : UInt32 := 12381

/-- The fields after purpose, including any deeper indices, ERC-2334, Path. -/
structure Path where
  coinType : UInt32
  account : UInt32
  use : UInt32
  subpath : List UInt32 := []
deriving DecidableEq, Repr

/-- All child indices: purpose, coin type, account and use, then any deeper indices. -/
def Path.indices (path : Path) : List UInt32 :=
  PURPOSE :: path.coinType :: path.account :: path.use :: path.subpath

/-- Read ASCII decimal digits into an accumulator, rejecting any other byte. -/
def decimalValue : List UInt8 → Nat → Option Nat
  | [], value => some value
  | byte :: rest, value =>
    if 48 ≤ byte && byte ≤ 57 then
      decimalValue rest (10 * value + (byte.toNat - 48))
    else none

/-- Parse one decimal child index without a BIP-32 apostrophe, ERC-2334, Backwards Compatibility. -/
def parseIndex (segment : String) : Except KeyPathError UInt32 := do
  let bytes := segment.toByteArray.data.toList
  if bytes.isEmpty then throw (.invalidIndex segment)
  let some value := decimalValue bytes 0 | throw (.invalidIndex segment)
  if value < 2 ^ 32 then return UInt32.ofNat value
  else throw (.indexOutOfRange value)

/-- Parse a purpose-12381 path of at least four indices, ERC-2334, Path and Purpose. -/
def parsePath (text : String) : Except KeyPathError Path := do
  match text.splitOn "/" with
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

/-- Write a path with decimal indices and no spaces, as ERC-2334, Validator keys, does. -/
def Path.toString (path : Path) : String :=
  "m/" ++ String.intercalate "/" (path.indices.map fun index => ToString.toString index.toNat)

/-- The Ethereum withdrawal path, ERC-2334, Validator keys. -/
def withdrawalPath (index : UInt32) : Path := ⟨3600, index, 0, []⟩

/-- The signing key is child zero of the withdrawal key, ERC-2334, Validator keys. -/
def signingPath (index : UInt32) : Path := ⟨3600, index, 0, [0]⟩

end EthLib.Cryptography.Bls.KeyPath
