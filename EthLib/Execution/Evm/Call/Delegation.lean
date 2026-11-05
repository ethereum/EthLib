module

public import EthLib.Base.Address

/-!
# `Evm.Call.Delegation`

The delegation indicator of an account, from Pectra.

A set code transaction writes the indicator as the code of each account that authorizes it.

The indicator is the three bytes `0xef0100`, then the 20 bytes of the address it delegates to.

Its first byte is `0xef`, and from London no creation may deploy code that starts with `0xef`.

[EIP-3541](https://eips.ethereum.org/EIPS/eip-3541#specification) sets that rule.

So the code of a contract deployed from London is never an indicator.

[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702#delegation-indicator) defines it.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base

/-- The three bytes that start a delegation indicator. -/
def DELEGATION_MARKER : ByteArray := ⟨#[0xef, 0x01, 0x00]⟩

/-- The size of a delegation indicator: the marker and an address. -/
def DELEGATION_SIZE : Nat := 23

/-- The delegation indicator of an address: the marker, then the address. -/
def delegationIndicator (address : Address) : ByteArray :=
  DELEGATION_MARKER ++ ⟨address.toArray⟩

/-- Whether some code is a delegation indicator: the marker, then exactly one address. -/
def isValidDelegation (code : ByteArray) : Bool :=
  code.size = DELEGATION_SIZE && code.extract 0 3 = DELEGATION_MARKER

/-- The address that a delegation indicator delegates to, or none for any other code. -/
def delegatedAddress (code : ByteArray) : Option Address :=
  if h : isValidDelegation code then
    -- An indicator has 23 bytes, so the 20 bytes after the marker are in bounds.
    some (Vector.ofFn fun i : Fin 20 => code[3 + i.val]'(by
      simp only [isValidDelegation, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, DELEGATION_SIZE]
      omega))
  else none

end EthLib.Execution.Evm
