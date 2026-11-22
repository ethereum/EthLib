module

public import EthLib.Execution.Evm.Delegation
public import EthLib.Execution.Transactions.Settlement

/-!
# `Transactions.Inclusion`

The rules that a transaction must pass to enter a block, against the block and the state.

The rules alone need no state, and these rules add what the block and the state decide.

A sender given by a simulation, with no signature, may have code.

The checks run in the order that decides which error a transaction gets.

Section 6.2 of the Yellow Paper, Shanghai version, states the rules on gas, nonce and balance.

Source: [`Paper.tex` at `efc5f9a`][yp].

The step comments write the Yellow Paper's relations in ASCII.

Only `ethereum/execution-specs` spells out the order of the checks, and the step comments quote it.

They quote `process_transaction` and `check_transaction` in the `fork.py` of each fork.

Those are [Osaka's][es-osaka] and [Amsterdam's][es-amsterdam].

They quote `check_block_gas_capacity` and `check_max_fee_per_blob_gas` in [`vm/gas.py`][es-gas].

They quote `calculate_effective_gas_price` and `check_nonce` in [`transactions.py`][es-tx].

The EIPs that add a rule:

- [EIP-1559][eip1559], the base fee
- [EIP-3607][eip3607], the sender without code, at every fork
- [EIP-4844][eip4844], the blob gas and its fee
- [EIP-7702][eip7702], the sender with a delegation indicator
- [EIP-8037][eip8037], the execution gas and the state gas that the block has left

These rules hold up to Glamsterdam, which changes the rule on the gas of the block and the order.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[es-osaka]: https://github.com/ethereum/execution-specs/blob/391d8a05d5cb182542ac7e7330c858b6ee03f990/src/ethereum/forks/osaka/fork.py
[es-amsterdam]: https://github.com/ethereum/execution-specs/blob/391d8a05d5cb182542ac7e7330c858b6ee03f990/src/ethereum/forks/amsterdam/fork.py
[es-gas]: https://github.com/ethereum/execution-specs/blob/391d8a05d5cb182542ac7e7330c858b6ee03f990/src/ethereum/forks/amsterdam/vm/gas.py
[es-tx]: https://github.com/ethereum/execution-specs/blob/391d8a05d5cb182542ac7e7330c858b6ee03f990/src/ethereum/forks/amsterdam/transactions.py
[eip1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
[eip3607]: https://eips.ethereum.org/EIPS/eip-3607#specification
[eip4844]: https://eips.ethereum.org/EIPS/eip-4844#execution-layer-validation
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#transaction-origination
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-validation
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm (BlockEnvironment isValidDelegation)
open EthLib.Execution.Evm.GasCosts (TX_MAX_GAS_LIMIT)
open EthLib.Execution.State (EMPTY_CODE_HASH TransactionState)
open EthLib.Execution.Fees.BlobBaseFee

/-! ## The fees that a transaction offers -/

namespace Transaction

/-- The most wei per blob gas that a transaction pays, or 0 for a transaction without blobs. -/
def maxFeePerBlobGas : Transaction → Nat
  | .blob tx => tx.maxFeePerBlobGas.toNat
  | _ => 0

/-- The most that the gas and the blobs of a transaction can cost, at its maximum fees. -/
def maxGasFee (tx : Transaction) : Nat :=
  -- Osaka: `max_gas_fee = tx.gas * tx.max_fee_per_gas`, or `tx.gas * tx.gas_price`.
  --
  -- Then `max_gas_fee += Uint(calculate_total_blob_gas(tx)) * Uint(tx.max_fee_per_blob_gas)`.
  --
  -- That second term is 0 for a transaction without blobs.
  tx.gas.toNat * tx.maxFeePerGas + calculateTotalBlobGas tx * tx.maxFeePerBlobGas

end Transaction

/-- The most blob gas of a block at `fork`: the most blobs times the blob gas of one blob.

The most blobs come from the blob schedule of the block.

A block before Dencun has no blobs. -/
def maxBlobGasPerBlock {fork : Fork} (env : BlockEnvironment fork) : Nat :=
  -- `MAX_BLOB_GAS_PER_BLOCK = GasCosts.BLOB_SCHEDULE_MAX * GasCosts.PER_BLOB`.
  --
  -- The `max` of EIP-7840's `blobSchedule` gives that most, from Dencun.
  if h : .dencun ≤ fork then GAS_PER_BLOB * (env.blobSchedule h).max.toNat else 0

/-- The gas of a transaction that must fit in the execution gas that its block has left, at `fork`.

It is the gas limit, capped from Glamsterdam at `2^24`, the most execution gas of a transaction.

A simulation can lift that cap. -/
def executionCapacity (fork : Fork) (tx : Transaction) (lifted : LiftedRules := {}) : Nat :=
  -- Amsterdam: `min(GasCosts.TX_MAX_GAS_LIMIT, tx_gas)`; before, `tx.gas` itself.
  --
  -- A simulation may lift the cap; the source has no such mode.
  if fork ≥ .glamsterdam then
    if lifted.gasCap then tx.gas.toNat else min TX_MAX_GAS_LIMIT tx.gas.toNat
  else tx.gas.toNat

/-! ## The rules -/

/-- Why a transaction cannot enter its block. -/
inductive InclusionError where
  /-- The transaction fails a rule that needs no state. -/
  | transaction (error : TransactionError)
  /-- The gas `gas` of the transaction is above the gas `available` that the block has left.

  From Glamsterdam it is either the execution gas or the state gas. -/
  | gasAllowanceExceeded (gas available : Nat)
  /-- The blob gas `blobGas` is above the blob gas `available` that the block has left. -/
  | blobGasLimitExceeded (blobGas available : Nat)
  /-- The most wei per gas `maxFee` is below the base fee `baseFee` of the block. -/
  | insufficientMaxFeePerGas (maxFee baseFee : Nat)
  /-- The most wei per blob gas `maxFee` is below the base fee per blob gas `blobGasPrice`. -/
  | insufficientMaxFeePerBlobGas (maxFee blobGasPrice : Nat)
  /-- The nonce `nonce` is below the nonce `expected` of the sender. -/
  | nonceTooLow (expected nonce : Nat)
  /-- The nonce `nonce` is above the nonce `expected` of the sender. -/
  | nonceTooHigh (expected nonce : Nat)
  /-- The balance `balance` of the sender is below the most `cost` that the transaction costs. -/
  | insufficientBalance (balance cost : Nat)
  /-- The sender `sender` has code, and that code is not a delegation indicator the fork allows. -/
  | senderNotEoa (sender : Address)
  /-- The state does not hold the code of the sender, whose hash is `codeHash`. -/
  | missingCode (codeHash : Hash32)
  deriving DecidableEq

/-- An inclusion error constructor, named in full, applied to its arguments. -/
def inclusionErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Transactions.InclusionError." ++ name) args prec

/-- The form of an inclusion error in Lean syntax, with its arguments.

Each value has its name, and each hash and address is in hex. -/
def InclusionError.reprPrec : InclusionError → Nat → Std.Format
  | .transaction error, p => inclusionErrorFormat "transaction" [reprArg error] p
  | .gasAllowanceExceeded gas available, p =>
    inclusionErrorFormat "gasAllowanceExceeded"
      [namedArg "gas" gas, namedArg "available" available] p
  | .blobGasLimitExceeded blobGas available, p =>
    inclusionErrorFormat "blobGasLimitExceeded"
      [namedArg "blobGas" blobGas, namedArg "available" available] p
  | .insufficientMaxFeePerGas maxFee baseFee, p =>
    inclusionErrorFormat "insufficientMaxFeePerGas"
      [namedArg "maxFee" maxFee, namedArg "baseFee" baseFee] p
  | .insufficientMaxFeePerBlobGas maxFee blobGasPrice, p =>
    inclusionErrorFormat "insufficientMaxFeePerBlobGas"
      [namedArg "maxFee" maxFee, namedArg "blobGasPrice" blobGasPrice] p
  | .nonceTooLow expected nonce, p =>
    inclusionErrorFormat "nonceTooLow" [namedArg "expected" expected, namedArg "nonce" nonce] p
  | .nonceTooHigh expected nonce, p =>
    inclusionErrorFormat "nonceTooHigh" [namedArg "expected" expected, namedArg "nonce" nonce] p
  | .insufficientBalance balance cost, p =>
    inclusionErrorFormat "insufficientBalance"
      [namedArg "balance" balance, namedArg "cost" cost] p
  | .senderNotEoa sender, p => inclusionErrorFormat "senderNotEoa" [namedArg "sender" sender] p
  | .missingCode codeHash, p =>
    inclusionErrorFormat "missingCode" [namedArg "codeHash" codeHash] p

instance : Repr InclusionError := ⟨InclusionError.reprPrec⟩

/-- The stable code of an error, one per constructor, for the C exports.

A rule that needs no state keeps the code of its error.

The other codes start at 201, above every code of a transaction error and of its network form.

A new constructor takes a new code, so that each code keeps its meaning. -/
def InclusionError.code : InclusionError → UInt32
  | .transaction error => error.code
  | .gasAllowanceExceeded .. => 201
  | .blobGasLimitExceeded .. => 202
  | .insufficientMaxFeePerGas .. => 203
  | .insufficientMaxFeePerBlobGas .. => 204
  | .nonceTooLow .. => 205
  | .nonceTooHigh .. => 206
  | .insufficientBalance .. => 207
  | .senderNotEoa _ => 208
  | .missingCode _ => 209

/-- What a transaction that may enter its block brings to its run. -/
structure Included where
  /-- The sender, from the signature or given by a simulation. -/
  sender : Address
  /-- The intrinsic gas of the transaction. -/
  intrinsicGas : Nat
  /-- The price per gas that the sender pays. -/
  gasPrice : Nat
  /-- The blob gas of the transaction. -/
  blobGasUsed : Nat
  deriving DecidableEq, Repr

/-- Fail with `error` when `condition` holds. -/
def failIf (condition : Bool) (error : InclusionError) : Except InclusionError Unit :=
  if condition then .error error else .ok ()

/-- Check that a transaction fits in what its block has left, after the gas `used` before it.

- The gas limit, capped from Glamsterdam unless lifted, fits in the execution gas left.
- From Glamsterdam, the gas limit fits in the state gas left.
- The blob gas fits in the blob gas left. -/
def checkBlockGas {fork : Fork} (env : BlockEnvironment fork) (used : BlockGas)
    (tx : Transaction) (lifted : LiftedRules := {}) : Except InclusionError Unit := do
  -- `execution_gas_available = block_env.block_gas_limit - block_output.block_gas_used`.
  let available := env.gasLimit - used.execution
  let gas := executionCapacity fork tx lifted
  -- `if min(GasCosts.TX_MAX_GAS_LIMIT, tx_gas) > execution_gas_available`.
  --
  -- Before Glamsterdam, `if tx.gas > gas_available`.
  --
  -- That is the Yellow Paper's `T_g <= B_H_l - l(B_R)_u`.
  failIf (available < gas) (.gasAllowanceExceeded gas available)
  -- `state_gas_available = block_env.block_gas_limit - block_output.block_state_gas_used`.
  let stateAvailable := env.gasLimit - used.state
  -- `if tx_gas > state_gas_available`, from Glamsterdam.
  failIf (fork ≥ .glamsterdam ∧ stateAvailable < tx.gas.toNat)
    (.gasAllowanceExceeded tx.gas.toNat stateAvailable)
  let blobGas := calculateTotalBlobGas tx
  -- `blob_gas_available = MAX_BLOB_GAS_PER_BLOCK - block_output.blob_gas_used`.
  let blobAvailable := maxBlobGasPerBlock env - used.blob
  -- `if tx_blob_gas > blob_gas_available`.
  failIf (blobAvailable < blobGas) (.blobGasLimitExceeded blobGas blobAvailable)

/-- Check that `sender` may send a transaction at `fork`, in the state `state`.

- The nonce is the nonce of the sender.
- The sender holds the most that the transaction can cost, with the value it sends.
- The sender has no code, and from Pectra it may have a delegation indicator.

A sender that no signature names, as in a simulation, may have code, which is then not read.

A simulation can also skip the check of the nonce.

The nonce of the sender must then still be below `2^64 - 1`, as EIP-2681 asks.
-/
def checkSender (fork : Fork) (state : TransactionState) (sender : Address) (tx : Transaction)
    (signed : Bool := true) (skipNonce : Bool := false) : Except InclusionError Unit := do
  -- `sender_account = get_account(tx_state, sender)`.
  let account := state.getAccount sender
  if skipNonce then
    -- A simulation's own rule: the sender's nonce must still be below `2^64 - 1`.
    failIf (2 ^ 64 - 1 ≤ account.nonce) (.transaction (.nonceOverflow account.nonce))
  else
    -- `T_n = sigma[S(T)]_n`, in the two branches of `check_nonce`.
    --
    -- `if sender_nonce > Uint(tx.nonce): raise NonceMismatchError("nonce too low")`.
    failIf (tx.nonce.toNat < account.nonce) (.nonceTooLow account.nonce tx.nonce.toNat)
    -- `elif sender_nonce < Uint(tx.nonce): raise NonceMismatchError("nonce too high")`.
    failIf (account.nonce < tx.nonce.toNat) (.nonceTooHigh account.nonce tx.nonce.toNat)
  -- `v_0 <= sigma[S(T)]_b`, with `v_0 = T_g T_p + T_v`, or `T_g T_m + T_v` for type 2.
  --
  -- EIP-4844 adds the blob fee.
  --
  -- `if Uint(sender_account.balance) < max_gas_fee + Uint(tx.value)`.
  let cost := tx.maxGasFee + tx.value.toNat
  failIf (account.balance.toNat < cost) (.insufficientBalance account.balance.toNat cost)
  if signed then
    -- `sender_code = get_code(tx_state, sender_account.code_hash)`.
    --
    -- A state without that code gives an error of its own, where the source reads a full state.
    let code ← (state.getCode account.codeHash).mapError fun _ => .missingCode account.codeHash
    -- `sigma[S(T)]_c = KEC(())`, by EIP-3607, which EIP-7702 relaxes from Pectra.
    --
    -- `if sender_account.code_hash != EMPTY_CODE_HASH and not is_valid_delegation(sender_code)`.
    failIf (account.codeHash ≠ EMPTY_CODE_HASH ∧ !(fork ≥ .pectra ∧ isValidDelegation code))
      (.senderNotEoa sender)

/-- Check that a transaction may enter its block at `fork`, on the chain `chainId`.

The block has used the gas `used` before it, and `state` is the state.

The first check that fails gives the error, and the body marks the order of each fork.

A simulation may give the sender, which skips the signature and the rule on the sender's code.

A legacy transaction then names no chain, since only its signature does.

A simulation may also lift some rules. -/
def checkInclusion {fork : Fork} (chainId : UInt64) (env : BlockEnvironment fork)
    (used : BlockGas) (state : TransactionState) (tx : Transaction)
    (knownSender : Option Address := none) (lifted : LiftedRules := {}) :
    Except InclusionError Included := do
  -- The checks are named first and run below in the order of each fork.
  --
  -- From London, `m >= H_f`.
  --
  -- `if tx.max_fee_per_gas < block_env.base_fee_per_gas`, or the same with `tx.gas_price`.
  --
  -- A simulation may pay a maximum fee of 0 at a base fee of 0; the source has no such mode.
  let baseFee := paidBaseFee env tx lifted
  let coversBaseFee := failIf (tx.maxFeePerGas < baseFee)
    (.insufficientMaxFeePerGas tx.maxFeePerGas baseFee)
  -- `sender_address = recover_sender(tx)`, unless a simulation gives the sender.
  --
  -- The source has no such mode.
  let recover : Except InclusionError Address :=
    match knownSender with
    | some sender => pure sender
    | none => (recoverSender fork tx).mapError .transaction
  -- `if tx_chain_id is not None and tx_chain_id != block_env.chain_id`.
  --
  -- A legacy transaction with a given sender has no signature, so it names no chain.
  --
  -- The source has no such mode.
  let checkChain : Except InclusionError Unit :=
    if knownSender.isSome && tx.type == 0 then pure ()
    else (checkChainId fork chainId tx).mapError .transaction
  let (sender, intrinsic) ←
    if fork ≥ .glamsterdam then do
      -- Amsterdam's `process_transaction` checks the chain, then `check_transaction` runs.
      checkChain
      -- `sender = recover_sender(tx)`.
      let sender ← recover
      -- `intrinsic = validate_transaction(tx, sender)`.
      let intrinsic ← (validateTransaction fork sender tx lifted).mapError .transaction
      -- `check_block_gas_capacity(block_env, block_output, tx.gas, calculate_total_blob_gas(tx))`.
      checkBlockGas env used tx lifted
      -- `effective_gas_price = calculate_effective_gas_price(tx, block_env.base_fee_per_gas)`.
      coversBaseFee
      pure (sender, intrinsic)
    else do
      -- Osaka's `process_transaction` runs `intrinsic = validate_transaction(tx)` first.
      --
      -- No rule alone reads the sender before Glamsterdam, so any address stands in for it.
      let intrinsic ← (validateTransaction fork default tx lifted).mapError .transaction
      -- Then `check_transaction`: the gas and the blob gas of the block.
      checkBlockGas env used tx lifted
      -- Then the chain, the sender and the base fee.
      checkChain
      let sender ← recover
      coversBaseFee
      -- Then the blobs and the authorizations.
      (checkContents fork tx).mapError .transaction
      pure (sender, intrinsic)
  let blobGas := calculateTotalBlobGas tx
  -- `blob_gas_price = calculate_blob_gas_price(block_env.excess_blob_gas)`.
  let blobGasPrice := blobGasPriceOf env
  -- From Dencun, `if Uint(tx.max_fee_per_blob_gas) < blob_gas_price`, for a transaction with blobs.
  failIf (0 < blobGas ∧ tx.maxFeePerBlobGas < blobGasPrice)
    (.insufficientMaxFeePerBlobGas tx.maxFeePerBlobGas blobGasPrice)
  -- Then the nonce, the balance and the code of the sender.
  checkSender fork state sender tx knownSender.isNone lifted.nonce
  -- `effective_gas_price = priority_fee_per_gas + block_env.base_fee_per_gas`, or `tx.gas_price`.
  return ⟨sender, intrinsic, effectiveGasPrice baseFee tx, blobGas⟩

end EthLib.Execution.Transactions
