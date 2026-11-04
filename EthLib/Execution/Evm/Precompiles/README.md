# Precompiles

A precompile is a contract at a fixed address whose code is not EVM bytecode.
A call to it runs a function of the protocol on the call data, for a price in gas.
Every client must return the same bytes and charge the same gas, or the chain splits.

Ethereum has 18 precompiles, added by six forks from Frontier to Fusaka.
This directory specifies all of them, and one table runs each by its address.
This page first states how every precompile is written.
A new precompile follows the same rules, and a review checks them.

## Families

A family is a set of precompiles that share one error type and one encoding of the call data.
The 18 precompiles form ten families:

- ECRECOVER at `0x01`, from Frontier.
- SHA256 at `0x02`, from Frontier.
- RIPEMD160 at `0x03`, from Frontier.
- IDENTITY at `0x04`, from Frontier.
- MODEXP at `0x05`, from Byzantium.
- The three alt_bn128 precompiles at `0x06` to `0x08`, from Byzantium.
- BLAKE2F at `0x09`, from Istanbul.
- The point evaluation at `0x0a`, from Dencun.
- The seven BLS12-381 precompiles at `0x0b` to `0x11`, from Pectra.
- P256VERIFY at `0x100`, from Fusaka.

Each family has one namespace, `EthLib.Execution.Evm.Precompiles.<Family>`.

## Files

A family is one file, `<Family>.lean`, in this directory.
It becomes a folder `<Family>/` only when one file would pass about 250 lines.
The folder then has an umbrella `<Family>.lean` beside it, which imports every file of the folder.
The files of a folder take their names from this list, in import order:

- `Constants.lean` holds the numbers of the sources, when several files share them.
- `Errors.lean` holds the error type.
- `Encoding.lean` reads the call data and writes the output.
- `Gas.lean` holds the price, when it depends on the fork.
- `Core.lean` holds the calls, or one file per group of calls, such as `G1.lean` for the G1 calls.

A folder holds Lean files, so no folder holds only a README.

## The call

Each precompile has one call, named after the precompile in lowerCamelCase, such as `ecadd`.
The call takes the fork first, when an EIP changes the precompile after the fork that adds it.
It then takes the call data and the gas:

```lean
def modexp (fork : Fork) (data : ByteArray) (gas : Nat) : Except ModexpError ByteArray
```

The call runs its steps in the order of the source:

1. It checks the call data that the source checks before the charge, such as the length.
2. It fails with `outOfGas` when the gas is below the price.
3. It decodes and checks the rest of the call data.
4. It returns the output.

The doc comment of the call states that order.
A check that a source leaves unordered gets an order in the code, and the doc comment says so.

Every failure of a precompile consumes all the gas given to the call, and returns no data.
So the order decides only which error the specification reports, and no client can observe it.

## Errors

Each family has one error type, `<Family>Error`, which derives `Repr` and `DecidableEq`.
Every error type has the constructor `outOfGas (cost gas : Nat)`.
The other constructors use one name for one cause across families:

- `invalidInputLength (size : Nat)` for call data of a length that the precompile does not accept.
- `invalidFieldElement`, `notOnCurve` and `notInSubgroup` for a point that does not decode.

An input that the source answers with an output is not an error.
For example, ECRECOVER returns empty output for an invalid signature, and the call succeeds.

Every error type has a code for each constructor, from 1, which ignores the arguments.
Its proofs show that the code is injective on constructors, as for every error type of EthLib.
A new constructor takes a new code, so that each code keeps its meaning.

The table wraps the error of each family in one type, which has a code for each family.
The C exports report that code, and the message prints the error of the family.

## The price

The price of a precompile is one declaration, which the call compares with the gas:

- A price that is one number at every fork is a constant, such as `GAS_ECRECOVER`.
- Any other price is a function: `gasCost` in a family of one precompile, `<call>Gas` otherwise.
- A price that changes at a fork takes the fork first, as the call does.

The price lives in the family, even when an EIP changes it at a later fork.
No precompile keeps its price in the gas schedule of the EVM, which is for instructions.

The table gives the price of each address at each fork.
Its proofs show that a call that succeeds had at least that price in gas.

## Proofs

The proofs of a family mirror its files in `EthLib/Execution/Proofs/Evm/Precompiles/`.
A family of one file has one proof file of the same name.
A property that needs more imports, such as the group law of a curve, gets its own file.
That file is named after the property.
The proofs then form a folder, and the properties of the single file go in `Basic.lean`.

Each call has these theorems, named after the call and the error constructor:

- `<call>_outOfGas`: once the checks before the charge pass, gas below the price fails the call.
- `<call>_<error>`: each other error constructor is reached, under its condition.
- `<call>_eq_ok_iff`, or `<call>_ok`: what a successful call returns.
- `<call>_size`: the length of every output.

Each error type has `<Family>Error.code_injective`.

A family proves more where its source asks for more, such as the round trip of an encoding.

## Exports and bindings

Python reaches every precompile through the table, by its address, at a fork:

- `eth_precompile_run` takes the fork name, the address, the call data and the gas.
- `eth_precompile_price` takes the fork name, the address and the call data, and returns the price.

An unknown fork, or a fork with no precompile at the address, gives the error code 0.
No precompile has an export of its own.

In Python, these are `ethlib.precompiles.run` and `ethlib.precompiles.price`.
A failed call raises `PrecompileError`, whose code names the family.
Its message is the error of the family, as Lean prints it.

## Tests

The tests of a family are `bindings/python/tests/precompile/test_<family>.py`.
They run the official vectors of the family through the table, at the prices that the EIPs give.
They run at the fork that adds the family, at each fork that changes it, and at the latest fork.
A test of the price, which costs little, runs at every fork from the fork that adds the family.
Each vector file has its pinned source, as `tests/sources.toml` records it.

## Sources

Each family cites its primary source, with the section:

- The Yellow Paper, Appendix E, for the four precompiles of Frontier.
- The EIP that adds the precompile, and each EIP that changes it later.
- The standard that defines the arithmetic, such as RFC 7693 for BLAKE2b or SEC 1 for ECDSA.

The code does not cite execution-specs.
A doc comment names a function of a source only when the cited EIP or standard defines it.

## This page

Each family has one section on this page, in the order of the addresses.
A family gets its section when its files follow the rules above.
Each section gives the source, the input and the output, the errors and the price.
It then gives the proofs and the test vectors.
A Lean module header says in a few lines what its precompile does, and this page gives the rest.
