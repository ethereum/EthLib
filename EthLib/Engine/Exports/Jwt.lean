module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Engine.Jwt

/-!
# Engine JWT exports

The token text, secret and clock cross the bindings as typed values.
-/

public section

namespace EthLib.Engine.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- Build an HS256 Engine token from a 32-byte secret and an issued-at time in seconds. -/
def jwtBuild (args : ByteArray × Nat) : Result String :=
  (Jwt.build args.1 args.2).mapError fun e => (e.code, reprStr e)

/-- Check the secret, compact token, HS256 signature and issued-at time against the clock. -/
def jwtCheck (args : ByteArray × String × Nat) : Result Bool :=
  pure (Jwt.check args.1 args.2.1 args.2.2)

/-- Build an HS256 Engine token from a 32-byte secret and an issued-at time in seconds.

The arguments are the secret and the issued-at time.

The result is the compact token text. -/
@[export eth_engine_jwt_build]
def jwtBuildExport (args : PyValue) : Result PyValue := pyExport jwtBuild args

/-- Accept an HS256 Engine token only within 60 seconds of its issued-at time.

The arguments are the 32-byte secret, the compact token text and the clock in seconds.

A malformed token, a wrong secret or a failed check returns false. -/
@[export eth_engine_jwt_check]
def jwtCheckExport (args : PyValue) : Result PyValue := pyExport jwtCheck args

end EthLib.Engine.Exports
