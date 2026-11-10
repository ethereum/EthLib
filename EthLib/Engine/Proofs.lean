module

public import EthLib.Engine.Proofs.Block
public import EthLib.Engine.Proofs.ExecutionEngine
public import EthLib.Engine.Proofs.ForkchoiceUpdated
public import EthLib.Engine.Proofs.GetBlobs
public import EthLib.Engine.Proofs.Json
public import EthLib.Engine.Proofs.Jwt
public import EthLib.Engine.Proofs.NewPayload
public import EthLib.Engine.Proofs.PayloadBodies
public import EthLib.Engine.Proofs.PreparePayload

/-!
# `EthLib.Engine.Proofs`

Machine-checked properties of the Engine API.

The proofs for `EthLib.Engine.Foo` live in `EthLib.Engine.Proofs.Foo`.

They build in the `Proofs` Lake library, which the library code does not depend on.
-/
