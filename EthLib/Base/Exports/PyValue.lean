module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.PyValueCore
public import EthLib.Base.Exports.PyValueJson
public meta import EthLib.Base.Proofs.Exports.PyValue

/-!
# The Python value boundary

The conversions used by C exports, their laws and their JSON representation.

The conversion laws are imported only for elaboration, so runtime code does not depend on them.
-/
