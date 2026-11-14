module

public import EthLib.Serialization.Exports.Rlp
public import EthLib.Serialization.Exports.Ssz
public import EthLib.Serialization.Exports.Proofs.Ssz

/-!
# `EthLib.Serialization.Exports`

The C exports of the serialization layer, for the Python bindings.

They are compiled by the `Exports` Lake library.

It also brings the proofs that the SSZ readers and writer agree with their JSON reference.

The specification does not import them.
-/
