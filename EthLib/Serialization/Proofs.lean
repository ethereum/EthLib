module

public import EthLib.Serialization.Proofs.Der
public import EthLib.Serialization.Proofs.E2store
public import EthLib.Serialization.Proofs.Exports.Ssz
public import EthLib.Serialization.Proofs.Exports.SszRecord
public import EthLib.Serialization.Proofs.JsonRpc
public import EthLib.Serialization.Proofs.Rlp
public import EthLib.Serialization.Proofs.Ssz

/-!
# `EthLib.Serialization.Proofs`

Machine-checked properties of the serialization specifications.
This tree mirrors the layout of the definitions it proves things about.

The SSZ readers and writer of the C exports agree with their JSON reference.
-/
