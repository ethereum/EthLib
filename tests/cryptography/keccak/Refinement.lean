import EthLib.Cryptography.Proofs.Hash.KeccakBitsRepresentation

open EthLib.Cryptography.Hash

example (msg : ByteArray) : Keccak.keccak256 msg = KeccakBits.keccak256 msg :=
  KeccakBits.keccak256_eq msg

example (state : KeccakBits.State) : KeccakBits.ofLanes (KeccakBits.toLanes state) = state :=
  KeccakBits.ofLanes_toLanes state

example (state : Keccak.State) : KeccakBits.toLanes (KeccakBits.ofLanes state) = state :=
  KeccakBits.toLanes_ofLanes state

example (state : KeccakBits.State) :
    KeccakBits.toLanes (KeccakBits.permutation state) = Keccak.keccakF (KeccakBits.toLanes state) :=
  KeccakBits.toLanes_permutation state
