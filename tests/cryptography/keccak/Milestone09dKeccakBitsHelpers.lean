import EthLib.Cryptography.Proofs.Hash.KeccakBitsHelpers

open EthLib.Cryptography.Hash

example (n : Nat) : (KeccakBits.rhoPosition n).1 < 5 ∧ (KeccakBits.rhoPosition n).2 < 5 :=
  KeccakBits.rhoPosition_bounds n

example (t : Nat) : KeccakBits.rc (t + 255) = KeccakBits.rc t :=
  KeccakBits.rc_periodic t

example (a : KeccakBits.State) (i : Nat) :
    KeccakBits.stateBit a (i + 1600) = KeccakBits.stateBit a i :=
  KeccakBits.stateBit_periodic a i

example (a : KeccakBits.State) (i : Nat) :
    KeccakBits.outputByte a (i + 200) = KeccakBits.outputByte a i :=
  KeccakBits.outputByte_periodic a i

example (a : KeccakBits.State) (ir : Nat) :
    KeccakBits.round (ir + 255) a = KeccakBits.round ir a :=
  KeccakBits.round_periodic ir a
