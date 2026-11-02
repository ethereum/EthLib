import EthLib.Cryptography.Proofs.Hash.KeccakBitsPermutation

open EthLib.Cryptography.Hash

example (a : Keccak.State) :
    KeccakBits.ofLanes (Keccak.pi a) = KeccakBits.pi (KeccakBits.ofLanes a) :=
  KeccakBits.pi_ofLanes a

example (a : Keccak.State) :
    KeccakBits.ofLanes (Keccak.chi a) = KeccakBits.chi (KeccakBits.ofLanes a) :=
  KeccakBits.chi_ofLanes a

example (msg : ByteArray) :
    (KeccakBits.padded msg).length = 8 * (Keccak.pad msg).size :=
  KeccakBits.padded_length_eq_lane msg

example (x y : Fin 5) : KeccakBits.rhoOffset x y =
    (Keccak.RHO[x.val + 5 * y.val]'(by simp only [Keccak.LANES]; omega)).toNat :=
  KeccakBits.rhoOffset_eq x y

example (msg : ByteArray) (i : Fin ((KeccakBits.padded msg).length / 1088))
    (j : Fin 1088) :
    (KeccakBits.paddedBlock msg i)[j] =
      (KeccakBits.padded msg)[1088 * i.val + j.val]'(by
        have hm := KeccakBits.padded_size_multiple msg
        have hi := i.isLt
        have hj := j.isLt
        omega) :=
  KeccakBits.paddedBlock_bit msg i j

example (a : Keccak.State) :
    KeccakBits.ofLanes (Keccak.theta a) = KeccakBits.theta (KeccakBits.ofLanes a) :=
  KeccakBits.theta_ofLanes a

example (a : Keccak.State) :
    KeccakBits.ofLanes (Keccak.rho a) = KeccakBits.rho (KeccakBits.ofLanes a) :=
  KeccakBits.rho_ofLanes a

example (a : Keccak.State) (ir : Fin 24) :
    KeccakBits.ofLanes (Keccak.iota ir a) = KeccakBits.iota ir.val (KeccakBits.ofLanes a) :=
  KeccakBits.iota_ofLanes a ir

example (a : Keccak.State) :
    KeccakBits.ofLanes (Keccak.keccakF a) = KeccakBits.permutation (KeccakBits.ofLanes a) :=
  KeccakBits.permutation_ofLanes a

example (t : Nat) : KeccakBits.rc t = Keccak.Internal.rc t := KeccakBits.rc_eq t
