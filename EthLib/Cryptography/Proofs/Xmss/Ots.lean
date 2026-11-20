module

public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash

/-!
# Proofs: WOTS+C one-time signatures

Correctness of the one-time signature: an honest one leads back to the key's own leaf.

Each theorem holds for every hash function `f`, run in the identity monad.

Keccak-256 is one such function, so the theorems cover the specification as it runs.

A variable `f` also keeps every proof from unfolding the hash on a concrete input.

The theorems also hold for every source of derived values.

With the derivations from `S`, chain starts and randomizer bases are the note's hashes of `S`.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {f : ByteArray → Vector UInt8 32} {pp : PublicParam} {layer : Layer} {e : UInt32}
  {i : Fin V}
  {start s₁ s₂ : Nat} {value : Digest}

/-! ## Randomizer trials -/

/-- Writing byte `i` changes the little-endian integer by the byte's weight. -/
private theorem foldr_set (l : List UInt8) (i : Nat) (hi : i < l.length) (b : UInt8) :
    (l.set i b).foldr (fun byte acc => byte.toNat + 256 * acc) 0 + l[i].toNat * 256 ^ i
      = l.foldr (fun byte acc => byte.toNat + 256 * acc) 0 + b.toNat * 256 ^ i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp only [List.set_cons_zero, List.foldr_cons, List.getElem_cons_zero]; ring
    | succ i =>
      have := ih i (by simpa using hi)
      simp only [List.set_cons_succ, List.foldr_cons, List.getElem_cons_succ, pow_succ]
      linear_combination 256 * this

/-- Bytes keep only the integer modulo `256^k`. -/
private theorem uintToBytes_mod_pow (k n : Nat) :
    uintToBytes k (n % 256 ^ k) = uintToBytes k n := by
  conv_rhs => rw [← Base.uintToBytes_bytesToUint (uintToBytes k n), Base.bytesToUint_uintToBytes]

/-- Adding a carry from byte `i` up gives the bytes of the integer plus `carry * 256^i`. -/
private theorem trialRandomizer_go (acc : Randomizer) (carry i : Nat) (hi : i ≤ RANDOMIZER_LEN) :
    trialRandomizer.go acc carry i
      = uintToBytes RANDOMIZER_LEN (bytesToUint acc + carry * 256 ^ i) := by
  fun_induction trialRandomizer.go acc carry i with
  | case1 acc carry i h sum ih =>
    rw [ih h]
    congr 1
    -- The new byte holds the sum modulo 256, and the next carry holds the rest.
    have hset := foldr_set acc.toList i (by simpa using h) (UInt8.ofNat sum)
    rw [← Vector.toList_set h, ← Base.bytesToUint_eq_foldr, ← Base.bytesToUint_eq_foldr,
      Vector.getElem_toList, UInt8.toNat_ofNat'] at hset
    have hdiv := Nat.mod_add_div sum 256
    simp only [sum] at hset hdiv ⊢
    rw [pow_succ]
    linear_combination hset + 256 ^ i * hdiv
  | case2 acc carry i h =>
    -- Every byte is written, so the carry past the top byte is dropped.
    obtain rfl : i = RANDOMIZER_LEN := by omega
    rw [← uintToBytes_mod_pow, Nat.add_mul_mod_self_right, uintToBytes_mod_pow,
      Base.uintToBytes_bytesToUint]

/-- The randomizer of trial `c` is the little-endian bytes of `R_0 + c` modulo `2^128`. -/
theorem trialRandomizer_eq (base : Randomizer) (c : Nat) :
    trialRandomizer base c = uintToBytes RANDOMIZER_LEN ((bytesToUint base + c) % 2 ^ 128) := by
  rw [trialRandomizer, trialRandomizer_go _ _ _ (Nat.zero_le _), pow_zero, mul_one,
    show (2 : Nat) ^ 128 = 256 ^ RANDOMIZER_LEN by norm_num [RANDOMIZER_LEN], uintToBytes_mod_pow]

/-- The search tests trial `c` on the digest of its randomizer `rho_c`, in any monad.

It builds `P | A_msg(l, e) | M` once, and each trial hashes those bytes followed by `rho_c`.

That is the input of the digest of `rho_c`, so the trials make the same hash calls. -/
theorem Internal.findCodeword_eq {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
    (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer)
    (c fuel : Nat) :
    Internal.findCodeword H pp layer e msg base c fuel =
      Wots.findFirst (trialRandomizer base)
        (fun rho => codeword? <$> messageDigest H pp layer e msg rho) c fuel := by
  simp only [Internal.findCodeword, messageDigest, th, thInput, ByteArray.append_assoc]

/-! ## Derivations from the seed -/

section SeedPrf

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32)) (s : Seed)

/-- With the seed's derivations, the chain starts hash `P | A_prf(l, e, j) | S`. -/
theorem chainStarts_seedPrf (pp : PublicParam) (layer : Layer) (e : UInt32) :
    chainStarts pp (seedPrf H s) layer e = (do
      let pairs ← ofFnInOrder (V / 2) fun j => H (thInput pp (addrPrf layer e j) (packBytes s))
      return Vector.ofFn fun i =>
        halfOf ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
          (pairs[i.val / 2]'(by have := i.isLt; simp only [V] at *; omega))) := by
  simp only [chainStarts, seedPrf_empty]

/-- With the seed's derivations, the randomizer base is `Th(P, A_rnd(l, e), S | M)`. -/
theorem randomizerBase_seedPrf (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) :
    randomizerBase pp (seedPrf H s) layer e msg = th H pp (addrRnd layer e) (packBytes s ++ msg) :=
  rfl

end SeedPrf

/-! ## Chains -/

/-- Walking no steps leaves the value alone. -/
@[simp] theorem chain_zero (h : start + 0 < CHAIN_LENGTH) :
    (chain (pureHash f) pp layer e i start 0 h value).run = value := rfl

/-! ## An honest signature leads to the key's leaf -/

/-- What the one-time signer computes: the grinding result, with each chain walked to its digit.

`rw` unfolds the signer, not `simp`.

`simp` rewrites with `rfl` lemmas, and checking those makes Lean unfold the grinding loop.

That loop runs up to `2^32` trials. -/
theorem otsSign_run {prf : SeedPrf Id} {msg : ByteArray} :
    (otsSign (pureHash f) pp prf layer e msg).run =
      ((Internal.findCodeword (pureHash f) pp layer e msg
          (randomizerBase pp prf layer e msg).run 0 MAX_RANDOMIZER_TRIALS).run).map
        fun found => (found.1, Vector.ofFn fun i => (chain (pureHash f) pp layer e i 0
          (found.2[i]).val (by have := (found.2[i]).isLt; omega)
          (chainStarts pp prf layer e).run[i]).run) := by
  rw [otsSign, Id.run_bind, Id.run_bind]
  cases (Internal.findCodeword (pureHash f) pp layer e msg
      (randomizerBase pp prf layer e msg).run 0 MAX_RANDOMIZER_TRIALS).run with
  | none => rfl
  | some found =>
    obtain ⟨rho, x⟩ := found
    -- The signer reveals the chains in order, which is the vector of the walked chains.
    rw [Option.map_some, ← HashSig.ofFnInOrder_run]
    rfl

/-- A one-time signature from the derivations recovers the leaf they give the key.

The verifier walks each revealed value from position `x_i` to 3.

The signer walked it from 0 to `x_i`, so together they walk the whole chain. -/
theorem otsLeaf_otsSign {prf : SeedPrf Id} {msg : ByteArray} {rho : Randomizer}
    {y : Vector Digest V}
    (h : (otsSign (pureHash f) pp prf layer e msg).run = some (rho, y)) :
    (otsLeaf (pureHash f) pp layer e msg rho y).run
      = some (otsPublicLeaf (pureHash f) pp prf layer e).run := by
  -- Name the grinding result: a randomizer and its codeword.
  rw [otsSign_run, Option.map_eq_some_iff] at h
  obtain ⟨⟨rho', x⟩, hfind, hxy⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
  rw [Internal.findCodeword_eq] at hfind
  obtain ⟨-, -, -, -, hcw, -⟩ := Wots.findFirst_spec hfind
  unfold Id.run at hcw
  replace hcw : codeword? (messageDigest (pureHash f) pp layer e msg rho').run = some x := hcw
  -- The verifier recomputes the same codeword.
  simp only [otsLeaf, otsPublicLeaf, Id.run_bind, Id.run_pure, hcw, HashSig.ofFnInOrder_run]
  refine congrArg (fun ends => some (otsLeafHash (pureHash f) pp layer e ends).run)
    (Vector.ext fun j hj => ?_)
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  -- Signer's steps plus verifier's steps make the whole chain.
  have hx := (x[j]'hj).isLt
  have hsplit := Wots.chain_add (m := Id) (step := chainStep (pureHash f) pp layer e ⟨j, hj⟩)
    (start := 0) (s₁ := (x[j]'hj : Nat)) (s₂ := CHAIN_LENGTH - 1 - (x[j]'hj : Nat))
    (value := (chainStarts pp prf layer e).run[j]'hj) (Nat.zero_add _).symm
    (by simp only [CHAIN_LENGTH] at *; omega) (by simp only [CHAIN_LENGTH] at *; omega)
  -- Steps revealed plus steps walked is the whole chain.
  exact hsplit.trans (Wots.chain_steps_congr (by simp only [CHAIN_LENGTH] at *; omega) _ _)

/-! ## A key's leaf in pieces -/

/-- A key's leaf, from its chain starts, its chain ends and its leaf hash.

A known answer checks each piece on its own. -/
theorem otsPublicLeaf_eq {prf : SeedPrf Id} {starts ends : Vector Digest V} {leaf : Digest}
    (hstarts : (chainStarts pp prf layer e).run = starts)
    (hends : ∀ i : Fin V,
      (chain (pureHash f) pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i]).run = ends[i])
    (hleaf : (otsLeafHash (pureHash f) pp layer e ends).run = leaf) :
    (otsPublicLeaf (pureHash f) pp prf layer e).run = leaf := by
  -- The walked chains are the stated ends, chain by chain.
  have hv : (Vector.ofFn fun i =>
      (chain (pureHash f) pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) starts[i]).run) = ends :=
    Vector.ext fun i hi => by simpa using hends ⟨i, hi⟩
  simp only [otsPublicLeaf, Id.run_bind, hstarts, HashSig.ofFnInOrder_run, hv, hleaf]

end EthLib.Cryptography.Xmss
