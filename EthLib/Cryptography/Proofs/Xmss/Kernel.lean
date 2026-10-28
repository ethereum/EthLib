import EthLib.Cryptography.Xmss
import EthLib.Cryptography.Proofs.Hash.KeccakKernel

/-!
# Proofs: leanXMSS over the kernel's fast hash

The known answers evaluate hundreds of Keccak permutations in the kernel.

The kernel reads an array by walking a list, and appends to one an element at a time.

So the known answers run on a fast form instead, proved equal to the specification:

```text
    hash             =  the fast form of the hash
    Th(P, A, M)      =  that hash of the list P ++ A ++ M
    a chain walk     =  the same walk over that Th
    a path fold      =  the same fold over that Th
```

A known answer rewrites its statement with these equalities, then lets the kernel evaluate it.
-/

namespace EthLib.Cryptography.Xmss.Kernel

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-! ## Bytes as lists -/

/-- An object's bytes, as a list. -/
@[simp] theorem toList_packBytes {n : Nat} (v : Vector UInt8 n) :
    (packBytes v).data.toList = v.toList := rfl

/-- A list of digests' bytes, as a list. -/
@[simp] theorem toList_packDigests {n : Nat} (ds : Vector Digest n) :
    (packDigests ds).data.toList = (ds.toList.map Vector.toList).flatten := by
  simp [packDigests, packBytes, Vector.flatten, Array.toList_flatten, Vector.toList]
  rfl

/-- Concatenated bytes, as a list. -/
@[simp] theorem toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

/-! ## The hash -/

/-- The fast form of the scheme's hash: Keccak-256 over the record form of Keccak-f. -/
def hash (input : ByteArray) : Vector UInt8 32 :=
  Hash.Keccak.Kernel.keccak256 input

/-- The scheme's hash is its fast form. -/
theorem hash_eq (input : ByteArray) : Xmss.hash input = hash input :=
  Hash.Keccak.Kernel.keccak256_eq input

/-- A tweakable hash input, written as one list. -/
theorem hash_thInput (pp : PublicParam) (address : Address) (payload : ByteArray) :
    hash (thInput pp address payload)
      = hash ⟨⟨pp.toList ++ address.toList ++ payload.data.toList⟩⟩ := rfl

/-- `Th` over the fast hash, its input written as one list. -/
def th (pp : PublicParam) (address : Address) (payload : List UInt8) : Digest :=
  halfOf 0 (hash ⟨⟨pp.toList ++ address.toList ++ payload⟩⟩)

/-- `Th` is `Th` over the fast hash, of the payload's bytes. -/
theorem th_eq (pp : PublicParam) (address : Address) (payload : ByteArray) :
    Xmss.th pp address payload = th pp address payload.data.toList := by
  simp only [Xmss.th, hashHalf, hash_eq, th]
  -- The two inputs are the same bytes, by definition.
  rfl

/-! ## Chains -/

/-- A chain walk over the fast hash, step for step the specification's. -/
def chain (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) : Digest :=
  match steps, h with
  | 0, _ => value
  | s + 1, h => th pp (addrChain layer e ⟨start + s, by simp only [CHAIN_LENGTH] at *; omega⟩)
      ((chain pp layer e i start s (by omega) value).toList ++ (littleEndian 16 i.val).toList)

/-- A chain walk is the walk over the fast hash. -/
theorem chain_eq (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V) (start : Nat) :
    ∀ steps h value,
      Xmss.chain pp layer e i start steps h value = chain pp layer e i start steps h value := by
  intro steps
  induction steps with
  | zero => intro h value; rfl
  | succ s ih =>
    intro h value
    -- One step on each side, the walks below it equal by induction.
    simp only [Xmss.chain, chainStep, chain, th_eq, ih, toList_append, toList_packBytes]

/-! ## Paths -/

/-- Climbing a path over the fast hash, level for level the specification's. -/
def climbUpto (pp : PublicParam) (layer : Layer) (e : Nat) (pi : Vector Digest LAYER_HEIGHT)
    (leaf : Digest) : (levels : Nat) → levels ≤ LAYER_HEIGHT → Digest
  | 0, _ => leaf
  | l + 1, h =>
    let current := climbUpto pp layer e pi leaf l (by omega)
    let sibling := pi[l]'(by omega)
    let address := addrNode layer ⟨l + 1, by omega⟩ (UInt32.ofNat (e >>> (l + 1)))
    -- Bit `l` of the key's index says which child the held node is.
    if (e >>> l) % 2 == 0 then th pp address (current.toList ++ sibling.toList)
    else th pp address (sibling.toList ++ current.toList)

/-- Climbing a path is climbing it over the fast hash. -/
theorem climbUpto_eq (pp : PublicParam) (layer : Layer) (e : Nat)
    (pi : Vector Digest LAYER_HEIGHT) (leaf : Digest) :
    ∀ levels h,
      Internal.climbUpto pp layer e pi leaf levels h = climbUpto pp layer e pi leaf levels h := by
  intro levels
  induction levels with
  | zero => intro h; rfl
  | succ l ih =>
    intro h
    -- One level on each side, the climbs below it equal by induction.
    simp only [Internal.climbUpto, Internal.climbStep, nodeHash, climbUpto, th_eq, ih,
      toList_append, toList_packBytes]

/-- A path fold is the fold over the fast hash. -/
theorem fold_eq (pp : PublicParam) (layer : Layer) (e : Nat) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) :
    fold pp layer e leaf pi = climbUpto pp layer e pi leaf LAYER_HEIGHT (Nat.le_refl _) :=
  climbUpto_eq pp layer e pi leaf _ _

end EthLib.Cryptography.Xmss.Kernel
