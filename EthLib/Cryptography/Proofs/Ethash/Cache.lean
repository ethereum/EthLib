module

public import EthLib.Cryptography.Ethash.Cache
public import EthLib.Cryptography.Proofs.Ethash.Sizes

/-!
# Proofs: the Ethash seed and cache

The seed of an epoch is the Keccak-256 digest of the seed of the epoch before.

The cache has one item per 64 bytes of its size, so a prime number of items.

So the cache is never empty, and a dataset item never reads a default item.

The official cache digests are in the Python suite, through the bindings.
-/

@[expose] public section

namespace EthLib.Cryptography.Ethash

open EthLib.Cryptography.Hash.Keccak (keccak256)

/-! ## The seed -/

/-- The seed of the first epoch is 32 zero bytes. -/
theorem seed_of_lt {number : Nat} (h : number < EPOCH_LENGTH) :
    seed number = ⟨Array.replicate 32 0⟩ := by
  simp [seed, epoch, Nat.div_eq_of_lt h, Nat.repeat]

/-- One epoch later, the seed is the Keccak-256 digest of the seed. -/
theorem seed_add_epoch (number : Nat) :
    seed (number + EPOCH_LENGTH) = ⟨(keccak256 (seed number)).toArray⟩ := by
  simp only [seed, epoch, Nat.add_div_right _ (by decide : 0 < EPOCH_LENGTH), Nat.repeat]

/-! ## The size of the cache -/

/-- The bytes of `n` words are `4 · n` bytes. -/
theorem size_bytesOfWords {n : Nat} (words : Vector UInt32 n) :
    (bytesOfWords words).size = 4 * n := by
  simp only [bytesOfWords, ByteArray.size, Array.size_flatMap]
  rw [← Array.sum_toList]
  simp [Array.toList_map, List.sum_replicate, Nat.mul_comm]

/-- A fold whose step keeps the size of an array keeps it. -/
private theorem size_foldl_eq {α β : Type} (f : Array β → α → Array β)
    (hf : ∀ c a, (f c a).size = c.size) (l : List α) (c : Array β) :
    (l.foldl f c).size = c.size := by
  induction l generalizing c with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, hf]

/-- A fold whose step adds one item to an array adds one per element. -/
private theorem size_foldl_succ {α β : Type} (f : Array β → α → Array β)
    (hf : ∀ c a, (f c a).size = c.size + 1) (l : List α) (c : Array β) :
    (l.foldl f c).size = c.size + l.length := by
  induction l generalizing c with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, hf, List.length_cons]; omega

/-- The initial cache has `n` items. -/
theorem size_initialCache (n : Nat) (s : ByteArray) : (initialCache n s).size = n := by
  unfold initialCache
  -- Each step pushes one item.
  rw [size_foldl_succ _ (fun c _ => Array.size_push ..)]
  simp

/-- A round keeps the number of items. -/
theorem size_cacheRound (c : Array Item) : (cacheRound c).size = c.size := by
  unfold cacheRound
  -- Each step sets one item in place.
  exact size_foldl_eq _ (fun d i => Array.size_setIfInBounds ..) _ c

/-- The cache has one item per 64 bytes of the cache size. -/
theorem size_cache (number : Nat) : (cache number).size = cacheSize number / HASH_BYTES := by
  unfold cache
  -- Each round keeps the size of the initial cache.
  induction CACHE_ROUNDS with
  | zero => simp [Nat.repeat, size_initialCache]
  | succ r ih => simp only [Nat.repeat, size_cacheRound, ih]

/-- The cache holds a prime number of items. -/
theorem prime_size_cache (number : Nat) : Nat.Prime (cache number).size := by
  rw [size_cache]
  exact prime_cacheSize_div number

/-- The cache is never empty. -/
theorem size_cache_pos (number : Nat) : 0 < (cache number).size :=
  (prime_size_cache number).pos

end EthLib.Cryptography.Ethash
