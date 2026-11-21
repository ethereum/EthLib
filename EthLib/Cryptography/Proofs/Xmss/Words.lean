module

public import EthLib.Cryptography.Xmss.Ots
public import EthLib.Base.Proofs.LittleEndian
public import EthLib.Base.Proofs.Bytes
public import EthLib.Cryptography.Proofs.Hash.Keccak.Lanes

/-!
# Proofs: leanXMSS values as lanes

A randomizer is two lanes, and a trial adds to it on the lanes.

That sum is the sum on the little-endian integer of the 16 bytes, modulo `2^128`.

The scheme's name is one lane, and a list of digests is two lanes per digest, with the same bytes.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.Hash.Keccak (lanesBytes)

/-- The randomizer of trial `c` is `R_0 + c` modulo `2^128`, on the integers of the lanes. -/
theorem toNat_trialRandomizer (w : Lanes2) (c : Nat) :
    (trialRandomizer w c).toNat = (w.toNat + c) % 2 ^ 128 := by
  have := w.lo.toNat_lt
  have := w.hi.toNat_lt
  simp only [trialRandomizer, Hash.Keccak.Lanes2.toNat]
  split_ifs with h <;>
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.shiftRight_eq_div_pow, UInt64.toNat_one, UInt64.toNat_zero] at h ⊢ <;>
    omega

/-- The scheme's name as one lane has the name's 8 bytes. -/
theorem bytesOfLane_seedTagLane : Hash.Keccak.Internal.bytesOfLane SEED_TAG_LANE = SEED_TAG := by
  decide

/-! ## Strings of lanes as bytes -/

/-- A number below `2^64` in the first of two lanes is its 16 little-endian bytes. -/
theorem lanesBytes_index (n : Nat) (h : n < 2 ^ 64) :
    lanesBytes (⟨n.toUInt64, 0⟩ : Lanes2).toArray = (uintToBytes 16 n).toList := by
  rw [Hash.Keccak.lanesBytes_lanes2, Hash.Keccak.Lanes2.bytes_eq_uintToBytes]
  congr 2
  simp only [Hash.Keccak.Lanes2.toNat, Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_zero]
  omega

/-- The lanes of a list of digests are, as bytes, the digests' bytes one after the other. -/
theorem lanesBytes_digestLanes {n : Nat} (ds : Vector Digest n) :
    lanesBytes (digestLanes ds) = (ds.toList.map fun d => d.bytes.toList).flatten := by
  -- Pushing the lanes of each digest appends its two lanes.
  have hpush : ∀ (l : List Digest) (acc : Array UInt64),
      (l.foldl (fun acc d => (acc.push d.lo).push d.hi) acc).toList
        = acc.toList ++ l.flatMap fun d => [d.lo, d.hi] := by
    intro l
    induction l with
    | nil => simp
    | cons d l ih => intro acc; simp [ih]
  have hlanes : (digestLanes ds).toList = ds.toList.flatMap fun d => [d.lo, d.hi] := by
    rw [digestLanes, ← Array.foldl_toList, hpush]
    simp [Vector.toList]
  simp only [lanesBytes, hlanes]
  generalize ds.toList = l
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [List.flatMap_cons, List.flatMap_append, ih, List.map_cons, List.flatten_cons,
      ← Hash.Keccak.lanesBytes_lanes2]
    rfl

end EthLib.Cryptography.Xmss
