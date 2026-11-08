module

public import EthLib.Cryptography.Proofs.QueryAvoidance
public import EthLib.Cryptography.Proofs.Xmss.Address
public import EthLib.Cryptography.Proofs.Xmss.CodewordSearch

/-!
# Proofs: a whole signature rarely fails, in the random-oracle model

A signature signs on two layers, and each layer searches for a codeword.

Signing fails when either search finds none.

Each search hashes at its key's message address, with a payload of one fixed length.

Before a search, the signer hashes no such input.

The calls before it have other addresses, or the 40-byte input that grows the scheme seed.

So a cache that holds no trial input of either key keeps none until its search starts.

Each search then fails with probability at most `exp(-4000)`, and signing at most twice that.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants
open OracleSpec OracleComp ENNReal

/-- The hash as a query to the random oracle of the game. -/
local notation "Hq" => Unforgeability.queryH (m := OracleComp XmssSecurity.OracleWorld)

/-! ## Trial inputs -/

/-- A query of an input at address `A` whose payload has `k` bytes.

A key's codeword search queries only such inputs, at its message address. -/
def IsTrialQuery (A : Address) (k : Nat) : XmssSecurity.OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr x => ∃ pp payload, payload.size = k ∧ x = (thInput pp A payload).data.toList

noncomputable instance (A : Address) (k : Nat) : DecidablePred (IsTrialQuery A k) :=
  Classical.decPred _

/-- An input `P | A | M` has `32` bytes before its payload. -/
theorem size_thInput (pp : PublicParam) (A : Address) (payload : ByteArray) :
    (thInput pp A payload).size = 32 + payload.size := by
  rw [thInput, ByteArray.size_append, ByteArray.size_append, Base.size_packBytes,
    Base.size_packBytes]
  rfl

/-- A hash at another address is not a trial query. -/
theorem isQueryBoundP_queryH_of_ne {A A' : Address} (k : Nat) (pp : PublicParam)
    (payload : ByteArray) (hA : A' ≠ A) :
    IsQueryBoundP (Hq (thInput pp A' payload)) (IsTrialQuery A k) 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  obtain ⟨_, _, _, heq⟩ := h
  exact absurd (thInput_inj (ByteArray.ext (Array.toList_inj.mp heq))).2.1 hA

/-- A hash of an input of another length is not a trial query. -/
theorem isQueryBoundP_queryH_of_size {A : Address} {k : Nat} {x : ByteArray}
    (hx : x.size ≠ 32 + k) : IsQueryBoundP (Hq x) (IsTrialQuery A k) 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  obtain ⟨pp, payload, hsize, heq⟩ := h
  change x.data.toList = _ at heq
  have hlen : x.size = (thInput pp A payload).size := by
    have := congrArg List.length heq
    rw [Array.length_toList, Array.length_toList] at this
    exact this
  rw [size_thInput, hsize] at hlen
  exact absurd hlen hx

/-- An address on one layer is not the message address of a key on the other. -/
theorem encodeAddress_ne_addrMsg {layer layer' : Layer} (hl : layer ≠ layer') (tau : Fin 32)
    (mu : Fin 8) (a : Fin (2 ^ 23)) (e e' : UInt32) :
    encodeAddress tau mu (layerHi layer a) e ≠ addrMsg layer' e' := fun h =>
  hl (layerHi_inj.mp (encodeAddress_inj.mp h).2.2.1).1

/-! ## A layer never queries the other layer's trial inputs -/

section OtherLayer

variable {layer layer' : Layer} (hl : layer ≠ layer') (e' : UInt32) (k : Nat)
include hl

/-- A hash at an address of the layer is not a trial query of the other layer. -/
theorem th_isQueryBoundP_otherLayer (pp : PublicParam) (tau : Fin 32) (mu : Fin 8)
    (a : Fin (2 ^ 23)) (e : UInt32) (payload : ByteArray) :
    IsQueryBoundP (th Hq pp (encodeAddress tau mu (layerHi layer a) e) payload)
      (IsTrialQuery (addrMsg layer' e') k) 0 :=
  isQueryBoundP_bind_zero _ _
    (isQueryBoundP_queryH_of_ne k pp payload (encodeAddress_ne_addrMsg hl _ _ _ _ _))
    fun _ => isQueryBoundP_pure _ _ _

/-- A key's chain starts query no trial input of the other layer. -/
theorem chainStarts_isQueryBoundP_otherLayer (pp : PublicParam) (seed : Seed) (e : UInt32) :
    IsQueryBoundP (chainStarts pp (seedPrf Hq seed) layer e)
      (IsTrialQuery (addrMsg layer' e') k) 0 :=
  isQueryBoundP_bind_zero _ _
    (ofFnInOrder_isQueryBoundP_zero _ _ fun _ => isQueryBoundP_queryH_of_ne k pp _
      (encodeAddress_ne_addrMsg hl _ _ _ _ _))
    fun _ => isQueryBoundP_pure _ _ _

/-- A walk along a key's chain queries no trial input of the other layer. -/
theorem chain_isQueryBoundP_otherLayer (pp : PublicParam) (e : UInt32) (i : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    IsQueryBoundP (chain Hq pp layer e i start steps h value)
      (IsTrialQuery (addrMsg layer' e') k) 0 :=
  chain_isQueryBoundP_zero _ (fun _ _ => th_isQueryBoundP_otherLayer hl e' k _ _ _ _ _ _) _ _ _ _

/-- A key's leaf, from the seed, queries no trial input of the other layer. -/
theorem otsPublicLeaf_isQueryBoundP_otherLayer (pp : PublicParam) (seed : Seed) (e : UInt32) :
    IsQueryBoundP (otsPublicLeaf Hq pp (seedPrf Hq seed) layer e)
      (IsTrialQuery (addrMsg layer' e') k) 0 :=
  isQueryBoundP_bind_zero _ _ (chainStarts_isQueryBoundP_otherLayer hl e' k pp seed e) fun _ =>
    isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
      chain_isQueryBoundP_otherLayer hl e' k _ _ _ _ _ _ _) fun _ =>
      th_isQueryBoundP_otherLayer hl e' k _ _ _ _ _ _

/-- A node hash of the layer queries no trial input of the other layer. -/
theorem nodeHash_isQueryBoundP_otherLayer (pp : PublicParam) (level j : Nat)
    (left right : Digest) :
    IsQueryBoundP (nodeHash Hq pp layer level j left right)
      (IsTrialQuery (addrMsg layer' e') k) 0 :=
  th_isQueryBoundP_otherLayer hl e' k _ _ _ _ _ _

/-- A node of the layer queries no trial input of the other layer. -/
theorem node_isQueryBoundP_otherLayer (pp : PublicParam) (seed : Seed) (level j : Nat) :
    IsQueryBoundP (node Hq pp (seedPrf Hq seed) layer level j)
      (IsTrialQuery (addrMsg layer' e') k) 0 :=
  merkleNode_isQueryBoundP_zero _ _
    (fun _ => otsPublicLeaf_isQueryBoundP_otherLayer hl e' k _ _ _)
    (fun _ _ _ _ => nodeHash_isQueryBoundP_otherLayer hl e' k _ _ _ _ _) _ _

/-- A key's path queries no trial input of the other layer. -/
theorem path_isQueryBoundP_otherLayer (pp : PublicParam) (seed : Seed) (e : Nat) :
    IsQueryBoundP (path Hq pp (seedPrf Hq seed) layer e) (IsTrialQuery (addrMsg layer' e') k) 0 :=
  merkleSiblings_isQueryBoundP_zero _ _
    (fun _ => otsPublicLeaf_isQueryBoundP_otherLayer hl e' k _ _ _)
    (fun _ _ _ _ => nodeHash_isQueryBoundP_otherLayer hl e' k _ _ _ _ _) _ _ _

/-- A one-time signature on the layer queries no trial input of the other layer. -/
theorem otsSign_isQueryBoundP_otherLayer (pp : PublicParam) (seed : Seed) (e : UInt32)
    (msg : ByteArray) :
    IsQueryBoundP (otsSign Hq pp (seedPrf Hq seed) layer e msg)
      (IsTrialQuery (addrMsg layer' e') k) 0 := by
  refine isQueryBoundP_bind_zero _ _ (th_isQueryBoundP_otherLayer hl e' k _ _ _ _ _ _)
    fun base => isQueryBoundP_bind_zero _ _
      (findFirst_isQueryBoundP_zero _ _ (fun _ => isQueryBoundP_map_iff _ _ _ |>.2
        (th_isQueryBoundP_otherLayer hl e' k _ _ _ _ _ _)) _ _) fun r => ?_
  rcases r with _ | ⟨rho, x⟩
  · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_bind_zero _ _ (chainStarts_isQueryBoundP_otherLayer hl e' k _ _ _)
      fun _ => isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
        chain_isQueryBoundP_otherLayer hl e' k _ _ _ _ _ _ _) fun _ => isQueryBoundP_pure _ _ _

/-- A layer's signature queries no trial input of the other layer. -/
theorem signLayer_isQueryBoundP_otherLayer (pp : PublicParam) (seed : Seed) (e : Nat)
    (msg : ByteArray) :
    IsQueryBoundP (signLayer Hq pp (seedPrf Hq seed) layer e msg)
      (IsTrialQuery (addrMsg layer' e') k) 0 := by
  refine isQueryBoundP_bind_zero _ _ (otsSign_isQueryBoundP_otherLayer hl e' k _ _ _ _) fun r => ?_
  rcases r with _ | ⟨rho, y⟩
  · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_bind_zero _ _ (path_isQueryBoundP_otherLayer hl e' k _ _ _)
      fun _ => isQueryBoundP_pure _ _ _

end OtherLayer

/-! ## One layer fails rarely -/

/-- The randomizer base is not a trial query of its own key. -/
theorem randomizerBase_isQueryBoundP (pp : PublicParam) (seed : Seed) (layer : Layer)
    (e : UInt32) (msg : ByteArray) (k : Nat) :
    IsQueryBoundP (randomizerBase pp (seedPrf Hq seed) layer e msg)
      (IsTrialQuery (addrMsg layer e) k) 0 :=
  isQueryBoundP_bind_zero _ _ (isQueryBoundP_queryH_of_ne k pp _
    (encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide))) fun _ => isQueryBoundP_pure _ _ _

/-- **A key's one-time signature finds no codeword with probability at most `exp(-4000)`.**

The cache holds no trial input of the key: no input at its message address of the trial length. -/
theorem prEvent_otsSign_none_le (pp : PublicParam) (seed : Seed) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (cache : XmssSecurity.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery (addrMsg layer e) (msg.size + 16)) cache) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (otsSign Hq pp (seedPrf Hq seed) layer e msg)).run' cache}[z = none]
      ≤ ENNReal.ofReal (Real.exp (-4000)) := by
  unfold otsSign
  refine prEvent_run'_romImpl_bind_le (CacheAvoids (IsTrialQuery (addrMsg layer e) (msg.size + 16)))
    _ _ _ (fun z hz => cache_eq_none_of_mem_support_run_romImpl
      (randomizerBase_isQueryBoundP pp seed layer e msg _) hcache hz) fun base c hc => ?_
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun z => z.1 = none) _ fun z _ hz => ?_).trans ?_
  · rcases z with ⟨_ | ⟨rho, x⟩, c'⟩
    · exact absurd rfl hz
    · dsimp only
      rw [← bind_assoc]
      exact prEvent_run'_romImpl_bind_pure_some _ (fun y => (rho, y)) _
  · rw [prEvent_run_romImpl_fst _ _ fun r => r = none]
    refine prEvent_findCodeword_none_le pp layer e msg base c fun j _ => hc _ ⟨pp, _, ?_, rfl⟩
    rw [ByteArray.size_append, Base.size_packBytes]
    rfl

/-- **A layer's signature fails with probability at most `exp(-4000)`.**

The cache holds no trial input of the layer's key. -/
theorem prEvent_signLayer_error_le (pp : PublicParam) (seed : Seed) (layer : Layer) (e : Nat)
    (msg : ByteArray) (cache : XmssSecurity.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery (addrMsg layer (UInt32.ofNat e)) (msg.size + 16)) cache) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signLayer Hq pp (seedPrf Hq seed) layer e msg)).run' cache}[z.isOk = false]
      ≤ ENNReal.ofReal (Real.exp (-4000)) := by
  unfold signLayer
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun z => z.1 = none) _ fun z _ hz => ?_).trans ?_
  · rcases z with ⟨_ | ⟨rho, y⟩, c'⟩
    · exact absurd rfl hz
    · dsimp only
      exact prEvent_run'_romImpl_bind_pure_ok _ _ _
  · rw [prEvent_run_romImpl_fst _ _ fun r => r = none]
    exact prEvent_otsSign_none_le pp seed layer _ msg cache hcache

/-! ## A whole signature fails rarely -/

/-- The two layers differ. -/
theorem bottom_ne_top : Layer.bottom ≠ Layer.top := by decide

/-- The trial queries of the bottom key of leaf index `idx`: 32-byte message, 16-byte trial. -/
abbrev IsBottomTrialQuery (idx : LeafIndex) : XmssSecurity.OracleWorld.Domain → Prop :=
  IsTrialQuery (addrMsg .bottom idx) 48

/-- The trial queries of the top key above leaf index `idx`: 16-byte root, 16-byte trial. -/
abbrev IsTopTrialQuery (idx : LeafIndex) : XmssSecurity.OracleWorld.Domain → Prop :=
  IsTrialQuery (addrMsg .top (UInt32.ofNat (bottomTree idx))) 32

/- A concrete height would let Lean unfold a whole tree, so the height stays opaque. -/
attribute [local irreducible] LAYER_HEIGHT

/-- **Signing from the derivations fails with probability at most `2 exp(-4000)`.**

The cache holds no trial input of the bottom key nor of the top key. -/
theorem prEvent_signDerived_error_le (s : Seed) (pp : PublicParam) (idx : LeafIndex)
    (msg : Message) (cache : XmssSecurity.HashSpec.QueryCache)
    (hbottom : CacheAvoids (IsBottomTrialQuery idx) cache)
    (htop : CacheAvoids (IsTopTrialQuery idx) cache) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signDerived Hq (seedPrf Hq s) pp idx msg)).run' cache}[z.isOk = false]
      ≤ 2 * ENNReal.ofReal (Real.exp (-4000)) := by
  unfold signDerived
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support _ _
    (fun z => z.1.isOk = false) _ (ε := ENNReal.ofReal (Real.exp (-4000)))
    fun z hz hok => ?_).trans ?_
  · -- The bottom layer signed; the top layer's trial inputs are still fresh.
    rcases z with ⟨_ | sig, c⟩
    · exact absurd rfl hok
    have hc : CacheAvoids (IsTopTrialQuery idx) c := cache_eq_none_of_mem_support_run_romImpl
      (signLayer_isQueryBoundP_otherLayer bottom_ne_top _ _ _ _ _ _) htop hz
    dsimp only
    simp only [pure_bind]
    refine prEvent_run'_romImpl_bind_le (CacheAvoids (IsTopTrialQuery idx)) _ _ _ ?_
      fun root c' hc' => ?_
    · intro z hz
      exact cache_eq_none_of_mem_support_run_romImpl
        (node_isQueryBoundP_otherLayer bottom_ne_top _ _ _ _ _ _) hc hz
    rw [run'_simulateQ_romImpl_bind]
    refine (prEvent_bind_le_prEvent_of_support _ _ (fun z => z.1.isOk = false) _
      fun z _ hz => ?_).trans ?_
    · rcases z with ⟨_ | sig', c''⟩
      · exact absurd rfl hz
      · simp [Except.isOk, Except.toBool]
    · rw [prEvent_run_romImpl_fst _ _ fun r : Except XmssError LayerSignature => r.isOk = false]
      refine prEvent_signLayer_error_le pp s .top _ _ c' ?_
      rwa [Base.size_packBytes]
  · -- The bottom layer fails rarely, and the top layer after it.
    rw [prEvent_run_romImpl_fst _ _ fun r : Except XmssError LayerSignature => r.isOk = false,
      two_mul]
    refine add_le_add (prEvent_signLayer_error_le pp s .bottom _ _ cache ?_)
      (mul_le_of_le_one_right' (prEvent_le_one _))
    have hsize : (packBytes msg).size + 16 = 48 := by
      rw [Base.size_packBytes]
      rfl
    rw [hsize, UInt32.ofNat_toNat]
    exact hbottom

/-- The input that grows the scheme seed has 40 bytes: 8 for the name, 32 for the seed. -/
theorem size_schemeSeedInput (seed : Seed) :
    (ByteArray.mk SEED_TAG.toArray ++ packBytes seed).size = 40 := by
  rw [ByteArray.size_append, Base.size_packBytes, seed_tag_eq]
  rfl

/-- Growing the scheme seed is not a trial query of a key with a payload of more than 8 bytes. -/
theorem schemeSeed_isQueryBoundP (seed : Seed) (A : Address) {k : Nat} (hk : 8 < k) :
    IsQueryBoundP (schemeSeed Hq seed) (IsTrialQuery A k) 0 :=
  isQueryBoundP_queryH_of_size (by rw [size_schemeSeedInput]; omega)

/-- The public parameter is not a trial query of any key. -/
theorem publicParamOf_isQueryBoundP (s : Seed) (layer : Layer) (e : UInt32) (k : Nat) :
    IsQueryBoundP (publicParamOf (seedPrf Hq s)) (IsTrialQuery (addrMsg layer e) k) 0 :=
  isQueryBoundP_bind_zero _ _ (isQueryBoundP_queryH_of_ne k _ _
    (encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide))) fun _ => isQueryBoundP_pure _ _ _

/-- **A leanXMSS signature fails with probability at most `2 exp(-4000)`.**

The hash is a lazily sampled random oracle, and signing starts from any cache.

The cache must hold no trial input of the two keys that sign:

- the bottom key `idx`: inputs at its message address with a 48-byte payload;
- the top key above it: inputs at its message address with a 32-byte payload.

Each layer's search then fails with probability at most `exp(-4000)`. -/
theorem prEvent_signWith_error_le (sk : SecretKey) (idx : LeafIndex) (msg : Message)
    (cache : XmssSecurity.HashSpec.QueryCache)
    (hbottom : CacheAvoids (IsBottomTrialQuery idx) cache)
    (htop : CacheAvoids (IsTopTrialQuery idx) cache) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signWith Hq sk idx msg)).run' cache}[z.isOk = false]
      ≤ 2 * ENNReal.ofReal (Real.exp (-4000)) := by
  unfold signWith
  refine prEvent_run'_romImpl_bind_le (fun c => CacheAvoids (IsBottomTrialQuery idx) c ∧
    CacheAvoids (IsTopTrialQuery idx) c) _ _ _ ?_ fun s c hc => ?_
  · exact fun z hz =>
      ⟨cache_eq_none_of_mem_support_run_romImpl (schemeSeed_isQueryBoundP _ _ (by decide))
        hbottom hz,
      cache_eq_none_of_mem_support_run_romImpl (schemeSeed_isQueryBoundP _ _ (by decide))
        htop hz⟩
  refine prEvent_run'_romImpl_bind_le (fun c => CacheAvoids (IsBottomTrialQuery idx) c ∧
    CacheAvoids (IsTopTrialQuery idx) c) _ _ _ ?_
    fun pp c' hc' => prEvent_signDerived_error_le s pp idx msg c' hc'.1 hc'.2
  exact fun z hz =>
    ⟨cache_eq_none_of_mem_support_run_romImpl (publicParamOf_isQueryBoundP _ _ _ _) hc.1 hz,
    cache_eq_none_of_mem_support_run_romImpl (publicParamOf_isQueryBoundP _ _ _ _) hc.2 hz⟩

/-- From an empty cache, a leanXMSS signature fails with probability at most `2 exp(-4000)`. -/
theorem prEvent_signWith_error_le_empty (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signWith Hq sk idx msg)).run' ∅}[z.isOk = false]
      ≤ 2 * ENNReal.ofReal (Real.exp (-4000)) :=
  prEvent_signWith_error_le sk idx msg ∅ (fun _ _ => rfl) fun _ _ => rfl

end EthLib.Cryptography.Xmss
