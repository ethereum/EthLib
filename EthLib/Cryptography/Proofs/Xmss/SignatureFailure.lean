module

public import EthLib.Cryptography.Proofs.Xmss.Constants
public import EthLib.Cryptography.Proofs.QueryAvoidance
public import EthLib.Cryptography.Proofs.Xmss.Address
public import EthLib.Cryptography.Proofs.Xmss.CodewordSearch
public import EthLib.Cryptography.Xmss.Sign

/-!
# Proofs: a whole signature rarely fails, in the random-oracle model

A signature signs on two layers, and each layer searches for a codeword.

Signing fails when either search finds none.

Each search hashes at its key's message call site, with a payload of one fixed length.

Before a search, the signer hashes no such input.

The calls before it have other call sites.

So a cache that holds no trial input of either key keeps none until its search starts.

Each search then fails with probability at most `exp(-4000)`, and signing at most twice that.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.Xmss.Internal (signRootWith cacheTreeWith fetchTreeWith)
open OracleSpec OracleComp ENNReal

/-- The hash as a query to the random oracle of the game. -/
local notation "Hq" => Unforgeability.queryH (m := OracleComp XmssSecurity.OracleWorld)

/-! ## Trial inputs -/

/-- A query of an input at a given call site whose payload has `k` lanes, `8 k` bytes.

A key's codeword search queries only such inputs, at its message call site. -/
def IsTrialQuery (A : CallSite) (k : Nat) : XmssSecurity.OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr x => ∃ publicParam payload, payload.size = k ∧ x = Hash.Keccak.lanesBytes
    (thInput publicParam A payload)

noncomputable instance (A : CallSite) (k : Nat) : DecidablePred (IsTrialQuery A k) :=
  Classical.decPred _

/-- An input `P | A | M` has `4` lanes before its payload. -/
theorem size_thInput (publicParam : PublicParam) (A : CallSite) (payload : Array UInt64) :
    (thInput publicParam A payload).size = 4 + payload.size := by
  rw [thInput, Array.size_append]
  rfl

/-- A hash at another call site is not a trial query. -/
theorem isQueryBoundP_queryH_of_ne {A A' : CallSite} (k : Nat) (publicParam : PublicParam)
    (payload : Array UInt64) (hA : A' ≠ A) :
    IsQueryBoundP (Hq (thInput publicParam A' payload)) (IsTrialQuery A k) 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  obtain ⟨_, _, _, heq⟩ := h
  exact absurd (thInput_inj (Hash.Keccak.lanesBytes_injective heq)).2.1 hA

/-! ## A layer never queries the other layer's trial inputs -/

section OtherLayer

variable {layer layer' : Layer} (hl : layer ≠ layer') (e' : UInt32) (k : Nat)
include hl

/-- A hash at a call site of the layer is not a trial query of the other layer.

The layer's flag in `hi` differs from the other layer's.

So the call site is not the message call site of a key of the other layer. -/
theorem th_isQueryBoundP_otherLayer (publicParam : PublicParam) (site : CallSite) {a : Fin (2 ^ 23)}
    (hsite : site.hi = layerHi layer a) (payload : Array UInt64) :
    IsQueryBoundP (th Hq publicParam site payload) (IsTrialQuery (CallSite.msg layer' e') k) 0 :=
  isQueryBoundP_bind_zero _ _
    (isQueryBoundP_queryH_of_ne k publicParam payload (CallSite.ne_msg_of_hi hsite hl e'))
    fun _ => isQueryBoundP_pure _ _ _

/-- A key's chain starts query no trial input of the other layer. -/
theorem chainStarts_isQueryBoundP_otherLayer (publicParam : PublicParam)
    (seed : Seed) (e : UInt32) :
    IsQueryBoundP (chainStarts publicParam (seedPrf Hq seed) layer e)
      (IsTrialQuery (CallSite.msg layer' e') k) 0 :=
  isQueryBoundP_bind_zero _ _
    (ofFnInOrder_isQueryBoundP_zero _ _ fun _ => isQueryBoundP_queryH_of_ne k publicParam _
      (CallSite.ne_msg_of_hi rfl hl e'))
    fun _ => isQueryBoundP_pure _ _ _

/-- A walk along a key's chain queries no trial input of the other layer. -/
theorem chain_isQueryBoundP_otherLayer (publicParam : PublicParam) (e : UInt32) (i : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    IsQueryBoundP (chain Hq publicParam layer e i start steps h value)
      (IsTrialQuery (CallSite.msg layer' e') k) 0 :=
  chain_isQueryBoundP_zero _ (fun _ _ => th_isQueryBoundP_otherLayer hl e' k _ _ rfl _) _ _ _ _

/-- A key's leaf, from the seed, queries no trial input of the other layer. -/
theorem otsPublicLeaf_isQueryBoundP_otherLayer (publicParam : PublicParam)
    (seed : Seed) (e : UInt32) :
    IsQueryBoundP (otsPublicLeaf Hq publicParam (seedPrf Hq seed) layer e)
      (IsTrialQuery (CallSite.msg layer' e') k) 0 :=
  isQueryBoundP_bind_zero _ _
    (chainStarts_isQueryBoundP_otherLayer hl e' k publicParam seed e) fun _ =>
    isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
      chain_isQueryBoundP_otherLayer hl e' k _ _ _ _ _ _ _) fun _ =>
      th_isQueryBoundP_otherLayer hl e' k _ _ rfl _

/-- A node hash of the layer queries no trial input of the other layer. -/
theorem nodeHash_isQueryBoundP_otherLayer (publicParam : PublicParam) (q : Merkle.Position)
    (left right : Digest) :
    IsQueryBoundP (nodeHash Hq publicParam layer q left right)
      (IsTrialQuery (CallSite.msg layer' e') k) 0 :=
  th_isQueryBoundP_otherLayer hl e' k _ _ rfl _

/-- A node of the layer queries no trial input of the other layer. -/
theorem node_isQueryBoundP_otherLayer (publicParam : PublicParam) (seed : Seed) (level j : Nat) :
    IsQueryBoundP (node Hq publicParam (seedPrf Hq seed) layer level j)
      (IsTrialQuery (CallSite.msg layer' e') k) 0 :=
  merkleNode_isQueryBoundP_zero _ _
    (fun _ => otsPublicLeaf_isQueryBoundP_otherLayer hl e' k _ _ _)
    (fun _ _ _ => nodeHash_isQueryBoundP_otherLayer hl e' k _ _ _ _) _

/-- A build of the layer queries no trial input of the other layer. -/
theorem build_isQueryBoundP_otherLayer (publicParam : PublicParam) (seed : Seed) (level j : Nat) :
    IsQueryBoundP (build Hq publicParam (seedPrf Hq seed) layer level j)
      (IsTrialQuery (CallSite.msg layer' e') k) 0 :=
  merkleBuild_isQueryBoundP_zero _ _
    (fun _ => otsPublicLeaf_isQueryBoundP_otherLayer hl e' k _ _ _)
    (fun _ _ _ => nodeHash_isQueryBoundP_otherLayer hl e' k _ _ _ _) _

/-- The codeword search of a key on the layer queries no trial input of the other layer. -/
theorem findCodeword_isQueryBoundP_otherLayer (publicParam : PublicParam) (e : UInt32)
    (msg : Array UInt64)
    (base : Randomizer) (c fuel : Nat) :
    IsQueryBoundP (Internal.findCodeword Hq publicParam layer e msg base c fuel)
      (IsTrialQuery (CallSite.msg layer' e') k) 0 := by
  rw [Internal.findCodeword_eq]
  exact findFirst_isQueryBoundP_zero _ _ (fun _ => isQueryBoundP_map_iff _ _ _ |>.2
    (th_isQueryBoundP_otherLayer hl e' k _ _ rfl _)) _ _

/-- A one-time signature on the layer queries no trial input of the other layer. -/
theorem otsSign_isQueryBoundP_otherLayer (publicParam : PublicParam) (seed : Seed) (e : UInt32)
    (msg : Array UInt64) :
    IsQueryBoundP (otsSign Hq publicParam (seedPrf Hq seed) layer e msg)
      (IsTrialQuery (CallSite.msg layer' e') k) 0 := by
  refine isQueryBoundP_bind_zero _ _ (th_isQueryBoundP_otherLayer hl e' k _ _ rfl _)
    fun base => isQueryBoundP_bind_zero _ _
      (findCodeword_isQueryBoundP_otherLayer hl e' k _ _ _ _ _ _) fun r => ?_
  rcases r with _ | ⟨rho, x⟩
  · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_bind_zero _ _ (chainStarts_isQueryBoundP_otherLayer hl e' k _ _ _)
      fun _ => isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
        chain_isQueryBoundP_otherLayer hl e' k _ _ _ _ _ _ _) fun _ => isQueryBoundP_pure _ _ _

end OtherLayer

/-! ## One layer fails rarely -/

/-- The randomizer base is not a trial query of its own key. -/
theorem randomizerBase_isQueryBoundP (publicParam : PublicParam) (seed : Seed) (layer : Layer)
    (e : UInt32) (msg : Array UInt64) (k : Nat) :
    IsQueryBoundP (randomizerBase publicParam (seedPrf Hq seed) layer e msg)
      (IsTrialQuery (CallSite.msg layer e) k) 0 :=
  isQueryBoundP_bind_zero _ _ (isQueryBoundP_queryH_of_ne k publicParam _
    fun h => nomatch h) fun _ => isQueryBoundP_pure _ _ _

/-- **A key's one-time signature finds no codeword with probability at most `exp(-4000)`.**

The cache holds no trial input of the key: no input at its message call site of the trial length. -/
theorem prEvent_otsSign_none_le (publicParam : PublicParam) (seed : Seed)
    (layer : Layer) (e : UInt32)
    (msg : Array UInt64) (cache : XmssSecurity.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery (CallSite.msg layer e) (msg.size + 2)) cache) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (otsSign Hq publicParam (seedPrf Hq seed) layer e msg)).run' cache}[z = none]
      ≤ ENNReal.ofReal (Real.exp (-4000)) := by
  unfold otsSign Internal.otsSignTrials
  refine prEvent_run'_romImpl_bind_le
    (CacheAvoids (IsTrialQuery (CallSite.msg layer e) (msg.size + 2))) _ _ _
    (fun z hz => cache_eq_none_of_mem_support_run_romImpl
      (randomizerBase_isQueryBoundP publicParam seed layer e msg _) hcache hz) fun base c hc => ?_
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun z => z.1 = none) _ fun z _ hz => ?_).trans ?_
  · rcases z with ⟨_ | ⟨rho, x⟩, c'⟩
    · exact absurd rfl hz
    · dsimp only
      rw [← bind_assoc]
      exact prEvent_run'_romImpl_bind_pure_some _ (fun y => (rho, y)) _
  · rw [prEvent_run_romImpl_fst _ _ fun r => r = none]
    refine prEvent_findCodeword_none_le publicParam layer e msg base c fun j _ => hc _
      ⟨publicParam, _, ?_, rfl⟩
    rw [Array.size_append]
    rfl

/-! ## A whole signature fails rarely -/

/-- The two layers differ. -/
theorem bottom_ne_top : Layer.bottom ≠ Layer.top := by decide

/-- The trial queries of the bottom key of leaf index `idx`: 32-byte message, 16-byte trial. -/
abbrev IsBottomTrialQuery (idx : LeafIndex) : XmssSecurity.OracleWorld.Domain → Prop :=
  IsTrialQuery (CallSite.msg .bottom idx) 6

/-- The trial queries of the top key above leaf index `idx`: 16-byte root, 16-byte trial. -/
abbrev IsTopTrialQuery (idx : LeafIndex) : XmssSecurity.OracleWorld.Domain → Prop :=
  IsTrialQuery (CallSite.msg .top (UInt32.ofNat (bottomTree idx))) 4

/- A concrete height would let Lean unfold a whole tree, so the height stays opaque. -/
attribute [local irreducible] LAYER_HEIGHT

/-! ## The specification's signer fails rarely -/

/-- **The top key's signature of a root fails with probability at most `exp(-4000)`.**

The cache holds no trial input of the top key. -/
theorem prEvent_signRootWith_error_le (sk : SecretKey) (b : Nat) (root : Digest)
    (cache : XmssSecurity.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery (CallSite.msg .top (UInt32.ofNat b)) 4) cache) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signRootWith Hq (seedPrf Hq sk.schemeSeed) sk b root)).run' cache}[z.isOk = false]
      ≤ ENNReal.ofReal (Real.exp (-4000)) := by
  unfold signRootWith
  simp only [Internal.otsSignTrials_hashTrials]
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun z => z.1 = none) _ fun z _ hz => ?_).trans ?_
  · rcases z with ⟨_ | ⟨rho, y⟩, c'⟩
    · exact absurd rfl hz
    · simp [Except.isOk, Except.toBool]
  · rw [prEvent_run_romImpl_fst _ _ fun r => r = none]
    refine prEvent_otsSign_none_le _ _ .top _ _ cache ?_
    exact hcache

/-- **A leanXMSS signature fails with probability at most `2 exp(-4000)`.**

The hash is a lazily sampled random oracle, and signing starts from any cache and any key.

The cache must hold no trial input of the two keys that sign:

- the bottom key `idx`: inputs at its message call site with a payload of 6 lanes, 48 bytes;
- the top key above it: inputs at its message call site with a payload of 4 lanes, 32 bytes.

A bottom tree of `idx` that the key keeps must hold a top signature, not an error.

Each layer's search then fails with probability at most `exp(-4000)`. -/
theorem prEvent_signWith_error_le (sk : SecretKey) (idx : LeafIndex) (msg : Message)
    (cache : XmssSecurity.HashSpec.QueryCache)
    (hbottom : CacheAvoids (IsBottomTrialQuery idx) cache)
    (htop : CacheAvoids (IsTopTrialQuery idx) cache)
    (hkept : ∀ t ∈ sk.cache, t.index = bottomTree idx → t.top.isOk = true) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signWith Hq sk idx msg)).run' cache}[z.1.isOk = false]
      ≤ 2 * ENNReal.ofReal (Real.exp (-4000)) := by
  unfold signWith Internal.signWithTrials
  simp only [Internal.otsSignTrials_hashTrials]
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support _ _
    (fun z => z.1 = none) _ (ε := ENNReal.ofReal (Real.exp (-4000)))
    fun z hz hok => ?_).trans ?_
  · -- The bottom key signed; the top layer's trial inputs are still fresh.
    rcases z with ⟨_ | ⟨rho, y⟩, c⟩
    · exact absurd rfl hok
    have hc : CacheAvoids (IsTopTrialQuery idx) c := cache_eq_none_of_mem_support_run_romImpl
      (otsSign_isQueryBoundP_otherLayer bottom_ne_top _ _ _ _ _ _) htop hz
    dsimp only
    unfold fetchTreeWith
    split
    · -- A kept tree holds a top signature, and no hash is called.
      next t ht =>
      have htok : t.top.isOk = true :=
        hkept t (List.mem_of_find?_eq_some ht) (by simpa using List.find?_some ht)
      rw [pure_bind]
      cases htt : t.top with
      | ok top => simp [Except.isOk, Except.toBool]
      | error err => rw [htt] at htok; cases htok
    · -- A new tree: its build, then the top key's search.
      unfold cacheTreeWith
      simp only [bind_assoc, pure_bind]
      refine prEvent_run'_romImpl_bind_le (CacheAvoids (IsTopTrialQuery idx)) _ _ _ ?_
        fun tree c' hc' => ?_
      · intro z hz
        exact cache_eq_none_of_mem_support_run_romImpl
          (build_isQueryBoundP_otherLayer bottom_ne_top _ _ _ _ _ _) hc hz
      rw [run'_simulateQ_romImpl_bind]
      refine (prEvent_bind_le_prEvent_of_support _ _ (fun z => z.1.isOk = false) _
        fun z _ hz => ?_).trans ?_
      · rcases z with ⟨_ | top, c''⟩
        · exact absurd rfl hz
        · simp [Except.isOk, Except.toBool]
      · rw [prEvent_run_romImpl_fst _ _ fun r : Except XmssError LayerSignature => r.isOk = false]
        exact prEvent_signRootWith_error_le sk _ _ c' hc'
  · -- The bottom key fails rarely, and the top layer after it.
    rw [prEvent_run_romImpl_fst _ _ fun r => r = none, two_mul]
    refine add_le_add (prEvent_otsSign_none_le _ _ .bottom _ _ cache ?_)
      (mul_le_of_le_one_right' (prEvent_le_one _))
    have hsize : msg.toArray.size + 2 = 6 := by
      rfl
    rw [hsize, UInt32.ofNat_toNat]
    exact hbottom

/-- From an empty cache, a leanXMSS signature fails with probability at most `2 exp(-4000)`.

A bottom tree of `idx` that the key keeps must hold a top signature.

A key of key generation keeps no bottom tree. -/
theorem prEvent_signWith_error_le_empty (sk : SecretKey) (idx : LeafIndex) (msg : Message)
    (hkept : ∀ t ∈ sk.cache, t.index = bottomTree idx → t.top.isOk = true) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signWith Hq sk idx msg)).run' ∅}[z.1.isOk = false]
      ≤ 2 * ENNReal.ofReal (Real.exp (-4000)) :=
  prEvent_signWith_error_le sk idx msg ∅ (fun _ _ => rfl) (fun _ _ => rfl) hkept

end EthLib.Cryptography.Xmss
