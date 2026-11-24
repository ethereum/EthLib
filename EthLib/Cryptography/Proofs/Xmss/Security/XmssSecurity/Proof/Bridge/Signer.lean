module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Real
public import EthLib.Cryptography.Proofs.Xmss.MapMonad
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Adversary

/-!
# EthLib's signer under the prepared cache

EthLib's signer, with a key the prepared cache knows, is the model's table signer.

So signing erases to the values the model's key stores, and returns a key the cache knows.
-/

@[expose] public section

open OracleComp OracleSpec
open EthLib.Cryptography
open EthLib.Cryptography.Xmss.Constants (V CHAIN_LENGTH LAYER_HEIGHT MAX_RANDOMIZER_TRIALS)
open EthLib.Cryptography.Xmss.Unforgeability (queryH ofParam ofSeed ofDigest ofOutput ofChains
  ofLeafIndex ofTopIndex ofMessage ofRandomizer ofEncoding ofPath ofLayerSig ofSignature chainOf
  toLeafIndex)

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

/-- A query to the oracle, as the query and the four lanes of its answer. -/
theorem queryH_eq (x : Array UInt64) :
    (queryH x : OracleComp HashSpec Hash.Keccak.Lanes4)
      = liftM (HashSpec.query (Hash.Keccak.lanesBytes x)) >>= fun y => pure (ofOutput y) := by
  unfold queryH HashSig.queryLanes
  rw [map_eq_bind_pure_comp]
  rfl

/-- The first half of an answer, read as a randomizer. -/
theorem halfOf_zero_ofOutput_randomizer (y : HashOutput) :
    (Xmss.halfOf 0 (ofOutput y) : Xmss.Randomizer)
      = ofRandomizer (y.extractLsb' 0 randomnessBits) := by
  rw [Xmss.Unforgeability.halfOf_zero_ofOutput]
  rfl

/-- The randomizer base is one query, its answer's first half read as a randomizer.

Stated at the randomizer's type, so later binds associate with it. -/
theorem randomizerBase_queryH (publicParam : Xmss.PublicParam) (s : Xmss.Seed) (layer : Xmss.Layer)
    (e : UInt32) (msg : Array UInt64) :
    (Xmss.randomizerBase publicParam (Xmss.seedPrf queryH s) layer e msg :
      OracleComp HashSpec Xmss.Randomizer)
      = liftM (HashSpec.query
          (Hash.Keccak.lanesBytes
            (Xmss.thInput publicParam (Xmss.Address.rnd layer e) (s.toArray ++ msg)))) >>=
        fun y => pure (ofRandomizer (y.extractLsb' 0 randomnessBits)) := by
  rw [Xmss.randomizerBase_seedPrf]
  unfold Xmss.th
  simp only [queryH_eq, bind_assoc, pure_bind]
  refine bind_congr fun y => ?_
  exact congrArg pure (halfOf_zero_ofOutput_randomizer y)

/-- The bottom randomizer base `R0(idx, m)` is the bottom derivation's input. -/
theorem rndInput_toList (P : PublicParameter) (seed : MasterSeed) (index : LeafIndex)
    (message : Message) :
    Hash.Keccak.lanesBytes (Xmss.thInput (ofParam P) (Xmss.Address.rnd .bottom (ofLeafIndex index))
      ((ofSeed seed).toArray ++ (ofMessage message).toArray))
      = rndInput P seed ⟨index, message⟩ := by
  rw [rndInput_eq]
  simp only [Xmss.thInput_eq_append,
    EthLib.Cryptography.Hash.Keccak.lanesBytes_append, Xmss.Unforgeability.toList_ofParam,
    Xmss.Unforgeability.toList_ofSeed, Xmss.Unforgeability.toList_ofMessage,
    Xmss.Unforgeability.toList_encode_rnd, Xmss.Unforgeability.toNat_ofLeafIndex]
  -- The bottom layer adds no flag to `hi`.
  exact congrArg (fun x => bytesLE 16 P ++ fieldBytes (tweakFields 7 0 x index.val) ++
    (bytesLE 32 seed ++ bytesLE 32 message)) (by simp [Xmss.Layer.toNat])

/-- The top randomizer base `R0_top(b, r)` is the top derivation's input. -/
theorem topRndInput_toList (P : PublicParameter) (seed : MasterSeed) (key : TopIndex)
    (root : Digest) :
    Hash.Keccak.lanesBytes (Xmss.thInput (ofParam P) (Xmss.Address.rnd .top (ofTopIndex key))
      ((ofSeed seed).toArray ++ (ofDigest root).toArray))
      = topRndInput P seed (key, root) := by
  rw [topRndInput_eq]
  simp only [Xmss.thInput_eq_append,
    EthLib.Cryptography.Hash.Keccak.lanesBytes_append, Xmss.Unforgeability.toList_ofParam,
    Xmss.Unforgeability.toList_ofSeed, Xmss.Unforgeability.toList_ofDigest,
    Xmss.Unforgeability.toList_encode_rnd, Xmss.Unforgeability.toNat_ofTopIndex]
  -- The top layer adds its flag to `hi`.
  exact congrArg (fun x => bytesLE 16 P ++ fieldBytes (tweakFields 7 0 x key.val) ++
    (bytesLE 32 seed ++ bytesLE 16 root)) (by simp [Xmss.Layer.toNat, topFlag])

/-- The bottom search is the table signer's trials, whatever follows each. -/
theorem erases_findCodeword_bottom {β : Type} (cache : QueryCache HashSpec)
    (sk : XmssSecurity.SecretKey) (index : LeafIndex) (message : Message) (base : Randomness)
    (K : Option (Xmss.Randomizer × Vector (Fin CHAIN_LENGTH) V) → OracleComp HashSpec β)
    (K' : Option Signature → OracleComp HashSpec β) (hnone : Erases cache (K none) (K' none))
    (hsome : ∀ rho enc, Erases cache (K (some (ofRandomizer rho, ofEncoding enc)))
      (K' (some (Concrete.precomputedSignWithEncoding sk index rho enc)))) :
    ∀ fuel trial, Erases cache
      (Xmss.Internal.findCodeword queryH (ofParam sk.parameter) .bottom (ofLeafIndex index)
        ((ofMessage message).toArray) (ofRandomizer base) trial fuel >>= K)
      (tableSignFrom base sk index message fuel trial >>= K')
  | 0, _ => by simpa [Xmss.Internal.findCodeword_eq, Wots.findFirst, tableSignFrom] using hnone
  | fuel + 1, trial => by
    rw [Xmss.Internal.findCodeword_eq]
    unfold Wots.findFirst tableSignFrom
    simp only [Xmss.Unforgeability.trialRandomizer_ofRandomizer,
      Xmss.Unforgeability.messageDigest_bottom, Concrete.precomputedSignAttempt, bind_assoc,
      bind_map_left]
    refine (Erases.refl _ _).bind _ _ fun digest => ?_
    rw [Xmss.Unforgeability.codeword?_ofDigest]
    cases TargetSum.decodeDigest digest with
    | none =>
      simpa [Xmss.Internal.findCodeword_eq] using
        erases_findCodeword_bottom cache sk index message base K K' hnone hsome fuel (trial + 1)
    | some enc => simpa using hsome _ enc

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec}

theorem xor_one_lt {n k : Nat} (hn : n < 2 ^ k) (hk : 1 ≤ k) : Nat.xor n 1 < 2 ^ k :=
  Nat.xor_lt_two_pow hn (Nat.one_lt_two_pow (by omega))

/-- The top search of a bottom root resolves to the key's top signature. -/
theorem realTopFind (h : Prepared seed d result cache) (key : TopIndex) (base : Randomness)
    (res : Option (Randomness × Encoding)) :
    ∀ fuel trial,
      Resolves cache (Concrete.topSignFrom d.parameter key (h.root key) base fuel trial) res →
      Resolves cache (Xmss.Internal.findCodeword queryH (ofParam d.parameter) .top (ofTopIndex key)
          ((ofDigest (h.root key)).toArray) (ofRandomizer base) trial fuel :
          OracleComp HashSpec _)
        (res.map fun p => (ofRandomizer p.1, ofEncoding p.2))
  | 0, _, hmodel => by
    rw [← hmodel.pure_inv]
    exact .pure _
  | fuel + 1, trial, hmodel => by
    rw [Concrete.topSignFrom] at hmodel
    rw [Xmss.Internal.findCodeword_eq]
    unfold Wots.findFirst
    simp only [Xmss.Unforgeability.trialRandomizer_ofRandomizer,
      Xmss.Unforgeability.messageDigest_top, bind_map_left]
    obtain ⟨digest, hdigest, hrest⟩ := hmodel.of_bind
    refine hdigest.bind ?_
    rw [Xmss.Unforgeability.codeword?_ofDigest]
    cases hdec : TargetSum.decodeDigest digest with
    | none =>
      rw [hdec] at hrest
      have next := realTopFind h key base res fuel (trial + 1) hrest
      rwa [Xmss.Internal.findCodeword_eq] at next
    | some encoding =>
      rw [hdec] at hrest
      rw [← hrest.pure_inv]
      exact .pure _

/-- A top key's chains, opened at a codeword, resolve to the key's stored values. -/
theorem realTopChains (h : Prepared seed d result cache) (key : TopIndex) (encoding : Encoding) :
    Resolves cache (Xmss.ofFnInOrder V fun i => Xmss.chain queryH (ofParam d.parameter) .top
        (ofTopIndex key) i 0 (ofEncoding encoding)[i] (by simp)
        (ofChains (d.topSecret key))[i] : OracleComp HashSpec _)
      (ofChains fun chain => (modelSecretKey d result).topChainValue key chain (encoding chain)) :=
  Resolves.ofFnInOrder fun i => by
    rw [show (ofChains (d.topSecret key))[i] = ofDigest (d.topSecret key (chainOf i)) from
      Vector.getElem_ofFn _, Xmss.Unforgeability.chain_top]
    rw [show ((ofEncoding encoding)[i] : Nat) = (encoding (chainOf i)).val from
      congrArg Fin.val (Vector.getElem_ofFn _)]
    exact (h.topChain key (chainOf i) (encoding (chainOf i))).map _

/-- A bottom key's chains, opened at a codeword, resolve to the key's stored values. -/
theorem realBottomChains (h : Prepared seed d result cache) (index : LeafIndex)
    (encoding : Encoding) :
    Resolves cache (Xmss.ofFnInOrder V fun i => Xmss.chain queryH (ofParam d.parameter) .bottom
        (ofLeafIndex index) i 0 (ofEncoding encoding)[i] (by simp)
        (ofChains (d.secret index))[i] : OracleComp HashSpec _)
      (ofChains fun chain => (modelSecretKey d result).chainValue index chain (encoding chain)) :=
  Resolves.ofFnInOrder fun i => by
    rw [show (ofChains (d.secret index))[i] = ofDigest (d.secret index (chainOf i)) from
      Vector.getElem_ofFn _, Xmss.Unforgeability.chain_bottom]
    rw [show ((ofEncoding encoding)[i] : Nat) = (encoding (chainOf i)).val from
      congrArg Fin.val (Vector.getElem_ofFn _)]
    exact (h.chain index (chainOf i) (encoding (chainOf i))).map _

/-- A top key's path resolves to the key's stored nodes. -/
theorem realTopPath (h : Prepared seed d result cache) (key : TopIndex) :
    Resolves cache (Xmss.path queryH (ofParam d.parameter) (realPrf seed) .top key.val :
        OracleComp HashSpec _)
      (ofPath fun level =>
        (modelSecretKey d result).topTreeValue level.castSucc
          (Concrete.topPathNode key level)) := by
  rw [Xmss.path_eq_ofFnInOrder]
  refine Resolves.ofFnInOrder fun level => ?_
  have hlevel : level.val < 16 := level.isLt
  have hb : key.val / 2 ^ level.val < 2 ^ (16 - level.val) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
      show 16 - level.val + level.val = 16 by omega]
    exact lt_of_lt_of_eq key.isLt (by norm_num [topLifetime, treeHeight])
  exact h.realTopNode level.val (by omega) _ (xor_one_lt hb (by omega))

/-- A bottom key's path resolves to the key's stored nodes. -/
theorem realBottomPath (h : Prepared seed d result cache) (index : LeafIndex) :
    Resolves cache (Xmss.path queryH (ofParam d.parameter) (realPrf seed) .bottom index.val :
        OracleComp HashSpec _)
      (ofPath fun level => (modelSecretKey d result).treeValue level.castSucc
        (Concrete.authenticationPathNode index level)) := by
  rw [Xmss.path_eq_ofFnInOrder]
  refine Resolves.ofFnInOrder fun level => ?_
  have hlevel : level.val < 16 := level.isLt
  have hb : index.val / 2 ^ level.val < 2 ^ (32 - level.val) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
      show 32 - level.val + level.val = 32 by omega]
    exact lt_of_lt_of_eq index.isLt (by norm_num [lifetime, treeHeight])
  exact h.realBottomNode level.val (by omega) _ (xor_one_lt hb (by omega))

theorem bottomKey_lt (index : LeafIndex) : (topKeyOf index).val < 2 ^ (32 - 16) :=
  lt_of_lt_of_eq (topKeyOf index).isLt (by norm_num [topLifetime, treeHeight])

/-- The root of bottom tree `b` resolves to the one the key stores. -/
theorem root_resolves (h : Prepared seed d result cache) (index : LeafIndex) :
    Resolves cache (Xmss.node queryH (ofParam d.parameter) (realPrf seed) .bottom LAYER_HEIGHT
        (topKeyOf index).val : OracleComp HashSpec Xmss.Digest)
      (ofDigest (h.root (topKeyOf index))) := by
  have hroot := h.realBottomNode 16 le_rfl (topKeyOf index).val (bottomKey_lt index)
  unfold Prepared.root
  rw [Prepared.bottomRootNode_eq]
  exact hroot

/-- The build of bottom tree `b` resolves to a tree with the stored root and the key's path. -/
theorem realBottomBuild (h : Prepared seed d result cache) (index : LeafIndex) :
    ∃ t, Resolves cache (Xmss.build queryH (ofParam d.parameter) (realPrf seed) .bottom
        LAYER_HEIGHT (topKeyOf index).val : OracleComp HashSpec _) t ∧
      t.value = ofDigest (h.root (topKeyOf index)) ∧
      t.path LAYER_HEIGHT index.val = ofPath fun level =>
        (modelSecretKey d result).treeValue level.castSucc
          (Concrete.authenticationPathNode index level) := by
  obtain ⟨t, ht, hroot⟩ := resolves_build _ _ _ _ (h.root_resolves index)
  replace ht : Resolves cache (Xmss.build queryH (ofParam d.parameter) (realPrf seed) .bottom
      LAYER_HEIGHT (topKeyOf index).val : OracleComp HashSpec _) t := ht
  refine ⟨t, ht, hroot, ?_⟩
  -- Answer every query from the cache: the build and the path then evaluate to their values.
  let f : QueryImpl HashSpec Id := fun x => (cache x).getD default
  have hf : ∀ x a, cache x = some a → f x = a := fun x a hx => by simp [f, hx]
  rw [← ht.eval f hf, ← (h.realBottomPath index).eval f hf]
  have hbuild := Xmss.build_map_monad (m := OracleComp HashSpec) (m' := Id)
    (fun {β} (c : OracleComp HashSpec β) => (evalWithAnswerFn f c : Id β)) (fun _ => rfl)
    (fun x g => evalWithAnswerFn_bind f x g) queryH (realPrf seed) (ofParam d.parameter) .bottom
    LAYER_HEIGHT (topKeyOf index).val
  have hpath := Xmss.path_map_monad (m := OracleComp HashSpec) (m' := Id)
    (fun {β} (c : OracleComp HashSpec β) => (evalWithAnswerFn f c : Id β)) (fun _ => rfl)
    (fun x g => evalWithAnswerFn_bind f x g) queryH (realPrf seed) (ofParam d.parameter) .bottom
    index.val
  rw [hbuild, hpath, show (topKeyOf index).val = index.val / 2 ^ LAYER_HEIGHT from rfl]
  exact Xmss.path_build_run index.val

end Prepared

/-! ## A resolved build resolves its paths -/

section Merkle

variable {α : Type} {cache : QueryCache HashSpec}
  (hash : Merkle.Position → α → α → OracleComp HashSpec α) (leaves : Nat → OracleComp HashSpec α)

/-- A resolved build resolves the build of every node below it. -/
theorem resolves_build_below : ∀ (L J : Nat) (T : Merkle.Built α),
    Resolves cache (Merkle.build hash leaves ⟨L, J⟩) T →
    ∀ k i, k ≤ L → i / 2 ^ (L - k) = J →
      ∃ T', Resolves cache (Merkle.build hash leaves ⟨k, i⟩) T'
  | 0, J, T, h, k, i, hk, hi => by
    obtain rfl : k = 0 := by omega
    simp only [Nat.sub_self, pow_zero, Nat.div_one] at hi
    subst hi
    exact ⟨T, h⟩
  | L + 1, J, T, h, k, i, hk, hi => by
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · simp only [Nat.sub_self, pow_zero, Nat.div_one] at hi
      subst hi
      exact ⟨T, h⟩
    · rw [Merkle.build_succ] at h
      obtain ⟨l, hl, h⟩ := h.of_bind
      obtain ⟨r, hr, -⟩ := h.of_bind
      -- The node sits below the left child or the right child, by one bit of its index.
      have hdiv : i / 2 ^ (L - k) / 2 = J := by
        rw [Merkle.div_pow_div_two, show L - k + 1 = L + 1 - k by omega, hi]
      rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ (L - k)) with h0 | h1
      · exact resolves_build_below L (2 * J) l hl k i (by omega) (by omega)
      · exact resolves_build_below L (2 * J + 1) r hr k i (by omega) (by omega)

/-- A resolved build resolves the node at its position, to its top value. -/
theorem resolves_node_of_build {p : Merkle.Position} {T : Merkle.Built α}
    (h : Resolves cache (Merkle.build hash leaves p) T) :
    Resolves cache (Merkle.node hash leaves p) T.value := by
  rw [← Merkle.value_build]
  exact h.map _

/-- The siblings resolve when each sibling node does. -/
theorem resolves_siblings : ∀ (n : Nat) (p : Merkle.Position),
    (∀ t < n, ∃ v, Resolves cache (Merkle.node hash leaves (p.ancestor t).sibling) v) →
    ∃ v, Resolves cache (Merkle.siblings hash leaves p n) v
  | 0, _, _ => ⟨_, .pure _⟩
  | n + 1, p, h => by
    obtain ⟨s, hs⟩ := h 0 (by omega)
    obtain ⟨rest, hrest⟩ := resolves_siblings n p.parent fun t ht => by
      simpa only [Merkle.Position.ancestor_parent] using h (t + 1) (by omega)
    rw [Merkle.Position.ancestor_zero] at hs
    exact ⟨_, hs.bind (hrest.bind (.pure _))⟩

/-- A resolved build of a tree of height `h` resolves the path of each of its leaves. -/
theorem resolves_path_of_build {h : Nat} {T : Merkle.Built α}
    (hT : Resolves cache (Merkle.build hash leaves ⟨h, 0⟩) T) {j : Nat} (hj : j < 2 ^ h) :
    ∃ v, Resolves cache (Merkle.path hash leaves h j) v := by
  refine resolves_siblings hash leaves h ⟨0, j⟩ fun t ht => ?_
  -- The sibling on level `t` is a node of the tree, below its root.
  have hlt : j / 2 ^ t < 2 ^ (h - t) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, show h - t + t = h by omega]
    exact hj
  have hsib : (j / 2 ^ t) ^^^ 1 < 2 ^ (h - t) :=
    Nat.xor_lt_two_pow hlt (Nat.one_lt_two_pow (by omega))
  obtain ⟨T', hT'⟩ := resolves_build_below hash leaves h 0 T hT t ((j / 2 ^ t) ^^^ 1) (by omega)
    (Nat.div_eq_of_lt hsib)
  refine ⟨T'.value, ?_⟩
  rw [Merkle.Position.ancestor_mk_zero, Merkle.Position.sibling_mk]
  exact resolves_node_of_build hash leaves hT'

end Merkle

/- A concrete height would let Lean unfold a whole tree, so the height stays opaque. -/
attribute [local irreducible] LAYER_HEIGHT

/-- A resolved top tree resolves the path of each top key, to the path the tree holds. -/
theorem resolves_path_top {cache : QueryCache HashSpec}
    {publicParam : Xmss.PublicParam} {s : Xmss.Seed}
    {T : Merkle.Built Xmss.Digest}
    (hT : Resolves cache (Xmss.build queryH publicParam
      (Xmss.seedPrf queryH s) .top LAYER_HEIGHT 0 :
      OracleComp HashSpec _) T) {b : Nat} (hb : b < 2 ^ LAYER_HEIGHT) :
    Resolves cache (Xmss.path queryH publicParam
      (Xmss.seedPrf queryH s) .top b : OracleComp HashSpec _)
      (T.path LAYER_HEIGHT b) := by
  obtain ⟨v, hv⟩ := resolves_path_of_build _ _ hT hb
  change Resolves cache (Xmss.path queryH publicParam (Xmss.seedPrf queryH s) .top b :
    OracleComp HashSpec _) v at hv
  convert hv using 1
  -- Answer every query from the cache: the build and the path then evaluate to their values.
  let f : QueryImpl HashSpec Id := fun x => (cache x).getD default
  have hf : ∀ x a, cache x = some a → f x = a := fun x a hx => by simp [f, hx]
  rw [← hT.eval f hf, ← hv.eval f hf]
  have hbuild := Xmss.build_map_monad (m := OracleComp HashSpec) (m' := Id)
    (fun {β} (c : OracleComp HashSpec β) => (evalWithAnswerFn f c : Id β)) (fun _ => rfl)
    (fun x g => evalWithAnswerFn_bind f x g) queryH
      (Xmss.seedPrf queryH s) publicParam .top LAYER_HEIGHT 0
  have hpath := Xmss.path_map_monad (m := OracleComp HashSpec) (m' := Id)
    (fun {β} (c : OracleComp HashSpec β) => (evalWithAnswerFn f c : Id β)) (fun _ => rfl)
    (fun x g => evalWithAnswerFn_bind f x g) queryH (Xmss.seedPrf queryH s) publicParam .top b
  rw [hbuild, hpath]
  have := Xmss.path_build_run (H := fun x => (evalWithAnswerFn f (queryH x) : Id _))
    (publicParam := publicParam)
    (prf := fun publicParam a suffix => (evalWithAnswerFn f
      (Xmss.seedPrf queryH s publicParam a suffix) : Id _))
    (layer := .top) b
  rwa [Nat.div_eq_of_lt hb] at this

/-! ## A key the prepared cache knows -/

/-- A key whose parts the cache resolves, as key generation and signing build them from `S`.

Its seed and parameter are the programmed ones, and its top tree is the top layer's build.

Each kept tree is the build of its index, with the top signature of its root. -/
structure KeyResolves (seed : MasterSeed) (d : Derivations) (cache : QueryCache HashSpec)
    (sk : Xmss.SecretKey) : Prop where
  /-- The scheme seed is `S`. -/
  schemeSeed_eq : sk.schemeSeed = ofSeed seed
  /-- The parameter is the programmed one. -/
  publicParam_eq : sk.publicParam = ofParam d.parameter
  /-- The top tree is the build of the top layer. -/
  top_resolves : Resolves cache (Xmss.build queryH (ofParam d.parameter) (realPrf seed) .top
    LAYER_HEIGHT 0 : OracleComp HashSpec _) sk.top
  /-- Each kept tree is the build of its index, with its top signature. -/
  kept_resolves : ∀ t ∈ sk.cache,
    Resolves cache (Xmss.Internal.cacheTreeWith queryH (realPrf seed) sk t.index) t

/-- A key's trees are built and signed alike, whatever trees it keeps. -/
theorem cacheTreeWith_withCache (prf : Xmss.SeedPrf (OracleComp HashSpec)) (sk : Xmss.SecretKey)
    (kept : List Xmss.CachedTree) (b : Nat) :
    Xmss.Internal.cacheTreeWith queryH prf { sk with cache := kept } b =
      Xmss.Internal.cacheTreeWith queryH prf sk b :=
  rfl

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec} {sk : Xmss.SecretKey}

/-- The top key's signature of the root of bottom tree `b`, or its error, as the key stores it.

The path is read from the key's top tree, which is the top layer's build. -/
theorem realTopRoot (h : Prepared seed d result cache) (hk : KeyResolves seed d cache sk)
    (key : TopIndex) :
    Resolves cache (Xmss.Internal.signRootWith queryH (realPrf seed) sk key.val
        (ofDigest (h.root key)) : OracleComp HashSpec _)
      (match (modelSecretKey d result).topSigned key with
        | some _ => .ok (ofLayerSig (Concrete.topPart (modelSecretKey d result) key))
        | none => .error (.noAdmissibleEncoding .top key.val)) := by
  -- The top path read from the key is the path the cache resolves to the stored nodes.
  have hkey : key.val < 2 ^ LAYER_HEIGHT :=
    lt_of_lt_of_eq key.isLt (by norm_num [topLifetime, treeHeight, LAYER_HEIGHT])
  have hpath := (resolves_path_top hk.top_resolves hkey).unique (h.realTopPath key)
  unfold Xmss.Internal.signRootWith
  rw [Xmss.Internal.otsSignTrials_hashTrials, hk.publicParam_eq]
  unfold Xmss.otsSign Xmss.Internal.otsSignTrials
  rw [Xmss.Unforgeability.ofNat_val_topIndex, randomizerBase_queryH]
  simp only [bind_assoc]
  have hbase : cache (topRndInput d.parameter seed (key, h.root key))
      = some (d.topRnd (key, h.root key)) :=
    h.prog_le (progCache_topRnd seed d (key, h.root key))
  refine .query _ (d.topRnd (key, h.root key)) ?_ _ _ ?_
  · rw [topRndInput_toList]
    exact hbase
  simp only [pure_bind]
  have hgrind := h.realTopFind key _ _ signingAttemptLimit 0 (h.topSign key)
  refine hgrind.bind ?_
  cases hsigned : result.1.2 key with
  | none =>
    have : (modelSecretKey d result).topSigned key = none := hsigned
    simp only [Option.map_none, this]
    exact .pure _
  | some signed =>
    obtain ⟨randomness, encoding⟩ := signed
    have hsk : (modelSecretKey d result).topSigned key = some (randomness, encoding) := hsigned
    simp only [Option.map_some, bind_assoc, pure_bind]
    refine ((chainStarts_top seed d key).mono h.prog_le).bind ?_
    refine (h.realTopChains key encoding).bind ?_
    simp only [hsk, Concrete.topPart, hpath]
    exact .pure _

/-- The tree of bottom tree `b` that signing builds and signs, with what the model stores.

Its root and the key's path are the stored ones, and its top signature is the stored one. -/
theorem realCachedTree (h : Prepared seed d result cache) (hk : KeyResolves seed d cache sk)
    (index : LeafIndex) :
    ∃ t, Resolves cache (Xmss.Internal.cacheTreeWith queryH (realPrf seed) sk
        (topKeyOf index).val) t ∧
      t.index = (topKeyOf index).val ∧
      t.tree.path LAYER_HEIGHT index.val = ofPath (fun level =>
        (modelSecretKey d result).treeValue level.castSucc
          (Concrete.authenticationPathNode index level)) ∧
      t.top = (match (modelSecretKey d result).topSigned (topKeyOf index) with
        | some _ => .ok (ofLayerSig (Concrete.topPart (modelSecretKey d result) (topKeyOf index)))
        | none => .error (.noAdmissibleEncoding .top (topKeyOf index).val)) := by
  obtain ⟨tree, htree, hroot, hpath⟩ := h.realBottomBuild index
  refine ⟨
    { index := (topKeyOf index).val
      tree := tree
      top := match (modelSecretKey d result).topSigned (topKeyOf index) with
        | some _ => .ok (ofLayerSig (Concrete.topPart (modelSecretKey d result) (topKeyOf index)))
        | none => .error (.noAdmissibleEncoding .top (topKeyOf index).val) },
    ?_, rfl, hpath, rfl⟩
  unfold Xmss.Internal.cacheTreeWith
  rw [hk.publicParam_eq]
  refine htree.bind ?_
  rw [hroot]
  exact (h.realTopRoot hk (topKeyOf index)).bind (.pure _)

/-- Fetching bottom tree `b` resolves to the stored tree, and to a key the cache still knows. -/
theorem realFetch (h : Prepared seed d result cache) (hk : KeyResolves seed d cache sk)
    (index : LeafIndex) :
    ∃ t sk', Resolves cache (Xmss.Internal.fetchTreeWith queryH (realPrf seed) sk
        (topKeyOf index).val) (t, sk') ∧
      t.tree.path LAYER_HEIGHT index.val = ofPath (fun level =>
        (modelSecretKey d result).treeValue level.castSucc
          (Concrete.authenticationPathNode index level)) ∧
      t.top = (match (modelSecretKey d result).topSigned (topKeyOf index) with
        | some _ => .ok (ofLayerSig (Concrete.topPart (modelSecretKey d result) (topKeyOf index)))
        | none => .error (.noAdmissibleEncoding .top (topKeyOf index).val)) ∧
      KeyResolves seed d cache sk' := by
  obtain ⟨t0, ht0, hidx, hpath, htop⟩ := h.realCachedTree hk index
  unfold Xmss.Internal.fetchTreeWith
  split
  · -- A kept tree is the stored one, since the cache resolves its build to one value.
    next t ht =>
    have hmem := List.mem_of_find?_eq_some ht
    have htidx : t.index = (topKeyOf index).val := by simpa using List.find?_some ht
    have hres := hk.kept_resolves t hmem
    rw [htidx] at hres
    obtain rfl := hres.unique ht0
    refine ⟨t, _, .pure _, hpath, htop, ⟨hk.schemeSeed_eq, hk.publicParam_eq, hk.top_resolves,
      fun u hu => ?_⟩⟩
    rw [cacheTreeWith_withCache]
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hk.kept_resolves _ hmem
    · exact hk.kept_resolves u (List.mem_filter.1 hu).1
  · -- A new tree is built and signed, and goes in front.
    refine ⟨t0, _, ht0.bind (.pure _), hpath, htop, ⟨hk.schemeSeed_eq, hk.publicParam_eq,
      hk.top_resolves, fun u hu => ?_⟩⟩
    rw [cacheTreeWith_withCache]
    rcases List.mem_cons.1 (List.mem_of_mem_take hu) with rfl | hu
    · rw [hidx]
      exact ht0
    · exact hk.kept_resolves u hu

/-- EthLib's signer, with a key the cache knows, erases to the table signer.

Its signatures are translated, and its updated key is forgotten. -/
theorem erases_signWith (h : Prepared seed d result cache) (hk : KeyResolves seed d cache sk)
    (index : LeafIndex) (message : Message) :
    Erases cache ((fun r => r.1.toOption) <$>
        Xmss.signWith queryH sk (ofLeafIndex index) (ofMessage message))
      (Option.map (ofSignature index) <$> (tableSign d.rnd (modelSecretKey d result) index message :
        OracleComp HashSpec (Option Signature))) := by
  unfold Xmss.signWith Xmss.Internal.signWithTrials tableSign
  rw [hk.schemeSeed_eq, hk.publicParam_eq]
  -- Only the bottom key is unfolded: the tree and the top layer resolve as a whole.
  rw [Xmss.Internal.otsSignTrials.eq_1, Xmss.Unforgeability.toNat_ofLeafIndex,
    Xmss.Unforgeability.ofNat_val_leafIndex, randomizerBase_queryH]
  simp only [bind_assoc, map_bind]
  have hR0 : cache (rndInput d.parameter seed ⟨index, message⟩) = some (d.rnd ⟨index, message⟩) :=
    h.prog_le (progCache_rnd seed d ⟨index, message⟩)
  -- With a key the cache knows, the signer derives the same randomizer base.
  --
  -- It then makes the same trials.
  refine Erases.skip (spec := HashSpec) _ (d.rnd ⟨index, message⟩) ?_ _ _ ?_
  · rw [rndInput_toList]
    exact hR0
  simp only [pure_bind]
  refine erases_findCodeword_bottom cache (modelSecretKey d result) index message _ _ _ ?_ ?_
    signingAttemptLimit 0
  · simp [Except.toOption]
    exact .pure _
  · intro randomness encoding
    -- Everything the signer computes after a codeword is cached.
    --
    -- That is the chains, the bottom tree and the whole top signature.
    apply erases_pure_of_resolves
    dsimp only
    simp only [bind_assoc, pure_bind]
    refine ((chainStarts_bottom seed d index).mono h.prog_le).bind ?_
    refine (h.realBottomChains index encoding).bind ?_
    rw [Xmss.Unforgeability.bottomTree_ofLeafIndex]
    simp only [map_bind]
    -- A kept tree is the one the cache resolves, so it holds the same values.
    obtain ⟨t, sk', hfetch, hpath, htop, -⟩ := h.realFetch hk index
    refine hfetch.bind ?_
    dsimp only
    rw [hpath, htop]
    cases hsigned : (modelSecretKey d result).topSigned (topKeyOf index) with
    | none =>
      have hat : Concrete.topSignedAt (modelSecretKey d result) index = false := by
        simp [Concrete.topSignedAt, hsigned]
      simp [hat, Except.toOption]
      exact .pure _
    | some signed =>
      have hat : Concrete.topSignedAt (modelSecretKey d result) index = true := by
        simp [Concrete.topSignedAt, hsigned]
      simp [hat, Except.toOption, ofSignature, Concrete.precomputedSignWithEncoding]
      exact .pure _

/-- A signature with a key the cache knows returns a key that the cache still knows.

It holds for any larger cache that resolves the signature. -/
theorem keyResolves_signWith (h : Prepared seed d result cache) (hk : KeyResolves seed d cache sk)
    {cache' : QueryCache HashSpec} (hle : cache ≤ cache') (idx : Xmss.LeafIndex)
    (msg : Xmss.Message) {r : Except Xmss.XmssError Xmss.Signature} {sk' : Xmss.SecretKey}
    (hr : Resolves cache' (Xmss.signWith queryH sk idx msg) (r, sk')) :
    KeyResolves seed d cache sk' := by
  unfold Xmss.signWith Xmss.Internal.signWithTrials at hr
  obtain ⟨o, -, hr⟩ := hr.of_bind
  rcases o with _ | ⟨rho, y⟩
  · obtain ⟨-, rfl⟩ := Prod.mk.inj hr.pure_inv.symm
    exact hk
  · obtain ⟨⟨t, sk1⟩, hfetch, hr⟩ := hr.of_bind
    have hsk : sk1 = sk' := by
      dsimp only at hr
      rcases htt : t.top with top | err <;> rw [htt] at hr <;> exact (Prod.mk.inj hr.pure_inv).2
    subst hsk
    -- The fetch resolves in the prepared cache, so its key is the one the cache knows.
    have hidx : Xmss.bottomTree idx = (topKeyOf (toLeafIndex idx)).val := by
      rw [← Xmss.Unforgeability.bottomTree_ofLeafIndex, Xmss.Unforgeability.ofLeafIndex_toLeafIndex]
    rw [hk.schemeSeed_eq, hidx] at hfetch
    obtain ⟨t0, sk0, hfetch0, -, -, hk0⟩ := h.realFetch hk (toLeafIndex idx)
    obtain ⟨-, rfl⟩ := Prod.mk.inj (hfetch.unique (hfetch0.mono hle))
    exact hk0

end Prepared

end XmssSecurity.Bridge
