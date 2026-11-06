module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Count
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.GraphView.Cost
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.CostProgram

/-!
# Proofs: the hash calls of one signing request, under one answer function

Under one answer function, a signing request costs the model at most what it costs EthLib.

Both signers sign the layers from the bottom up.

Both stop at the first layer whose counter search fails, so they reach the same layers.

Each layer costs EthLib at least what it costs the model.

EthLib also makes more calls before the layers.

- It derives the scheme seed and the public parameter again on each request.
- It derives each FORS secret for its own leaf, where the model derives a pair of secrets once.

The model makes one more digest call, to accept its randomizer.

So a budget of hash calls against EthLib is a budget against the model.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open OracleComp OracleSpec
open HashSig (HashSpec OracleWorld)
open SphincsSecurity.Security.Prefix (hashCalls hashCalls_bind hashCalls_pure seqCost)
open SphincsSecurity.Security.GraphView (keyMessageCost)

variable (f : QueryImpl HashSpec Id)

/-- A sequence counts its calls whatever the bound's name. -/
theorem hashCalls_sequenceFin_congr {α : Type} {n n' : Nat} (h : n = n')
    (g : Nat → OracleComp HashSpec α) :
    hashCalls f (SphincsSecurity.Concrete.sequenceFin fun i : Fin n ↦ g i.val) =
      hashCalls f (SphincsSecurity.Concrete.sequenceFin fun i : Fin n' ↦ g i.val) := by
  subst h
  rfl

open EthLib.Cryptography.Sphincs in
/-- An EthLib layer makes the calls of the model's layer, except the key message. -/
theorem hashCalls_signLayer_add (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (index : SphincsSecurity.Index) (lay : SphincsSecurity.Layer) (msg : ByteArray)
    (hmsg : msg.data.toList =
      SphincsSecurity.Completeness.layerMessageValue f ⟨S, P, root⟩ index lay) :
    hashCalls f (signLayer (queryH (m := OracleComp HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) (layerOf lay) index.val msg) + keyMessageCost lay =
      hashCalls f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index lay :
        OracleComp HashSpec _) := by
  unfold signLayer
  rw [ofIndex_eq]
  simp only [SphincsSecurity.Seeded.signLayer, hashCalls_bind]
  rw [show evalWithAnswerFn f (SphincsSecurity.Seeded.layerMessage ⟨S, P, root⟩ index lay
      : OracleComp HashSpec _) =
        SphincsSecurity.Completeness.layerMessageValue f ⟨S, P, root⟩ index lay from rfl,
    ← hmsg, otsSign_queryH, hashCalls_map, evalWithAnswerFn_map]
  rw [SphincsSecurity.Seeded.layerMessage, SphincsSecurity.Security.GraphView.hashCalls_keyMessage]
  cases evalWithAnswerFn f (SphincsSecurity.Seeded.otsSign P lay
      (SphincsSecurity.Concrete.treeIndexAt index lay)
      (SphincsSecurity.Concrete.leafIndexAt index lay)
      S msg.data.toList : OracleComp HashSpec _) with
  | none =>
    simp only [Option.map_none, hashCalls_pure]
    omega
  | some ots =>
    obtain ⟨counter, values⟩ := ots
    simp only [Option.map_some, ofOts, keyOf, hashCalls_bind, hashCalls_pure, Nat.add_zero]
    rw [path_queryH, hashCalls_map, SphincsSecurity.Seeded.treePath]
    simp only [keptHeight_eq, Fin.is_lt, ↓reduceIte]
    rw [Nat.add_comm _ (keyMessageCost lay),
      hashCalls_sequenceFin_congr f (height_layerOf lay) fun level ↦
        SphincsSecurity.Seeded.treeNode P lay (SphincsSecurity.Concrete.treeIndexAt index lay) S
          level (Nat.xor ((SphincsSecurity.Concrete.leafIndexAt index lay).val / 2 ^ level) 1)]

/-- A vector computed in order makes the calls of its entries. -/
theorem hashCalls_ofFnInOrder {α : Type} :
    ∀ (n : Nat) (g : Fin n → OracleComp HashSpec α),
      hashCalls f (HashSig.ofFnInOrder n g) = ∑ i, hashCalls f (g i)
  | 0, _ => rfl
  | n + 1, g => by
    simp only [HashSig.ofFnInOrder, hashCalls_bind, hashCalls_pure, Nat.add_zero,
      hashCalls_ofFnInOrder n, Fin.sum_univ_succ]

/-- A query to the oracle is one hash call. -/
theorem hashCalls_queryH (input : ByteArray) :
    hashCalls f (HashSig.queryH (m := OracleComp HashSpec) input) = 1 := by
  rw [HashSig.queryH, hashCalls_map]
  exact SphincsSecurity.Security.Prefix.hashCalls_oracleHash f _

/-- A node of height `level` makes `(c + 1) 2^level - 1` calls if each leaf makes `c`.

That is `c` calls for each of its `2^level` leaves and one for each of its `2^level - 1` hashes. -/
theorem hashCalls_node {α : Type} (hash : Nat → Nat → α → α → OracleComp HashSpec α)
    (leaves : Nat → OracleComp HashSpec α) (c : Nat)
    (hhash : ∀ level j left right, hashCalls f (hash level j left right) = 1)
    (hleaf : ∀ j, hashCalls f (leaves j) = c) :
    ∀ level j, hashCalls f (Merkle.node hash leaves level j) = (c + 1) * 2 ^ level - 1
  | 0, j => by
    rw [Merkle.node, hleaf, Nat.pow_zero, Nat.mul_one, Nat.add_sub_cancel]
  | level + 1, j => by
    rw [Merkle.node, hashCalls_bind, hashCalls_bind, hhash,
      hashCalls_node hash leaves c hhash hleaf level,
      hashCalls_node hash leaves c hhash hleaf level,
      Nat.pow_succ, ← Nat.mul_assoc]
    have hpos : 1 ≤ (c + 1) * 2 ^ level := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega

/-- The siblings of `n` nodes from `(level, j)` up make one whole node each. -/
theorem hashCalls_siblings {α : Type} (hash : Nat → Nat → α → α → OracleComp HashSpec α)
    (leaves : Nat → OracleComp HashSpec α) (c : Nat)
    (hhash : ∀ level j left right, hashCalls f (hash level j left right) = 1)
    (hleaf : ∀ j, hashCalls f (leaves j) = c) :
    ∀ level j n, hashCalls f (Merkle.siblings hash leaves level j n) =
      ∑ i : Fin n, ((c + 1) * 2 ^ (level + i.val) - 1)
  | _, _, 0 => rfl
  | level, j, n + 1 => by
    rw [Merkle.siblings, hashCalls_bind, hashCalls_bind, hashCalls_pure, Nat.add_zero,
      hashCalls_node f hash leaves c hhash hleaf,
      hashCalls_siblings hash leaves c hhash hleaf (level + 1) (j / 2) n, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

open EthLib.Cryptography.Sphincs in
/-- A tweakable hash with its whole output is one call. -/
theorem hashCalls_thFull (P : PublicParam) (address : Address) (payload : ByteArray) :
    hashCalls f (thFull (queryH (m := OracleComp HashSpec)) P address payload) = 1 :=
  hashCalls_queryH f _

open EthLib.Cryptography.Sphincs in
/-- A tweakable hash is one call. -/
theorem hashCalls_th (P : PublicParam) (address : Address) (payload : ByteArray) :
    hashCalls f (th (queryH (m := OracleComp HashSpec)) P address payload) = 1 :=
  (hashCalls_bind f _ _).trans (by rw [hashCalls_thFull, hashCalls_pure])

open EthLib.Cryptography.Sphincs in
/-- A FORS secret is one derivation. -/
theorem hashCalls_forsSecret (P : PublicParam) (s : Seed) (idx : Nat)
    (kappa : Fin Constants.FORS_TREES) (l : Fin (2 ^ Constants.FORS_HEIGHT)) :
    hashCalls f (forsSecret P (seedPrf (queryH (m := OracleComp HashSpec)) s) idx kappa l) = 1 :=
  (hashCalls_bind f _ _).trans (by rw [seedPrf, hashCalls_thFull, hashCalls_pure])

open EthLib.Cryptography.Sphincs in
/-- A FORS leaf makes two calls: the derivation of its secret, then its hash. -/
theorem hashCalls_forsLeaves (P : PublicParam) (s : Seed) (idx : Nat)
    (kappa : Fin Constants.FORS_TREES) (j : Nat) :
    hashCalls f (forsLeaves (queryH (m := OracleComp HashSpec)) P (seedPrf queryH s) idx kappa
      j) = 2 :=
  (hashCalls_bind f _ _).trans (by rw [hashCalls_forsSecret, forsLeafHash, hashCalls_th])

open EthLib.Cryptography.Sphincs in
/-- A FORS node hash is one call. -/
theorem hashCalls_forsNodeHash (P : PublicParam) (idx : Nat) (kappa : Fin Constants.FORS_TREES)
    (level j : Nat) (left right : Digest) :
    hashCalls f (forsNodeHash (queryH (m := OracleComp HashSpec)) P idx kappa level j left
      right) = 1 :=
  hashCalls_th f _ _ _

open EthLib.Cryptography.Sphincs in
/-- A FORS node of height `level` makes `3 * 2^level - 1` calls.

Each leaf derives its own secret, so a pair of leaves derives it twice. -/
theorem hashCalls_forsNode (P : PublicParam) (s : Seed) (idx : Nat)
    (kappa : Fin Constants.FORS_TREES) (level j : Nat) :
    hashCalls f (forsNode (queryH (m := OracleComp HashSpec)) P (seedPrf queryH s) idx kappa
      level j) = 3 * 2 ^ level - 1 :=
  hashCalls_node f _ _ 2 (hashCalls_forsNodeHash f P idx kappa) (hashCalls_forsLeaves f P s idx
    kappa) level j

open EthLib.Cryptography.Sphincs in
/-- The FORS key makes `3 * 2^9 - 1` calls for each of its two top nodes per tree. -/
theorem hashCalls_forsKey (P : PublicParam) (s : Seed) (idx : Nat) :
    hashCalls f (forsKey (queryH (m := OracleComp HashSpec)) P (seedPrf queryH s) idx) =
      Constants.FORS_TREES * (2 * (3 * 2 ^ (Constants.FORS_HEIGHT - 1) - 1)) := by
  simp only [forsKey, hashCalls_ofFnInOrder, hashCalls_bind, hashCalls_pure, Nat.add_zero,
    hashCalls_forsNode, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

open EthLib.Cryptography.Sphincs in
/-- Opening FORS makes, per tree, the derivation of the secret and one whole node per level. -/
theorem hashCalls_forsSign (P : PublicParam) (s : Seed) (idx : Nat)
    (leaves : Vector (Fin (2 ^ Constants.FORS_HEIGHT)) Constants.FORS_TREES) :
    hashCalls f (forsSign (queryH (m := OracleComp HashSpec)) P (seedPrf queryH s) idx leaves) =
      Constants.FORS_TREES *
        (1 + ∑ level : Fin Constants.FORS_HEIGHT, (3 * 2 ^ level.val - 1)) := by
  simp only [forsSign, treeOpen, Merkle.path, hashCalls_ofFnInOrder, hashCalls_bind,
    hashCalls_pure, Nat.add_zero, hashCalls_forsSecret,
    hashCalls_siblings f _ _ 2 (hashCalls_forsNodeHash f P idx _)
      (hashCalls_forsLeaves f P s idx _),
    Nat.zero_add, Nat.reduceAdd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

open EthLib.Cryptography.Sphincs in
/-- The bottom message is the FORS key, made of `2 * 24` nodes of `3 * 2^9 - 1` calls. -/
theorem hashCalls_layerMessage_bottom (P : PublicParam) (s : Seed) (idx : Nat) :
    hashCalls f (layerMessage (queryH (m := OracleComp HashSpec)) P (seedPrf queryH s) .bottom
      idx) = Constants.FORS_TREES * (2 * (3 * 2 ^ (Constants.FORS_HEIGHT - 1) - 1)) :=
  (hashCalls_bind f _ _).trans (by rw [hashCalls_forsKey, hashCalls_pure, Nat.add_zero])

open EthLib.Cryptography.Sphincs in
/-- EthLib's bottom message costs at least the model's.

A FORS node of height `l` costs EthLib `3 * 2^l - 1` calls and the model `5 * 2^(l - 1) - 1`.

The model derives each pair of leaf secrets once, and EthLib once per leaf. -/
theorem keyMessageCost_bottom_le (P : PublicParam) (s : Seed) (idx : Nat) :
    keyMessageCost bottomLayer ≤ hashCalls f (layerMessage (queryH (m := OracleComp HashSpec)) P
      (seedPrf queryH s) .bottom idx) := by
  rw [hashCalls_layerMessage_bottom]
  decide

open EthLib.Cryptography.Sphincs in
/-- EthLib's middle message is the root of the bottom tree, with the model's calls. -/
theorem keyMessageCost_middle_le (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index) :
    keyMessageCost middleLayer ≤ hashCalls f (layerMessage (queryH (m := OracleComp HashSpec))
      (ofParam P) (seedPrf queryH (ofSeed S)) .middle index.val) := by
  have hroot : treeRoot (queryH (m := OracleComp HashSpec)) (ofParam P)
      (seedPrf queryH (ofSeed S)) .bottom
      (SphincsSecurity.Concrete.treeIndexAt index bottomLayer).val
      = ofDigest <$> SphincsSecurity.Seeded.treeRoot P bottomLayer
          (SphincsSecurity.Concrete.treeIndexAt index bottomLayer) S :=
    treeRoot_queryH S P bottomLayer _
  have hkey : OtsKey.ofIndex .bottom index.val
      = keyOf bottomLayer (SphincsSecurity.Concrete.treeIndexAt index bottomLayer)
          (SphincsSecurity.Concrete.leafIndexAt index bottomLayer) :=
    ofIndex_eq index bottomLayer
  refine le_of_le_of_eq ?_ (hashCalls_bind f _ _).symm
  simp only [hkey, keyOf, hroot, hashCalls_map, hashCalls_pure, Nat.add_zero,
    SphincsSecurity.Security.Prefix.hashCalls_treeRoot]
  decide

open EthLib.Cryptography.Sphincs in
/-- EthLib's top message is the root of the middle tree, with the model's calls. -/
theorem keyMessageCost_top_le (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index) :
    keyMessageCost SphincsSecurity.topLayer ≤ hashCalls f (layerMessage
      (queryH (m := OracleComp HashSpec)) (ofParam P) (seedPrf queryH (ofSeed S)) .top
      index.val) := by
  have hroot : treeRoot (queryH (m := OracleComp HashSpec)) (ofParam P)
      (seedPrf queryH (ofSeed S)) .middle
      (SphincsSecurity.Concrete.treeIndexAt index middleLayer).val
      = ofDigest <$> SphincsSecurity.Seeded.treeRoot P middleLayer
          (SphincsSecurity.Concrete.treeIndexAt index middleLayer) S :=
    treeRoot_queryH S P middleLayer _
  have hkey : OtsKey.ofIndex .middle index.val
      = keyOf middleLayer (SphincsSecurity.Concrete.treeIndexAt index middleLayer)
          (SphincsSecurity.Concrete.leafIndexAt index middleLayer) :=
    ofIndex_eq index middleLayer
  refine le_of_le_of_eq ?_ (hashCalls_bind f _ _).symm
  simp only [hkey, keyOf, hroot, hashCalls_map, hashCalls_pure, Nat.add_zero,
    SphincsSecurity.Security.Prefix.hashCalls_treeRoot]
  decide

open EthLib.Cryptography.Sphincs in
/-- EthLib's layer costs at least the model's, if its message costs at least the model's.

The message must also have the model's bytes. -/
theorem hashCalls_layer_le (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (index : SphincsSecurity.Index) (lay : SphincsSecurity.Layer)
    (msg : OracleComp HashSpec ByteArray)
    (hcost : keyMessageCost lay ≤ hashCalls f msg)
    (hmsg : (evalWithAnswerFn f msg).data.toList =
      SphincsSecurity.Completeness.layerMessageValue f ⟨S, P, root⟩ index lay) :
    hashCalls f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index lay :
        OracleComp HashSpec _) ≤
      hashCalls f msg + hashCalls f (signLayer (queryH (m := OracleComp HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) (layerOf lay) index.val (evalWithAnswerFn f msg)) := by
  rw [← hashCalls_signLayer_add f S P root index lay _ hmsg]
  omega

/-- The cost of the model's request.

It makes the randomizer, one digest call to accept it, the digest and the FORS opening.

Then it signs the layers from the bottom up, to the first failure. -/
theorem hashCalls_sign_model (sk : SphincsSecurity.Seeded.SecretKey)
    (msg : SphincsSecurity.Message) (rho : SphincsSecurity.Randomness)
    (hrho : (evalWithAnswerFn f (SphincsSecurity.deriveRandomizer sk.parameter sk.seed msg :
      OracleComp HashSpec _)).1 = rho) :
    hashCalls f (SphincsSecurity.Seeded.sign sk msg : OracleComp HashSpec _) =
      4 + SphincsSecurity.forsTrees * SphincsSecurity.Security.GraphView.treeOpenCost +
        seqCost (fun lay => (evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer sk
            (SphincsSecurity.Concrete.digestIndex
              (SphincsSecurity.Completeness.digestValue f sk msg rho)) lay :
            OracleComp HashSpec _)).isSome)
          (fun lay => hashCalls f (SphincsSecurity.Seeded.signLayer sk
            (SphincsSecurity.Concrete.digestIndex
              (SphincsSecurity.Completeness.digestValue f sk msg rho)) lay :
            OracleComp HashSpec _)) := by
  rw [SphincsSecurity.Seeded.sign, hashCalls_bind, hashCalls_bind,
    show SphincsSecurity.digestAttemptLimit = 2 ^ 32 - 1 + 1 from rfl, signDigestLoop_succ,
    hashCalls_map, evalWithAnswerFn_map, hrho]
  dsimp only
  rw [SphincsSecurity.Security.Det.hashCalls_deriveRandomizer,
    SphincsSecurity.Security.Prefix.hashCalls_messageDigestCall, hashCalls_bind,
    SphincsSecurity.Security.Prefix.hashCalls_messageDigest, hashCalls_bind,
    SphincsSecurity.Security.GraphView.hashCalls_forsOpen_exact, hashCalls_bind,
    SphincsSecurity.Security.Prefix.hashCalls_sequenceLayers]
  have hd : SphincsSecurity.digestCalls = 2 := rfl
  have hv : SphincsSecurity.Completeness.digestValue f sk msg rho = evalWithAnswerFn f
      (SphincsSecurity.Concrete.messageDigest sk.parameter sk.root msg rho :
        OracleComp HashSpec _) := rfl
  rw [hd, hv]
  split <;> simp only [hashCalls_pure] <;> omega

open EthLib.Cryptography.Sphincs in
/-- EthLib's FORS opening costs at least the model's.

Per tree EthLib makes `1 + sum_{l < 10} (3 * 2^l - 1) = 3060` calls and the model `2548`. -/
theorem forsOpenCost_le :
    SphincsSecurity.forsTrees * SphincsSecurity.Security.GraphView.treeOpenCost ≤
      Constants.FORS_TREES *
        (1 + ∑ level : Fin Constants.FORS_HEIGHT, (3 * 2 ^ level.val - 1)) := by
  decide

/-- The cost of the model's layers, from the bottom up to the first failure. -/
theorem seqCost_layers (ok : SphincsSecurity.Layer → Bool) (cost : SphincsSecurity.Layer → Nat) :
    seqCost ok cost = cost bottomLayer + if ok bottomLayer then cost middleLayer +
      (if ok middleLayer then cost SphincsSecurity.topLayer else 0) else 0 := by
  simp only [seqCost, ite_self, Nat.add_zero]
  rfl

open EthLib.Cryptography.Sphincs in
/-- The model's request costs at most one call more than EthLib's signing from `S` and `P`. -/
theorem hashCalls_sign_le_signDerived (S : SphincsSecurity.MasterSeed)
    (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (msg : SphincsSecurity.Message) :
    hashCalls f (SphincsSecurity.Seeded.sign ⟨S, P, root⟩ msg : OracleComp HashSpec _) ≤
      1 + hashCalls f (signDerived (queryH (m := OracleComp HashSpec))
        (seedPrf queryH (ofSeed S)) (ofParam P) (ofMessage msg)) := by
  generalize hrho : (evalWithAnswerFn f (SphincsSecurity.deriveRandomizer P S msg
    : OracleComp HashSpec _)).1 = rho
  rw [hashCalls_sign_model f ⟨S, P, root⟩ msg rho hrho]
  unfold signDerived
  rw [hashCalls_bind, randomizer_queryH, hashCalls_map, evalWithAnswerFn_map, hrho,
    SphincsSecurity.Security.Det.hashCalls_deriveRandomizer, hashCalls_bind,
    messageDigest_queryH (root := root),
    hashCalls_map, evalWithAnswerFn_map]
  have hdc : hashCalls f (SphincsSecurity.Concrete.sequenceFin
      (SphincsSecurity.Concrete.messageDigestCall P root msg rho) : OracleComp HashSpec _) = 2 := by
    rw [SphincsSecurity.Security.Prefix.hashCalls_sequenceFin]
    simp only [SphincsSecurity.Security.Prefix.hashCalls_messageDigestCall, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]
    rfl
  have hdigest : SphincsSecurity.Completeness.digestValue f ⟨S, P, root⟩ msg rho
      = SphincsSecurity.truncateMessageDigest fun call =>
          evalWithAnswerFn f (SphincsSecurity.Concrete.messageDigestCall P root msg rho call) := by
    rw [SphincsSecurity.Completeness.digestValue, SphincsSecurity.Concrete.messageDigest,
      evalWithAnswerFn_bind, SphincsSecurity.Completeness.eval_sequenceFin, evalWithAnswerFn_pure]
  rw [hdc, SphincsSecurity.Completeness.eval_sequenceFin, hdigest]
  generalize (fun call => evalWithAnswerFn f
    (SphincsSecurity.Concrete.messageDigestCall P root msg rho call
      : OracleComp HashSpec _)) = outs
  dsimp only
  rw [digestIndex_ofOutputs, digestLeaves_ofOutputs]
  generalize SphincsSecurity.Concrete.digestIndex (SphincsSecurity.truncateMessageDigest outs)
    = index
  rw [hashCalls_bind, hashCalls_forsSign]
  have hfors := forsOpenCost_le
  rw [seqCost_layers]
  have hb : evalWithAnswerFn f (signLayer (queryH (m := OracleComp HashSpec)) (ofParam P)
      (seedPrf queryH (ofSeed S)) .bottom index.val (evalWithAnswerFn f (layerMessage
        (queryH (m := OracleComp HashSpec)) (ofParam P) (seedPrf queryH (ofSeed S))
        .bottom index.val)))
      = toLayerResult bottomLayer (evalWithAnswerFn f
          (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index bottomLayer
            : OracleComp HashSpec _)) :=
    signLayer_answers f S P root index bottomLayer _ (layerMessage_bottom_answers f S P root index)
  have hbc : hashCalls f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index bottomLayer
      : OracleComp HashSpec _) ≤ hashCalls f (layerMessage (queryH (m := OracleComp HashSpec))
        (ofParam P) (seedPrf queryH (ofSeed S)) .bottom index.val) +
      hashCalls f (signLayer (queryH (m := OracleComp HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) .bottom index.val (evalWithAnswerFn f (layerMessage
          (queryH (m := OracleComp HashSpec)) (ofParam P) (seedPrf queryH (ofSeed S))
          .bottom index.val))) :=
    hashCalls_layer_le f S P root index bottomLayer _ (keyMessageCost_bottom_le f _ _ index.val)
      (layerMessage_bottom_answers f S P root index)
  rw [hashCalls_bind, hashCalls_bind, hb]
  cases hbottom : evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index
      bottomLayer : OracleComp HashSpec _) with
  | none =>
    dsimp only [toLayerResult]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hashCalls_pure]
    omega
  | some bottom =>
    dsimp only [toLayerResult]
    simp only [Option.isSome_some, ↓reduceIte]
    have h0 : hashCalls f (pure (ofLayerSignature bottomLayer bottom) :
        OracleComp HashSpec (LayerSignature .bottom)) = 0 := hashCalls_pure f _
    rw [hashCalls_bind, h0, Nat.zero_add]
    have hm : evalWithAnswerFn f (signLayer (queryH (m := OracleComp HashSpec)) (ofParam P)
        (seedPrf queryH (ofSeed S)) .middle index.val (evalWithAnswerFn f (layerMessage
          (queryH (m := OracleComp HashSpec)) (ofParam P) (seedPrf queryH (ofSeed S))
          .middle index.val)))
        = toLayerResult middleLayer (evalWithAnswerFn f
            (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index middleLayer
              : OracleComp HashSpec _)) :=
      signLayer_answers f S P root index middleLayer _
        (layerMessage_middle_answers f S P root index)
    have hmc : hashCalls f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index middleLayer
        : OracleComp HashSpec _) ≤ hashCalls f (layerMessage (queryH (m := OracleComp HashSpec))
          (ofParam P) (seedPrf queryH (ofSeed S)) .middle index.val) +
        hashCalls f (signLayer (queryH (m := OracleComp HashSpec)) (ofParam P)
          (seedPrf queryH (ofSeed S)) .middle index.val (evalWithAnswerFn f (layerMessage
            (queryH (m := OracleComp HashSpec)) (ofParam P) (seedPrf queryH (ofSeed S))
            .middle index.val))) :=
      hashCalls_layer_le f S P root index middleLayer _ (keyMessageCost_middle_le f S P index)
        (layerMessage_middle_answers f S P root index)
    rw [hashCalls_bind, hashCalls_bind, hm]
    cases hmiddle : evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index
        middleLayer : OracleComp HashSpec _) with
    | none =>
      dsimp only [toLayerResult]
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hashCalls_pure]
      omega
    | some middle =>
      dsimp only [toLayerResult]
      simp only [Option.isSome_some, ↓reduceIte]
      have h1 : hashCalls f (pure (ofLayerSignature middleLayer middle) :
          OracleComp HashSpec (LayerSignature .middle)) = 0 := hashCalls_pure f _
      rw [hashCalls_bind, h1, Nat.zero_add]
      have ht : evalWithAnswerFn f (signLayer (queryH (m := OracleComp HashSpec)) (ofParam P)
          (seedPrf queryH (ofSeed S)) .top index.val (evalWithAnswerFn f (layerMessage
            (queryH (m := OracleComp HashSpec)) (ofParam P) (seedPrf queryH (ofSeed S))
            .top index.val)))
          = toLayerResult SphincsSecurity.topLayer (evalWithAnswerFn f
              (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index SphincsSecurity.topLayer
                : OracleComp HashSpec _)) :=
        signLayer_answers f S P root index SphincsSecurity.topLayer _
          (layerMessage_top_answers f S P root index)
      have htc : hashCalls f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index
          SphincsSecurity.topLayer : OracleComp HashSpec _) ≤
          hashCalls f (layerMessage (queryH (m := OracleComp HashSpec)) (ofParam P)
            (seedPrf queryH (ofSeed S)) .top index.val) +
          hashCalls f (signLayer (queryH (m := OracleComp HashSpec)) (ofParam P)
            (seedPrf queryH (ofSeed S)) .top index.val (evalWithAnswerFn f (layerMessage
              (queryH (m := OracleComp HashSpec)) (ofParam P) (seedPrf queryH (ofSeed S))
              .top index.val))) :=
        hashCalls_layer_le f S P root index SphincsSecurity.topLayer _
          (keyMessageCost_top_le f S P index) (layerMessage_top_answers f S P root index)
      rw [hashCalls_bind, hashCalls_bind, ht]
      cases htop : evalWithAnswerFn f (SphincsSecurity.Seeded.signLayer ⟨S, P, root⟩ index
          SphincsSecurity.topLayer : OracleComp HashSpec _) <;>
        dsimp only [toLayerResult] <;>
        simp only [hashCalls_bind, hashCalls_pure, Nat.add_zero] <;>
        omega

/-- One signing request costs the model at most what it costs EthLib, under every answer function.

The model's key holds the scheme seed `S` and the parameter `P` that EthLib derives from `S0`.

- Before the layers, EthLib makes 5 calls: `S`, `P`, the randomizer and the two digest calls.
  The model makes 4: the randomizer, its first digest call to accept it, and the digest.
- The FORS opening costs EthLib 3060 calls per tree, and the model 2548.
- Each layer, signed from the bottom up, costs EthLib at least what it costs the model.
  Both signers fail at the same layer, so they reach the same layers.

So the model's cost is at most EthLib's on success and on a failure at any of the three layers. -/
theorem hashCalls_sign_le (S0 : SphincsSecurity.MasterSeed) (root : SphincsSecurity.Digest)
    (m : Message) :
    hashCalls f (SphincsSecurity.Seeded.sign
      ⟨evalWithAnswerFn f (SphincsSecurity.schemeSeed S0 : OracleComp HashSpec _),
        evalWithAnswerFn f (SphincsSecurity.deriveKey 0 .parameter
          (evalWithAnswerFn f (SphincsSecurity.schemeSeed S0 : OracleComp HashSpec _)) :
            OracleComp HashSpec _), root⟩
      (toMessage m) : OracleComp HashSpec _) ≤ hashCalls f (signWith H ⟨ofSeed S0⟩ m) := by
  conv_rhs => rw [← ofMessage_toMessage m]
  rw [signWith, schemeSeed_queryH, bind_map_left, hashCalls_bind, publicParamOf_queryH,
    bind_map_left, hashCalls_bind]
  have hS : hashCalls f (SphincsSecurity.schemeSeed S0 : OracleComp HashSpec _) = 1 :=
    SphincsSecurity.Security.Prefix.hashCalls_oracleHash f _
  have hP : hashCalls f (SphincsSecurity.deriveKey 0 .parameter
      (evalWithAnswerFn f (SphincsSecurity.schemeSeed S0 : OracleComp HashSpec _)) :
        OracleComp HashSpec SphincsSecurity.PublicParameter) = 1 :=
    SphincsSecurity.Security.Prefix.hashCalls_deriveKey f _ _ _
  rw [hS, hP]
  exact (hashCalls_sign_le_signDerived f _ _ root _).trans
    (Nat.add_le_add_left (Nat.le_add_left _ _) 1)

omit f in
/-- An adversary with `q` hash calls against EthLib, translated, has `q` against the model. -/
theorem hasHashQueryBound_translate_self (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound adversary q) :
    SphincsSecurity.Security.HasHashQueryBound (translate adversary) q := by
  have h := hasHashQueryBound_translate Nat.one_pos le_rfl
    (fun f S0 root m => by simpa only [Nat.one_mul] using hashCalls_sign_le f S0 root m)
    adversary q hq
  rwa [Nat.one_mul, Nat.div_one] at h

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
