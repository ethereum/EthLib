module

public import EthLib.Cryptography.Proofs.Bls.Signatures
public import EthLib.Cryptography.Proofs.Bls.KeyValidate
public import EthLib.Cryptography.Proofs.Bls.CofactorSubgroupLanding

/-!
# Proofs: honest BLS signatures verify

Under the pairing law, an honest signature passes verification.

So do an honest proof of possession and an aggregate of honest signatures.

The source is [draft-04](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04),
§2.6 to §2.9 and §3.3.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open scoped EthLib.Cryptography.Bls.Fr

/-- The point at infinity represents `0 • g1`. -/
theorem G1.represents_zero : G1.Represents G1.zero 0 :=
  ⟨G1.valid_zero, by rw [G1.toPoint_zero, G1.toPoint_mul_generator, G1.ofFr_zero]⟩

/-- The sum of representatives of `a • g1` and `c • g1` represents `(a + c) • g1`. -/
theorem G1.Represents.add {P P' : G1} {a c : Fr} (h : G1.Represents P a)
    (h' : G1.Represents P' c) : G1.Represents (G1.add P P') (a + c) := by
  refine ⟨G1.valid_add h.1 h'.1, ?_⟩
  rw [G1.toPoint_add h.1 h'.1, h.2, h'.2, G1.toPoint_mul_generator, G1.toPoint_mul_generator,
    G1.toPoint_mul_generator, G1.ofFr_add]

/-- The point at infinity represents `0 • g2`. -/
theorem G2.represents_zero : G2.Represents G2.zero 0 :=
  ⟨G2.valid_zero, by rw [G2.toPoint_zero, G2.toPoint_mul_generator, G2.ofFr_zero]⟩

/-- The sum of representatives of `b • g2` and `d • g2` represents `(b + d) • g2`. -/
theorem G2.Represents.add {Q Q' : G2} {b d : Fr} (h : G2.Represents Q b)
    (h' : G2.Represents Q' d) : G2.Represents (G2.add Q Q') (b + d) := by
  refine ⟨G2.valid_add h.1 h'.1, ?_⟩
  rw [G2.toPoint_add h.1 h'.1, h.2, h'.2, G2.toPoint_mul_generator, G2.toPoint_mul_generator,
    G2.toPoint_mul_generator, G2.ofFr_add]

/-- A multiple by `s` of a representative of `b • g2` represents `(s * b) • g2`. -/
theorem G2.Represents.mul {Q : G2} {b : Fr} (h : G2.Represents Q b) (s : Fr) :
    G2.Represents (G2.mul Q s) (s * b) := by
  refine ⟨G2.valid_mul h.1 s, ?_⟩
  rw [G2.toPoint_mul h.1, h.2, G2.toPoint_mul_generator, G2.toPoint_mul_generator, G2.ofFr_mul]

namespace Signatures

/-- The bytes of a vector built from a byte array are that byte array. -/
private theorem bytes_of_vector {n : Nat} (b : ByteArray) (h : b.data.size = n) :
    (⟨(⟨b.data, h⟩ : Vector UInt8 n).toArray⟩ : ByteArray) = b :=
  rfl

/-- The scalar identity of a verification, stated over `ZMod` so that ring tactics apply. -/
private theorem one_mul_add_neg_mul (a b : ZMod Fr.modulus) : 1 * (a * b) + -a * b = 0 := by
  ring

/-- The core verification accepts a key for `a • g1` and a signature for `(a * b) • g2`.

Here the message hashes to a representative of `b • g2`, and `a` is not zero. -/
theorem coreVerify_of_represents (laws : PairingLaws) {P : G1} {S Q : G2} {a b : Fr}
    {msg dst : ByteArray} (hP : G1.Represents P a) (ha : a ≠ 0)
    (hQ : HashToCurve.hashToG2 msg dst = .ok Q) (hb : G2.Represents Q b)
    (hS : G2.Represents S (a * b)) :
    coreVerify (G1.compress P) msg (G2.compress S) dst = true := by
  obtain ⟨r, hr, hsub, hrep⟩ := G2.uncompress_compress_of_represents hS
  obtain ⟨P', hP', hP'rep⟩ := G1.keyValidatePoint_compress_of_represents hP ha
  have hcheck := (laws.two_pairs G1.represents_generator hrep hP'rep.neg hb).mpr
    (one_mul_add_neg_mul a b)
  unfold coreVerify
  rw [hr]
  dsimp only
  rw [show signatureSubgroupCheck r = true from hsub, hP']
  dsimp only
  -- Rewrite `true && _` first, so the kernel does not unfold the pairing check.
  rw [hQ, Bool.true_and]
  exact hcheck

/-- An honest core signature passes the core verification under the same tag. -/
theorem coreVerify_coreSign (laws : PairingLaws) (sk : SecretKey) (msg dst : ByteArray) :
    ∃ sig, coreSign sk msg dst = .ok sig ∧
      coreVerify ⟨(skToPk sk).toArray⟩ msg ⟨sig.toArray⟩ dst = true := by
  obtain ⟨Q, hQ, hv, hs⟩ := HashToCurve.hashToG2_total_inSubgroup msg dst
  obtain ⟨b, hb⟩ := (G2.inSubgroup_iff_exists_represents hv).mp hs
  refine ⟨pointToSignature (G2.mul Q sk.val), ?_, ?_⟩
  · simp only [coreSign, hQ, bind, Except.bind, pure, Except.pure]
  unfold skToPk pointToPubkey pointToSignature
  rw [bytes_of_vector, bytes_of_vector]
  exact coreVerify_of_represents laws (G1.represents_mul_generator sk.val) sk.property hQ hb
    (hb.mul sk.val)

/-- An honest signature verifies. -/
theorem verify_sign (laws : PairingLaws) (sk : SecretKey) (msg : ByteArray) :
    ∃ sig, sign sk msg = .ok sig ∧ verify ⟨(skToPk sk).toArray⟩ msg ⟨sig.toArray⟩ = true :=
  coreVerify_coreSign laws sk msg DST

/-- An honest proof of possession verifies. -/
theorem popVerify_popProve (laws : PairingLaws) (sk : SecretKey) :
    ∃ proof, popProve sk = .ok proof ∧
      popVerify ⟨(skToPk sk).toArray⟩ ⟨proof.toArray⟩ = true :=
  coreVerify_coreSign laws sk _ POP_DST


/-! ## Aggregation on one message -/

/-- The bytes of a signature. -/
abbrev sigBytes (sig : BLSSignature) : ByteArray := ⟨sig.toArray⟩

/-- The bytes of the public key of a secret key. -/
abbrev pkBytes (sk : SecretKey) : ByteArray := ⟨(skToPk sk).toArray⟩

/-- Over `ZMod`, folding one more term into a running sum is associative. -/
private theorem add_sum_cons (a x : ZMod Fr.modulus) (l : List (ZMod Fr.modulus)) :
    a + (x :: l).sum = a + x + l.sum := by
  rw [List.sum_cons]
  ring

/-- Over `ZMod`, a sum of multiples of `b` is the sum of the factors times `b`. -/
private theorem sum_map_mul {α : Type} (l : List α) (f : α → ZMod Fr.modulus)
    (b : ZMod Fr.modulus) : 0 + (l.map fun x => f x * b).sum = (0 + (l.map f).sum) * b := by
  rw [zero_add, zero_add, List.sum_map_mul_right]

/-- Signing on one message is the multiple of its hash by the key. -/
private theorem sign_eq {msg : ByteArray} {Q : G2} (hQ : HashToCurve.hashToG2 msg DST = .ok Q)
    (sk : SecretKey) : sign sk msg = .ok (pointToSignature (G2.mul Q sk.val)) := by
  simp only [sign, coreSign, hQ, bind, Except.bind, pure, Except.pure]

/-- Signing each key of a list succeeds with the multiples of the hash. -/
private theorem mapM_sign {msg : ByteArray} {Q : G2} (hQ : HashToCurve.hashToG2 msg DST = .ok Q)
    (sks : List SecretKey) :
    sks.mapM (fun sk => sign sk msg) =
      .ok (sks.map fun sk => pointToSignature (G2.mul Q sk.val)) := by
  induction sks with
  | nil => rfl
  | cons sk sks ih =>
    simp only [List.mapM_cons, sign_eq hQ, bind, Except.bind, pure, Except.pure] at ih ⊢
    rw [ih]
    rfl

/-- Aggregation of honest signatures from an accumulator represents the running sum. -/
private theorem foldlM_aggregate {α : Type} (pt : α → G2) (sc : α → Fr)
    (hpt : ∀ x, G2.Represents (pt x) (sc x)) (l : List α) {acc : G2} {a : Fr}
    (hacc : G2.Represents acc a) :
    ∃ R, (l.map fun x => sigBytes (pointToSignature (pt x))).foldlM
        (fun agg sig => do
          let p ← G2.uncompress sig
          pure (agg.add p)) acc = .ok R ∧
      G2.Represents R (a + (l.map sc).sum) := by
  induction l generalizing acc a with
  | nil => exact ⟨acc, rfl, (congrArg (G2.Represents acc) (Fin.add_zero a)).mpr hacc⟩
  | cons x l ih =>
    obtain ⟨r, hr, -, hrep⟩ := G2.uncompress_compress_of_represents (hpt x)
    obtain ⟨R, hR, hRrep⟩ := ih (hacc.add hrep)
    refine ⟨R, ?_, ?_⟩
    · simp only [List.map_cons, List.foldlM_cons, sigBytes, pointToSignature, hr,
        bind, Except.bind, pure, Except.pure]
      exact hR
    · rw [List.map_cons]
      exact (add_sum_cons a (sc x) _) ▸ hRrep

/-- Key validation and decoding accept the public key of a secret key, as a representative. -/
private theorem pkBytes_checks (sk : SecretKey) :
    ∃ P, (pkBytes sk).size = 48 ∧ (G1.keyValidate (pkBytes sk)).isOk = true ∧
      G1.uncompress (pkBytes sk) = .ok P ∧ G1.Represents P sk.val := by
  obtain ⟨P, hP, hrep⟩ := G1.keyValidatePoint_compress_mul sk.property
  have hb : pkBytes sk = G1.compress (G1.mul G1.generator sk.val) := rfl
  refine ⟨P, ?_, ?_, (G1.keyValidatePoint_eq_ok_iff.mp (hb ▸ hP)).1, hrep⟩
  · rw [hb]
    exact G1.size_compress _
  · simp only [G1.keyValidate, hb, hP, bind, Except.bind, pure, Except.pure]
    rfl

/-- The loop of the fast aggregate verification sums honest public keys without stopping. -/
private theorem forIn_pkBytes (sks : List SecretKey) {acc : G1} {a : Fr}
    (hacc : G1.Represents acc a) :
    ∃ R, forIn (m := Id) (sks.map pkBytes) ((none : Option Bool), acc)
        (fun pk (s : Option Bool × G1) =>
          if (decide (pk.size ≠ 48) || !(G1.keyValidate pk).isOk) = true then
            pure (ForInStep.done (some false, s.2))
          else
            match G1.uncompress pk with
            | .error _ => pure (ForInStep.done (some false, s.2))
            | .ok p => pure (ForInStep.yield (none, s.2.add p))) = (none, R) ∧
      G1.Represents R (a + (sks.map (·.val)).sum) := by
  induction sks generalizing acc a with
  | nil => exact ⟨acc, rfl, (congrArg (G1.Represents acc) (Fin.add_zero a)).mpr hacc⟩
  | cons sk sks ih =>
    obtain ⟨P, hsize, hvalid, hP, hrep⟩ := pkBytes_checks sk
    obtain ⟨R, hR, hRrep⟩ := ih (hacc.add hrep)
    refine ⟨R, ?_, ?_⟩
    · rw [List.map_cons, List.forIn_cons]
      simp only [hsize, hvalid, hP, ne_eq, not_true_eq_false, decide_false, Bool.not_true,
        Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      exact hR
    · rw [List.map_cons]
      exact (add_sum_cons a sk.val _) ▸ hRrep

/-- Honest signatures on one message aggregate to a signature that verifies under the key sum.

The secret keys must not sum to zero.

If they sum to zero, the aggregate key is the point at infinity, which key validation rejects. -/
theorem fastAggregateVerify_aggregate (laws : PairingLaws) (sks : List SecretKey) (hne : sks ≠ [])
    (hsum : (sks.map (·.val)).sum ≠ 0) (msg : ByteArray) :
    ∃ sigs, sks.mapM (fun sk => sign sk msg) = .ok sigs ∧
      ∃ sig, aggregate (sigs.map sigBytes).toArray = .ok sig ∧
        fastAggregateVerify (sks.map pkBytes).toArray msg (sigBytes sig) = true := by
  obtain ⟨Q, hQ, hv, hs⟩ := HashToCurve.hashToG2_total_inSubgroup msg DST
  obtain ⟨b, hb⟩ := (G2.inSubgroup_iff_exists_represents hv).mp hs
  have hpt : ∀ sk : SecretKey, G2.Represents (G2.mul Q sk.val) (sk.val * b) :=
    fun sk => hb.mul sk.val
  obtain ⟨S, hS, hSrep⟩ := foldlM_aggregate _ _ hpt sks G2.represents_zero
  obtain ⟨P, hP, hPrep⟩ := forIn_pkBytes sks G1.represents_zero
  refine ⟨_, mapM_sign hQ sks, pointToSignature S, ?_, ?_⟩
  · unfold aggregate
    rw [ite_eq_right (by cases sks with
      | nil => exact absurd rfl hne
      | cons _ _ => exact Bool.false_ne_true)]
    simp only [List.foldlM_toArray, List.map_map]
    rw [show (List.map (sigBytes ∘ fun sk => pointToSignature (G2.mul Q sk.val)) sks) =
      List.map (fun sk => sigBytes (pointToSignature (G2.mul Q sk.val))) sks from rfl, hS]
    rfl
  · unfold fastAggregateVerify
    rw [ite_eq_right (by cases sks with
      | nil => exact absurd rfl hne
      | cons _ _ => exact Bool.false_ne_true)]
    simp only [List.forIn_toArray]
    rw [Id.run_bind]
    erw [hP]
    -- The sum of the keys and the sum of the signatures fit one verification.
    have hS' : G2.Represents S ((0 + (sks.map (·.val)).sum) * b) :=
      (sum_map_mul sks (·.val) b) ▸ hSrep
    have ha : 0 + (sks.map (·.val)).sum ≠ 0 := fun h => hsum ((Fin.zero_add _).symm.trans h)
    exact coreVerify_of_represents laws hPrep ha hQ hb hS'


/-! ## Aggregation on several messages -/

/-- The hash of a message under the message tag. -/
private noncomputable def hashPoint (msg : ByteArray) : G2 :=
  Classical.choose (HashToCurve.hashToG2_total_inSubgroup msg DST)

private theorem hashPoint_spec (msg : ByteArray) :
    HashToCurve.hashToG2 msg DST = .ok (hashPoint msg) ∧ G2.Valid (hashPoint msg) ∧
      G2.inSubgroup (hashPoint msg) = true :=
  Classical.choose_spec (HashToCurve.hashToG2_total_inSubgroup msg DST)

/-- The discrete logarithm of the hash of a message, which exists but is never computed. -/
private noncomputable def hashScalar (msg : ByteArray) : Fr :=
  Classical.choose ((G2.inSubgroup_iff_exists_represents (hashPoint_spec msg).2.1).mp
    (hashPoint_spec msg).2.2)

private theorem hashScalar_spec (msg : ByteArray) :
    G2.Represents (hashPoint msg) (hashScalar msg) :=
  Classical.choose_spec ((G2.inSubgroup_iff_exists_represents (hashPoint_spec msg).2.1).mp
    (hashPoint_spec msg).2.2)

/-- The point that key validation returns for the public key of a secret key. -/
private noncomputable def keyPoint (sk : SecretKey) : G1 :=
  Classical.choose (G1.keyValidatePoint_compress_mul sk.property)

private theorem keyPoint_spec (sk : SecretKey) :
    G1.keyValidatePoint (pkBytes sk) = .ok (keyPoint sk) ∧ G1.Represents (keyPoint sk) sk.val :=
  Classical.choose_spec (G1.keyValidatePoint_compress_mul sk.property)

/-- Signing each pair of a key and a message succeeds with the multiple of its hash. -/
private theorem mapM_sign_pairs (l : List (SecretKey × ByteArray)) :
    l.mapM (fun p => sign p.1 p.2) =
      .ok (l.map fun p => pointToSignature (G2.mul (hashPoint p.2) p.1.val)) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.mapM_cons, sign_eq (hashPoint_spec p.2).1, bind, Except.bind, pure,
      Except.pure] at ih ⊢
    rw [ih]
    rfl

/-- The pairs that the aggregate verification builds from honest keys and messages. -/
private theorem mapM_pairs (l : List (SecretKey × ByteArray)) :
    (l.map fun p => (pkBytes p.1, p.2)).mapM (fun x => do
        let xP ← G1.keyValidatePoint x.1
        let q ← HashToCurve.hashToG2 x.2 DST
        pure (G1.neg xP, q)) =
      .ok (l.map fun p => (G1.neg (keyPoint p.1), hashPoint p.2)) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mapM_cons, (keyPoint_spec p.1).1, (hashPoint_spec p.2).1,
      bind, Except.bind, pure, Except.pure] at ih ⊢
    rw [ih]

/-- Over `ZMod`, the scalars of an aggregate verification cancel. -/
private theorem aggregate_scalars {α : Type} (l : List α) (f g : α → ZMod Fr.modulus) :
    (List.zipWith (· * ·) (1 :: l.map fun x => -f x)
      ((0 + (l.map fun x => f x * g x).sum) :: l.map g)).sum = 0 := by
  rw [List.zipWith_cons_cons, List.sum_cons, List.zipWith_map, List.zipWith_self, zero_add,
    one_mul]
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    linear_combination ih

/-- Zipping two maps of one list maps the list to pairs. -/
private theorem zip_map_map {α β γ : Type} (l : List α) (f : α → β) (g : α → γ) :
    (l.map f).zip (l.map g) = l.map fun x => (f x, g x) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- Honest signatures on several messages aggregate to a signature that verifies.

The messages need not differ, as the proof-of-possession scheme allows. -/
theorem aggregateVerify_aggregate (laws : PairingLaws) (l : List (SecretKey × ByteArray))
    (hne : l ≠ []) :
    ∃ sigs, l.mapM (fun p => sign p.1 p.2) = .ok sigs ∧
      ∃ sig, aggregate (sigs.map sigBytes).toArray = .ok sig ∧
        aggregateVerify (l.map (pkBytes ·.1)).toArray (l.map (·.2)).toArray (sigBytes sig) =
          true := by
  have hpt : ∀ p : SecretKey × ByteArray,
      G2.Represents (G2.mul (hashPoint p.2) p.1.val) (p.1.val * hashScalar p.2) :=
    fun p => (hashScalar_spec p.2).mul p.1.val
  obtain ⟨S, hS, hSrep⟩ := foldlM_aggregate _ _ hpt l G2.represents_zero
  refine ⟨_, mapM_sign_pairs l, pointToSignature S, ?_, ?_⟩
  · unfold aggregate
    rw [ite_eq_right (by cases l with
      | nil => exact absurd rfl hne
      | cons _ _ => exact Bool.false_ne_true)]
    simp only [List.foldlM_toArray, List.map_map]
    rw [show (List.map (sigBytes ∘ fun p => pointToSignature (G2.mul (hashPoint p.2) p.1.val)) l) =
      List.map (fun p => sigBytes (pointToSignature (G2.mul (hashPoint p.2) p.1.val))) l from rfl,
      hS]
    rfl
  · obtain ⟨r, hr, hsub, hrep⟩ := G2.uncompress_compress_of_represents hSrep
    unfold aggregateVerify coreAggregateVerify
    rw [ite_eq_right (by cases l with
      | nil => exact absurd rfl hne
      | cons _ _ => simp)]
    rw [show sigBytes (pointToSignature S) = G2.compress S from rfl, hr]
    dsimp only
    rw [show signatureSubgroupCheck r = true from hsub, Bool.true_and, List.zip_toArray,
      zip_map_map, List.mapM_toArray, mapM_pairs]
    dsimp only [Functor.map, Except.map]
    -- One pair for the signature, then one for each key and message.
    have hpairs : #[(G1.generator, r)] ++
        (l.map fun p => (G1.neg (keyPoint p.1), hashPoint p.2)).toArray =
        ((G1.generator, r) :: l.map fun p => (G1.neg (keyPoint p.1), hashPoint p.2)).toArray := by
      simp
    rw [hpairs]
    refine (laws.pairingCheck_iff
      ((G1.generator, r) :: l.map fun p => (G1.neg (keyPoint p.1), hashPoint p.2))
      (1 :: l.map fun p => -p.1.val)
      ((0 + (l.map fun p => p.1.val * hashScalar p.2).sum) :: l.map fun p => hashScalar p.2)
      (by rw [List.length_cons, List.length_map, List.length_cons, List.length_map])
      (by rw [List.length_cons, List.length_map, List.length_cons, List.length_map]) ?_).mpr ?_
    · intro i hi
      cases i with
      | zero => exact ⟨G1.represents_generator, hrep⟩
      | succ i =>
        simp only [List.length_cons, List.length_map, Nat.add_lt_add_iff_right] at hi
        simp only [List.getElem_cons_succ, List.getElem_map, List.getElem!_cons_succ]
        rw [getElem!_pos _ i (by simpa using hi), getElem!_pos _ i (by simpa using hi)]
        simp only [List.getElem_map]
        exact ⟨(keyPoint_spec _).2.neg, hashScalar_spec _⟩
    · exact aggregate_scalars l (fun p => p.1.val) (fun p => hashScalar p.2)


/-! ## The Ethereum wrapper -/

/-- With no keys, the Ethereum fast aggregate verification accepts only the point at infinity. -/
theorem ethFastAggregateVerify_empty (msg sig : ByteArray) :
    ethFastAggregateVerify #[] msg sig = true ↔ sig = G2_POINT_AT_INFINITY := by
  simp [ethFastAggregateVerify]

/-- Honest signatures on one message pass the Ethereum fast aggregate verification.

The secret keys must not sum to zero. -/
theorem ethFastAggregateVerify_aggregate (laws : PairingLaws) (sks : List SecretKey)
    (hne : sks ≠ []) (hsum : (sks.map (·.val)).sum ≠ 0) (msg : ByteArray) :
    ∃ sigs, sks.mapM (fun sk => sign sk msg) = .ok sigs ∧
      ∃ sig, aggregate (sigs.map sigBytes).toArray = .ok sig ∧
        ethFastAggregateVerify (sks.map pkBytes).toArray msg (sigBytes sig) = true := by
  obtain ⟨sigs, hsigs, sig, hagg, hv⟩ := fastAggregateVerify_aggregate laws sks hne hsum msg
  refine ⟨sigs, hsigs, sig, hagg, ?_⟩
  unfold ethFastAggregateVerify
  rw [ite_eq_right (by cases sks with
    | nil => exact absurd rfl hne
    | cons _ _ => exact Bool.false_ne_true)]
  exact hv

end Signatures

end EthLib.Cryptography.Bls
