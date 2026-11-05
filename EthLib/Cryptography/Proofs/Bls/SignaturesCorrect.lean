module

public import EthLib.Cryptography.Proofs.Bls.Signatures
public import EthLib.Cryptography.Proofs.Bls.Represents
public import EthLib.Cryptography.Proofs.Bls.KeyValidate
public import EthLib.Cryptography.Proofs.Bls.CofactorSubgroupLanding
public import EthLib.Base.Proofs.MapM

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

/-- The point at infinity represents `0 • g2`. -/
theorem G2.represents_zero : G2.Represents G2.zero 0 :=
  ⟨G2.valid_zero, by rw [G2.toPoint_zero, G2.toPoint_mul_generator, G2.ofFr_zero]⟩

namespace Signatures

/-- The bytes of a vector built from a byte array are that byte array. -/
private theorem bytes_of_vector {n : Nat} (b : ByteArray) (h : b.data.size = n) :
    (⟨(⟨b.data, h⟩ : Vector UInt8 n).toArray⟩ : ByteArray) = b :=
  rfl

/-- The scalar identity of a verification. -/
private theorem one_mul_add_neg_mul (a b : Fr) : 1 * (a * b) + -a * b = 0 := by
  ring

/-- The bytes of the public key of a point are its compression.

It is stated on a variable point, so the kernel never evaluates a compression. -/
theorem pointToPubkey_bytes (p : G1) :
    (⟨(pointToPubkey p).toArray⟩ : ByteArray) = G1.compress p := by
  unfold pointToPubkey
  exact bytes_of_vector _ _

/-- The bytes of the signature of a point are its compression. -/
theorem pointToSignature_bytes (p : G2) :
    (⟨(pointToSignature p).toArray⟩ : ByteArray) = G2.compress p := by
  unfold pointToSignature
  exact bytes_of_vector _ _

/-- The bytes of the public key of a secret key are the compressed multiple of the generator. -/
theorem skToPk_bytes (sk : SecretKey) :
    (⟨(skToPk sk).toArray⟩ : ByteArray) = G1.compress (G1.mul G1.generator sk.val) := by
  unfold skToPk
  exact pointToPubkey_bytes _

/-- A success passed on to a pure function gives its value. -/
theorem bind_ok_pure {ε α β : Type} (a : α) (f : α → β) :
    ((Except.ok a : Except ε α) >>= fun q => pure (f q)) = .ok (f a) :=
  rfl

/-- The core signature is the multiple of the hash by the secret key. -/
theorem coreSign_eq {msg dst : ByteArray} {Q : G2}
    (hQ : HashToCurve.hashToG2 msg dst = .ok Q) (sk : SecretKey) :
    coreSign sk msg dst = .ok (pointToSignature (G2.mul Q sk.val)) := by
  -- Rewrite the hash first, and close on variables, so the kernel never evaluates a point.
  unfold coreSign
  rw [hQ]
  exact bind_ok_pure Q fun q => pointToSignature (G2.mul q sk.val)

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
  · exact coreSign_eq hQ sk
  refine (congrArg₂ (fun pk sig => coreVerify pk msg sig dst = true) (skToPk_bytes sk)
    (pointToSignature_bytes _)).mpr ?_
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

/-- Folding one more term into a running sum is associative. -/
private theorem add_sum_cons (a x : Fr) (l : List Fr) :
    a + (x :: l).sum = a + x + l.sum := by
  rw [List.sum_cons]
  ring

/-- A sum of multiples of `b` is the sum of the factors times `b`. -/
private theorem sum_map_mul {α : Type} (l : List α) (f : α → Fr)
    (b : Fr) : 0 + (l.map fun x => f x * b).sum = (l.map f).sum * b := by
  rw [zero_add, List.sum_map_mul_right]

/-- Signing on one message is the multiple of its hash by the key. -/
private theorem sign_eq {msg : ByteArray} {Q : G2} (hQ : HashToCurve.hashToG2 msg DST = .ok Q)
    (sk : SecretKey) : sign sk msg = .ok (pointToSignature (G2.mul Q sk.val)) :=
  coreSign_eq hQ sk

/-- Signing each key of a list succeeds with the multiples of the hash. -/
private theorem mapM_sign {msg : ByteArray} {Q : G2} (hQ : HashToCurve.hashToG2 msg DST = .ok Q)
    (sks : List SecretKey) :
    sks.mapM (fun sk => sign sk msg) =
      .ok (sks.map fun sk => pointToSignature (G2.mul Q sk.val)) :=
  EthLib.Base.mapM_eq_ok_map fun sk _ => sign_eq hQ sk

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
  | nil => exact ⟨acc, rfl, (congrArg (G2.Represents acc) (add_zero a)).mpr hacc⟩
  | cons x l ih =>
    obtain ⟨r, hr, -, hrep⟩ := G2.uncompress_compress_of_represents (hpt x)
    obtain ⟨R, hR, hRrep⟩ := ih (hacc.add hrep)
    refine ⟨R, ?_, ?_⟩
    · -- Rewrite the decoding first, so the kernel never evaluates it.
      simp only [List.map_cons, List.foldlM_cons, sigBytes, pointToSignature]
      rw [hr]
      exact hR
    · rw [List.map_cons]
      exact (add_sum_cons a (sc x) _) ▸ hRrep

/-- The public key of a secret key is the compressed multiple of the generator. -/
theorem pkBytes_eq (sk : SecretKey) :
    pkBytes sk = G1.compress (G1.mul G1.generator sk.val) :=
  skToPk_bytes sk

/-- Key validation and decoding accept the public key of a secret key, as a representative. -/
private theorem pkBytes_checks (sk : SecretKey) :
    ∃ P, (pkBytes sk).size = 48 ∧ (G1.keyValidate (pkBytes sk)).isOk = true ∧
      G1.uncompress (pkBytes sk) = .ok P ∧ G1.Represents P sk.val := by
  obtain ⟨P, hP, hrep⟩ := G1.keyValidatePoint_compress_mul sk.property
  have hb := pkBytes_eq sk
  refine ⟨P, ?_, ?_, (G1.keyValidatePoint_eq_ok_iff.mp (hb ▸ hP)).1, hrep⟩
  · rw [hb]
    exact G1.size_compress _
  · -- Rewrite the validation first, so the kernel never evaluates it.
    unfold G1.keyValidate
    rw [hb, hP]
    rfl

/-- One step of the loop of the fast aggregate verification adds a valid key.

It is stated on a variable key, so the kernel never evaluates a public key. -/
private theorem forIn_cons_valid {pk : ByteArray} {P : G1} (hsize : pk.size = 48)
    (hvalid : (G1.keyValidate pk).isOk = true) (hP : G1.uncompress pk = .ok P)
    (rest : List ByteArray) (acc : G1) :
    forIn (m := Id) (pk :: rest) ((none : Option Bool), acc)
        (fun pk (s : Option Bool × G1) =>
            if (decide (pk.size ≠ 48) || !(G1.keyValidate pk).isOk) = true then
              pure (ForInStep.done (some false, s.2))
            else
              match G1.uncompress pk with
              | .error _ => pure (ForInStep.done (some false, s.2))
              | .ok p => pure (ForInStep.yield (none, s.2.add p))) =
      forIn (m := Id) rest ((none : Option Bool), acc.add P)
        (fun pk (s : Option Bool × G1) =>
            if (decide (pk.size ≠ 48) || !(G1.keyValidate pk).isOk) = true then
              pure (ForInStep.done (some false, s.2))
            else
              match G1.uncompress pk with
              | .error _ => pure (ForInStep.done (some false, s.2))
              | .ok p => pure (ForInStep.yield (none, s.2.add p))) := by
  rw [List.forIn_cons]
  simp only [hsize, hvalid, hP, ne_eq, not_true_eq_false, decide_false, Bool.not_true,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte]
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
  | nil => exact ⟨acc, rfl, (congrArg (G1.Represents acc) (add_zero a)).mpr hacc⟩
  | cons sk sks ih =>
    obtain ⟨P, hsize, hvalid, hP, hrep⟩ := pkBytes_checks sk
    obtain ⟨R, hR, hRrep⟩ := ih (hacc.add hrep)
    refine ⟨R, ?_, ?_⟩
    · rw [List.map_cons, forIn_cons_valid hsize hvalid hP]
      exact hR
    · rw [List.map_cons]
      exact (add_sum_cons a sk.val _) ▸ hRrep

/-- The fast aggregate verification accepts honest keys and a signature for their sum.

The signature must represent `(sum_i sk_i * b) • g2`, where the message hashes to `b • g2`. -/
theorem fastAggregateVerify_of_represents (laws : PairingLaws) {sks : List SecretKey}
    (hne : sks ≠ []) (hsum : (sks.map (·.val)).sum ≠ 0) {msg : ByteArray} {Q S : G2} {b : Fr}
    (hQ : HashToCurve.hashToG2 msg DST = .ok Q) (hb : G2.Represents Q b)
    (hS : G2.Represents S ((sks.map (·.val)).sum * b)) :
    fastAggregateVerify (sks.map pkBytes).toArray msg (G2.compress S) = true := by
  obtain ⟨P, hP, hPrep⟩ := forIn_pkBytes sks G1.represents_zero
  unfold fastAggregateVerify
  rw [ite_eq_right (by cases sks with
    | nil => exact absurd rfl hne
    | cons _ _ => exact Bool.false_ne_true)]
  simp only [List.forIn_toArray]
  rw [Id.run_bind]
  erw [hP]
  -- The loop starts from the point at infinity, so its sum carries a leading `0 +`.
  have hPrep' : G1.Represents P (sks.map (·.val)).sum :=
    (congrArg (G1.Represents P) (zero_add _)).mp hPrep
  exact coreVerify_of_represents laws hPrep' hsum hQ hb hS

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
  refine ⟨_, mapM_sign hQ sks, pointToSignature S, ?_, ?_⟩
  · unfold aggregate
    rw [ite_eq_right (by cases sks with
      | nil => exact absurd rfl hne
      | cons _ _ => exact Bool.false_ne_true)]
    simp only [List.foldlM_toArray, List.map_map]
    rw [show (List.map (sigBytes ∘ fun sk => pointToSignature (G2.mul Q sk.val)) sks) =
      List.map (fun sk => sigBytes (pointToSignature (G2.mul Q sk.val))) sks from rfl, hS]
    rfl
  · -- The sum of the signatures is the sum of the keys times the discrete logarithm of the hash.
    exact fastAggregateVerify_of_represents laws hne hsum hQ hb
      ((sum_map_mul sks (·.val) b) ▸ hSrep)

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
    G1.keyValidatePoint (pkBytes sk) = .ok (keyPoint sk) ∧ G1.Represents (keyPoint sk) sk.val := by
  rw [pkBytes_eq]
  exact Classical.choose_spec (G1.keyValidatePoint_compress_mul sk.property)

/-- Signing each pair of a key and a message succeeds with the multiple of its hash. -/
private theorem mapM_sign_pairs (l : List (SecretKey × ByteArray)) :
    l.mapM (fun p => sign p.1 p.2) =
      .ok (l.map fun p => pointToSignature (G2.mul (hashPoint p.2) p.1.val)) :=
  EthLib.Base.mapM_eq_ok_map fun p _ => sign_eq (hashPoint_spec p.2).1 p.1

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
    -- Rewrite the key and the hash first, so the kernel never evaluates them.
    simp only [List.map_cons, List.mapM_cons]
    rw [(keyPoint_spec p.1).1, (hashPoint_spec p.2).1, ih]
    rfl

/-- The scalars of an aggregate verification cancel. -/
private theorem aggregate_scalars {α : Type} (l : List α) (f g : α → Fr) :
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
    rw [show sigBytes (pointToSignature S) = G2.compress S from pointToSignature_bytes S, hr]
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

/-- The signature of the point at infinity is the constant of the Ethereum wrapper. -/
theorem pointToSignature_zero : pointToSignature G2.zero = infinitySignature := by
  simp [pointToSignature, infinitySignature, G2_POINT_AT_INFINITY]

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
