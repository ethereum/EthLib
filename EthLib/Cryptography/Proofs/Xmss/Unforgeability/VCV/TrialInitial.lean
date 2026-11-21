module

public import EthLib.Cryptography.Proofs.Xmss.SignatureFailure
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialSource
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RegisteredDigest

/-!
# The message cache at key generation

The leanXMSS draft separates message hashes from tree hashes in "Hashing and parameters".

Its key generator derives the scheme seed, the public parameter and the top root.

These computations leave every message input available for a fresh trial.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch.Trials

open Constants HashSig OracleComp OracleSpec CachedCodeword PostSigning

local notation "Hq" => queryH (m := OracleComp OracleWorld)

private theorem tree_hash_avoids {pp : PublicParam} {l : Layer} {e : UInt32} {k : Nat}
    {a : Address} {payload : ByteArray} (other : a ≠ addrMsg l e) :
    IsQueryBoundP (th Hq pp a payload) (IsTrialQuery (addrMsg l e) k) 0 :=
  isQueryBoundP_bind_zero _ _ (isQueryBoundP_queryH_of_ne k pp payload other)
    fun _ => isQueryBoundP_pure _ _ _

private theorem leaf_avoids (pp : PublicParam) (seed : Seed) (i : UInt32)
    (l : Layer) (e : UInt32) (k : Nat) :
    IsQueryBoundP (otsPublicLeaf Hq pp (seedPrf Hq seed) .top i)
      (IsTrialQuery (addrMsg l e) k) 0 := by
  -- The first seed query in each chain uses the PRF address.
  refine isQueryBoundP_bind_zero _ _ (isQueryBoundP_bind_zero _ _
    (ofFnInOrder_isQueryBoundP_zero _ _ fun _ => isQueryBoundP_queryH_of_ne k pp _
      (encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide))) fun _ => isQueryBoundP_pure _ _ _) ?_
  -- Chain steps and the final leaf compression use two further address types.
  exact fun _ => isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
    chain_isQueryBoundP_zero _ (fun _ _ => tree_hash_avoids
      (encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide))) _ _ _ _) fun _ =>
      tree_hash_avoids (encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide))

private theorem node_avoids (pp : PublicParam) (seed : Seed) (level j : Nat)
    (l : Layer) (e : UInt32) (k : Nat) :
    IsQueryBoundP (node Hq pp (seedPrf Hq seed) .top level j) (IsTrialQuery (addrMsg l e) k) 0 :=
  merkleNode_isQueryBoundP_zero _ _ (fun _ => leaf_avoids pp seed _ l e k)
    (fun _ _ _ => tree_hash_avoids (encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide))) _

private theorem key_avoids (seed : Seed) (l : Layer) (e : UInt32) (k : Nat) (hk : 8 < k) :
    IsQueryBoundP (schemeSeed Hq seed >>= fun s => publicKeyOf Hq (seedPrf Hq s))
      (IsTrialQuery (addrMsg l e) k) 0 := by
  apply isQueryBoundP_bind_zero (schemeSeed Hq seed) (fun s => publicKeyOf Hq (seedPrf Hq s))
    (schemeSeed_isQueryBoundP seed _ hk)
  intro s
  unfold publicKeyOf
  generalize LAYER_HEIGHT = height
  apply isQueryBoundP_bind_zero (publicParamOf (seedPrf Hq s)) _
    (publicParamOf_isQueryBoundP s l e k)
  intro pp
  -- Keep the root computation intact while attaching its public parameter.
  exact isQueryBoundP_bind_zero (node Hq pp (seedPrf Hq s) .top height 0)
    (fun root => pure ({ root, publicParam := pp } : PublicKey))
    (node_avoids pp s height 0 l e k) (fun _ => isQueryBoundP_pure _ _ _)

private theorem erase_meter {α : Type} (body : OracleComp World α)
    (s : HashSpec.QueryCache × Nat) {z}
    (hz : z ∈ support ((simulateQ randomOracle.Targets.publicMeter body).run s)) :
    (z.1, z.2.1) ∈ support ((simulateQ HashSpec.romImpl body).run s.1) := by
  rw [← extendState_run_proj_eq _ _ body s.1 s.2, support_map]
  exact ⟨z, hz, rfl⟩

/-- Every encoded message input is cold after the original key generator and its physical meter. -/
theorem initialKey_cold {z} (hz : z ∈ support initialKey)
    (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) (r : Randomizer) :
    z.2.2.1 (trialInput pp l e msg r) = none := by
  simp only [initialKey, support_bind, Set.mem_iUnion, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨u, hu, v, hv, rfl⟩ := hz
  -- Sampling the master seed uses private coins and leaves the hash cache empty.
  have seed := erase_meter _ _ hu
  rw [run_simulateQ_unifFwdImpl_add_liftM, support_map] at seed
  obtain ⟨_, _, same⟩ := seed
  have empty : (∅ : HashSpec.QueryCache) = u.2.1 := congrArg Prod.snd same
  have keyed := erase_meter _ _ hv
  apply cache_eq_none_of_mem_support_run_romImpl
    (key_avoids _ l e (msg.size + 16) (by omega)) (z := (v.1, v.2.1)) _ keyed
  · exact ⟨pp, _, by rw [ByteArray.size_append, Base.size_packBytes, RANDOMIZER_LEN], rfl⟩
  · intro b _
    rw [← empty]
    rfl

/-- No row that is already cached at key generation belongs to a watched message key. -/
theorem initialKey_other {z} (hz : z ∈ support initialKey) (pp : PublicParam)
    (b : HashInput) {w : HashOutput} (present : z.2.2.1 b = some w) : messageKey pp b = none := by
  classical
  unfold messageKey
  split
  next encoded =>
    obtain ⟨⟨l, e⟩, msg, r, rfl⟩ := encoded
    rw [initialKey_cold hz pp l e msg r] at present
    contradiction
  next => rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch.Trials
