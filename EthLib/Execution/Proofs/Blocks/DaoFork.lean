module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.DaoFork
public import EthLib.Execution.Proofs.State.Tracker
import EthLib.Base.Proofs.ByteOrder

/-!
# Proofs: the DAO Fork

The list holds 116 distinct accounts, and the recovery contract is not among them.

After the fork every listed account holds no ether, and the recovery contract holds their ether.

Every other account is unchanged, so the fork creates and destroys no ether.

The fork succeeds exactly when the listed accounts and the contract hold under 2^256 wei in total.

On mainnet, blocks 1,920,000 to 1,920,009 must carry the fork's extra data.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State
open EthLib.Execution.State.TransactionState

/-- The list holds 116 accounts. -/
theorem length_daoAccounts : DAO_ACCOUNTS.length = 116 := rfl

/-- The 116 account numbers of the DAO Fork, in the order of `DAO_ACCOUNTS`. -/
private def daoAccountNats : List Nat := [
  0xd4fe7bc31cedb7bfb8a345f31e668033056b2728, 0xb3fb0e5aba0e20e5c49d252dfd30e102b171a425,
  0x2c19c7f9ae8b751e37aeb2d93a699722395ae18f, 0xecd135fa4f61a655311e86238c92adcd779555d2,
  0x1975bd06d486162d5dc297798dfc41edd5d160a7, 0xa3acf3a1e16b1d7c315e23510fdd7847b48234f6,
  0x319f70bab6845585f412ec7724b744fec6095c85, 0x06706dd3f2c9abf0a21ddcc6941d9b86f0596936,
  0x5c8536898fbb74fc7445814902fd08422eac56d0, 0x6966ab0d485353095148a2155858910e0965b6f9,
  0x779543a0491a837ca36ce8c635d6154e3c4911a6, 0x2a5ed960395e2a49b1c758cef4aa15213cfd874c,
  0x5c6e67ccd5849c0d29219c4f95f1a7a93b3f5dc5, 0x9c50426be05db97f5d64fc54bf89eff947f0a321,
  0x200450f06520bdd6c527622a273333384d870efb, 0xbe8539bfe837b67d1282b2b1d61c3f723966f049,
  0x6b0c4d41ba9ab8d8cfb5d379c69a612f2ced8ecb, 0xf1385fb24aad0cd7432824085e42aff90886fef5,
  0xd1ac8b1ef1b69ff51d1d401a476e7e612414f091, 0x8163e7fb499e90f8544ea62bbf80d21cd26d9efd,
  0x51e0ddd9998364a2eb38588679f0d2c42653e4a6, 0x627a0a960c079c21c34f7612d5d230e01b4ad4c7,
  0xf0b1aa0eb660754448a7937c022e30aa692fe0c5, 0x24c4d950dfd4dd1902bbed3508144a54542bba94,
  0x9f27daea7aca0aa0446220b98d028715e3bc803d, 0xa5dc5acd6a7968a4554d89d65e59b7fd3bff0f90,
  0xd9aef3a1e38a39c16b31d1ace71bca8ef58d315b, 0x63ed5a272de2f6d968408b4acb9024f4cc208ebf,
  0x6f6704e5a10332af6672e50b3d9754dc460dfa4d, 0x77ca7b50b6cd7e2f3fa008e24ab793fd56cb15f6,
  0x492ea3bb0f3315521c31f273e565b868fc090f17, 0x0ff30d6de14a8224aa97b78aea5388d1c51c1f00,
  0x9ea779f907f0b315b364b0cfc39a0fde5b02a416, 0xceaeb481747ca6c540a000c1f3641f8cef161fa7,
  0xcc34673c6c40e791051898567a1222daf90be287, 0x579a80d909f346fbfb1189493f521d7f48d52238,
  0xe308bd1ac5fda103967359b2712dd89deffb7973, 0x4cb31628079fb14e4bc3cd5e30c2f7489b00960c,
  0xac1ecab32727358dba8962a0f3b261731aad9723, 0x4fd6ace747f06ece9c49699c7cabc62d02211f75,
  0x440c59b325d2997a134c2c7c60a8c61611212bad, 0x4486a3d68fac6967006d7a517b889fd3f98c102b,
  0x9c15b54878ba618f494b38f0ae7443db6af648ba, 0x27b137a85656544b1ccb5a0f2e561a5703c6a68f,
  0x21c7fdb9ed8d291d79ffd82eb2c4356ec0d81241, 0x23b75c2f6791eef49c69684db4c6c1f93bf49a50,
  0x1ca6abd14d30affe533b24d7a21bff4c2d5e1f3b, 0xb9637156d330c0d605a791f1c31ba5890582fe1c,
  0x6131c42fa982e56929107413a9d526fd99405560, 0x1591fc0f688c81fbeb17f5426a162a7024d430c2,
  0x542a9515200d14b68e934e9830d91645a980dd7a, 0xc4bbd073882dd2add2424cf47d35213405b01324,
  0x782495b7b3355efb2833d56ecb34dc22ad7dfcc4, 0x58b95c9a9d5d26825e70a82b6adb139d3fd829eb,
  0x3ba4d81db016dc2890c81f3acec2454bff5aada5, 0xb52042c8ca3f8aa246fa79c3feaa3d959347c0ab,
  0xe4ae1efdfc53b73893af49113d8694a057b9c0d1, 0x3c02a7bc0391e86d91b7d144e61c2c01a25a79c5,
  0x0737a6b837f97f46ebade41b9bc3e1c509c85c53, 0x97f43a37f595ab5dd318fb46e7a155eae057317a,
  0x52c5317c848ba20c7504cb2c8052abd1fde29d03, 0x4863226780fe7c0356454236d3b1c8792785748d,
  0x5d2b2e6fcbe3b11d26b525e085ff818dae332479, 0x5f9f3392e9f62f63b8eac0beb55541fc8627f42c,
  0x057b56736d32b86616a10f619859c6cd6f59092a, 0x9aa008f65de0b923a2a4f02012ad034a5e2e2192,
  0x304a554a310c7e546dfe434669c62820b7d83490, 0x914d1b8b43e92723e64fd0a06f5bdb8dd9b10c79,
  0x4deb0033bb26bc534b197e61d19e0733e5679784, 0x07f5c1e1bc2c93e0402f23341973a0e043f7bf8a,
  0x35a051a0010aba705c9008d7a7eff6fb88f6ea7b, 0x4fa802324e929786dbda3b8820dc7834e9134a2a,
  0x9da397b9e80755301a3b32173283a91c0ef6c87e, 0x8d9edb3054ce5c5774a420ac37ebae0ac02343c6,
  0x0101f3be8ebb4bbd39a2e3b9a3639d4259832fd9, 0x5dc28b15dffed94048d73806ce4b7a4612a1d48f,
  0xbcf899e6c7d9d5a215ab1e3444c86806fa854c76, 0x12e626b0eebfe86a56d633b9864e389b45dcb260,
  0xa2f1ccba9395d7fcb155bba8bc92db9bafaeade7, 0xec8e57756626fdc07c63ad2eafbd28d08e7b0ca5,
  0xd164b088bd9108b60d0ca3751da4bceb207b0782, 0x6231b6d0d5e77fe001c2a460bd9584fee60d409b,
  0x1cba23d343a983e9b5cfd19496b9a9701ada385f, 0xa82f360a8d3455c5c41366975bde739c37bfeb8a,
  0x9fcd2deaff372a39cc679d5c5e4de7bafb0b1339, 0x005f5cee7a43331d5a3d3eec71305925a62f34b6,
  0x0e0da70933f4c7849fc0d203f5d1d43b9ae4532d, 0xd131637d5275fd1a68a3200f4ad25c71a2a9522e,
  0xbc07118b9ac290e4622f5e77a0853539789effbe, 0x47e7aa56d6bdf3f36be34619660de61275420af8,
  0xacd87e28b0c9d1254e868b81cba4cc20d9a32225, 0xadf80daec7ba8dcf15392f1ac611fff65d94f880,
  0x5524c55fb03cf21f549444ccbecb664d0acad706, 0x40b803a9abce16f50f36a77ba41180eb90023925,
  0xfe24cdd8648121a43a7c86d289be4dd2951ed49f, 0x17802f43a0137c506ba92291391a8a8f207f487d,
  0x253488078a4edf4d6f42f113d1e62836a942cf1a, 0x86af3e9626fce1957c82e88cbf04ddf3a2ed7915,
  0xb136707642a4ea12fb4bae820f03d2562ebff487, 0xdbe9b615a3ae8709af8b93336ce9b477e4ac0940,
  0xf14c14075d6c4ed84b86798af0956deef67365b5, 0xca544e5c4687d109611d0f8f928b53a25af72448,
  0xaeeb8ff27288bdabc0fa5ebb731b6f409507516c, 0xcbb9d3703e651b0d496cdefb8b92c25aeb2171f7,
  0x6d87578288b6cb5549d5076a207456a1f6a63dc0, 0xb2c6f0dfbb716ac562e2d85d6cb2f8d5ee87603e,
  0xaccc230e8a6e5be9160b8cdf2864dd2a001c28b6, 0x2b3455ec7fedf16e646268bf88846bd7a2319bb2,
  0x4613f3bca5c44ea06337a9e439fbc6d42e501d0a, 0xd343b217de44030afaa275f54d31a9317c7f441e,
  0x84ef4b2357079cd7a7c69fd7a37cd0609a679106, 0xda2fef9e4a3230988ff17df2165440f37e8b1708,
  0xf4c64518ea10f995918a454158c6b61407ea345c, 0x7602b46df5390e432ef1c307d4f2c9ff6d65cc97,
  0xbb9bc244d798123fde783fcc1c72d3bb8c189413, 0x807640a13483f8ac783c557fcdf27be11ea4ac7a]

/-- A strictly increasing list of naturals has no duplicates. -/
private theorem nodup_of_strictly_increasing :
    ∀ {l : List Nat}, l.Pairwise (· < ·) → l.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, List.Pairwise.cons hhead htail =>
    List.nodup_cons.mpr ⟨fun hmem => Nat.ne_of_lt (hhead _ hmem) rfl,
      nodup_of_strictly_increasing htail⟩

/-- Check strictly increasing order in one linear pass. -/
private def strictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && strictlyIncreasing (b :: rest)

/-- A list that passes the linear adjacent check is pairwise strictly increasing. -/
private theorem pairwise_lt_of_strictlyIncreasing :
    ∀ {l : List Nat}, strictlyIncreasing l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have htail := pairwise_lt_of_strictlyIncreasing h.2
    refine List.Pairwise.cons (fun c hc => ?_) htail
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons htail hc)

/-- Insert a natural into a list in ascending order, structurally so the kernel reduces it. -/
private def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Structural insertion sort on naturals. -/
private def sortNats : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (sortNats xs)

/-- Insertion produces a permutation of cons. -/
private theorem insertSorted_perm (x : Nat) : ∀ l, (insertSorted x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertSorted
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons y (insertSorted_perm x ys)).trans (List.Perm.swap x y ys)

/-- Sorting produces a permutation of the input list. -/
private theorem sortNats_perm : ∀ l, (sortNats l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertSorted_perm x (sortNats xs)).trans (List.Perm.cons x (sortNats_perm xs))

/-- Mapping a function injective on list elements preserves `Nodup`. -/
private theorem nodup_map_of_inj_on {α β : Type} {f : α → β} {l : List α}
    (hn : l.Nodup) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact hn.imp_of_mem fun ha hb hne heq => hne (hinj _ ha _ hb heq)

/-- No account appears twice in the list. -/
theorem daoAccounts_nodup : DAO_ACCOUNTS.Nodup := by
  -- Sort the 116 numbers and check adjacent `<` in linear time instead of `O(n^2)` byte compares.
  have hinc : strictlyIncreasing (sortNats daoAccountNats) = true := by decide +kernel
  have hnodup : daoAccountNats.Nodup :=
    (sortNats_perm daoAccountNats).nodup_iff.mp
      (nodup_of_strictly_increasing (pairwise_lt_of_strictlyIncreasing hinc))
  have hlt : ∀ n ∈ daoAccountNats, n < 256 ^ 20 := by decide +kernel
  change (daoAccountNats.map addressOfNat).Nodup
  exact nodup_map_of_inj_on hnodup fun a ha b hb heq =>
    ByteOrder.toBE_inj (hlt a ha) (hlt b hb) heq

/-- The recovery contract is not in the list, so no account sends ether to itself. -/
theorem daoRecovery_not_mem : DAO_RECOVERY ∉ DAO_ACCOUNTS := by decide

/-- The ether that some accounts hold, in wei. -/
def balanceSum (tx : TransactionState) (addresses : List Address) : Nat :=
  (addresses.map fun a => (tx.getAccount a).balance.toNat).sum

/-- Moving a whole balance empties the sender and credits the recipient with it. -/
theorem moveEther_whole {fork : Fork} {tx tx' : TransactionState} {sender recipient : Address}
    (hne : sender ≠ recipient)
    (h : tx.moveEther fork sender recipient (tx.getAccount sender).balance = .ok tx') :
    (tx'.getAccount sender).balance = 0 ∧
      (tx'.getAccount recipient).balance.toNat =
        (tx.getAccount recipient).balance.toNat + (tx.getAccount sender).balance.toNat ∧
      ∀ other, other ≠ sender → other ≠ recipient →
        tx'.getAccount other = tx.getAccount other := by
  obtain ⟨-, hfit, hsender, hrecipient, hrest⟩ := moveEther_eq_ok hne h
  -- The sender's balance minus itself is zero, and the credit stays below 2^256.
  refine ⟨by rw [hsender]; exact BitVec.sub_self _, ?_, hrest⟩
  rw [hrecipient, BitVec.toNat_add, Nat.mod_eq_of_lt hfit]

/-- A whole-balance move to an outside recipient leaves the other listed balances as they were. -/
private theorem balanceSum_moveEther_whole {fork : Fork} {tx mid : TransactionState}
    {a recipient : Address} {l : List Address} (ha : a ∉ l) (hr : recipient ∉ l)
    (hne : a ≠ recipient)
    (h : tx.moveEther fork a recipient (tx.getAccount a).balance = .ok mid) :
    balanceSum mid l = balanceSum tx l := by
  obtain ⟨-, -, hrest⟩ := moveEther_whole hne h
  unfold balanceSum
  congr 1
  apply List.map_congr_left
  intro b hb
  rw [hrest b (fun he => ha (he ▸ hb)) (fun he => hr (he ▸ hb))]

/-- Moving each listed balance to an outside recipient empties the list and credits the recipient.

The listed accounts are distinct.

Every other account is left alone. -/
theorem foldlM_moveEther {fork : Fork} (recipient : Address) :
    ∀ (l : List Address) (tx tx' : TransactionState), l.Nodup → recipient ∉ l →
      l.foldlM (fun tx a => tx.moveEther fork a recipient (tx.getAccount a).balance) tx = .ok tx' →
      (∀ a ∈ l, (tx'.getAccount a).balance = 0) ∧
        (tx'.getAccount recipient).balance.toNat =
          (tx.getAccount recipient).balance.toNat + balanceSum tx l ∧
        ∀ other, other ∉ l → other ≠ recipient → tx'.getAccount other = tx.getAccount other := by
  intro l
  induction l with
  | nil =>
    intro tx tx' _ _ h
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [balanceSum]
  | cons a l ih =>
    intro tx tx' hnd hr h
    simp only [List.foldlM, bind, Except.bind] at h
    have hne : a ≠ recipient := fun he => hr (he ▸ List.mem_cons_self)
    cases hstep : tx.moveEther fork a recipient (tx.getAccount a).balance with
    | error e => simp [hstep] at h
    | ok mid =>
      rw [hstep] at h
      obtain ⟨hzero, hcredit, hrest⟩ := moveEther_whole hne hstep
      have hnd' := (List.nodup_cons.mp hnd)
      obtain ⟨hall, hrec, hother⟩ :=
        ih mid tx' hnd'.2 (fun hm => hr (List.mem_cons_of_mem _ hm)) h
      have hsame :=
        balanceSum_moveEther_whole hnd'.1 (fun hm => hr (List.mem_cons_of_mem _ hm)) hne hstep
      refine ⟨fun b hb => ?_, ?_, fun other hno hrc => ?_⟩
      · rcases List.mem_cons.mp hb with rfl | hb
        · rw [hother b hnd'.1 hne, hzero]
        · exact hall b hb
      · rw [hrec, hcredit, hsame]
        simp only [balanceSum, List.map_cons, List.sum_cons]
        omega
      · rw [hother other (fun hm => hno (List.mem_cons_of_mem _ hm)) hrc,
          hrest other (fun he => hno (he ▸ List.mem_cons_self)) hrc]

/-- After the DAO Fork the listed accounts hold no ether, and the recovery contract holds it.

Every other account is unchanged. -/
theorem applyDaoFork_spec {fork : Fork} {tx tx' : TransactionState}
    (h : applyDaoFork fork tx = .ok tx') :
    (∀ a ∈ DAO_ACCOUNTS, (tx'.getAccount a).balance = 0) ∧
      (tx'.getAccount DAO_RECOVERY).balance.toNat =
        (tx.getAccount DAO_RECOVERY).balance.toNat + balanceSum tx DAO_ACCOUNTS ∧
      ∀ other, other ∉ DAO_ACCOUNTS → other ≠ DAO_RECOVERY →
        tx'.getAccount other = tx.getAccount other :=
  foldlM_moveEther DAO_RECOVERY DAO_ACCOUNTS tx tx' daoAccounts_nodup daoRecovery_not_mem h

/-- The DAO Fork keeps every nonce and every code hash. -/
theorem applyDaoFork_nonce_codeHash {fork : Fork} {tx tx' : TransactionState}
    (h : applyDaoFork fork tx = .ok tx') (address : Address) :
    (tx'.getAccount address).nonce = (tx.getAccount address).nonce ∧
      (tx'.getAccount address).codeHash = (tx.getAccount address).codeHash :=
  foldlM_ok_invariant (fun mid : TransactionState =>
      (mid.getAccount address).nonce = (tx.getAccount address).nonce ∧
        (mid.getAccount address).codeHash = (tx.getAccount address).codeHash)
    (fun _ _ _ keeps hstep => by
      obtain ⟨hn, hc⟩ := moveEther_nonce_codeHash hstep address
      exact ⟨hn.trans keeps.1, hc.trans keeps.2⟩)
    ⟨rfl, rfl⟩ h

/-- Moving each listed balance to an outside recipient succeeds when a sum stays below 2^256.

The listed accounts are distinct.

The sum is the balance of the recipient plus the balances of the listed accounts. -/
theorem foldlM_moveEther_isOk {fork : Fork} (recipient : Address) :
    ∀ (l : List Address) (tx : TransactionState), l.Nodup → recipient ∉ l →
      (tx.getAccount recipient).balance.toNat + balanceSum tx l < 2 ^ 256 →
      ∃ tx', l.foldlM (fun tx a => tx.moveEther fork a recipient (tx.getAccount a).balance) tx =
        .ok tx' := by
  intro l
  induction l with
  | nil => intro tx _ _ _; exact ⟨tx, rfl⟩
  | cons a l ih =>
    intro tx hnd hr hfit
    have hne : a ≠ recipient := fun he => hr (he ▸ List.mem_cons_self)
    have hnd' := List.nodup_cons.mp hnd
    have hr' : recipient ∉ l := fun hm => hr (List.mem_cons_of_mem _ hm)
    simp only [balanceSum, List.map_cons, List.sum_cons] at hfit
    -- The first move succeeds: the sender gives what it holds, and the credit fits.
    obtain ⟨mid, hstep⟩ := (moveEther_isOk_iff (fork := fork) (tx := tx)
      (amount := (tx.getAccount a).balance) hne).mpr ⟨BitVec.lt_irrefl _, by omega⟩
    obtain ⟨-, hcredit, -⟩ := moveEther_whole hne hstep
    have hsame := balanceSum_moveEther_whole hnd'.1 hr' hne hstep
    obtain ⟨tx', h⟩ := ih mid hnd'.2 hr' (by rw [hcredit, hsame]; unfold balanceSum; omega)
    exact ⟨tx', by simp only [List.foldlM, bind, Except.bind, hstep]; exact h⟩

/-- The DAO Fork succeeds exactly when a sum stays below 2^256.

The sum is the balance of the recovery contract plus the balances of the listed accounts. -/
theorem applyDaoFork_isOk_iff {fork : Fork} {tx : TransactionState} :
    (∃ tx', applyDaoFork fork tx = .ok tx') ↔
      (tx.getAccount DAO_RECOVERY).balance.toNat + balanceSum tx DAO_ACCOUNTS < 2 ^ 256 := by
  constructor
  · rintro ⟨tx', h⟩
    rw [← (applyDaoFork_spec h).2.1]
    exact (tx'.getAccount DAO_RECOVERY).balance.isLt
  · exact foldlM_moveEther_isOk DAO_RECOVERY DAO_ACCOUNTS tx daoAccounts_nodup daoRecovery_not_mem

/-- Mainnet activates the DAO Fork at block 1,920,000. -/
theorem daoForkBlock_mainnet : daoForkBlock ChainConfig.mainnet = some 1920000 := rfl

/-- Before Paris on mainnet, blocks 1,920,000 to 1,920,009 pass exactly with the DAO extra data.

Every other header passes. -/
theorem daoExtraDataValid_mainnet {fork : Fork} (hFork : fork < .paris) (header : Header fork) :
    daoExtraDataValid ChainConfig.mainnet header = true ↔
      (1920000 ≤ header.number ∧ header.number < 1920010 → header.extraData = DAO_EXTRA_DATA) := by
  simp only [daoExtraDataValid, hFork, ↓reduceIte, daoForkBlock_mainnet, DAO_EXTRA_DATA_BLOCKS,
    Nat.reduceAdd]
  by_cases h : 1920000 ≤ header.number ∧ header.number < 1920010 <;> simp [h]

/-- From Paris every header passes the extra data rule of the DAO Fork, on every chain. -/
theorem daoExtraDataValid_of_paris_le {config : ChainConfig} {fork : Fork} (hFork : .paris ≤ fork)
    (header : Header fork) : daoExtraDataValid config header = true := by
  have hNot : ¬fork < .paris := Nat.not_lt.mpr hFork
  simp only [daoExtraDataValid, hNot, ↓reduceIte]

end EthLib.Execution.Blocks
