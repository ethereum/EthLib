module

public import EthLib.Execution.Rpc.Account
public import EthLib.Execution.Proofs.Rpc.Raw

/-!
# Proofs: the account queries

Each word that `eth_getStorageValues` gives is the word that `eth_getStorageAt` gives.

Each word is read at the same address, key and block, in the order of the request.

At a block that the node holds, an address with no account has balance and nonce zero.

Its code is empty.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.State (State)

namespace ChainView

/-- When the storage query of a block answers, its words are those of the one-key query.

They come for each key of each address of the request, in order. -/
theorem storageValues_agree {v : ChainView} {requests : List (Address × List Bytes32)}
    {p : BlockParam} {values : List (Address × List U256)}
    (h : v.storageValues requests p = .ok values) :
    requests.mapM (fun q => (q.1, ·) <$> q.2.mapM fun key => v.storageAt q.1 key p) =
      .ok values := by
  obtain ⟨r, hr, hv⟩ := ofBlock_eq_ok.mp h
  rw [← Except.ok.inj hv]
  refine mapM_eq_ok_map fun q _ => ?_
  rw [mapM_eq_ok_map (f := fun key => v.storageAt q.1 key p) (g := r.storage q.1)
    fun key _ => ofBlock_eq_ok.mpr ⟨r, hr, rfl⟩]
  rfl

/-- At a block that the node holds, an address with no account has balance zero. -/
theorem balance_of_none {v : ChainView} {p : BlockParam} {r : BlockRecord} {a : Address}
    (hr : v.resolve p = .ok (some r)) (ha : r.state.getAccountOptional a = none) :
    v.balance a p = .ok 0 :=
  ofBlock_eq_ok.mpr ⟨r, hr, by simp [BlockRecord.account, ha]; rfl⟩

/-- At a block that the node holds, an address with no account has nonce zero. -/
theorem nonce_of_none {v : ChainView} {p : BlockParam} {r : BlockRecord} {a : Address}
    (hr : v.resolve p = .ok (some r)) (ha : r.state.getAccountOptional a = none) :
    v.nonce a p = .ok 0 :=
  ofBlock_eq_ok.mpr ⟨r, hr, by simp [BlockRecord.account, ha]; rfl⟩

/-- At a block that the node holds, an address with no account has empty code. -/
theorem code_of_none {v : ChainView} {p : BlockParam} {r : BlockRecord} {a : Address}
    (hr : v.resolve p = .ok (some r)) (ha : r.state.getAccountOptional a = none) :
    v.code a p = .ok .empty :=
  ofBlock_eq_ok.mpr ⟨r, hr, by
    simp [BlockRecord.code, BlockRecord.account, ha, EthLib.Execution.State.EMPTY_ACCOUNT,
      EthLib.Execution.State.State.getCode]
    rfl⟩

end ChainView

end EthLib.Execution.Rpc
