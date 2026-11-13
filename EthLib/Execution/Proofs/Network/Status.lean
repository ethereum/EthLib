module

public import EthLib.Execution.Network.Status
public import EthLib.Networking.Proofs.Devp2p.ForkId

/-!
# Proofs: Status and BlockRangeUpdate

Each message reads back from its RLP item on the versions that use its form.

The decoder of eth/68 rejects the Status of eth/69.

The decoder of each later version rejects the Status of eth/68.

A node accepts a Status that carries its own version and fork identifier and a range in order.

It accepts a Status exactly when the version matches and the fork identifier passes.

From eth/69 the range must also not start after it ends, so a range of one block passes.

At every version, the network ID and the genesis hash play no part.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Networking.Devp2p
open EthLib.Serialization.Rlp

instance : LawfulCodec BlockRange where
  ofItem_toItem r := by
    show (Codec.ofItem (.list r.items) : Except RlpError BlockRange) = _
    simp [Codec.ofItem, BlockRange.items, Item.fields, Item.toItems, Item.field_toItem, bind,
      Except.bind, pure, Except.pure]
  toItem_of_ofItem {item r} h := by
    obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp h
    rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hlen
    obtain ⟨x, rfl, h1⟩ := Item.field_bind_eq_ok.mp hrest
    obtain ⟨y, rfl, h2⟩ := Item.field_bind_eq_ok.mp h1
    obtain ⟨z, rfl, h3⟩ := Item.field_bind_eq_ok.mp h2
    cases h3
    rfl

namespace Status

/-- The Status of eth/68 reads back on eth/68. -/
theorem ofItem_eth68 (v n td : Nat) (h g : Hash32) (id : ForkId) :
    ofItem .eth68 (eth68 v n td h g id).toItem = .ok (eth68 v n td h g id) := by
  simp [ofItem, toItem, Item.fields, Item.toItems, Item.field_toItem, bind, Except.bind, pure,
    Except.pure]

/-- The Status of eth/69 reads back on every version from eth/69 on. -/
theorem ofItem_eth69 {version : EthVersion} (hv : version ≠ .eth68) (v n : Nat) (g : Hash32)
    (id : ForkId) (r : BlockRange) :
    ofItem version (eth69 v n g id r).toItem = .ok (eth69 v n g id r) := by
  simp [ofItem, toItem, hv, BlockRange.items, Item.fields, Item.toItems, Item.field_toItem, bind,
    Except.bind, pure, Except.pure]

/-- eth/68 rejects the Status of eth/69, which has seven fields. -/
theorem ofItem_eth68_of_eth69 (v n : Nat) (g : Hash32) (id : ForkId) (r : BlockRange) :
    ofItem .eth68 (eth69 v n g id r).toItem = .error (.wrongFieldCount 6 7) := by
  simp [ofItem, toItem, BlockRange.items, Item.fields, Item.toItems, bind, Except.bind]

/-- Every version from eth/69 on rejects the Status of eth/68, which has six fields. -/
theorem ofItem_of_eth68 {version : EthVersion} (hv : version ≠ .eth68) (v n td : Nat)
    (h g : Hash32) (id : ForkId) :
    ofItem version (eth68 v n td h g id).toItem = .error (.wrongFieldCount 7 6) := by
  simp [ofItem, toItem, hv, Item.fields, Item.toItems, bind, Except.bind]

end Status

/-- Two errors with one code come from one constructor. -/
theorem StatusError.code_injective (e₁ e₂ : StatusError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [StatusError.code] at h; exact absurd h (by decide))

/--
A node accepts a Status from eth/69 on that carries three things.

They are the negotiated version, the node's own fork identifier and a range in order.

A range is in order when it does not start after it ends.

The forks of the node must fit rule 1a, and its head must be a real block.
-/
theorem checkStatus_own {version : EthVersion} {s : Schedule} {number timestamp : Nat}
    (hs : s.Separated) (hn : number ≤ TIMESTAMP_THRESHOLD) (networkId : Nat) (genesis : Hash32)
    {r : BlockRange} (hr : r.earliest ≤ r.latest) :
    checkStatus version s number timestamp
      (.eth69 version.number networkId genesis (s.forkId number timestamp) r) = .ok () := by
  simp [checkStatus, Status.version, Status.forkId, s.validate_forkId_self number timestamp hs hn,
    BlockRange.Valid, hr, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- A node accepts a Status exactly when three conditions hold.

The Status carries the version of the node, and its fork identifier passes the check of the node.

From eth/69, the announced range does not start after it ends, so a range of one block passes.

The conditions do not read the network ID or the genesis hash. -/
theorem checkStatus_eq_ok_iff {version : EthVersion} {s : Schedule} {number timestamp : Nat}
    {status : Status} :
    checkStatus version s number timestamp status = .ok () ↔
      status.version = version.number ∧ s.validate number timestamp status.forkId = .ok () ∧
        match status with
        | .eth68 .. => True
        | .eth69 _ _ _ _ r => r.earliest ≤ r.latest := by
  unfold checkStatus
  by_cases hv : status.version = version.number
  · cases hf : s.validate number timestamp status.forkId with
    | error e => simp [hv, Except.mapError, bind, Except.bind]
    | ok u =>
      cases status with
      | eth68 => simp [hv, Except.mapError, bind, Except.bind, pure, Except.pure]
      | eth69 _ _ _ _ r =>
        by_cases hr : r.earliest ≤ r.latest <;>
          simp [BlockRange.Valid, hv, hr, Except.mapError, bind, Except.bind, pure, Except.pure,
            throw, throwThe, MonadExceptOf.throw]
  · simp [hv, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

end EthLib.Execution.Network
