module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedGameProgram
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialGraphErase
public import EthLib.Cryptography.Proofs.Xmss.Encoding

/-!
# Notices at real finder calls and successful signatures

The leanXMSS draft in "The scheme" signs the message at the bottom and its tree root at the top.

A start notice precedes even the first private randomizer draw.

A registration gives the selected physical input and its digest together.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig Constants OracleSpec OracleComp TwoLayerGraph Honest LayerGraph.Hidden

inductive FinderNotice where
  | attempt (layer : Layer) (epoch : UInt32) (msg : ByteArray)
  | register (layer : Layer) (epoch : UInt32) (input : HashInput) (digest : Digest)

/-- Both notices identify the WOTS+C key on which the finder operates. -/
@[expose] def FinderNotice.key : FinderNotice → Layer × UInt32
  | .attempt l e _ | .register l e _ _ => (l, e)

/-- The last six base-four digits of a valid encoded digest are zero. -/
@[expose] noncomputable def selectedDigest (x : Vector (Fin CHAIN_LENGTH) V) : Digest :=
  Base.uintToBytes DIGEST_LEN (∑ i : Fin V, (x[i] : Nat) * 4 ^ i.val)

/-- Registering the accepted digits yields the exact low digest returned on that trial. -/
theorem selectedDigest_eq {d : Digest} {x : Vector (Fin CHAIN_LENGTH) V}
    (h : codeword? d = some x) : selectedDigest x = d := by
  rw [selectedDigest, ← bytesToUint_of_codeword h, Base.uintToBytes_bytesToUint]

/-- A registration stores the exact message, key and selected randomizer in the physical input. -/
@[expose] noncomputable def selectedNotice (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) (rho : Randomizer) (x : Vector (Fin CHAIN_LENGTH) V) : FinderNotice :=
  .register l e (thInput pp (addrMsg l e) (msg ++ packBytes rho)).data.toList (selectedDigest x)

namespace FinderNotices

abbrev Queries := TrialGraphWatch.Spec FinderNotice
abbrev Program (pp : PublicParam) := StateT (ResidualCache pp) (OracleComp Queries)

/-- Forward the original physical operation. -/
@[expose] def raw : QueryImpl MixedWorld (OracleComp Queries) :=
  fun t => liftM (Queries.query (.inl t))

/-- Carry the full residual table across a physical computation. -/
@[expose] noncomputable def carry {pp : PublicParam} {α : Type}
    (p : MixedLocal pp α) : Program pp α :=
  StateT.mk fun s => simulateQ raw (p.run s)

/-- Notices use the observer port and leave every private and auxiliary entry unchanged. -/
@[expose] def emit {pp : PublicParam} (n : FinderNotice) : Program pp Unit :=
  StateT.mk fun s => (fun _ : Unit => ((), s)) <$>
    (liftM (Queries.query (.inr n)) : OracleComp Queries Unit)

/-- Dropping the observer reproduces the original stateful mixed computation. -/
@[expose] noncomputable def forget {pp : PublicParam} {α : Type}
    (p : Program pp α) : MixedLocal pp α :=
  StateT.mk fun s => simulateQ TrialGraphWatch.erase (p.run s)

@[simp] theorem forget_carry {pp : PublicParam} {α : Type} (p : MixedLocal pp α) :
    forget (carry p) = p := by
  ext1 s
  have comp : QueryImpl.compose (TrialGraphWatch.erase (Note := FinderNotice)) raw =
      QueryImpl.id' MixedWorld := by
    funext t
    simp [QueryImpl.compose, raw, TrialGraphWatch.erase, QueryImpl.id']
  change simulateQ TrialGraphWatch.erase (simulateQ raw (p.run s)) = p.run s
  rw [← QueryImpl.simulateQ_compose, comp, simulateQ_id']

@[simp] theorem forget_pure {pp : PublicParam} {α : Type} (a : α) :
    forget (pure a : Program pp α) = pure a := by
  ext1 s
  simp [forget, StateT.run_pure]

@[simp] theorem forget_bind {pp : PublicParam} {α β : Type} (p : Program pp α)
    (f : α → Program pp β) :
    forget (p >>= f) = forget p >>= fun x => forget (f x) := by
  ext1 s
  simp [forget, StateT.run_bind, simulateQ_bind]

@[simp] theorem forget_emit {pp : PublicParam} (n : FinderNotice) :
    forget (emit (pp := pp) n) = pure () := by
  ext1 s
  simp [forget, emit, TrialGraphWatch.erase]

end FinderNotices
end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
