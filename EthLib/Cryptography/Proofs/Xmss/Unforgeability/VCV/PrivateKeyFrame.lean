module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeSigner
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphPrefix
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedResidual

/-!
# Cold private randomizer rows at untouched signing keys

A randomizer lookup can insert its two tagged words only at the addressed key.

The parameter word and auxiliary tick have distinct private addresses.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography Constants HashSig OracleComp OracleSpec
open ChainGraph (Word)
open scoped Classical

/-- The physical private low row queried before this message is searched. -/
@[expose] def privateLow (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray) :
    OtherPrivate pp :=
  ⟨.inl (pp, addrRnd l e, m), (randomizer_residual pp l e m).1⟩

private theorem away_param (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray) :
    (pp, addrRnd l e, m) ≠ parameterLabel := by
  intro same
  have bad : addrRnd l e = addrParam := congrArg (fun t : PrfInput => t.2.1) same
  exact (by decide : AddressType.rnd.code ≠ AddressType.param.code) (encodeAddress_inj.mp bad).1

/-- Parameter generation leaves every potential finder base cold. -/
theorem prefix_private_cold (w : HashOutput) (l : Layer) (e : UInt32) (m : ByteArray) :
    let pp := parameterOfWord w
    let r := SecretEncoding.Residual.localState _ _ (toKeyedState pp (afterWord w))
    r.2 (privateLow pp l e m) = none := by
  intro pp r
  change (toKeyedState pp (afterWord w)).2 (.inr (privateLow pp l e m)) = none
  rw [toKeyedState_other]
  simp [RandomOraclePairedValue.splitCache, privateLow, afterWord, QueryCache.cacheQuery_of_ne,
    away_param pp l e m]

private theorem row_frame {pp : PublicParam} (j k : OtherPrivate pp) (diff : j ≠ k)
    (s : (OtherPrivate pp →ₒ Word).QueryCache) {z}
    (real : z ∈ support ((((OtherPrivate pp →ₒ Word).randomOracle k).run s))) :
    z.2 j = s j := by
  rw [randomOracle.run_eq] at real
  cases found : s k with
  | none =>
    simp only [found, mem_support_bind_iff, mem_support_pure_iff] at real
    obtain ⟨_,_,rfl⟩ := real
    exact QueryCache.cacheQuery_of_ne _ _ diff
  | some w =>
    simp only [found, mem_support_pure_iff] at real
    rw [real]

/-- A full private word operation cannot change the protected low row at another input. -/
theorem word_frame {pp : PublicParam} (l : Layer) (e : UInt32) (m : ByteArray)
    (key : PrfInput) (lo hi) (different : (pp,addrRnd l e,m) ≠ key)
    (r : ResidualCache pp) {z} (real : z ∈ support ((mixedLocalWord pp key lo hi).run r)) :
    z.2.2 (privateLow pp l e m) = r.2 (privateLow pp l e m) := by
  simp only [mixedLocalWord, StateT.run_mk, mem_support_bind_iff, mem_support_pure_iff] at real
  obtain ⟨a,ha,b,hb,rfl⟩ := real
  let j := privateLow pp l e m
  have low : j ≠ ⟨.inl key,lo⟩ := fun eq => different (Sum.inl.inj (congrArg Subtype.val eq))
  have high : j ≠ ⟨.inr key,hi⟩ := by
    intro eq
    have clash := congrArg (fun x : OtherPrivate pp => x.val) eq
    cases clash
  exact (row_frame j _ high _ (coin_support _ hb)).trans
    (row_frame j _ low _ (coin_support _ ha))

/-- Neither the lower nor the upper lookup writes the private low word of any different key. -/
theorem randomizer_frame {pp : PublicParam} (l l' : Layer) (e e' : UInt32)
    (msg msg' : ByteArray) (other : (l,e) ≠ (l',e')) (r : ResidualCache pp) {z}
    (real : z ∈ support ((mixedRandomizer pp l' e' msg').run r)) :
    z.2.2 (privateLow pp l e msg) = r.2 (privateLow pp l e msg) := by
  rw [mixedRandomizer, StateT.run_map, support_map] at real
  obtain ⟨v,h,rfl⟩ := real
  have different : (pp,addrRnd l e,msg) ≠ (pp,addrRnd l' e',msg') := by
    intro same
    have address := addrRnd_inj.mp (congrArg (fun t : PrfInput => t.2.1) same)
    exact other (Prod.ext address.1 address.2)
  exact word_frame l e msg (pp,addrRnd l' e',msg') _ _ different r h

/-- The parameter callback has the same frame at all residual tables. -/
theorem parameter_frame {pp : PublicParam} (l : Layer) (e : UInt32) (msg : ByteArray)
    (r : ResidualCache pp) {z} (real : z ∈ support
      ((mixedLocalWord pp parameterLabel (parameter_local pp).1 (parameter_local pp).2).run r)) :
    z.2.2 (privateLow pp l e msg) = r.2 (privateLow pp l e msg) :=
  word_frame l e msg _ _ _ (away_param pp l e msg) r real

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
