/- Authors: Matthias Meijers -/

module
public import EthereumXMSSHypertree.HashInputs
public import EthLib.Cryptography.Xmss.KeyGen

/-!
# Complete source node, leaf and message inputs

Fixed source widths make each complete input recover its public parameter, bounded address
coordinates and ordered payload. Message bytes may have arbitrary length because the randomizer
suffix has a fixed length. Node indices are UInt32 values and levels are bounded before encoding.
-/

public section

namespace EthereumXMSSHypertree.FullInputs

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants

/-- Splitting the flattened source digest vector recovers every digest in its original position. -/
theorem splitDigests_flatten {n : Nat} (digests : Vector Digest n) :
    splitDigests digests.flatten = digests := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hj16 : j < 16 := hj
  have hdiv : (i * 16 + j) / 16 = i := by omega
  have hmod : (i * 16 + j) % 16 = j := by omega
  rw [splitDigests, Vector.getElem_ofFn hi, Vector.getElem_ofFn hj, Vector.getElem_flatten]
  simp only [DIGEST_LEN, hdiv, hmod]
  rfl

/-- Packing source digest vectors preserves every ordered digest and byte. -/
theorem packDigests_injective {n : Nat} : Function.Injective (@packDigests n) := by
  intro first second h
  have hflat : first.flatten = second.flatten := packBytes_injective h
  exact (splitDigests_flatten first).symm.trans
    ((congrArg (splitDigests (n := n)) hflat).trans (splitDigests_flatten second))

/-- The complete source node input with its address fields already in their exact finite domains. -/
@[expose] def nodeInput (pp : PublicParam) (layer : Layer) (level : Fin 17) (index : UInt32)
    (left right : Digest) : ByteArray :=
  thInput pp (addrNode layer level index) (packBytes left ++ packBytes right)

/-- The complete source leaf input keeps all 58 chain ends in order. -/
@[expose] def leafInput (pp : PublicParam) (layer : Layer) (index : UInt32)
    (ends : Vector Digest 58) : ByteArray :=
  thInput pp (addrLeaf layer index) (packDigests ends)

/-- The complete source message input keeps the variable-length message before its fixed suffix. -/
@[expose] def messageInput (pp : PublicParam) (layer : Layer) (index : UInt32)
    (msg : ByteArray) (rho : Randomizer) : ByteArray :=
  thInput pp (addrMsg layer index) (msg ++ packBytes rho)

/-- Equal node inputs recover their parameter, layer, level, UInt32 index and ordered children. -/
theorem nodeInput_inj {pp pp' : PublicParam} {layer layer' : Layer} {level level' : Fin 17}
    {index index' : UInt32} {left left' right right' : Digest}
    (h : nodeInput pp layer level index left right =
      nodeInput pp' layer' level' index' left' right') :
    pp = pp' ∧ layer = layer' ∧ level = level' ∧ index = index' ∧
      left = left' ∧ right = right' := by
  obtain ⟨hpp, haddress, hpayload⟩ := thInput_inj h
  obtain ⟨hlayer, hlevel, hindex⟩ := addrNode_inj.mp haddress
  obtain ⟨hleft, hright⟩ :=
    EthLib.Cryptography.HashSig.byteArray_append_inj hpayload (by simp)
  exact ⟨hpp, hlayer, hlevel, hindex, packBytes_injective hleft, packBytes_injective hright⟩

/-- Equal leaf inputs recover their parameter, layer, index and complete ordered endpoint vector. -/
theorem leafInput_inj {pp pp' : PublicParam} {layer layer' : Layer} {index index' : UInt32}
    {ends ends' : Vector Digest 58}
    (h : leafInput pp layer index ends = leafInput pp' layer' index' ends') :
    pp = pp' ∧ layer = layer' ∧ index = index' ∧ ends = ends' := by
  obtain ⟨hpp, haddress, hpayload⟩ := thInput_inj h
  obtain ⟨hlayer, hindex⟩ := addrLeaf_inj.mp haddress
  exact ⟨hpp, hlayer, hindex, packDigests_injective hpayload⟩

/-- Equal message inputs recover arbitrary message bytes and the fixed 16-byte randomizer. -/
theorem messageInput_inj {pp pp' : PublicParam} {layer layer' : Layer} {index index' : UInt32}
    {msg msg' : ByteArray} {rho rho' : Randomizer}
    (h : messageInput pp layer index msg rho = messageInput pp' layer' index' msg' rho') :
    pp = pp' ∧ layer = layer' ∧ index = index' ∧ msg = msg' ∧ rho = rho' := by
  obtain ⟨hpp, haddress, hpayload⟩ := thInput_inj h
  obtain ⟨hlayer, hindex⟩ := addrMsg_inj.mp haddress
  have hsize : msg.size = msg'.size := by
    have htotal := congrArg ByteArray.size hpayload
    simp only [ByteArray.size_append, size_packBytes] at htotal
    omega
  obtain ⟨hmsg, hrho⟩ := EthLib.Cryptography.HashSig.byteArray_append_inj hpayload hsize
  exact ⟨hpp, hlayer, hindex, hmsg, packBytes_injective hrho⟩

/-- The typed complete node input is the input of the actual source node call. -/
theorem nodeHash_input {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (layer : Layer)
    (level : Fin 17) (index : UInt32) (left right : Digest) :
    nodeHash H pp layer level.val index.toNat left right =
      (do return halfOf 0 (← H (nodeInput pp layer level index left right))) := by
  change th H pp (addrNode layer (Fin.ofNat 17 level.val) (UInt32.ofNat index.toNat))
    (packBytes left ++ packBytes right) =
    th H pp (addrNode layer level index) (packBytes left ++ packBytes right)
  simp only [Fin.ofNat_val_eq_self, UInt32.ofNat_toNat]

/-- The complete leaf input is the input of the actual source leaf call. -/
theorem otsLeafHash_input {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (layer : Layer) (index : UInt32)
    (ends : Vector Digest 58) :
    otsLeafHash H pp layer index ends =
      (do return halfOf 0 (← H (leafInput pp layer index ends))) := rfl

/-- The complete message input is the input of the actual source message digest call. -/
theorem messageDigest_input {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (layer : Layer) (index : UInt32)
    (msg : ByteArray) (rho : Randomizer) :
    messageDigest H pp layer index msg rho =
      (do return halfOf 0 (← H (messageInput pp layer index msg rho))) := rfl

/-- The raw-seed derivation has the source's scheme tag before the 32-byte seed. -/
@[expose] def schemeSeedInput (rawSeed : Seed) : ByteArray :=
  ByteArray.mk SEED_TAG.toArray ++ packBytes rawSeed

/-- The exact tagged raw-seed derivation input has 40 bytes. -/
theorem schemeSeedInput_size (rawSeed : Seed) : (schemeSeedInput rawSeed).size = 40 := by
  have hseed : (packBytes rawSeed).size = 32 := EthLib.Base.size_packBytes rawSeed
  rw [schemeSeedInput, ByteArray.size_append, hseed, seed_tag_eq]
  rfl

/-- The tagged raw-seed input is the actual source scheme-seed input. -/
theorem schemeSeed_input {m : Type → Type} (H : ByteArray → m (Vector UInt8 32))
    (rawSeed : Seed) : schemeSeed H rawSeed = H (schemeSeedInput rawSeed) := rfl

/-- The 40-byte tagged seed input cannot equal a source input with a payload of at least 32 bytes. -/
theorem schemeSeedInput_ne_thInput (rawSeed : Seed) (pp : PublicParam) (address : Address)
    (payload : ByteArray) (hpayload : 32 ≤ payload.size) :
    schemeSeedInput rawSeed ≠ thInput pp address payload := by
  intro h
  have hsize := congrArg ByteArray.size h
  have hpp : (packBytes pp).size = 16 := EthLib.Base.size_packBytes pp
  have haddress : (packBytes address).size = 16 := EthLib.Base.size_packBytes address
  simp only [schemeSeedInput_size, thInput, ByteArray.size_append] at hsize
  rw [hpp, haddress] at hsize
  omega

end EthereumXMSSHypertree.FullInputs
