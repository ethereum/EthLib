module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedRequest
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedWorldPass
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedSignerProgram
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedStructure
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedVerifier

/-!
# The normalized keyed client and verifier

Each request uses the private parameter read and the same two-layer signature routine.

The client receives the optional signature while the proof retains the raw return.

The verifier uses the physical full-word port and the public key actually given to the client.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig OracleComp OracleSpec Constants TwoLayerGraph Honest
open LayerGraph.Hidden

/-- The stateful optional-signature interface retains every raw signing attempt. -/
@[expose] noncomputable def mixedOracle (pp : PublicParam) :
    QueryImpl (World + SigningSpec) (WriterT RawLog (MixedLocal pp))
  | .inl t => liftM (mixedWorldPass pp t)
  | .inr req => WriterT.mk (mixedRequest pp req (mixedSignature emitStructure
      pp req.leafIndex req.message))

/-- The client uses the sampled public key, its private coins and the physical verifier. -/
@[expose] noncomputable def mixedGame (pp : PublicParam)
    (A : Adversary) : MixedLocal pp Outcome := do
  let root ← liftM (emitStructure (simulateQ (selection pp .top).liftQuery
      (beforeNode pp .top LAYER_HEIGHT 0 >>=
    fun _ => LayerGraph.readOutput (LayerGraph.treeRole LAYER_HEIGHT 0))))
  let pk : PublicKey := ⟨root,pp⟩
  let (candidate, records) ← (simulateQ (mixedOracle pp) (A.main pk)).run
  let valid ← liftM (verifyWith mixedHash pk candidate.message candidate.signature)
  return ⟨pk, candidate, records, valid⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
