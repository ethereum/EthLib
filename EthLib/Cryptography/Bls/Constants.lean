namespace EthLib.Cryptography.Bls.Constants

/-- Number of bytes in a serialized G1 pubkey (compressed). -/
def BYTES_PER_PUBKEY : Nat := 48

/-- Number of bytes in a serialized G2 signature (compressed). -/
def BYTES_PER_SIGNATURE : Nat := 96

/-! ## C-callable size accessors

Mirrors the pattern used by `EthLib.Cryptography.Kzg.Constants`: the
Python C extension queries every size at module-init time via these
`@[export]`-d functions and caches the results, so the wrapper has no
hardcoded constants of its own. -/

@[export eth_bls_const_bytes_per_pubkey]
def constBytesPerPubkey (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_PUBKEY

@[export eth_bls_const_bytes_per_signature]
def constBytesPerSignature (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_SIGNATURE

end EthLib.Cryptography.Bls.Constants
