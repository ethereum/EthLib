module

public import EthLib.Execution.Proofs.Evm.Precompiles.P256Verify
public import EthLib.Serialization.Proofs.Rlp.Vectors

/-!
# Proofs: known answers for P256VERIFY, part 2 of 2

Cases of `assets/eip-7951/test-vectors.json` in `ethereum/EIPs`, at commit `d386b29b5a31bd5cfd8d21bbf4e8a0c87734085e`.

The EIP derives them from `ecdsa_secp256r1_sha256_p1363_test.json` of `C2SP/wycheproof`, under the Apache License 2.0.

They keep the first case of each kind of rejection.

They also keep the first valid signature of each kind that tests an edge of the algorithm.

The kernel runs a whole verification in about 17 seconds, so the 781 cases would take it hours.

Each case runs with the price, 6900 gas.

The EIP lists 3450 gas, the price that an earlier draft set, and the output does not depend on it.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.P256Verify.KnownAnswers

open EthLib.Execution.Evm.Precompiles.P256Verify
open EthLib.Serialization.Rlp.Vectors (byteArrayOf)

-- Start of material derived from `C2SP/wycheproof`, under the Apache License 2.0.

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #3: Modified r or s, e.g. by adding or subtracting the order of the group. -/
theorem p256Verify_Modified_r_or_s_e_g_by_adding_or_subtracting_the_order_of_the_group_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023d45c5740946b2a147f59262ee6f5bc90bd01ed280528b62b3aed5fc93f06f739b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #58: Edge case for Shamir multiplication. -/
theorem p256Verify_Edge_case_for_Shamir_multiplication_valid :
    p256Verify (byteArrayOf 160 0x70239dd877f7c944c422f44dea4ed1a52f2627416faf2f072fa50c772ed6f80764a1aab5000d0e804f3e2fc02bdee9be8ff312334e2ba16d11547c97711c898e6af015971cc30be6d1a206d4e013e0997772a2f91d73286ffd683b9bb2cf4f1b2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #113: k*G has a large x-coordinate. -/
theorem p256Verify_k_G_has_a_large_x_coordinate_valid :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023000000000000000000000000000000004319055358e8617b0c46353d039cdaabffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e0ad99500288d466940031d72a9f5445a4d43784640855bf0a69874d2de5fe103c5011e6ef2c42dcd50d5d3d29f99ae6eba2c80c9244f4c5422f0979ff0c3ba5e) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #126: r is larger than n. -/
theorem p256Verify_r_is_larger_than_n_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325560000000000000000000000000000000000000000000000000000000000000006cbe0c29132cd738364fedd603152990c048e5e2fff996d883fa6caca7978c73770af6a8ce44cb41224b2603606f4c04d188e80bff7cc31ad5189d4ab0d70e8c1) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #134: s == 1. -/
theorem p256Verify_s_1_valid :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023555555550000000055555555555555553ef7a8e48d07df81a693439654210c7000000000000000000000000000000000000000000000000000000000000000018aeb368a7027a4d64abdea37390c0c1d6a26f399e2d9734de1eb3d0e1937387405bd13834715e1dbae9b875cf07bd55e1b6691c7f7536aef3b19bf7a4adf576d) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #136: point at infinity during verify. -/
theorem p256Verify_point_at_infinity_during_verify_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca6050237fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a8555555550000000055555555555555553ef7a8e48d07df81a693439654210c70b533d4695dd5b8c5e07757e55e6e516f7e2c88fa0239e23f60e8ec07dd70f2871b134ee58cc583278456863f33c3a85d881f7d4a39850143e29d4eaf009afe47) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #140: u1 == n - 1. -/
theorem p256Verify_u1_n_1_valid :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023555555550000000055555555555555553ef7a8e48d07df81a693439654210c7044a5ad0ad0636d9f12bc9e0a6bdd5e1cbcb012ea7bf091fcec15b0c43202d52ed8adc00023a8edc02576e2b63e3e30621a471e2b2320620187bf067a1ac1ff3233e2b50ec09807accb36131fff95ed12a09a86b4ea9690aa32861576ba2362e1) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #142: u2 == n - 1. -/
theorem p256Verify_u2_n_1_valid :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023555555550000000055555555555555553ef7a8e48d07df81a693439654210c70aaaaaaaa00000000aaaaaaaaaaaaaaaa7def51c91a0fbf034d26872ca84218e1cf04ea77e9622523d894b93ff52dc3027b31959503b6fa3890e5e04263f922f1e8528fb7c006b3983c8b8400e57b4ed71740c2f3975438821199bedeaecab2e9) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #172: duplication bug. -/
theorem p256Verify_duplication_bug_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca6050236f2347cab7dd76858fe0555ac3bc99048c4aacafdfb6bcbe05ea6c42c4934569bb726660235793aa9957a61e76e00c2c435109cf9a15dd624d53f4301047856b5b812fd521aafa69835a849cce6fbdeb6983b442d2444fe70e134c027fc469637c75bf0c5c9f6d17ffb16d2726bf30a9c7aaf31a8d317472b1ea145ab66db616) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #175: comparison with point at infinity . -/
theorem p256Verify_comparison_with_point_at_infinity_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023555555550000000055555555555555553ef7a8e48d07df81a693439654210c703333333300000000333333333333333325c7cbbc549e52e763f1f55a327a3aa9dd86d3b5f4a13e8511083b78002081c53ff467f11ebd98a51a633db76665d25045d5c8200c89f2fa10d849349226d21d8dfaed6ff8d5cb3e1b7e17474ebc18f7) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #192: pseudorandom signature. -/
theorem p256Verify_pseudorandom_signature_valid :
    p256Verify (byteArrayOf 160 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855b292a619339f6e567a305c951c0dcbcc42d16e47f219f9e98e76e09d8770b34a0177e60492c5a8242f76f07bfe3661bde59ec2a17ce5bd2dab2abebdf89a62e204aaec73635726f213fb8a9e64da3b8632e41495a944d0045b522eba7240fad587d9315798aaa3a5ba01775787ced05eaaf7b4e09fc81d6d1aa546e8365d525d) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_test.json EcdsaVerify SHA-256 #118: modify first byte of integer. -/
theorem p256Verify_modify_first_byte_of_integer_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca60502329a3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_test.json EcdsaVerify SHA-256 #124: truncated integer. -/
theorem p256Verify_truncated_integer_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca6050232ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e1800b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b491568472927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- invalid public key y param errors. -/
theorem p256Verify_invalid_public_key_y_param_errors_rejected :
    p256Verify (byteArrayOf 160 0x2f77668a9dfbf8d5848b9eeb4a7145ca94c6ed9236e4a773f6dcafa5132b2f9170bebe684cdcb5ca72a42f0d873879359bd1781a591809947628d313a3814f67aec03aca8f5587a4d535fa31027bbe9cc0e464b1c3577f4c2dcde6b2094798a9bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af0150000000000000000000000000000000000000000000000000000000000000000) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)
-- End of material derived from `C2SP/wycheproof`.

end EthLib.Execution.Evm.Precompiles.P256Verify.KnownAnswers
