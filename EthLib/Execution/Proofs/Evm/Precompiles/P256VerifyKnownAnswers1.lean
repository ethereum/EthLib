module

public import EthLib.Execution.Proofs.Evm.Precompiles.P256Verify
public import EthLib.Serialization.Proofs.Rlp.Vectors

/-!
# Proofs: known answers for P256VERIFY, part 1 of 2

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

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #1: signature malleability. -/
theorem p256Verify_signature_malleability_valid :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca6050232ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e184cd60b855d442f5b3c7b11eb6c4e0ae7525fe710fab9aa7c77a67f79e6fadd762927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #9: Signature with special case values for r and s. -/
theorem p256Verify_Signature_with_special_case_values_for_r_and_s_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #59: special case hash. -/
theorem p256Verify_special_case_hash_valid :
    p256Verify (byteArrayOf 160 0x00000000690ed426ccf17803ebe2bd0884bcd58a1bb5e7477ead3645f356e7a916aea964a2f6506d6f78c81c91fc7e8bded7d397738448de1e19a0ec580bf266252cd762130c6667cfe8b7bc47d27d78391e8e80c578d1cd38c3ff033be928e92927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #114: r too large. -/
theorem p256Verify_r_too_large_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023ffffffff00000001000000000000000000000000fffffffffffffffffffffffcffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e0ad99500288d466940031d72a9f5445a4d43784640855bf0a69874d2de5fe103c5011e6ef2c42dcd50d5d3d29f99ae6eba2c80c9244f4c5422f0979ff0c3ba5e) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #127: s is larger than n. -/
theorem p256Verify_s_is_larger_than_n_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca6050230000000000000000000000000000000000000000000000000000000000000005ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc75fbd84be4178097002f0deab68f0d9a130e0ed33a6795d02a20796db83444b037e13920f13051e0eecdcfce4dacea0f50d1f247caa669f193c1b4075b51ae296d2d56) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #135: s == 0. -/
theorem p256Verify_s_0_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023555555550000000055555555555555553ef7a8e48d07df81a693439654210c7000000000000000000000000000000000000000000000000000000000000000008aeb368a7027a4d64abdea37390c0c1d6a26f399e2d9734de1eb3d0e1937387405bd13834715e1dbae9b875cf07bd55e1b6691c7f7536aef3b19bf7a4adf576d) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #139: u1 == 1. -/
theorem p256Verify_u1_1_valid :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023555555550000000055555555555555553ef7a8e48d07df81a693439654210c70bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca60502369da0364734d2e530fece94019265fefb781a0f1b08f6c8897bdf6557927c8b866d2d3c7dcd518b23d726960f069ad71a933d86ef8abbcce8b20f71e2a847002) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #141: u2 == 1. -/
theorem p256Verify_u2_1_valid :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023555555550000000055555555555555553ef7a8e48d07df81a693439654210c70555555550000000055555555555555553ef7a8e48d07df81a693439654210c703623ac973ced0a56fa6d882f03a7d5c7edca02cfc7b2401fab3690dbe75ab7858db06908e64b28613da7257e737f39793da8e713ba0643b92e9bb3252be7f8fe) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #171: point duplication during verification. -/
theorem p256Verify_point_duplication_during_verification_valid :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca6050236f2347cab7dd76858fe0555ac3bc99048c4aacafdfb6bcbe05ea6c42c4934569bb726660235793aa9957a61e76e00c2c435109cf9a15dd624d53f4301047856b5b812fd521aafa69835a849cce6fbdeb6983b442d2444fe70e134c027fc46963838a40f2a36092e9004e92d8d940cf5638550ce672ce8b8d4e15eba5499249e9) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #173: point with x-coordinate 0. -/
theorem p256Verify_point_with_x_coordinate_0_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca6050230000000000000000000000000000000000000000000000000000000000000001555555550000000055555555555555553ef7a8e48d07df81a693439654210c706adda82b90261b0f319faa0d878665a6b6da497f09c903176222c34acfef72a647e6f50dcc40ad5d9b59f7602bb222fad71a41bf5e1f9df4959a364c62e488d9) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_p1363_test.json EcdsaP1363Verify SHA-256 #188: testing point duplication. -/
theorem p256Verify_testing_point_duplication_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023249249246db6db6ddb6db6db6db6db6dad4591868595a8ee6bf5f864ff7be0c26b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c2964fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_test.json EcdsaVerify SHA-256 #3: valid. -/
theorem p256Verify_valid_valid :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca6050232ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e) 6900 = .ok VALID :=
  eq_ok_of_kernel (by decide +kernel)

/-- wycheproof/ecdsa_secp256r1_sha256_test.json EcdsaVerify SHA-256 #120: modify last byte of integer. -/
theorem p256Verify_modify_last_byte_of_integer_rejected :
    p256Verify (byteArrayOf 160 0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca6050232ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e98b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- invalid public key x param errors. -/
theorem p256Verify_invalid_public_key_x_param_errors_rejected :
    p256Verify (byteArrayOf 160 0x2f77668a9dfbf8d5848b9eeb4a7145ca94c6ed9236e4a773f6dcafa5132b2f9170bebe684cdcb5ca72a42f0d873879359bd1781a591809947628d313a3814f67aec03aca8f5587a4d535fa31027bbe9cc0e464b1c3577f4c2dcde6b2094798a90000000000000000000000000000000000000000000000000000000000000000fffffffeecad44b6f05d15b33146549c2297b522a5eed8430cff596758e6c43d) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)

/-- reference point errors. -/
theorem p256Verify_reference_point_errors_rejected :
    p256Verify (byteArrayOf 160 0x2f77668a9dfbf8d5848b9eeb4a7145ca94c6ed9236e4a773f6dcafa5132b2f9170bebe684cdcb5ca72a42f0d873879359bd1781a591809947628d313a3814f67aec03aca8f5587a4d535fa31027bbe9cc0e464b1c3577f4c2dcde6b2094798a900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) 6900 = .ok .empty :=
  eq_ok_of_kernel (by decide +kernel)
-- End of material derived from `C2SP/wycheproof`.

end EthLib.Execution.Evm.Precompiles.P256Verify.KnownAnswers
