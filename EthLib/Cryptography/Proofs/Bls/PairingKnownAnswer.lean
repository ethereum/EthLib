module

public import EthLib.Cryptography.Proofs.Bls.PairingKnownAnswerMiller
public import EthLib.Cryptography.Proofs.Bls.PairingCongr

/-!
# Proofs: the pairing of the generators

The kernel computes the pairing of the two generators.

The result equals the value that the pairing-friendly curves draft publishes.

See [draft-11](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11),
Appendix B, curve BLS12_381.

In the order of the fields of the result, its 12 coefficients are `e_0` to `e_11` of the draft.

The final exponentiation runs through checkpoints, so each step stays small in the kernel.

The checkpoints come from EthLib's own code, and only the last value is a check.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.PairingKnownAnswer

/-- A power by `a * 2^k + b` is a power by `2^k` of a power by `a`, times a power by `b`. -/
theorem powNat_horner (x : Fp12) (a b k : Nat) :
    Fp12.powNat x (a * 2 ^ k + b) =
      Fp12.powNat (Fp12.powNat x a) (2 ^ k) * Fp12.powNat x b := by
  rw [Fp12.powNat_eq_pow, Fp12.powNat_eq_pow, Fp12.powNat_eq_pow, Fp12.powNat_eq_pow, pow_add,
    pow_mul]

/-- The easy part of the final exponentiation. -/
def easyGenerators : Fp12 :=
  ⟨⟨⟨coeff 0x13427a84d54f3f6e8d3e7e5f93c6f59d6bcb99a8dda366c22115641ca5bc9a59
          0xea6cf9364b31e3695c91f953914d8af2,
        coeff 0x0371ff74042d4cfe01c554e6766de1b4d023256cab2f70b7517f5c6677a60e58
          0x1524e096dce00a8134831f7982294ff8⟩,
      ⟨coeff 0x0989eac81bb4b6e3bb766959dfcad77a1d032814d8cacd0bdacdd6c92fe045d9
          0x78e5bd0a389fb57aa34651b7ceb238b2,
        coeff 0x1888f8b97b677b7db516d13035cc0665393ca3f46c23135b2a5cdb8fc304ba39
          0x8bcb1e17e0751cae5988dbef5c9552a3⟩,
      ⟨coeff 0x12757edd66aa395eafaa473cd97ad801c1a60a0eba1ff4e81c08d483e9a74ca4
          0x26bde4b3b78c0980a0b5f112ed50af3b,
        coeff 0x0b0ca0fabf1a74409183b9e237d83aec2f9ba6d509682b26d3b9381b8e721b66
          0x7019352e90897d33cf8bac8c7bad88f0⟩⟩,
    ⟨⟨coeff 0x12d937a4c8ace7e5c9535fd05eb2f7074df3194292be15eae5cc2afc794513f6
          0x1e64d463a742f6eb497dc9b2343b143f,
        coeff 0x03828aec4960cc8a104baad3ce5a4d608a4b090d334935b17516cf9dbe6121d9
          0x86887cd3af2ee38c54bf71776be0a289⟩,
      ⟨coeff 0x18bb2d88d07a844ba2ddc4e40d08a321ac1ff139d4e7ea885d6d6903809fc47c
          0x3ddf20ff76b43b312033a5d1c461c2e5,
        coeff 0x11a2ca4bd496599b620e216e62c79c54b98ab94c9e13163bc23a43cbdb221724
          0x38355f06a4862f651f6569e5e02d0e29⟩,
      ⟨coeff 0x06cc225fc2a029af3c983bf1f2cbea6e7f3e37409f7f61c5f2259cffd0e3ab6d
          0xa2d186c6b99021c5178a704475cca4c0,
        coeff 0x04d65e8d67cfd7f5979bceff4987bf0e69487e4c95c64ced45e52ee6dc8484c2
          0x24752a5d9d31940c079b8de7ebf0b740⟩⟩⟩

/-- Checkpoint 1 of the power by `p^2`. -/
def middle1 : Fp12 :=
  ⟨⟨⟨coeff 0x15829854deee65b47da7eee87466a76dc3587c96c3e5d61efd70879efd25122e
          0xa314b180076a60e46064fbc413c781f1,
        coeff 0x0745f8f6083c092b4d39985cd68dce517fd2bc949c35a1645aca29c3654d6f17
          0xd93da9fa1df0e9dcbaee2e9668d9234c⟩,
      ⟨coeff 0x107fed62689737caaf0c11409379ab28ec5e566dd72a74c5e5cf43e98d0c0c7b
          0x84be6514704d2522e60737658f9e0aca,
        coeff 0x10ae64536589074e8405c439f351df28a25081fee8357012cbc5eb98f980b7dc
          0x7f1f39158bfbd43d1a4ecba93c630098⟩,
      ⟨coeff 0x1946706f3f9999c05ffa4ae95b393ad59eaafaac07d88d422a05ffa64cd89933
          0x9ea63decc6f6785acda0b49fdd46b358,
        coeff 0x07c88b359b1c04fc25ba721e6755a706a2fbc9b38beeef1edd340ca262a8139f
          0xcfb75a863fa56a73ffb63de86679ab1a⟩⟩,
    ⟨⟨coeff 0x11bb9ee602b66480f5231696db3ba63acc25198f6b640c65ff37dd2b7aadb09c
          0x55b4f15fd32c95e3ac004cfb3f734341,
        coeff 0x14eb344d7987c0f9bfb4e4604e718515e9148f9a1e080c71f511fa21618d799c
          0x9f1747b9d71a712717d74d86c070f562⟩,
      ⟨coeff 0x09a4121c0c96265e482af2baa6309157f7ee4b427f058b0067cf46445cd24243
          0x6df8501047276e10609409080e2953f9,
        coeff 0x10b8c54fde6d856e4d5942cb0d264b034fe64fa4c35505b2670dffb73a11571b
          0xb5ccfe3b535e4b7529d33100c25925f8⟩,
      ⟨coeff 0x0d8ff985ccbdc022f292fe80e31149db02d2ae7b8564da077bd2da3d1bc5752c
          0x1e05b77ec9d38062955006391e6a7031,
        coeff 0x0eb1138839d22ca815cc91ef5308654e25107345a8f86646ad9c5de5169a55d2
          0x745d5bf0ef654636c63f21f0b6115bec⟩⟩⟩

/-- Checkpoint 2 of the power by `p^2`. -/
def middle2 : Fp12 :=
  ⟨⟨⟨coeff 0x1720bb81e6010b495a2599ea257f20334dcebdd5c4cd3e93444b4db57e3e6bea
          0x020e83a0c8492ab8ca5cfd437a5f6f51,
        coeff 0x0d3508cf5d170ad06cb4704c6e5a273f5320484ee4078f1265b54dbccff0bdb6
          0x2e9eed05133de6a63d235cd70bc2bcc7⟩,
      ⟨coeff 0x13273a49c07667ee0283b4dac27cbfb255fa02880c614728f4dd34033bbffe60
          0xf0add58ba903b9cb9fa272f8fab1ca6a,
        coeff 0x01d19cd46f0c4b811d1273e8dd6d47128f9a701125c6e90cfc7a0c41ab80df6d
          0x0873b6ba46b9f06cab1fc5a66261b98b⟩,
      ⟨coeff 0x005588e77ba0e05b2648d30dd4b0e961abe7384fe2d4e4c41fcd007e7373cc52
          0x8714c52befde0037d1be65029ffe19ac,
        coeff 0x0b2e4ab3c3db0d16af3977a91afefb6d94497d0d64a54b54df0ef4d568e833e0
          0x2b9f16eda6bd420aafb40ac2b9f23f48⟩⟩,
    ⟨⟨coeff 0x14c931b6f4ca1f265c44204825f5b02bf1dd553841013f12b0fe8a16325ff4a2
          0x55c2aba331b7b6123a8c5092b1727754,
        coeff 0x025dd49175678048000a92091d1c9761cefa941b5c86f7baa340b77fcd749c1a
          0x0f494f34105ee5e0c4edfc0cf99f90a5⟩,
      ⟨coeff 0x191fb2caa72e24fd2ca7432c3f55da5d8c3d37907e1f48205427328bdce072f9
          0x1d90b029e5d9143159029ed349ea201e,
        coeff 0x1475cbb95240c877e8455bea2c0e33d45dbcef34bc7b8160d8ea1c54f9165bdc
          0x6c598b88b66fb094da853754a2574ce1⟩,
      ⟨coeff 0x0693e23a45d1e1811eeb1335ce51a501ba0405a51b0d047fde0b383fe03ecc43
          0x6ab9a10ffc4c99fa3a65a001072c399d,
        coeff 0x0fb89945ca757ac2357ed86d0e003d98026f3c0c1ed48f57ce5fdfd095eab4da
          0x3ce5e8bf65c34dc68d9de4675d83745d⟩⟩⟩

/-- Checkpoint 3 of the power by `p^2`. -/
def middle3 : Fp12 :=
  ⟨⟨⟨coeff 0x13427a84d54f3f6e8d3e7e5f93c6f59d6bcb99a8dda366c22115641ca5bc9a59
          0xea6cf9364b31e3695c91f953914d8af2,
        coeff 0x0371ff74042d4cfe01c554e6766de1b4d023256cab2f70b7517f5c6677a60e58
          0x1524e096dce00a8134831f7982294ff8⟩,
      ⟨coeff 0x08007dc2e99ed697edd2493140e34bc62866d0ca72029ca969674686985a91f1
          0x249f4541770e7467f7c36a64bebe9f90,
        coeff 0x04e13bd3c80e7183fcd25f94f774fda725f0be3fdb8bd55aa3eee2b9423acd12
          0x6d7fb555110e82752ed513e0bd7295ee⟩,
      ⟨coeff 0x19f065f8e6edb8600c5334a1534d984ad17f31deb2a5adde937a670b78ac5bbf
          0xae08833a13d86679645dffecea7b1654,
        coeff 0x017ae895162b3ccca0e876e153051482bfff75697b9ca255496f6290c411cea9
          0x169d0e9c0e36d16356041bf241c87c26⟩⟩,
    ⟨⟨coeff 0x02844c14212e947880eabb46b57942ca87dae1671d65ae0b2ee6efe775a25591
          0x4632d1287174ec6cce0c28463ccf4cae,
        coeff 0x01e4741fb4ea83515c531f151060be4a97b95dfe13b72775fbb126bc73e36bcf
          0x6a2e01c9c6c0fa32965ea0657111030b⟩,
      ⟨coeff 0x0145e4616905624ea83de2d2364309b5b8575a4b1e9d283709c3699d761131a7
          0xe0ccdeff3a9fc4ce99cb5a2e3b9de7c6,
        coeff 0x085e479e64e98cfee90d8647e0841082aaec92385571fc83a4f68ed51b8edeff
          0xe676a0f80ccdd09a9a99961a1fd29c82⟩,
      ⟨coeff 0x14725bc0769c0b3df5f9ec91bc233cecbd6b0ed1cb7771bec93fd9d4775d53bf
          0x8970f1d16386218babd79d1e42022bbe,
        coeff 0x0574a57c458fc346d5b456ab1d1f364b902221b11b18244cb946a692642e5127
          0x28199c5be1648e01f601cfdc43ea6d12⟩⟩⟩

/-- The middle part of the final exponentiation. -/
def middleGenerators : Fp12 :=
  ⟨⟨⟨coeff 0x09cfb5cdbdfb170f707acf2a119c60c7a42d9607400a07cf0a1ca6a66d678258
          0xb11fd6eef8dab538549b29fbe5e940a5,
        coeff 0x054010ee2fce8b2ef40ad45f69f8f34e8bff542a075af25a51b5558a3e20587f
          0x26c49ecb8f9d5e4f53502eca461a0191⟩,
      ⟨coeff 0x181b92344a97b2be5183ff569d4e788a5c265eeff42b00016ccabe069eb66045
          0xbb202f93fdff68c4a69c5a2b114983a6,
        coeff 0x1828b41889e6745acefd33c061bac175eff11b68853690f3fd4cf86bfa7da384
          0xd65c7694187f771c1dee96dd0e3e50ca⟩,
      ⟨coeff 0x152c9372d5c5379f2bc83de4767d582caad6d14a09b91556bcdb58f78cdc23e9
          0x726014205ca6e4daea514e835c30ffa6,
        coeff 0x0f63c4bee282d774a5f565bff148c57d6c872f426cfa0118f3326a32e339321b
          0xa7caf65c22bac0bbc12e567aafa5e20b⟩⟩,
    ⟨⟨coeff 0x055c3a150de9f27ddd94f8a9f44dff985452d80beb58d9109bbbc9b7155768c3
          0xe2ac57399be682674f77f5a593cf5fa3,
        coeff 0x080686fcf89ea3bea2bad2570e6882097895ea3828ad67d807349e2cf032a7c9
          0x65d83e06f795f295135ab0991f958aef⟩,
      ⟨coeff 0x11f5e6bd624a29d8effc4ec21dd46d995045e66cc8657fb91a582b06bfdb925b
          0x343b9b7c279e547f8373ae7c9b601f3d,
        coeff 0x19aa5557f245b2ca84ed238cb32b279150dbbf88415386a23c6fb0f05f167b86
          0xbef07a74921f06bb88092a6206cc58c3⟩,
      ⟨coeff 0x0832f3fef66f64b46560617243b5e38291a18c2e1c4e5c3383bfcf87b2f40996
          0xf5505d61197a00ac57ac462e389aeeb9,
        coeff 0x07e850bc5bf5dcb89dc030a689f045f36e464093aa549b95c3eace6873451db6
          0xcf6374a8a9c29bed19e0f3fa2899f03b⟩⟩⟩

/-- Checkpoint 1 of the hard part. -/
def hard1 : Fp12 :=
  ⟨⟨⟨coeff 0x19697d247c20efd45ef81a674586c5aaa7ec9e5a4bce9d0b02d6ffa98dd326f9
          0x3b521d2a789c2d48ee6cbf17b2926047,
        coeff 0x1203f7f9fb90886d6e8d53e15d842c6777543162f9d3c39e80f65e56ca9cc7e6
          0x40e7b6537a96a8dd11d9e372457e7905⟩,
      ⟨coeff 0x199023210232513b84eb3e4fa47e16ec26268231634291353b9f2e25a6c5173a
          0xdd870fc14d99e52986008e4d2eb6ec4c,
        coeff 0x050b92158a0dc5c89b0f3f047e2d08c2f5ee442977c4907570cd28edfa83007c
          0x310c3c9de8f1e714fd00451e7b66b47e⟩,
      ⟨coeff 0x14434445def705a12b1e409c2988cc9f1e9fc6cee28a527f032b72379bd4a782
          0x57fe97457a0b2dcf696e35c9505fc929,
        coeff 0x0988b7d36dcd919c36a7ccdd357869498ad8315bb8de377deb0e4e91d4cd3be5
          0x10c3790af2202f9f822ec6c260c4ca9d⟩⟩,
    ⟨⟨coeff 0x00e9b5063e085c9f4e56d71fb0e5d422c309a09191e049f15cb53c77d9add6f5
          0x7b8a13353ef17e54961b17eaeccd1e9a,
        coeff 0x0f7f4d2e97f6d5fdaf0835a2b9d697f4b7d2bfd4d35988799959262818d72403
          0xdc1a81d2eba485063a4e937197c1e65a⟩,
      ⟨coeff 0x0a58651e577c7c692d72711a62066b499b1a4e7ba44ba27f93617547c5aa61d3
          0x6d39b6c2fc1494e4c36c3deb354458ab,
        coeff 0x03aa071c03a49db1211c162aa08a849aaaff9abfb136e77a10fef645dc5980f7
          0xe8f0f5c37263a0db81ca5987db2b79f9⟩,
      ⟨coeff 0x09bb6a0d4ff92e9ca7d4c8bfe91014b1460f13931fb2802ff2073c3d37d2d5ca
          0x3a9fcb59ed5d39ec39ae7b3c61907e78,
        coeff 0x0ca8fc3f8093ace888fb1c932a1c313a546505a50e75d79c4c8732f6ebb4ad9f
          0x0a9949872968dc7921248dda0571429d⟩⟩⟩

/-- Checkpoint 2 of the hard part. -/
def hard2 : Fp12 :=
  ⟨⟨⟨coeff 0x001bd76dfd267ed032f511505e5f8fb5e6389c39201ed9c42fd6ca21652c1471
          0xcb897588be3a7b9398357d7d96d0a14e,
        coeff 0x0dfe0cfaa78a9fd1d312568c2c697e59a05249b5edf63db9db66b45412d4ff89
          0x6ec6e6409d749e8f4c848bb5cd38081e⟩,
      ⟨coeff 0x16b917ac2127fca69dad5d09952c761fea9caa387306116e1941b16f96af7b94
          0x0285e73eee42155edd91f899bec9fc23,
        coeff 0x04cb0ce5495a3cc8372efb66faf25de138fcb747d9ff68ae9ae119e836bcaaea
          0x1c33332731b4af19124906c07647e23c⟩,
      ⟨coeff 0x13d77919388f68f8aafac6aad7757e153e21f8e95e3a483280f0086bcb669da3
          0x4972bd08ac5af8c4234173bb564e61ee,
        coeff 0x1078302acdd4676356f2d6b00a9fdf22cf93ed811e756944bb986a3dc5ce0c82
          0x6797e4703dd45b245071d4e2e71580cc⟩⟩,
    ⟨⟨coeff 0x0be419369bbd88aa5ccdb3032a5433a3c135eab2f027c339d0fc3c6751ab88d4
          0xf234a1d05e3f140238d6652a48f810ec,
        coeff 0x05189a7dac5f6b5dec01b470785e3197cac04be81b4c44811453d77ab3ced0bc
          0x02905f97a024fdfd2513d998a6a64f0e⟩,
      ⟨coeff 0x0dabfa5410d39e1f366935cd58f3c8f91305f6fea3649d0b71a7e0c3bd0c976e
          0xb4c079d57f0d0035533dccb115127497,
        coeff 0x12d538ce538c47e736b0f4481799a16b7e6de155a0cbd2bc43756560833e6f38
          0x76a6bc07df66d0b6e90bbc1b6996ed98⟩,
      ⟨coeff 0x0b4954fcf44930514ffb0b15a169faa0c85beaed5b6b7d60e5c992066321cad9
          0xa5796c261d829513707a285994611335,
        coeff 0x1146ea4aa9a886f4ce7fc6138d3b8e18ef118e692a8ffc65954078b9b93b4e20
          0xa1f8622596dc9fb876cdf2eef8b8484e⟩⟩⟩

/-- Checkpoint 3 of the hard part. -/
def hard3 : Fp12 :=
  ⟨⟨⟨coeff 0x025e9d1c9da1c20e82e0a5b4a3b269bd126a6b129a53da36fc75926f3ee0d324
          0x7e7e6d5027620d7d3cb51c1db5759429,
        coeff 0x0683749cff5d87fcfa17897e3216dfe88a0ed32635362686c2e0cf2acf3cd486
          0x315760c2c529b7e3bf9ef3da58f1c67e⟩,
      ⟨coeff 0x0cd34279105830a4e1346befe071028db54e1d174ac8d17c2e9e2a3a7def4dc5
          0x9860aca43bf56fc8073bab9e24252b3a,
        coeff 0x19d01773db791035999a12fb724a40e4af34f3e1258bc3f2ebf8d05f41b0b761
          0x936ec69eee0ea0fbde0e34825905c5b4⟩,
      ⟨coeff 0x148ba47c10d3d19e6d96252d4e0d44a24b8f872521fa903ae424a05196a509f9
          0xee896a01b3f626a22cac004edc180b3e,
        coeff 0x0947b1d71a21a1cdb90dc8dc71aa034eb3900d58846c4e96cb1dbcc11efb2c70
          0x1acaf9cdc788cf597226fab8bee1b5f3⟩⟩,
    ⟨⟨coeff 0x08d8d49d23d39fc316602dc2dcfcfc350eb0af2e056eae44119e6acc59512d5f
          0xe2805c93cc7f851001f75a832414ff91,
        coeff 0x07c5140495111944adae84231ecd08c9cfa530d5cfdcd0ade5c2bbae87ca4b39
          0xd2ef82cacc1c2b52af5ebb2bbc085f25⟩,
      ⟨coeff 0x0b7de8dab9ea52bee8da8f0f35264c35e07c609a7c8cadc9b6430a0d01d94c2c
          0x301a861b3f8d804e0a54deff5e3c2b5f,
        coeff 0x121ac6cc7567a6418f22ee6363e779749b310b22273d5a3c8e755212f4959f4a
          0x3c37806433af761dab52975daca9099a⟩,
      ⟨coeff 0x080866a4b7c0711fa30d8a44084b41d8f886ec15f53076533d57956cb9ffa850
          0x8a58206ec15f151b1e41522b76dfd04f,
        coeff 0x0d5679ade4babd3b7ff258d87701d0946596b5821924306137ac22605438046e
          0xc1ff901723e3a1af3d00036f581df29e⟩⟩⟩

/-- Checkpoint 4 of the hard part. -/
def hard4 : Fp12 :=
  ⟨⟨⟨coeff 0x011a2cd34514604e64c71ecdb7f110fe3605a3ff945fcda08b7e64191167fe25
          0x0a07673eb6fd401305f3e14869d26039,
        coeff 0x198d7b78e48ba7b4f339a76baf40e4fe28c4817a720c84d56f35a2c066e7fa0c
          0x7d46853e1f60bd7e2df656f633773a62⟩,
      ⟨coeff 0x1764c1a264427563e262dcefb174acc2c64826ef8bfd3d80032d773db239afb1
          0x7084b886165461c78feaae94ae05d4d9,
        coeff 0x17d55ab04b14ff2abbb93741316def760cac4192947858e293c31dcc55b8d98c
          0x1e7bc21508bac7a3f5558c7193af3874⟩,
      ⟨coeff 0x0aac16786cdd976f603c101ac4b87844f49ae938f40fff2eba4240bce9ce78e1
          0xf2b198fad89ec47575e003b777195137,
        coeff 0x03ba2b34db5c02fdd0ad4df9e6affc5926fbece386ee2df864a4fbfd486e8728
          0xda44dd94d83a5f5f15a9dae8b48e9a1a⟩⟩,
    ⟨⟨coeff 0x0d716eecf8318ea0f2c3c6423a2ab269b6814cc517c55c9c4ffdc55ac501fd7f
          0xb5403ef9fbff6ee76845893c384cee08,
        coeff 0x0ef1c3d755ea74a62a98175586868c683282170e374de1f7a6c2fe2aa2987f6a
          0x093c75ee66983d00b2ffac7fdf84a0dd⟩,
      ⟨coeff 0x152a60d720104a02844808d9dbf4b3d2c619e8d401d0c488afdccad06061a853
          0xa0bc21a2150ff6b8d2d9dbbf8d519b08,
        coeff 0x061381c099efca6ae3976b9b7a81c8ab17f16d5d4ed5e38e922947e75c165b71
          0x3da5642dbddd3d438c5b9ca1f3b874ca⟩,
      ⟨coeff 0x1564c047c8ac45286e9a0df44cfe593b15c9baedf29cb544b0f71f5876a03b58
          0xc533dc092dd0323975ce9da27c09e0bc,
        coeff 0x159bb4f92bc9edd7b7f0f5813b29bc55642c966f54f3ed5ca6c123f88f7f0e7c
          0x93f3997c2e70ced428c21cddb4e1843a⟩⟩⟩

/-- The pairing of the generators, as the draft publishes it. -/
def pairingGenerators : Fp12 :=
  ⟨⟨⟨coeff 0x11619b45f61edfe3b47a15fac19442526ff489dcda25e59121d9931438907dfd
          0x448299a87dde3a649bdba96e84d54558,
        coeff 0x153ce14a76a53e205ba8f275ef1137c56a566f638b52d34ba3bf3bf22f277d70
          0xf76316218c0dfd583a394b8448d2be7f⟩,
      ⟨coeff 0x095668fb4a02fe930ed44767834c915b283b1c6ca98c047bd4c272e9ac3f3ba6
          0xff0b05a93e59c71fba77bce995f04692,
        coeff 0x16deedaa683124fe7260085184d88f7d036b86f53bb5b7f1fc5e248814782065
          0x413e7d958d17960109ea006b2afdeb5f⟩,
      ⟨coeff 0x09c92cf02f3cd3d2f9d34bc44eee0dd50314ed44ca5d30ce6a9ec0539be7a86b
          0x121edc61839ccc908c4bdde256cd6048,
        coeff 0x111061f398efc2a97ff825b04d21089e24fd8b93a47e41e60eae7e9b2a38d54f
          0xa4dedced0811c34ce528781ab9e929c7⟩⟩,
    ⟨⟨coeff 0x01ecfcf31c86257ab00b4709c33f1c9c4e007659dd5ffc4a735192167ce19705
          0x8cfb4c94225e7f1b6c26ad9ba68f63bc,
        coeff 0x08890726743a1f94a8193a166800b7787744a8ad8e2f9365db76863e894b7a11
          0xd83f90d873567e9d645ccf725b32d26f⟩,
      ⟨coeff 0x0e61c752414ca5dfd258e9606bac08daec29b3e2c57062669556954fb227d3f1
          0x260eedf25446a086b0844bcd43646c10,
        coeff 0x0fe63f185f56dd29150fc498bbeea78969e7e783043620db33f75a05a0a2ce5c
          0x442beaff9da195ff15164c00ab66bdde⟩,
      ⟨coeff 0x10900338a92ed0b47af211636f7cfdec717b7ee43900eee9b5fc24f0000c5874
          0xd4801372db478987691c566a8c474978,
        coeff 0x1454814f3085f0e6602247671bc408bbce2007201536818c901dbd4d2095dd86
          0xc1ec8b888e59611f60a301af7776be3d⟩⟩⟩

/-- The square of `p`, in digits of 256 bits. -/
theorem modulus_sq_eq :
    Fp.modulus ^ 2 =
      ((0x2a437a4b8c35fc74bd278eaa22f25e9e2dc90e50e7046b466e59e49349e8bd0) * 2 ^ 256 +
      0x50a62cfd16ddca6ef53149330978ef011d68619c86185c7b292e85a87091a049) * 2 ^ 256 +
      0x66bf91ed3e71b743162c338362113cfd7ced6b1d76382eab26aa00001c718e39 := by
  decide

/-- The exponent of the hard part, in digits of 256 bits. -/
theorem finalExpHard_eq :
    finalExpHard =
      ((((0xf686b3d807d01c0bd38c3195c899ed3cde88eeb996ca394506632528d6a9a) * 2 ^ 256 +
      0x2f230063cf081517f68f7764c28b6f8ae5a72bce8d63cb9f827eca0ba621315b) * 2 ^ 256 +
      0x2076995003fc77a17988f8761bdc51dc2378b9039096d1b767f17fcbde783765) * 2 ^ 256 +
      0x915c97f36c6f18212ed0b283ed237db421d160aeb6a1e79983774940996754c8) * 2 ^ 256 +
      0xc71a2629b0dea236905ce937335d5b68fa9912aae208ccf1e516c3f438e3ba79 := by
  decide

theorem easy_eq :
    millerGenerators.conjugate.conjugate * millerGenerators.conjugate.inverse =
      easyGenerators := by
  decide +kernel

theorem middle1_eq :
    Fp12.powNat easyGenerators
      0x2a437a4b8c35fc74bd278eaa22f25e9e2dc90e50e7046b466e59e49349e8bd0 = middle1 := by
  decide +kernel

theorem middle2_eq :
    Fp12.powNat middle1 (2 ^ 256) * Fp12.powNat easyGenerators
      0x50a62cfd16ddca6ef53149330978ef011d68619c86185c7b292e85a87091a049 = middle2 := by
  decide +kernel

theorem middle3_eq :
    Fp12.powNat middle2 (2 ^ 256) * Fp12.powNat easyGenerators
      0x66bf91ed3e71b743162c338362113cfd7ced6b1d76382eab26aa00001c718e39 = middle3 := by
  decide +kernel

theorem middle_eq : middle3 * easyGenerators = middleGenerators := by
  decide +kernel

theorem hard1_eq :
    Fp12.powNat middleGenerators
      0xf686b3d807d01c0bd38c3195c899ed3cde88eeb996ca394506632528d6a9a = hard1 := by
  decide +kernel

theorem hard2_eq :
    Fp12.powNat hard1 (2 ^ 256) * Fp12.powNat middleGenerators
      0x2f230063cf081517f68f7764c28b6f8ae5a72bce8d63cb9f827eca0ba621315b = hard2 := by
  decide +kernel

theorem hard3_eq :
    Fp12.powNat hard2 (2 ^ 256) * Fp12.powNat middleGenerators
      0x2076995003fc77a17988f8761bdc51dc2378b9039096d1b767f17fcbde783765 = hard3 := by
  decide +kernel

theorem hard4_eq :
    Fp12.powNat hard3 (2 ^ 256) * Fp12.powNat middleGenerators
      0x915c97f36c6f18212ed0b283ed237db421d160aeb6a1e79983774940996754c8 = hard4 := by
  decide +kernel

theorem pairingGenerators_eq :
    Fp12.powNat hard4 (2 ^ 256) * Fp12.powNat middleGenerators
      0xc71a2629b0dea236905ce937335d5b68fa9912aae208ccf1e516c3f438e3ba79 = pairingGenerators := by
  decide +kernel

/-- The final exponentiation of the Miller loop of the generators is the published pairing. -/
theorem finalExponentiation_generators :
    finalExponentiation millerGenerators.conjugate = pairingGenerators := by
  simp only [finalExponentiation]
  rw [easy_eq, modulus_sq_eq, powNat_horner, powNat_horner, middle1_eq, middle2_eq, middle3_eq,
    middle_eq, finalExpHard_eq, powNat_horner, powNat_horner, powNat_horner, powNat_horner,
    hard1_eq, hard2_eq, hard3_eq, hard4_eq, pairingGenerators_eq]

/-- The pairing of the generators is the value of the draft. -/
theorem pairing_generators :
    finalExponentiation
        (millerLoop blsX (Embedded.ofG2 G2.generator) (Embedded.ofG1 G1.generator)).conjugate =
      pairingGenerators := by
  rw [millerLoop_generators, finalExponentiation_generators]

/-- The pairing check rejects the pair of generators, since their pairing is not 1. -/
theorem pairingCheck_generators : pairingCheck #[(G1.generator, G2.generator)] = false := by
  rw [pairingCheck_eq_finalExp_prod]
  have hf : pairFactor (G1.generator, G2.generator) = some millerGenerators.conjugate := by
    unfold pairFactor
    rw [ite_eq_right (by decide), millerLoop_generators]
  show (finalExponentiation
    (([(G1.generator, G2.generator)].filterMap pairFactor).foldl (· * ·) Fp12.one)).isOne = false
  rw [List.filterMap_cons, hf, List.filterMap_nil, List.foldl_cons, List.foldl_nil,
    Fp12.one_eq_one, one_mul, finalExponentiation_generators]
  decide

end EthLib.Cryptography.Bls.PairingKnownAnswer
