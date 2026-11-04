module

public import EthLib.Base.BigEndian
public import EthLib.Base.ChainConfig
public import EthLib.Execution.Blocks.Header
public import EthLib.Execution.State.Tracker

/-!
# `Blocks.DaoFork`

The DAO Fork, which moves ether between accounts outside any transaction.

At the start of its first block, the ether of 116 accounts moves to one recovery contract.

The accounts are the DAO and its extra balance account.

They also include the children of the DAO's creator, and the extra balance account of each child.

The first ten blocks of the fork carry the extra data `dao-hard-fork`.

The fork changes no other rule.

[EIP-779](https://eips.ethereum.org/EIPS/eip-779#specification) lists the accounts and both rules.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State

/-- The address that a 160-bit number spells, the most significant byte first. -/
def addressOfNat (n : Nat) : Address :=
  ⟨(natToBytes 20 n).toArray, by simp [natToBytes_length]⟩

/-- The 116 accounts whose ether the DAO Fork moves: the list `L` of EIP-779, in its order. -/
def DAO_ACCOUNTS : List Address := [
  addressOfNat 0xd4fe7bc31cedb7bfb8a345f31e668033056b2728,
  addressOfNat 0xb3fb0e5aba0e20e5c49d252dfd30e102b171a425,
  addressOfNat 0x2c19c7f9ae8b751e37aeb2d93a699722395ae18f,
  addressOfNat 0xecd135fa4f61a655311e86238c92adcd779555d2,
  addressOfNat 0x1975bd06d486162d5dc297798dfc41edd5d160a7,
  addressOfNat 0xa3acf3a1e16b1d7c315e23510fdd7847b48234f6,
  addressOfNat 0x319f70bab6845585f412ec7724b744fec6095c85,
  addressOfNat 0x06706dd3f2c9abf0a21ddcc6941d9b86f0596936,
  addressOfNat 0x5c8536898fbb74fc7445814902fd08422eac56d0,
  addressOfNat 0x6966ab0d485353095148a2155858910e0965b6f9,
  addressOfNat 0x779543a0491a837ca36ce8c635d6154e3c4911a6,
  addressOfNat 0x2a5ed960395e2a49b1c758cef4aa15213cfd874c,
  addressOfNat 0x5c6e67ccd5849c0d29219c4f95f1a7a93b3f5dc5,
  addressOfNat 0x9c50426be05db97f5d64fc54bf89eff947f0a321,
  addressOfNat 0x200450f06520bdd6c527622a273333384d870efb,
  addressOfNat 0xbe8539bfe837b67d1282b2b1d61c3f723966f049,
  addressOfNat 0x6b0c4d41ba9ab8d8cfb5d379c69a612f2ced8ecb,
  addressOfNat 0xf1385fb24aad0cd7432824085e42aff90886fef5,
  addressOfNat 0xd1ac8b1ef1b69ff51d1d401a476e7e612414f091,
  addressOfNat 0x8163e7fb499e90f8544ea62bbf80d21cd26d9efd,
  addressOfNat 0x51e0ddd9998364a2eb38588679f0d2c42653e4a6,
  addressOfNat 0x627a0a960c079c21c34f7612d5d230e01b4ad4c7,
  addressOfNat 0xf0b1aa0eb660754448a7937c022e30aa692fe0c5,
  addressOfNat 0x24c4d950dfd4dd1902bbed3508144a54542bba94,
  addressOfNat 0x9f27daea7aca0aa0446220b98d028715e3bc803d,
  addressOfNat 0xa5dc5acd6a7968a4554d89d65e59b7fd3bff0f90,
  addressOfNat 0xd9aef3a1e38a39c16b31d1ace71bca8ef58d315b,
  addressOfNat 0x63ed5a272de2f6d968408b4acb9024f4cc208ebf,
  addressOfNat 0x6f6704e5a10332af6672e50b3d9754dc460dfa4d,
  addressOfNat 0x77ca7b50b6cd7e2f3fa008e24ab793fd56cb15f6,
  addressOfNat 0x492ea3bb0f3315521c31f273e565b868fc090f17,
  addressOfNat 0x0ff30d6de14a8224aa97b78aea5388d1c51c1f00,
  addressOfNat 0x9ea779f907f0b315b364b0cfc39a0fde5b02a416,
  addressOfNat 0xceaeb481747ca6c540a000c1f3641f8cef161fa7,
  addressOfNat 0xcc34673c6c40e791051898567a1222daf90be287,
  addressOfNat 0x579a80d909f346fbfb1189493f521d7f48d52238,
  addressOfNat 0xe308bd1ac5fda103967359b2712dd89deffb7973,
  addressOfNat 0x4cb31628079fb14e4bc3cd5e30c2f7489b00960c,
  addressOfNat 0xac1ecab32727358dba8962a0f3b261731aad9723,
  addressOfNat 0x4fd6ace747f06ece9c49699c7cabc62d02211f75,
  addressOfNat 0x440c59b325d2997a134c2c7c60a8c61611212bad,
  addressOfNat 0x4486a3d68fac6967006d7a517b889fd3f98c102b,
  addressOfNat 0x9c15b54878ba618f494b38f0ae7443db6af648ba,
  addressOfNat 0x27b137a85656544b1ccb5a0f2e561a5703c6a68f,
  addressOfNat 0x21c7fdb9ed8d291d79ffd82eb2c4356ec0d81241,
  addressOfNat 0x23b75c2f6791eef49c69684db4c6c1f93bf49a50,
  addressOfNat 0x1ca6abd14d30affe533b24d7a21bff4c2d5e1f3b,
  addressOfNat 0xb9637156d330c0d605a791f1c31ba5890582fe1c,
  addressOfNat 0x6131c42fa982e56929107413a9d526fd99405560,
  addressOfNat 0x1591fc0f688c81fbeb17f5426a162a7024d430c2,
  addressOfNat 0x542a9515200d14b68e934e9830d91645a980dd7a,
  addressOfNat 0xc4bbd073882dd2add2424cf47d35213405b01324,
  addressOfNat 0x782495b7b3355efb2833d56ecb34dc22ad7dfcc4,
  addressOfNat 0x58b95c9a9d5d26825e70a82b6adb139d3fd829eb,
  addressOfNat 0x3ba4d81db016dc2890c81f3acec2454bff5aada5,
  addressOfNat 0xb52042c8ca3f8aa246fa79c3feaa3d959347c0ab,
  addressOfNat 0xe4ae1efdfc53b73893af49113d8694a057b9c0d1,
  addressOfNat 0x3c02a7bc0391e86d91b7d144e61c2c01a25a79c5,
  addressOfNat 0x0737a6b837f97f46ebade41b9bc3e1c509c85c53,
  addressOfNat 0x97f43a37f595ab5dd318fb46e7a155eae057317a,
  addressOfNat 0x52c5317c848ba20c7504cb2c8052abd1fde29d03,
  addressOfNat 0x4863226780fe7c0356454236d3b1c8792785748d,
  addressOfNat 0x5d2b2e6fcbe3b11d26b525e085ff818dae332479,
  addressOfNat 0x5f9f3392e9f62f63b8eac0beb55541fc8627f42c,
  addressOfNat 0x057b56736d32b86616a10f619859c6cd6f59092a,
  addressOfNat 0x9aa008f65de0b923a2a4f02012ad034a5e2e2192,
  addressOfNat 0x304a554a310c7e546dfe434669c62820b7d83490,
  addressOfNat 0x914d1b8b43e92723e64fd0a06f5bdb8dd9b10c79,
  addressOfNat 0x4deb0033bb26bc534b197e61d19e0733e5679784,
  addressOfNat 0x07f5c1e1bc2c93e0402f23341973a0e043f7bf8a,
  addressOfNat 0x35a051a0010aba705c9008d7a7eff6fb88f6ea7b,
  addressOfNat 0x4fa802324e929786dbda3b8820dc7834e9134a2a,
  addressOfNat 0x9da397b9e80755301a3b32173283a91c0ef6c87e,
  addressOfNat 0x8d9edb3054ce5c5774a420ac37ebae0ac02343c6,
  addressOfNat 0x0101f3be8ebb4bbd39a2e3b9a3639d4259832fd9,
  addressOfNat 0x5dc28b15dffed94048d73806ce4b7a4612a1d48f,
  addressOfNat 0xbcf899e6c7d9d5a215ab1e3444c86806fa854c76,
  addressOfNat 0x12e626b0eebfe86a56d633b9864e389b45dcb260,
  addressOfNat 0xa2f1ccba9395d7fcb155bba8bc92db9bafaeade7,
  addressOfNat 0xec8e57756626fdc07c63ad2eafbd28d08e7b0ca5,
  addressOfNat 0xd164b088bd9108b60d0ca3751da4bceb207b0782,
  addressOfNat 0x6231b6d0d5e77fe001c2a460bd9584fee60d409b,
  addressOfNat 0x1cba23d343a983e9b5cfd19496b9a9701ada385f,
  addressOfNat 0xa82f360a8d3455c5c41366975bde739c37bfeb8a,
  addressOfNat 0x9fcd2deaff372a39cc679d5c5e4de7bafb0b1339,
  addressOfNat 0x005f5cee7a43331d5a3d3eec71305925a62f34b6,
  addressOfNat 0x0e0da70933f4c7849fc0d203f5d1d43b9ae4532d,
  addressOfNat 0xd131637d5275fd1a68a3200f4ad25c71a2a9522e,
  addressOfNat 0xbc07118b9ac290e4622f5e77a0853539789effbe,
  addressOfNat 0x47e7aa56d6bdf3f36be34619660de61275420af8,
  addressOfNat 0xacd87e28b0c9d1254e868b81cba4cc20d9a32225,
  addressOfNat 0xadf80daec7ba8dcf15392f1ac611fff65d94f880,
  addressOfNat 0x5524c55fb03cf21f549444ccbecb664d0acad706,
  addressOfNat 0x40b803a9abce16f50f36a77ba41180eb90023925,
  addressOfNat 0xfe24cdd8648121a43a7c86d289be4dd2951ed49f,
  addressOfNat 0x17802f43a0137c506ba92291391a8a8f207f487d,
  addressOfNat 0x253488078a4edf4d6f42f113d1e62836a942cf1a,
  addressOfNat 0x86af3e9626fce1957c82e88cbf04ddf3a2ed7915,
  addressOfNat 0xb136707642a4ea12fb4bae820f03d2562ebff487,
  addressOfNat 0xdbe9b615a3ae8709af8b93336ce9b477e4ac0940,
  addressOfNat 0xf14c14075d6c4ed84b86798af0956deef67365b5,
  addressOfNat 0xca544e5c4687d109611d0f8f928b53a25af72448,
  addressOfNat 0xaeeb8ff27288bdabc0fa5ebb731b6f409507516c,
  addressOfNat 0xcbb9d3703e651b0d496cdefb8b92c25aeb2171f7,
  addressOfNat 0x6d87578288b6cb5549d5076a207456a1f6a63dc0,
  addressOfNat 0xb2c6f0dfbb716ac562e2d85d6cb2f8d5ee87603e,
  addressOfNat 0xaccc230e8a6e5be9160b8cdf2864dd2a001c28b6,
  addressOfNat 0x2b3455ec7fedf16e646268bf88846bd7a2319bb2,
  addressOfNat 0x4613f3bca5c44ea06337a9e439fbc6d42e501d0a,
  addressOfNat 0xd343b217de44030afaa275f54d31a9317c7f441e,
  addressOfNat 0x84ef4b2357079cd7a7c69fd7a37cd0609a679106,
  addressOfNat 0xda2fef9e4a3230988ff17df2165440f37e8b1708,
  addressOfNat 0xf4c64518ea10f995918a454158c6b61407ea345c,
  addressOfNat 0x7602b46df5390e432ef1c307d4f2c9ff6d65cc97,
  addressOfNat 0xbb9bc244d798123fde783fcc1c72d3bb8c189413,
  addressOfNat 0x807640a13483f8ac783c557fcdf27be11ea4ac7a]

/-- The recovery contract that receives the ether of the DAO accounts. -/
def DAO_RECOVERY : Address := addressOfNat 0xbf4ed7b27f1d666546e30d74d50d173d20bca754

/-- The extra data of the first blocks of the DAO Fork: `dao-hard-fork` in ASCII. -/
def DAO_EXTRA_DATA : ByteArray := "dao-hard-fork".toUTF8

/-- The blocks from the first block of the DAO Fork that must carry its extra data. -/
def DAO_EXTRA_DATA_BLOCKS : Nat := 10

/-- The block at which a chain activates the DAO Fork, if it does by block number. -/
def daoForkBlock (config : ChainConfig) : Option Nat :=
  config.activations.findSome? fun
    | (.daoFork, .block number) => some number
    | _ => none

/-- Whether a header has the extra data that the DAO Fork asks of its first ten blocks.

A header outside those blocks, or on a chain without the fork, passes.

The header check takes no chain configuration, so a caller with one applies this rule as well. -/
def daoExtraDataValid (config : ChainConfig) {fork : Fork} (header : Header fork) : Bool :=
  match daoForkBlock config with
  | some first =>
    if first ≤ header.number ∧ header.number < first + DAO_EXTRA_DATA_BLOCKS then
      decide (header.extraData = DAO_EXTRA_DATA)
    else true
  | none => true

/-- Move the ether of every DAO account to the recovery contract, in the order of the list.

Each account gives its whole balance, so the move never lacks funds. -/
def applyDaoFork (fork : Fork) (tx : TransactionState) : Except StateError TransactionState :=
  DAO_ACCOUNTS.foldlM
    (fun tx address => tx.moveEther fork address DAO_RECOVERY (tx.getAccount address).balance)
    tx

end EthLib.Execution.Blocks
