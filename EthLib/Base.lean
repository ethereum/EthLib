module

public import EthLib.Base.Address
public import EthLib.Base.Base64
public import EthLib.Base.ByteOrder
public import EthLib.Base.Bytes
public import EthLib.Base.Denominations
public import EthLib.Base.ChainConfig
public import EthLib.Base.Except
public import EthLib.Base.ExecutionConfig
public import EthLib.Base.Fork
public import EthLib.Base.GasLimit
public import EthLib.Base.Hash32
public import EthLib.Base.Hex
public import EthLib.Base.Json
public import EthLib.Base.Json.Document
public import EthLib.Base.U256
public import EthLib.Base.Uint64
public import EthLib.Base.Word32

/-!
# `EthLib.Base`

The bytes, the integers and the forks that every layer uses.

It also holds the chain configuration and the gas limit step, which several layers share.

The rest are codecs of bytes and text, the units of ether, and an assertion in `Except`.
-/
