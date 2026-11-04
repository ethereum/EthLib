module

public import EthLib.Networking.Proofs.Discv5.Identity
public import EthLib.Networking.Proofs.Discv5.Message
public import EthLib.Networking.Proofs.Discv5.Packet
public import EthLib.Networking.Proofs.Devp2p.P2p
public import EthLib.Networking.Proofs.Discv4.Packet
public import EthLib.Networking.Proofs.Encoding.Varint
public import EthLib.Networking.Proofs.Enr.Base64
public import EthLib.Networking.Proofs.Enr.Consensus
public import EthLib.Networking.Proofs.Enr.Record
public import EthLib.Networking.Proofs.Gossip.MessageId
public import EthLib.Networking.Proofs.Gossip.Subnet
public import EthLib.Networking.Proofs.Gossip.Topic
public import EthLib.Networking.Proofs.Gossip.Validation
public import EthLib.Networking.Proofs.ReqResp.Encoding
public import EthLib.Networking.Proofs.Rlpx.Ecies
public import EthLib.Networking.Proofs.Rlpx.Frame
public import EthLib.Networking.Proofs.Rlpx.Handshake
public import EthLib.Networking.Proofs.Snappy.Block
public import EthLib.Networking.Proofs.Snappy.Frame

/-!
# `EthLib.Networking.Proofs`

Machine-checked properties of the networking specifications.

The tree mirrors the definitions it proves things about:

```text
    EthLib.Networking.Foo.Bar          the definitions
    EthLib.Networking.Proofs.Foo.Bar   the theorems about them
```

The proofs build in their own Lake library.

The runtime code never imports them, so nothing here is linked into the Python extension.
-/
