module

public import EthLib.Base.Hash32
public import EthLib.Serialization.Rlp.Codec

/-!
# `Execution.Network.Cells`

The cell exchange of eth/72, from three sections of [`caps/eth.md`][eth].

They are "Blob Transaction and Cell Exchange", "GetCells (0x14)" and "Cells (0x15)".

[eth]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#getcells-0x14

[EIP-8070][eip-8070], status Last Call, adds them.

A cell index refers to the cell at that index in every blob of a transaction.

A bitmap of 16 bytes marks the cell indices that a request asks for, or that a response holds.

The checks here compare two bitmaps bit by bit and count their bits.

So they need no order of the bits.

The `eth.md` text differs from EIP-8070 here: it adds a request ID to GetCells and to Cells.

EthLib follows `eth.md`, the protocol text.

[eip-8070]: https://eips.ethereum.org/EIPS/eip-8070#specification
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

/-- The message ID of GetCells. -/
def GET_CELLS_ID : Nat := 0x14

/-- The message ID of Cells. -/
def CELLS_ID : Nat := 0x15

/-- The size of a cell in bytes, 2 KiB. -/
def BYTES_PER_CELL : Nat := 2048

/-- The number of cell indices of a bitmap, 128. -/
def CELL_INDICES : Nat := 128

/-- A bitmap of cell indices: 16 bytes. -/
abbrev CellMask := Vector UInt8 16

/-- Whether bit `i` of a bitmap is set: bit `i % 8` of byte `i / 8`.

The checks here do not depend on this order. -/
def CellMask.has (mask : CellMask) (i : Nat) : Bool :=
  if h : i / 8 < 16 then (mask[i / 8] >>> (i % 8).toUInt8) &&& 1 == 1 else false

/-- The number of cell indices that a bitmap marks. -/
def CellMask.count (mask : CellMask) : Nat :=
  ((List.range CELL_INDICES).filter mask.has).length

/-- Whether every index that `a` marks, `b` marks too. -/
def CellMask.subset (a b : CellMask) : Bool :=
  (List.range CELL_INDICES).all fun i => !a.has i || b.has i

/-- Why the cells of a Cells answer do not answer a GetCells. -/
inductive CellsError where
  /-- The response marks a cell index that the request does not ask for. -/
  | maskNotSubset
  /-- The transactions are not requested ones, in the order of the request. -/
  | notRequested
  /-- The response does not have one group of cells for each transaction. -/
  | groupCount (transactions groups : Nat)
  /-- The caller gave the blob count of another number of transactions than the response has. -/
  | blobCount (transactions counts : Nat)
  /-- A group does not have one cell for each blob and each marked index. -/
  | cellCount (index expected actual : Nat)
  /-- A cell is not 2048 bytes. -/
  | cellSize (size : Nat)
  /-- The response is not Cells with the request ID of the request. -/
  | notAnswer
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 401, above every code of the other eth errors.

A new constructor takes a new code, so that each code keeps its meaning. -/
def CellsError.code : CellsError → UInt32
  | .maskNotSubset => 401
  | .notRequested => 402
  | .groupCount .. => 403
  | .cellCount .. => 404
  | .cellSize _ => 405
  | .notAnswer => 406
  | .blobCount .. => 407

/--
Whether a response of cells answers a request of the hashes `requested`.

The request has the bitmap `requestMask`.

`blobs` gives the number of blobs of each transaction of the response.

- The response bitmap is a subset of the request bitmap.
- The transactions are requested ones, in order; the peer may leave some out.
- Each transaction has one group of cells, with one cell for each blob and each marked index.
- Each cell has 2048 bytes.
-/
def checkCells (requested : List Hash32) (requestMask : CellMask) (blobs : List Nat)
    (hashes : List Hash32) (groups : List (List ByteArray)) (mask : CellMask) :
    Except CellsError Unit := do
  if !mask.subset requestMask then throw .maskNotSubset
  if !hashes.isSublist requested then throw .notRequested
  if groups.length ≠ hashes.length then throw (.groupCount hashes.length groups.length)
  if blobs.length ≠ hashes.length then throw (.blobCount hashes.length blobs.length)
  for (i, group, n) in (List.range groups.length).zip (groups.zip blobs) do
    if group.length ≠ n * mask.count then throw (.cellCount i (n * mask.count) group.length)
    for cell in group do
      if cell.size ≠ BYTES_PER_CELL then throw (.cellSize cell.size)

end EthLib.Execution.Network
