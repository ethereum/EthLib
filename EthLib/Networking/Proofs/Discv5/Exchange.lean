module

public import EthLib.Networking.Discv5.Exchange
public import EthLib.Networking.Proofs.Discv5.Identity

/-!
# `Networking.Proofs.Discv5.Exchange`

Properties of the rules that relate a discv5 answer to its request.
-/

@[expose] public section

namespace EthLib.Networking.Discv5

open EthLib.Serialization.Rlp
open EthLib.Networking.Proofs.Discv5.Identity

/-- With distance 0 alone, each record of a matching answer has the node ID of the recipient. -/
theorem nodesMatch_zero {recipient : NodeId} {records : List Item}
    (h : nodesMatch recipient [0] records = true) {item : Item} (member : item ∈ records) :
    recordNodeId item = some recipient := by
  unfold nodesMatch at h
  have hitem := List.all_eq_true.mp h item member
  split at hitem
  · rename_i id hid
    -- Only equal IDs are at logarithmic distance 0.
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hitem
    rw [hid, logDistance_eq_zero_iff.mp hitem]
  · cases hitem

/-- Two parts of a NODES answer match exactly when each part matches.

So an answer is checked piece by piece. -/
theorem nodesMatch_append (recipient : NodeId) (distances : List Nat) (first second : List Item) :
    nodesMatch recipient distances (first ++ second) =
      (nodesMatch recipient distances first && nodesMatch recipient distances second) := by
  simp [nodesMatch, List.all_append]

/-- Every message that a node keeps answers its request. -/
theorem answersRequest_of_mem_acceptNodes {limit : Nat} {request m : Message}
    {received : List Message} (member : m ∈ acceptNodes limit request received) :
    answersRequest request m = true := by
  unfold acceptNodes at member
  dsimp only at member
  cases h : received.filter (answersRequest request) with
  | nil => simp [h] at member
  | cons first rest =>
    rw [h] at member
    -- The kept messages are a prefix of the answers, which the filter keeps.
    have kept : m ∈ received.filter (answersRequest request) := by
      rw [h]
      cases first <;> simp only at member <;>
        first | cases member | exact List.mem_of_mem_take member
    exact (List.mem_filter.mp kept).2

/-- A node keeps at most as many NODES answers as its limit. -/
theorem length_acceptNodes_le (limit : Nat) (request : Message) (received : List Message) :
    (acceptNodes limit request received).length ≤ limit := by
  unfold acceptNodes
  dsimp only
  split
  · simp only [List.length_take]
    omega
  · simp

/-- A node keeps at most `total` NODES answers, as the first answer gives it. -/
theorem length_acceptNodes_le_total {limit : Nat} {request : Message} {received : List Message}
    {id : ByteArray} {total : UInt64} {records : List Item}
    (first : (received.filter (answersRequest request)).head? = some (.nodes id total records)) :
    (acceptNodes limit request received).length ≤ total.toNat := by
  unfold acceptNodes
  dsimp only
  cases h : received.filter (answersRequest request) with
  | nil => simp [h] at first
  | cons m rest =>
    simp only [h, List.head?_cons, Option.some.injEq] at first
    subst first
    simp only [List.length_take]
    omega

/-- A TALKREQ for an unknown protocol gets a TALKRESP with its request ID and an empty response.
-/
theorem talkResponse_unknown {handlers : ByteArray → Option (ByteArray → ByteArray)}
    {id protocol request : ByteArray} (unknown : handlers protocol = none) :
    talkResponse handlers (.talkreq id protocol request) = some (.talkresp id .empty) := by
  simp [talkResponse, unknown]

/-- The TALKRESP that a node sends answers the TALKREQ. -/
theorem answersRequest_talkResponse {handlers : ByteArray → Option (ByteArray → ByteArray)}
    {request answer : Message} (h : talkResponse handlers request = some answer) :
    answersRequest request answer = true := by
  cases request <;> simp only [talkResponse, reduceCtorEq] at h
  cases h
  simp [answersRequest, Message.answerType, Message.type, Message.requestId]

end EthLib.Networking.Discv5
