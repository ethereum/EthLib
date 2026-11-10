module

public import EthLib.Consensus.ForkChoice.Head
import EthLib.Base.Proofs.MapM
import Std.Data.HashMap.Lemmas

/-!
# Proofs: the votes of a node from a tally

The votes of a node are read from a tally that groups the votes by the node each one supports.

The count over the tally checks each group once, in the order of its first vote.

It agrees with a count over the validators in order.

That count adds the balance of each validator whose supported node descends from the node.

The results agree in every case: the same sum, the same overflow and the same first error.

So a computed score is a sum over the counted validators, one balance for each vote that counts.

The node of each such vote is then found, and the check that it descends passes.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

namespace Store

variable (store : Store preset fork)

/-- One when the check that a node descends from another passes and holds, and zero otherwise. -/
private def weightOf (supported node : ForkChoiceNode) : Nat :=
  match store.isAncestor supported node with
  | .ok true => 1
  | _ => 0

/-- The count over groups that all pass their check adds each sum whose node descends. -/
private theorem foldlM_groups_ok (node : ForkChoiceNode) (sums : Std.HashMap ForkChoiceNode Nat)
    {nodes : List ForkChoiceNode}
    (pass : ∀ supported ∈ nodes, ∃ descends, store.isAncestor supported node = .ok descends)
    (start : Nat) :
    (nodes.map fun supported => (supported, sums.getD supported 0)).foldlM (init := start)
        (fun (total : Nat) (supported, weight) => do
          if ← store.isAncestor supported node then return total + weight
          return total : Nat → ForkChoiceNode × Nat → Except ForkChoiceError Nat) =
      .ok (start + (nodes.map fun supported =>
        sums.getD supported 0 * store.weightOf supported node).sum) := by
  induction nodes generalizing start with
  | nil => simp [pure, Except.pure]
  | cons head tail ih =>
    obtain ⟨descends, passes⟩ := pass head List.mem_cons_self
    rw [List.map_cons, List.foldlM_cons]
    simp only [ih (fun other mem => pass other (List.mem_cons_of_mem _ mem))]
    cases descends <;> simp [weightOf, passes, bind, Except.bind, pure, Except.pure] <;> omega

/-- When every group passes its check, the count gives the error of the tally if any.

Otherwise it gives the sums whose node descends, or an overflow. -/
private theorem scoreFromTally_of_ok {nodes : List ForkChoiceNode}
    {sums : Std.HashMap ForkChoiceNode Nat} {failure : Option ForkChoiceError}
    {node : ForkChoiceNode}
    (pass : ∀ supported ∈ nodes, ∃ descends, store.isAncestor supported node = .ok descends) :
    store.scoreFromTally ⟨nodes.map fun supported => (supported, sums.getD supported 0), failure⟩
        node =
      match failure with
      | some error => .error error
      | none =>
        let total := (nodes.map fun supported =>
          sums.getD supported 0 * store.weightOf supported node).sum
        if 2 ^ 64 ≤ total then .error (.arith .overflow) else .ok total.toUInt64 := by
  unfold scoreFromTally
  rw [foldlM_groups_ok store node sums pass 0, Nat.zero_add]
  cases failure <;> simp [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]

/-- When the groups before it pass, the count fails as the check of the first group that fails. -/
private theorem scoreFromTally_of_error {before after : List ForkChoiceNode}
    {supported : ForkChoiceNode} {sums : Std.HashMap ForkChoiceNode Nat}
    {failure : Option ForkChoiceError} {node : ForkChoiceNode} {error : ForkChoiceError}
    (pass : ∀ earlier ∈ before, ∃ descends, store.isAncestor earlier node = .ok descends)
    (fails : store.isAncestor supported node = .error error) :
    store.scoreFromTally ⟨(before ++ supported :: after).map fun supported =>
      (supported, sums.getD supported 0), failure⟩ node = .error error := by
  unfold scoreFromTally
  rw [List.map_append, List.foldlM_append, foldlM_groups_ok store node sums pass 0]
  simp [List.foldlM_cons, fails, bind, Except.bind]

/-- The grouped nodes start with the given nodes, in reverse. -/
private theorem groupVotes_prefix (votes : List (ValidatorIndex × Gwei))
    (nodes : List ForkChoiceNode) (sums : Std.HashMap ForkChoiceNode Nat) :
    ∃ rest, (store.groupVotes votes nodes sums).1 = nodes.reverse ++ rest := by
  induction votes generalizing nodes sums with
  | nil => exact ⟨[], by simp [groupVotes]⟩
  | cons vote rest ih =>
    obtain ⟨index, balance⟩ := vote
    rw [groupVotes]
    split
    · exact ih nodes sums
    · split
      · exact ih nodes sums
      · split
        · exact ⟨[], by simp⟩
        · rename_i supported _
          split
          · exact ih nodes _
          · obtain ⟨more, eq⟩ := ih (supported :: nodes) (sums.insert supported
              (sums.getD supported 0 + balance.toNat))
            exact ⟨supported :: more, by simp [eq]⟩

omit store in
/-- A balance added at one node changes a weighted total over a list without repeats.

The total grows by the balance times the weight of that node, when the node is in the list. -/
private theorem sum_insert (sums : Std.HashMap ForkChoiceNode Nat) (weight : ForkChoiceNode → Nat)
    (supported : ForkChoiceNode) (balance : Nat) {nodes : List ForkChoiceNode}
    (distinct : nodes.Nodup) :
    (nodes.map fun other =>
        (sums.insert supported (sums.getD supported 0 + balance)).getD other 0 * weight other).sum =
      (nodes.map fun other => sums.getD other 0 * weight other).sum +
        if supported ∈ nodes then balance * weight supported else 0 := by
  induction nodes with
  | nil => simp
  | cons first rest ih =>
    rw [List.nodup_cons] at distinct
    rw [List.map_cons, List.sum_cons, ih distinct.2, List.map_cons, List.sum_cons]
    simp only [Std.HashMap.getD_insert, List.mem_cons, beq_iff_eq]
    by_cases same : supported = first
    · subst same
      simp [distinct.1, Nat.add_mul]
      omega
    · by_cases mem : supported ∈ rest <;> simp [same, mem] <;> omega

/-- The count over the remaining validators agrees with the tally built from the given nodes.

The given nodes pass their check, have no repeats, and are the nodes with a sum.

The count so far is the total of the sums whose node descends. -/
private theorem fold_eq_scoreFromTally (node : ForkChoiceNode)
    (votes : List (ValidatorIndex × Gwei)) (seen : List ForkChoiceNode)
    (sums : Std.HashMap ForkChoiceNode Nat) (start : Nat)
    (pass : ∀ supported ∈ seen, ∃ descends, store.isAncestor supported node = .ok descends)
    (weighted : start = (seen.map fun supported =>
      sums.getD supported 0 * store.weightOf supported node).sum)
    (keys : ∀ supported, sums.contains supported = true ↔ supported ∈ seen)
    (distinct : seen.Nodup) {nodes : List ForkChoiceNode}
    {grouped : Std.HashMap ForkChoiceNode Nat} {failure : Option ForkChoiceError}
    (group : store.groupVotes votes seen sums = (nodes, grouped, failure)) :
    (do
      let total ← votes.foldlM (init := start)
          fun (total : Nat) (index, balance) =>
            match store.latestMessages[index]? with
            | none => pure total
            | some message => do
              if store.equivocatingIndices.contains index then return total
              if ← store.isAncestor (← store.getSupportedNode message) node then
                return total + balance.toNat
              return total
      if 2 ^ 64 ≤ total then throw (.arith .overflow)
      return total.toUInt64 : Except ForkChoiceError Gwei) =
    store.scoreFromTally ⟨nodes.map fun supported => (supported, grouped.getD supported 0),
      failure⟩ node := by
  induction votes generalizing seen sums start with
  | nil =>
    simp only [groupVotes, Prod.mk.injEq] at group
    obtain ⟨rfl, rfl, rfl⟩ := group
    rw [scoreFromTally_of_ok store fun supported mem => pass supported (List.mem_reverse.mp mem)]
    simp only [List.map_reverse, List.sum_reverse, ← weighted]
    simp [pure, Except.pure, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  | cons vote rest ih =>
    obtain ⟨index, balance⟩ := vote
    rw [groupVotes] at group
    rw [List.foldlM_cons, bind_assoc]
    cases latest : store.latestMessages[index]? with
    | none =>
      simp only [latest] at group
      simpa only [latest, pure_bind] using ih seen sums start pass weighted keys distinct group
    | some message =>
      simp only [latest] at group
      by_cases equivocating : store.equivocatingIndices.contains index
      · simp only [equivocating, ↓reduceIte] at group
        simpa only [latest, equivocating, ↓reduceIte, pure_bind] using
          ih seen sums start pass weighted keys distinct group
      simp only [equivocating, ↓reduceIte, Bool.false_eq_true] at group
      simp only [latest, equivocating, ↓reduceIte, Bool.false_eq_true]
      have seenPass : ∀ supported ∈ seen.reverse, ∃ descends,
          store.isAncestor supported node = .ok descends := fun supported mem =>
        pass supported (List.mem_reverse.mp mem)
      cases supportedNode : store.getSupportedNode message with
      | error error =>
        simp only [supportedNode, Prod.mk.injEq] at group
        obtain ⟨rfl, rfl, rfl⟩ := group
        rw [scoreFromTally_of_ok store seenPass]
        rfl
      | ok supported =>
        simp only [supportedNode] at group
        cases check : store.isAncestor supported node with
        | error error =>
          -- A node seen before passes its check, so the failing node is new.
          have fresh : supported ∉ seen := fun mem => by
            obtain ⟨_, passes⟩ := pass supported mem
            rw [passes] at check
            cases check
          have absent : sums.contains supported = false := by
            cases contained : sums.contains supported
            · rfl
            · exact absurd ((keys supported).mp contained) fresh
          simp only [absent, Bool.false_eq_true, ↓reduceIte] at group
          obtain ⟨more, prefixEq⟩ := groupVotes_prefix store rest (supported :: seen)
            (sums.insert supported (sums.getD supported 0 + balance.toNat))
          rw [group] at prefixEq
          simp only at prefixEq
          rw [prefixEq, List.reverse_cons, List.append_assoc, List.singleton_append,
            scoreFromTally_of_error store seenPass check]
          simp only [check, bind, Except.bind]
        | ok descends =>
          have counted : store.weightOf supported node = if descends then 1 else 0 := by
            cases descends <;> simp [weightOf, check]
          have next := ih (if sums.contains supported then seen else supported :: seen)
            (sums.insert supported (sums.getD supported 0 + balance.toNat))
            (if descends then start + balance.toNat else start) ?pass ?weighted ?keys ?distinct
            group
          · cases descends <;> simpa only [check, Except.bind, bind, ↓reduceIte,
              Bool.false_eq_true, pure, Except.pure] using next
          case pass =>
            intro other mem
            by_cases contained : sums.contains supported
            · simp only [contained, ↓reduceIte] at mem
              exact pass other mem
            · simp only [contained, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at mem
              rcases mem with rfl | mem
              · exact ⟨descends, check⟩
              · exact pass other mem
          case weighted =>
            by_cases contained : sums.contains supported
            · have mem := (keys supported).mp contained
              simp only [contained, ↓reduceIte]
              rw [sum_insert _ _ _ _ distinct, ← weighted, counted]
              cases descends <;> simp [mem]
            · have fresh : supported ∉ seen := fun mem => contained ((keys supported).mpr mem)
              have zero : sums.getD supported 0 = 0 :=
                Std.HashMap.getD_eq_fallback_of_contains_eq_false (Bool.eq_false_iff.mpr contained)
              simp only [contained, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
              rw [sum_insert _ _ _ _ distinct, ← weighted, counted, Std.HashMap.getD_insert_self,
                zero]
              cases descends <;> simp [fresh] <;> omega
          case keys =>
            intro other
            rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, keys]
            by_cases contained : sums.contains supported
            · simp only [contained, ↓reduceIte]
              have mem := (keys supported).mp contained
              constructor
              · rintro (rfl | mem')
                · exact mem
                · exact mem'
              · exact Or.inr
            · simp only [contained, Bool.false_eq_true, ↓reduceIte, List.mem_cons, eq_comm]
          case distinct =>
            by_cases contained : sums.contains supported
            · simp only [contained, ↓reduceIte]
              exact distinct
            · simp only [contained, Bool.false_eq_true, ↓reduceIte, List.nodup_cons]
              exact ⟨fun mem => contained ((keys supported).mpr mem), distinct⟩

/-- The votes of a node from the tally are the count over the validators, one vote at a time.

The count reads the validators in order, and checks for each counted vote that its node descends.

It returns the first error, from finding the node of a vote or from checking that it descends.

It returns an overflow when the sum leaves 64 bits. -/
theorem getAttestationScore_eq_fold (node : ForkChoiceNode) (state : BeaconState preset fork) :
    store.getAttestationScore node state = (do
      let total ← (unslashedActiveBalances state).foldlM (init := 0)
          fun (total : Nat) (index, balance) =>
            match store.latestMessages[index]? with
            | none => pure total
            | some message => do
              if store.equivocatingIndices.contains index then return total
              if ← store.isAncestor (← store.getSupportedNode message) node then
                return total + balance.toNat
              return total
      if 2 ^ 64 ≤ total then throw (.arith .overflow)
      return total.toUInt64 : Except ForkChoiceError Gwei) := by
  rw [getAttestationScore, tallyVotes]
  rcases group : store.groupVotes (unslashedActiveBalances state) [] ∅ with
    ⟨nodes, grouped, failure⟩
  exact (fold_eq_scoreFromTally store node _ [] ∅ 0 (by simp) (by simp) (by simp) List.nodup_nil
    group).symm

/-- Whether the latest vote of a validator counts for a node.

The validator has a message and does not equivocate.

The node of its vote is found, and the check that it descends from the node passes and holds. -/
def voteCountsFor (node : ForkChoiceNode) (index : ValidatorIndex) : Bool :=
  match store.latestMessages[index]? with
  | none => false
  | some message =>
    if store.equivocatingIndices.contains index then false
    else
      match store.getSupportedNode message >>= (store.isAncestor · node) with
      | .ok descends => descends
      | .error _ => false

/-- The vote of a validator with a message that does not equivocate counts as its check says. -/
theorem voteCountsFor_of_check {node : ForkChoiceNode} {index : ValidatorIndex}
    {message : LatestMessage fork} {descends : Bool}
    (latest : store.latestMessages[index]? = some message)
    (honest : store.equivocatingIndices.contains index = false)
    (checked : (store.getSupportedNode message >>= (store.isAncestor · node)) = .ok descends) :
    store.voteCountsFor node index = descends := by
  simp only [voteCountsFor, latest, honest, Bool.false_eq_true, ↓reduceIte, checked]

/-- A computed score of a node found the node of each vote that it reads.

Those are the votes of the validators active and not slashed in the given state.

The check that the node of each such vote descends from the node passes too.

A validator without a message, or an equivocator, has no such vote. -/
theorem getAttestationScore_checked {node : ForkChoiceNode} {state : BeaconState preset fork}
    {score : Gwei} (computed : store.getAttestationScore node state = .ok score) :
    ∀ entry ∈ unslashedActiveBalances state, ∀ message,
      store.latestMessages[entry.1]? = some message →
      store.equivocatingIndices.contains entry.1 = false →
      ∃ descends,
        (store.getSupportedNode message >>= (store.isAncestor · node)) = .ok descends := by
  rw [getAttestationScore_eq_fold, bind_ok_iff] at computed
  obtain ⟨total, fold, -⟩ := computed
  refine foldlM_forall_of_ok (P := fun (entry : ValidatorIndex × Gwei) =>
      ∀ message, store.latestMessages[entry.1]? = some message →
        store.equivocatingIndices.contains entry.1 = false →
        ∃ descends, (store.getSupportedNode message >>= (store.isAncestor · node)) = .ok descends)
    ?_ _ _ _ fold
  rintro acc ⟨index, balance⟩ result step message latest honest
  simp only [latest, honest, Bool.false_eq_true, ↓reduceIte] at step
  cases supported : store.getSupportedNode message with
  | error e => simp [supported, bind, Except.bind] at step
  | ok supported' =>
    cases check : store.isAncestor supported' node with
    | error e => simp [supported, check, bind, Except.bind] at step
    | ok descends => exact ⟨descends, by simp [check, bind, Except.bind]⟩

/-- A computed score of a node is the sum of the balances of the validators whose vote counts.

The validators are those active and not slashed in the given state. -/
theorem getAttestationScore_toNat_eq_sum {node : ForkChoiceNode}
    {state : BeaconState preset fork} {score : Gwei}
    (computed : store.getAttestationScore node state = .ok score) :
    score.toNat = ((unslashedActiveBalances state).map fun entry =>
      if store.voteCountsFor node entry.1 then entry.2.toNat else 0).sum := by
  have checked := store.getAttestationScore_checked computed
  rw [getAttestationScore_eq_fold, bind_ok_iff] at computed
  obtain ⟨total, fold, bound⟩ := computed
  -- Each step adds the balance exactly when the vote counts.
  rw [foldlM_eq_ok_foldl (L := unslashedActiveBalances state)
    (step := fun (total : Nat) (entry : ValidatorIndex × Gwei) =>
      total + if store.voteCountsFor node entry.1 then entry.2.toNat else 0) ?steps 0,
    Except.ok.injEq] at fold
  case steps =>
    rintro acc ⟨index, balance⟩ mem
    cases latest : store.latestMessages[index]? with
    | none => simp [latest, voteCountsFor, pure, Except.pure]
    | some message =>
      by_cases equivocating : store.equivocatingIndices.contains index
      · have member : index ∈ store.equivocatingIndices := by simpa using equivocating
        simp [latest, voteCountsFor, member, pure, Except.pure]
      have honest := Bool.eq_false_iff.mpr equivocating
      obtain ⟨descends, found⟩ := checked _ mem message latest honest
      rw [voteCountsFor_of_check store latest honest found]
      have absent : index ∉ store.equivocatingIndices := by simpa using equivocating
      cases supported : store.getSupportedNode message with
      | error e => simp [supported, bind, Except.bind] at found
      | ok supported' =>
        simp only [supported, bind, Except.bind] at found
        cases descends <;>
          simp [latest, absent, supported, found, bind, Except.bind, pure, Except.pure]
  have sum : ∀ (entries : List (ValidatorIndex × Gwei)) (start : Nat),
      entries.foldl (fun total entry =>
          total + if store.voteCountsFor node entry.1 then entry.2.toNat else 0) start =
        start + (entries.map fun entry =>
          if store.voteCountsFor node entry.1 then entry.2.toNat else 0).sum := by
    intro entries
    induction entries with
    | nil => simp
    | cons entry rest ih =>
      intro start
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      omega
  rw [sum, Nat.zero_add] at fold
  subst fold
  by_cases big : 2 ^ 64 ≤ ((unslashedActiveBalances state).map fun entry =>
      if store.voteCountsFor node entry.1 then entry.2.toNat else 0).sum
  · have big' : 18446744073709551616 ≤ ((unslashedActiveBalances state).map
        fun entry => if store.voteCountsFor node entry.1 then entry.2.toNat else 0).sum := big
    simp [big', throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at bound
  simp only [big, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at bound
  subst bound
  exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)

end Store

end EthLib.Consensus
