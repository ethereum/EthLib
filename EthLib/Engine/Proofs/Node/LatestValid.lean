module

public import EthLib.Engine.Proofs.Node.Grounded
import all EthLib.Engine.Proofs.Node.Grounded

/-!
# Proofs: the latest valid hash of an invalid block on an execution node

An update to a block answered `INVALID` gives the latest valid hash of that first answer.

Sources, at commit `1ca0818` of execution-apis:

- steps 2 to 4 of the [payload validation][validation] of Paris
- the method [`engine_forkchoiceUpdatedV1`][update] of Paris

[validation]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#payload-validation
[update]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/paris.md#engine_forkchoiceupdatedv1
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (Block RecentBlock)
open EthLib.Execution.Transactions (Transaction)

namespace Node

variable {node : Node} {version : Nat} {params : Lean.Json}

/-- Each block of a path of invalid blocks is known as invalid. -/
private theorem InvalidDescent.mem_invalid {l : List Hash32} {v : Hash32}
    (h : node.InvalidDescent l v) :
    ∀ x ∈ l, ∃ c, node.blocks.lookup x = some c ∧ c.validity = .invalid := by
  induction l with
  | nil => simp
  | cons y rest ih =>
    obtain ⟨b, hb, hi, -, hr⟩ := h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, hb, hi⟩
    · exact ih hr x hx

/-- The end of a path of invalid blocks is known as valid. -/
private theorem InvalidDescent.end_valid {l : List Hash32} {v : Hash32}
    (h : node.InvalidDescent l v) : ∃ post, node.validState v = some post := by
  induction l with
  | nil => exact h
  | cons y rest ih =>
    obtain ⟨b, -, -, -, hr⟩ := h
    exact ih hr

/-- The walk from the start of a path of invalid blocks runs along the path, then from its end. -/
private theorem InvalidDescent.ancestors {l : List Hash32} {v : Hash32}
    (h : node.InvalidDescent l v) :
    ∀ n, l.length ≤ n →
      Engine.ancestors node.tree n (l.headD v) =
        l ++ Engine.ancestors node.tree (n - l.length) v := by
  induction l with
  | nil => intro n _; simp
  | cons y rest ih =>
    obtain ⟨b, hb, -, hp, hr⟩ := h
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    have ht : node.tree.lookup y = some b.toKnownPayload := by
      rw [tree_lookup, hb]
      rfl
    have hpar : b.toKnownPayload.parentHash = rest.headD v := hp
    simp only [List.headD_cons, Engine.ancestors, ht, hpar, List.length_cons, List.cons_append]
    rw [ih hr m (by simp at hn; omega)]
    congr 2
    simp

/-- A list of pairs that looks up a key holds that key among its keys. -/
private theorem mem_keys_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α}
    {b : β} (h : l.lookup a = some b) : a ∈ l.map Prod.fst := by
  induction l with
  | nil => simp at h
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    by_cases hk : a = k
    · simp [hk]
    · have hne : (a == k) = false := by simp [hk]
      simp only [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- A path of invalid blocks with no repeat, with its end, fits within the length of the tree. -/
private theorem InvalidDescent.length_le {l : List Hash32} {v : Hash32}
    (h : node.InvalidDescent l v) (hn : (l ++ [v]).Nodup) : l.length + 1 ≤ node.tree.length := by
  have hsub : l ++ [v] ⊆ node.blocks.map Prod.fst := by
    intro x hx
    obtain ⟨c, hc, -⟩ := InvalidDescent.not_accepted h x hx
    exact mem_keys_of_lookup hc
  have := hn.length_le_of_subset hsub
  simpa [tree] using this

/-- A path of invalid blocks with no repeat has its end as the latest valid block of its start. -/
private theorem InvalidDescent.latestValid {l : List Hash32} {v : Hash32}
    (h : node.InvalidDescent l v) (hn : (l ++ [v]).Nodup) :
    Engine.latestValid node.tree (l.headD v) = some v := by
  have hlen := h.length_le hn
  obtain ⟨m, hm⟩ : ∃ m, node.tree.length - l.length = m + 1 :=
    ⟨node.tree.length - l.length - 1, by omega⟩
  obtain ⟨c, hc, -⟩ := InvalidDescent.not_accepted h v (by simp)
  obtain ⟨post, hpost⟩ := h.end_valid
  obtain ⟨c', hc', hv⟩ := validState_eq_some_iff.mp hpost
  rw [hc] at hc'
  cases hc'
  have ht : node.tree.lookup v = some c.toKnownPayload := by
    rw [tree_lookup, hc]
    rfl
  -- The blocks of the path are not valid, and the end is.
  have hNone : l.find? (fun x => (node.tree.lookup x).any (·.valid)) = none := by
    rw [List.find?_eq_none]
    intro x hx
    obtain ⟨d, hd, hi⟩ := h.mem_invalid x hx
    simp [tree_lookup, hd, KnownBlock.toKnownPayload, hi, Validity.isValid]
  unfold Engine.latestValid chainOf
  rw [h.ancestors node.tree.length (by omega), hm, List.find?_append, hNone, Option.none_or,
    Engine.ancestors, ht]
  simp [ht, KnownBlock.toKnownPayload, hv, Validity.isValid]

/-- On a grounded node, the first totals on the walk from a valid block with none are terminal. -/
private theorem Grounded.findSome?_ancestors (hg : node.Grounded) :
    ∀ m x c, node.blocks.lookup x = some c → c.validity.isValid = true →
      c.powTotalDifficulty = none → ∀ t pt, (Engine.ancestors node.tree m x).findSome?
        (fun h => (node.tree.lookup h).bind (·.powTotalDifficulty)) = some (t, pt) →
        isTerminalPowBlock node.transition t pt = true := by
  intro m
  induction m with
  | zero =>
    intro x c _ _ _ t pt h
    simp [Engine.ancestors] at h
  | succ m ih =>
    intro x c hc hv hp t pt h
    have ht : node.tree.lookup x = some c.toKnownPayload := by
      rw [tree_lookup, hc]
      rfl
    have hx : c.toKnownPayload.powTotalDifficulty = none := hp
    simp only [Engine.ancestors, ht, List.findSome?_cons, Option.bind_some, hx] at h
    rcases hg.terminal x c hc hv hp with ⟨p, hpl, hpv, hterm⟩ | hNone
    · cases hpp : p.powTotalDifficulty with
      | none => exact ih _ p hpl hpv hpp t pt h
      | some tot =>
        -- The parent has totals, so the walk stops at it.
        cases m with
        | zero => simp [Engine.ancestors] at h
        | succ m =>
          have htp : node.tree.lookup c.block.header.parentHash = some p.toKnownPayload := by
            rw [tree_lookup, hpl]
            rfl
          simp [KnownBlock.toKnownPayload, Engine.ancestors, htp, hpp] at h
          subst h
          exact hterm _ _ hpp
    · -- No block has totals, so the walk finds none.
      have hAll : ∀ y, (node.tree.lookup y).bind (·.powTotalDifficulty) = none := by
        intro y
        rw [tree_lookup]
        cases hy : node.blocks.lookup y with
        | none => rfl
        | some d => simp [KnownBlock.toKnownPayload, hNone y d hy]
      simp only [hAll] at h
      rw [List.findSome?_eq_none_iff.mpr (fun _ _ => rfl)] at h
      cases h

/-- On a grounded node, the chain of a known invalid block passes the terminal check.

Otherwise its latest valid hash is zero. -/
private theorem Grounded.terminal_or_zero {hash : Hash32} {b : KnownBlock} (hg : node.Grounded)
    (hb : node.blocks.lookup hash = some b) (hInvalid : b.validity = .invalid) :
    chainPassesTerminalCheck node.transition node.tree hash = true ∨
      latestValidHash node.tree hash = some ZERO_HASH := by
  obtain ⟨rest, v, hd, hn⟩ := hg.descent hash b hb hInvalid
  obtain ⟨c, hc, -⟩ := InvalidDescent.not_accepted hd v (by simp)
  obtain ⟨post, hpost⟩ := hd.end_valid
  obtain ⟨c', hc', hv⟩ := validState_eq_some_iff.mp hpost
  rw [hc] at hc'
  cases hc'
  have hcv : c.validity.isValid = true := by simp [hv, Validity.isValid]
  have ht : node.tree.lookup v = some c.toKnownPayload := by
    rw [tree_lookup, hc]
    rfl
  have hlv : latestValid node.tree hash = some v := hd.latestValid hn
  cases hpow : c.powTotalDifficulty with
  | some tot =>
    -- The latest valid block is of proof of work, so the hash is zero.
    exact .inr (latestValidHash_of_isPow hlv ht
      (by simp [KnownPayload.isPow, KnownBlock.toKnownPayload, hpow]))
  | none =>
    -- The blocks of the path have no totals, so the walk reads those from the end on.
    have hlen := hd.length_le hn
    have hNone : (hash :: rest).findSome?
        (fun h => (node.tree.lookup h).bind (·.powTotalDifficulty)) = none := by
      rw [List.findSome?_eq_none_iff]
      intro x hx
      obtain ⟨d, hd', hi⟩ := hd.mem_invalid x hx
      have hdp : d.powTotalDifficulty = none := by
        cases hq : d.powTotalDifficulty with
        | none => rfl
        | some _ =>
          have := hg.valid_of_pow x d hd' (by simp [hq])
          simp [hi, Validity.isValid] at this
      simp [tree_lookup, hd', KnownBlock.toKnownPayload, hdp]
    left
    unfold chainPassesTerminalCheck latestPow chainOf
    rw [show hash = (hash :: rest).headD v from rfl, hd.ancestors node.tree.length (by omega),
      List.findSome?_append, hNone, Option.none_or]
    split
    · rename_i t pt heq
      exact hg.findSome?_ancestors _ v c hc hcv hpow t pt heq
    · rfl

/-- Validation of an update to a known invalid head leaves the node as it was. -/
private theorem validateHead_of_invalid_head {state : ForkchoiceState}
    {attributes : Option Lean.Json} {b : KnownBlock}
    (hParams : forkchoiceUpdatedParams version params = .ok (state, attributes))
    (hb : node.blocks.lookup state.headBlockHash = some b) (hInvalid : b.validity = .invalid) :
    node.validateHead version params = node := by
  obtain ⟨blk, pow, v⟩ := b
  simp only at hInvalid
  subst hInvalid
  simp only [validateHead, hParams]
  generalize node.blocks.length = n
  cases n <;> simp [validateChain, hb]

/-- An invalid answer on a chain ending at the parent names the parent, or zero before Paris. -/
private theorem latestValidHash_of_newPayloadOnChain {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : Execution.Blocks.BlockChain} {checked : CheckedBlock version}
    {parent : RecentBlock} {status : PayloadStatus} {reason : Option PayloadError}
    {next : Option (RecentBlock × Execution.State.State)}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (hParent : chain.recent.getLast? = some parent)
    (h : newPayloadOnChain transition totalDifficulty chain version params =
      .ok (status, reason, next))
    (hs : status.status = .invalid) :
    status.latestValidHash =
      some (if parent.fork < .paris then 0 else checked.block.header.parentHash) := by
  unfold newPayloadOnChain at h
  simp only [hCheck, hParent, bind, Except.bind] at h
  repeat' split at h
  all_goals simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, -, -⟩ := h
  all_goals first
    | (simp at hs; done)
    | (rename_i hlt; exact congrArg some (ite_eq_left hlt).symm)
    | (rename_i hlt; exact congrArg some (ite_eq_right hlt).symm)
    | skip
  -- A parent that fails the terminal check is from before Paris.
  rename_i hT
  have hlt : parent.fork < .paris := by
    simp only [passesTerminalCheck, Bool.or_eq_true, decide_eq_true_eq, not_or] at hT
    exact Nat.lt_of_not_le hT.1
  simp only [hlt, ↓reduceIte]

/-- A new invalid block on a known valid parent has that parent as latest valid hash.

The hash is zero when the parent is from before Paris. -/
private theorem Grounded.latestValidHash_record_valid {hash : Hash32}
    {blk : (fork : Fork) × Block fork Transaction} {p : KnownBlock}
    {post : Execution.State.State} (hg : node.Grounded)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (hp : node.blocks.lookup blk.2.header.parentHash = some p) (hpv : p.validity = .valid post) :
    latestValidHash (node.record hash ⟨blk, none, .invalid⟩).tree hash =
      some (if p.block.fork < .paris then 0 else blk.2.header.parentHash) := by
  -- The parent is valid, so it is not the new block.
  have hne : blk.2.header.parentHash ≠ hash := by
    intro h
    rw [h] at hp
    have := hFresh p hp
    simp [hpv, Validity.isAccepted] at this
  have hp' : (node.record hash ⟨blk, none, .invalid⟩).blocks.lookup blk.2.header.parentHash =
      some p := by
    rw [record_lookup_of_ne _ _ hne]
    exact hp
  have hd : (node.record hash ⟨blk, none, .invalid⟩).InvalidDescent [hash]
      blk.2.header.parentHash :=
    ⟨⟨blk, none, .invalid⟩, by simp [Node.record], rfl, rfl, post,
      validState_eq_some_iff.mpr ⟨p, hp', hpv⟩⟩
  have hn : ([hash] ++ [blk.2.header.parentHash]).Nodup := by
    simp [Ne.symm hne]
  have hl : latestValid (node.record hash ⟨blk, none, .invalid⟩).tree hash =
      some blk.2.header.parentHash := hd.latestValid hn
  have hpow := hg.pow_iff _ p hp
  unfold Engine.latestValidHash
  rw [hl]
  by_cases hlt : p.block.fork < .paris
  · simp [tree_lookup, hp', KnownPayload.isPow, KnownBlock.toKnownPayload, hpow.mpr hlt, hlt]
    ext i h
    simp [ZERO_HASH]
  · have hNone : p.powTotalDifficulty.isSome = false := by
      cases hq : p.powTotalDifficulty.isSome
      · rfl
      · exact absurd (hpow.mp hq) hlt
    simp [tree_lookup, hp', KnownPayload.isPow, KnownBlock.toKnownPayload, hNone, hlt]

/-- A new invalid block on a known invalid parent has the latest valid hash of that parent. -/
private theorem Grounded.latestValidHash_record_invalid {hash : Hash32}
    {blk : (fork : Fork) × Block fork Transaction} {p : KnownBlock} (hg : node.Grounded)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (hp : node.blocks.lookup blk.2.header.parentHash = some p) (hpi : p.validity = .invalid) :
    latestValidHash (node.record hash ⟨blk, none, .invalid⟩).tree hash =
      latestValidHash node.tree blk.2.header.parentHash := by
  obtain ⟨rest, v, hd, hn⟩ := hg.descent _ p hp hpi
  -- A block that is not accepted is not the new block, so it keeps its entry.
  have hne : ∀ x c, node.blocks.lookup x = some c → c.validity.isAccepted = false → x ≠ hash := by
    rintro x c hc ha rfl
    rw [hFresh c hc] at ha
    cases ha
  have hk : ∀ x c, node.blocks.lookup x = some c → c.validity.isAccepted = false →
      (node.record hash ⟨blk, none, .invalid⟩).blocks.lookup x = some c := fun x c hc ha => by
    rw [record_lookup_of_ne _ _ (hne x c hc ha)]
    exact hc
  have hd' : (node.record hash ⟨blk, none, .invalid⟩).InvalidDescent
      (hash :: blk.2.header.parentHash :: rest) v :=
    ⟨⟨blk, none, .invalid⟩, by simp [Node.record], rfl, rfl, InvalidDescent.mono hk hd⟩
  have hn' : (hash :: (blk.2.header.parentHash :: rest) ++ [v]).Nodup := by
    refine List.nodup_cons.mpr ⟨fun hm => ?_, hn⟩
    obtain ⟨d, hd'', hda⟩ := InvalidDescent.not_accepted hd _ hm
    exact hne _ _ hd'' hda rfl
  have h1 : latestValid (node.record hash ⟨blk, none, .invalid⟩).tree hash = some v :=
    hd'.latestValid hn'
  have h2 : latestValid node.tree blk.2.header.parentHash = some v := hd.latestValid hn
  obtain ⟨c, hc, ha⟩ := InvalidDescent.not_accepted hd v (by simp)
  unfold Engine.latestValidHash
  rw [h1, h2]
  simp [tree_lookup, hc, hk v c hc ha]

/-- On a grounded node, the latest valid hash of a known invalid block stays in later nodes. -/
theorem Reachable.latestValidHash {later : Node} {hash : Hash32} {b : KnownBlock}
    (hg : node.Grounded) (hb : node.blocks.lookup hash = some b) (hInvalid : b.validity = .invalid)
    (hr : Reachable node later) :
    latestValidHash later.tree hash = latestValidHash node.tree hash := by
  obtain ⟨rest, v, hd, hn⟩ := hg.descent hash b hb hInvalid
  have hk : ∀ x c, node.blocks.lookup x = some c → c.validity.isAccepted = false →
      later.blocks.lookup x = some c := fun x c hc ha => hr.lookup hc ha
  have hd' : later.InvalidDescent (hash :: rest) v := InvalidDescent.mono hk hd
  -- The end of the path is the latest valid block in both nodes, with the same entry.
  obtain ⟨c, hc, ha⟩ := InvalidDescent.not_accepted hd v (by simp)
  unfold Engine.latestValidHash
  rw [show hash = (hash :: rest).headD v from rfl, hd.latestValid hn, hd'.latestValid hn]
  simp [tree_lookup, hc, hk v c hc ha]

/-- An update to a known invalid head is invalid, with the latest valid hash of the head.

On a grounded node, a failed terminal block check gives a zero latest valid hash.

So the answer is the same either way.

The update leaves the node as it was. -/
theorem forkchoiceUpdatedStep_of_invalid_head_of_grounded {state : ForkchoiceState}
    {attributes : Option Lean.Json} {b : KnownBlock} (hg : node.Grounded)
    (hParams : forkchoiceUpdatedParams version params = .ok (state, attributes))
    (hb : node.blocks.lookup state.headBlockHash = some b) (hInvalid : b.validity = .invalid) :
    node.forkchoiceUpdatedStep version params =
      (.ok (⟨.invalid, latestValidHash node.tree state.headBlockHash⟩, none), node) := by
  have hV := validateHead_of_invalid_head hParams hb hInvalid
  have hNot : node.headAccepted version params = false := by
    simp [headAccepted, hParams, hb, hInvalid, Validity.isAccepted]
  have hTree : node.tree.lookup state.headBlockHash = some b.toKnownPayload := by
    rw [tree_lookup, hb]
    rfl
  cases hT : chainPassesTerminalCheck node.transition node.tree state.headBlockHash with
  | false =>
    -- The check fails, and then the latest valid hash is zero too.
    have hZ : latestValidHash node.tree state.headBlockHash = some ZERO_HASH := by
      rcases hg.terminal_or_zero hb hInvalid with h | h
      · rw [hT] at h
        cases h
      · exact h
    have hf := forkchoiceUpdated_of_not_terminal (finalized := node.finalized) hTree hT
    rw [hZ]
    simp [forkchoiceUpdatedStep, hV, hNot, updateStep, appliedState, forkchoiceUpdatedCall,
      hParams, hf, bind, Except.bind, pure, Except.pure, forkchoiceUpdatedResponse, Functor.map,
      Except.map]
  | true =>
    have h := forkchoiceUpdatedStep_of_invalid_head hParams hb hInvalid (by rw [hV]; exact hT)
    rw [hV] at h
    exact h

/-- An `INVALID` answer to a payload carries the latest valid hash of the payload in the next node.

The node is grounded, and the payload passes the checks with the hash of its block. -/
theorem newPayloadStep_latestValidHash {checked : CheckedBlock version} {hash : Hash32}
    {latest : Option Hash32} {reason : Option PayloadError} {next : Node}
    (hg : node.Grounded)
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (h : node.newPayloadStep version params = (.ok (⟨.invalid, latest⟩, reason), next)) :
    latest = latestValidHash next.tree hash := by
  by_cases hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true
  · rw [newPayloadStep_of_fresh hCheck hHash hFresh] at h
    simp only [onParent] at h
    split at h
    · rename_i blk pow post hp
      split at h
      · -- The payload runs on its valid parent, which is the head.
        simp only [executeOn] at h
        split at h
        · simp at h
        · rename_i st re nx hOn
          simp only [Prod.mk.injEq, Except.ok.injEq] at h
          obtain ⟨⟨rfl, -⟩, rfl⟩ := h
          -- An invalid answer brings back no block, so the payload is recorded as invalid.
          cases nx with
          | some bp =>
            obtain ⟨b', post'⟩ := bp
            have := (valid_iff_of_newPayloadOnChain hOn).mpr ⟨_, _, rfl⟩
            cases this
          | none =>
            have hl := latestValidHash_of_newPayloadOnChain (chain := node.chainAt _ post) hCheck
              (recentTo_getLast? hp) hOn rfl
            simp only at hl
            rw [hl]
            simp only [recordExecution, ↓reduceIte]
            exact (hg.latestValidHash_record_valid (blk := ⟨checked.fork, checked.block⟩)
              (p := ⟨blk, pow, .valid post⟩) hFresh hp rfl).symm
      · simp at h
    · simp at h
    · -- The parent is invalid.
      rename_i blk pow hp
      simp only [Prod.mk.injEq, Except.ok.injEq, PayloadStatus.mk.injEq] at h
      obtain ⟨⟨⟨-, rfl⟩, -⟩, rfl⟩ := h
      exact (hg.latestValidHash_record_invalid (blk := ⟨checked.fork, checked.block⟩)
        (p := ⟨blk, pow, .invalid⟩) hFresh hp rfl).symm
    · simp at h
  · simp only [Classical.not_forall] at hFresh
    obtain ⟨⟨blk, pow, v⟩, hk, hv⟩ := hFresh
    cases v with
    | valid post =>
      rw [newPayloadStep_of_known_valid hCheck hHash hk rfl] at h
      simp at h
    | invalid =>
      rw [newPayloadStep_of_known_invalid hCheck hHash hk rfl] at h
      simp only [Prod.mk.injEq, Except.ok.injEq, PayloadStatus.mk.injEq] at h
      obtain ⟨⟨⟨-, rfl⟩, -⟩, rfl⟩ := h
      rfl
    | accepted v' p' => simp [Validity.isAccepted] at hv

/-- A later update to a payload answered `INVALID` repeats the latest valid hash of that answer.

The nodes are reached from a node that starts from a block.

The payload passes the checks with the hash of its block.

The parameters of the update parse, and they name the payload as the head.

The update answers `INVALID` and leaves the node as it was. -/
theorem forkchoiceUpdatedStep_of_newPayloadStep_invalid {config : ChainConfig}
    {transition : TransitionConfiguration} {anchor : RecentBlock} {post : Execution.State.State}
    {total : Nat} {start next later : Node} {checked : CheckedBlock version} {hash : Hash32}
    {latest : Option Hash32} {reason : Option PayloadError} {version' : Nat}
    {params' : Lean.Json} {state : ForkchoiceState} {attributes : Option Lean.Json}
    (hStart : Node.start config transition anchor post total = some start)
    (hr : Reachable start node)
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (h : node.newPayloadStep version params = (.ok (⟨.invalid, latest⟩, reason), next))
    (hLater : Reachable next later)
    (hParams : forkchoiceUpdatedParams version' params' = .ok (state, attributes))
    (hHead : state.headBlockHash = hash) :
    later.forkchoiceUpdatedStep version' params' = (.ok (⟨.invalid, latest⟩, none), later) := by
  have hg0 := grounded_of_start hStart
  have hc0 := consistent_of_start hStart
  -- The answer names the latest valid hash of the payload in the next node.
  have hE := newPayloadStep_latestValidHash (hr.grounded hg0 hc0) hCheck hHash h
  have hNext : Reachable start next := by
    have := Reachable.newPayload version params hr
    rwa [h] at this
  have hgN : next.Grounded := hNext.grounded hg0 hc0
  have hgL : later.Grounded := hLater.grounded hgN (hNext.consistent hc0)
  -- The payload is known as invalid in the next node, and stays so in the later one.
  obtain ⟨b, hb, hi⟩ := newPayloadStep_invalid_known hCheck hHash h rfl
  have hbL := hLater.invalid hb hi
  subst hHead
  rw [hE, ← Reachable.latestValidHash hgN hb hi hLater]
  exact forkchoiceUpdatedStep_of_invalid_head_of_grounded hgL hParams hbL hi

end Node

end EthLib.Engine
