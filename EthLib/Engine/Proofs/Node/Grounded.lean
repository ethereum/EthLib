module

public import EthLib.Engine.Proofs.Node.Proposal
import all EthLib.Engine.Proofs.Node.Proposal

/-!
# Proofs: the ancestry of the blocks of an execution node

Every invalid block descends from a valid one, through invalid blocks.

A valid block from Paris on sits on a valid parent, which is terminal if it is of proof of work.

A node that knows no block of proof of work needs no such parent.

A node that starts from one block has both facts, and every step keeps them on a consistent node.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg (TrustedSetup)
open EthLib.Execution.Blocks (Block RecentBlock)
open EthLib.Execution.Transactions (Transaction)

namespace Node

variable {node : Node} {version : Nat} {params : Lean.Json}

/-- A path of known invalid blocks, each the parent of the one before, down to a valid block. -/
def InvalidDescent (node : Node) : List Hash32 → Hash32 → Prop
  -- The path ends at a block known as valid.
  | [], valid => ∃ post, node.validState valid = some post
  -- Each block of the path is known as invalid, and its parent comes next.
  | hash :: rest, valid => ∃ b, node.blocks.lookup hash = some b ∧ b.validity = .invalid ∧
      b.block.header.parentHash = rest.headD valid ∧ node.InvalidDescent rest valid

/-- A node is grounded when its invalid blocks descend from valid ones, through invalid blocks.

A known block has totals of proof of work exactly when it is from before Paris, and is then valid.

A valid block from Paris on sits on a valid parent, which is terminal if it is of proof of work.

A node that knows no block of proof of work needs no such parent. -/
structure Grounded (node : Node) : Prop where
  /-- A known block has totals of proof of work exactly when it is from before Paris. -/
  pow_iff : ∀ hash b, node.blocks.lookup hash = some b →
    (b.powTotalDifficulty.isSome ↔ b.block.fork < .paris)
  /-- A known block with totals of proof of work is valid. -/
  valid_of_pow : ∀ hash b, node.blocks.lookup hash = some b →
    b.powTotalDifficulty.isSome → b.validity.isValid
  /-- A known invalid block starts a path of invalid blocks to a valid one, with no repeat. -/
  descent : ∀ hash b, node.blocks.lookup hash = some b → b.validity = .invalid →
    ∃ rest valid, node.InvalidDescent (hash :: rest) valid ∧ (hash :: rest ++ [valid]).Nodup
  /-- A known valid block with no totals sits on a valid parent, terminal if of proof of work.

  Otherwise the node knows no block of proof of work. -/
  terminal : ∀ hash b, node.blocks.lookup hash = some b → b.validity.isValid →
    b.powTotalDifficulty = none →
      (∃ p, node.blocks.lookup b.block.header.parentHash = some p ∧ p.validity.isValid ∧
        ∀ total parentTotal, p.powTotalDifficulty = some (total, parentTotal) →
          isTerminalPowBlock node.transition total parentTotal) ∨
      ∀ other c, node.blocks.lookup other = some c → c.powTotalDifficulty = none

/-- A path of invalid blocks and its end are blocks that are not accepted. -/
private theorem InvalidDescent.not_accepted {l : List Hash32} {v : Hash32}
    (h : node.InvalidDescent l v) :
    ∀ x ∈ l ++ [v], ∃ c, node.blocks.lookup x = some c ∧ c.validity.isAccepted = false := by
  induction l with
  | nil =>
    obtain ⟨post, hp⟩ := h
    obtain ⟨c, hc, hv⟩ := validState_eq_some_iff.mp hp
    intro x hx
    simp only [List.nil_append, List.mem_singleton] at hx
    subst hx
    exact ⟨c, hc, by simp [hv, Validity.isAccepted]⟩
  | cons y rest ih =>
    obtain ⟨b, hb, hi, -, hr⟩ := h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, hb, by simp [hi, Validity.isAccepted]⟩
    · exact ih hr x hx

/-- A path of invalid blocks stays one in a node that keeps every block that is not accepted. -/
private theorem InvalidDescent.mono {node' : Node} {l : List Hash32} {v : Hash32}
    (hk : ∀ x c, node.blocks.lookup x = some c → c.validity.isAccepted = false →
      node'.blocks.lookup x = some c)
    (h : node.InvalidDescent l v) : node'.InvalidDescent l v := by
  induction l with
  | nil =>
    obtain ⟨post, hp⟩ := h
    obtain ⟨c, hc, hv⟩ := validState_eq_some_iff.mp hp
    exact ⟨post, validState_eq_some_iff.mpr
      ⟨c, hk _ _ hc (by simp [hv, Validity.isAccepted]), hv⟩⟩
  | cons y rest ih =>
    obtain ⟨b, hb, hi, hp, hr⟩ := h
    exact ⟨b, hk _ _ hb (by simp [hi, Validity.isAccepted]), hi, hp, ih hr⟩

/-- A node with the known blocks and the transition of a grounded node is grounded. -/
private theorem Grounded.of_blocks {node' : Node} (hg : node.Grounded)
    (hb : node'.blocks = node.blocks) (ht : node'.transition = node.transition) :
    node'.Grounded := by
  have hk : ∀ x c, node.blocks.lookup x = some c → c.validity.isAccepted = false →
      node'.blocks.lookup x = some c := fun x c h _ => by rw [hb]; exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hash b h
    rw [hb] at h
    exact hg.pow_iff hash b h
  · intro hash b h
    rw [hb] at h
    exact hg.valid_of_pow hash b h
  · intro hash b h hi
    rw [hb] at h
    obtain ⟨rest, v, hd, hn⟩ := hg.descent hash b h hi
    exact ⟨rest, v, InvalidDescent.mono hk hd, hn⟩
  · intro hash b h hv hp
    rw [hb] at h
    rw [hb, ht]
    exact hg.terminal hash b h hv hp

/-- Recording a block from Paris on, with no totals of proof of work, keeps a node grounded.

An invalid block needs a known parent that is not accepted.

A valid block needs a known valid parent, terminal if it is of proof of work.

The hash is new or that of an accepted block. -/
private theorem Grounded.record {hash : Hash32} {b : KnownBlock} (hg : node.Grounded)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (hPow : b.powTotalDifficulty = none) (hFork : .paris ≤ b.block.fork)
    (hInvalid : b.validity = .invalid → ∃ p, node.blocks.lookup b.block.header.parentHash = some p ∧
      p.validity.isAccepted = false)
    (hValid : b.validity.isValid → ∃ p, node.blocks.lookup b.block.header.parentHash = some p ∧
      p.validity.isValid ∧ ∀ total parentTotal, p.powTotalDifficulty = some (total, parentTotal) →
        isTerminalPowBlock node.transition total parentTotal) :
    (node.record hash b).Grounded := by
  -- A block that is not accepted is not the recorded one, so it keeps its entry.
  have hne : ∀ x c, node.blocks.lookup x = some c → c.validity.isAccepted = false → x ≠ hash := by
    rintro x c hc ha rfl
    rw [hFresh c hc] at ha
    cases ha
  have hk : ∀ x c, node.blocks.lookup x = some c → c.validity.isAccepted = false →
      (node.record hash b).blocks.lookup x = some c := fun x c hc ha => by
    rw [record_lookup_of_ne _ _ (hne x c hc ha)]
    exact hc
  have hNew : (node.record hash b).blocks.lookup hash = some b := by
    simp [Node.record]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x c hc
    by_cases hx : x = hash
    · subst hx
      rw [hNew] at hc
      cases hc
      simp only [hPow, Option.isSome_none, Bool.false_eq_true, false_iff]
      exact fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hFork)
    · rw [record_lookup_of_ne _ _ hx] at hc
      exact hg.pow_iff x c hc
  · intro x c hc
    by_cases hx : x = hash
    · subst hx
      rw [hNew] at hc
      cases hc
      simp [hPow]
    · rw [record_lookup_of_ne _ _ hx] at hc
      exact hg.valid_of_pow x c hc
  · intro x c hc hi
    by_cases hx : x = hash
    · subst hx
      rw [hNew] at hc
      cases hc
      obtain ⟨p, hp, hpa⟩ := hInvalid hi
      cases hpv : p.validity with
      | accepted v' j => simp [hpv, Validity.isAccepted] at hpa
      | valid post =>
        -- The parent is valid, so the path is the block alone.
        refine ⟨[], b.block.header.parentHash, ⟨b, hNew, hi, rfl, post,
          validState_eq_some_iff.mpr ⟨p, hk _ _ hp hpa, hpv⟩⟩, ?_⟩
        simp only [List.nil_append, List.cons_append, List.nodup_cons, List.mem_singleton,
          List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, and_true]
        exact fun h => hne _ _ hp hpa h.symm
      | invalid =>
        -- The parent is invalid, so the path goes on with the parent's path.
        obtain ⟨rest, v, hd, hn⟩ := hg.descent _ p hp hpv
        refine ⟨b.block.header.parentHash :: rest, v,
          ⟨b, hNew, hi, rfl, InvalidDescent.mono hk hd⟩, ?_⟩
        refine List.nodup_cons.mpr ⟨?_, hn⟩
        intro hm
        obtain ⟨d, hd', hda⟩ := InvalidDescent.not_accepted hd _ hm
        exact hne _ _ hd' hda rfl
    · rw [record_lookup_of_ne _ _ hx] at hc
      obtain ⟨rest, v, hd, hn⟩ := hg.descent x c hc hi
      exact ⟨rest, v, InvalidDescent.mono hk hd, hn⟩
  · intro x c hc hv hp
    by_cases hx : x = hash
    · subst hx
      rw [hNew] at hc
      cases hc
      obtain ⟨p, hpl, hpv, ht⟩ := hValid hv
      have hpa : p.validity.isAccepted = false := by
        revert hpv
        cases p.validity <;> simp [Validity.isValid, Validity.isAccepted]
      exact .inl ⟨p, hk _ _ hpl hpa, hpv, ht⟩
    · rw [record_lookup_of_ne _ _ hx] at hc
      rcases hg.terminal x c hc hv hp with ⟨p, hpl, hpv, ht⟩ | hNone
      · have hpa : p.validity.isAccepted = false := by
          revert hpv
          cases p.validity <;> simp [Validity.isValid, Validity.isAccepted]
        exact .inl ⟨p, hk _ _ hpl hpa, hpv, ht⟩
      · refine .inr fun other d hd => ?_
        by_cases ho : other = hash
        · subst ho
          rw [hNew] at hd
          cases hd
          exact hPow
        · rw [record_lookup_of_ne _ _ ho] at hd
          exact hNone other d hd

/-- A run of a block from Paris on, on a known valid parent, keeps a consistent node grounded.

The hash is new or that of an accepted block. -/
private theorem Grounded.executeOn {hash : Hash32}
    {block : (fork : Fork) × Block fork Transaction} {post : Execution.State.State}
    {p : KnownBlock} (hg : node.Grounded) (hc : node.Consistent)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (hp : node.blocks.lookup block.2.header.parentHash = some p) (hpv : p.validity = .valid post)
    (hFork : .paris ≤ block.1) :
    (node.executeOn hash block post version params).2.Grounded := by
  have hpa : p.validity.isAccepted = false := by simp [hpv, Validity.isAccepted]
  simp only [Node.executeOn]
  split
  · exact hg
  · rename_i status reason next hRun
    simp only [Node.recordExecution]
    split
    · -- A valid payload is recorded, and its parent passed the terminal check with its own total.
      refine hg.record hFresh rfl hFork (fun h => by cases h)
        (fun _ => ⟨p, hp, by simp [hpv, Validity.isValid], ?_⟩)
      intro total parentTotal hPow
      obtain ⟨parent, hl, ht⟩ := passesTerminalCheck_of_newPayloadOnChain_some hRun
      rw [show (node.chainAt block.2.header.parentHash post).recent =
        node.recentTo block.2.header.parentHash from rfl, recentTo_getLast? hp] at hl
      cases hl
      -- A parent with totals is from before Paris, so its first total is its total difficulty.
      have hlt := (hg.pow_iff _ p hp).mp (by simp [hPow])
      have hnle : ¬ (.paris ≤ p.block.fork) := fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt h)
      rcases (hc _ p hp).2 with hP | ⟨-, t, hT, -⟩
      · exact absurd hP hnle
      · rw [hT] at hPow
        simp only [Option.some.injEq, Prod.mk.injEq] at hPow
        obtain ⟨rfl, rfl⟩ := hPow
        have htd : node.totalDifficulty block.2.header.parentHash = t := by
          simp [totalDifficulty, hp, hT]
        rw [htd] at ht
        simp only [passesTerminalCheck, hnle, decide_false, Bool.false_or, Bool.and_eq_true] at ht
        exact ht.2
    · split
      · exact hg.record hFresh rfl hFork (fun _ => ⟨p, hp, hpa⟩) (fun h => by cases h)
      · exact hg

/-- Handling a block from Paris on by the validity of its parent keeps a consistent node grounded.

The hash is new or that of an accepted block. -/
private theorem Grounded.onParent {hash : Hash32}
    {block : (fork : Fork) × Block fork Transaction} (hg : node.Grounded) (hc : node.Consistent)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (hFork : .paris ≤ block.1) :
    (node.onParent hash block version params).2.Grounded := by
  -- An accepted block needs no parent.
  have hAccept : (node.record hash ⟨block, none, .accepted version params⟩).Grounded :=
    hg.record hFresh rfl hFork (fun h => by cases h) (fun h => by cases h)
  simp only [Node.onParent]
  split
  · rename_i blk pow post hp
    split
    · exact hg.executeOn hc hFresh hp rfl hFork
    · exact hAccept
  · exact hAccept
  · rename_i blk pow hp
    exact hg.record hFresh rfl hFork (fun _ => ⟨_, hp, rfl⟩) (fun h => by cases h)
  · exact hg

/-- Validation from a block of a set closed under parents leaves the node as it was.

Each block of the set is known and accepted, and its parent is in the set. -/
private theorem validateChain_of_closed {S : List Hash32}
    (hS : ∀ y ∈ S, ∃ c, node.blocks.lookup y = some c ∧ c.validity.isAccepted = true ∧
      c.block.header.parentHash ∈ S) :
    ∀ fuel x, x ∈ S → node.validateChain fuel x = node := by
  intro fuel
  induction fuel with
  | zero => intro x _; rfl
  | succ fuel ih =>
    intro x hx
    obtain ⟨⟨blk, pow, v⟩, hk, ha, hp⟩ := hS x hx
    cases v with
    | valid post => cases ha
    | invalid => cases ha
    | accepted v' p' =>
      -- The chain up to the parent stays as it was, and the parent is still accepted.
      obtain ⟨⟨blk', pow', w⟩, hk', ha', -⟩ := hS _ hp
      cases w with
      | valid post => cases ha'
      | invalid => cases ha'
      | accepted w' q' =>
        simp only [KnownBlock.block] at hp hk'
        simp only [Node.validateChain, hk, ih _ hp, hk']

/-- Validation keeps a known block, unless the walk from the start reaches it through a closed set.

Each block of that set, but the kept one, is accepted, with its parent in the set. -/
private theorem validateChain_lookup_or_cycle {y : Hash32} {c : KnownBlock}
    (hy : node.blocks.lookup y = some c) :
    ∀ fuel x, (node.validateChain fuel x).blocks.lookup y = some c ∨
      ∃ S : List Hash32, x ∈ S ∧ y ∈ S ∧ ∀ z ∈ S, z = y ∨ ∃ d, node.blocks.lookup z = some d ∧
        d.validity.isAccepted = true ∧ d.block.header.parentHash ∈ S := by
  intro fuel
  induction fuel with
  | zero => exact fun _ => .inl hy
  | succ fuel ih =>
    intro x
    by_cases hxy : x = y
    · subst hxy
      exact .inr ⟨[x], List.mem_singleton_self _, List.mem_singleton_self _, fun z hz =>
        .inl (List.mem_singleton.mp hz)⟩
    cases hx : node.blocks.lookup x with
    | none => exact .inl (by simp only [Node.validateChain, hx]; exact hy)
    | some b =>
      obtain ⟨blk, pow, v⟩ := b
      cases v with
      | valid post => exact .inl (by simp only [Node.validateChain, hx]; exact hy)
      | invalid => exact .inl (by simp only [Node.validateChain, hx]; exact hy)
      | accepted v' p' =>
        rcases ih blk.2.header.parentHash with hl | ⟨S, hq, hyS, hS⟩
        · -- Validation records only the start, which is not this block.
          have hne : y ≠ x := fun h => hxy h.symm
          refine .inl ?_
          simp only [Node.validateChain, hx]
          split
          · rw [executeOn_lookup_of_ne _ _ _ _ _ hne, hl]
          · rw [record_lookup_of_ne _ _ hne, hl]
          · exact hl
        · refine .inr ⟨x :: S, List.mem_cons_self, List.mem_cons_of_mem _ hyS, fun z hz => ?_⟩
          rcases List.mem_cons.mp hz with rfl | hz
          · exact .inr ⟨_, hx, rfl, List.mem_cons_of_mem _ hq⟩
          · rcases hS z hz with h | ⟨d, hd, ha, hp⟩
            · exact .inl h
            · exact .inr ⟨d, hd, ha, List.mem_cons_of_mem _ hp⟩

/-- Validation of the chain of the parent of an accepted block keeps that block accepted. -/
private theorem validateChain_lookup_accepted {hash : Hash32} {c : KnownBlock}
    (hk : node.blocks.lookup hash = some c) (ha : c.validity.isAccepted = true) (fuel : Nat) :
    (node.validateChain fuel c.block.header.parentHash).blocks.lookup hash = some c := by
  rcases validateChain_lookup_or_cycle hk fuel c.block.header.parentHash with
    hl | ⟨S, hp, hS, hClosed⟩
  · exact hl
  · -- On a cycle, the block closes it, so validation leaves the node as it was.
    rw [validateChain_of_closed (fun z hz => ?_) fuel _ hp]
    · exact hk
    · rcases hClosed z hz with rfl | h
      · exact ⟨c, hk, ha, hp⟩
      · exact h

/-- Validation of a chain keeps a node grounded and consistent. -/
private theorem Grounded.validateChain (hg : node.Grounded) (hc : node.Consistent) (fuel : Nat)
    (hash : Hash32) :
    (node.validateChain fuel hash).Grounded ∧ (node.validateChain fuel hash).Consistent := by
  induction fuel generalizing node hash with
  | zero => exact ⟨hg, hc⟩
  | succ fuel ih =>
    simp only [Node.validateChain]
    split
    · rename_i block pow v p hb
      obtain ⟨hHash, hFork⟩ := hc hash _ hb
      -- An accepted block of a consistent node is from Paris on.
      have hFork : .paris ≤ block.1 := by
        rcases hFork with h | ⟨h, -⟩
        · exact h
        · simp [Validity.isAccepted] at h
      obtain ⟨hg', hc'⟩ := ih hg hc block.2.header.parentHash
      -- The block is still accepted after the validation of the chain of its parent.
      have hk : (node.validateChain fuel block.2.header.parentHash).blocks.lookup hash =
          some _ := validateChain_lookup_accepted hb rfl fuel
      have hFresh : ∀ c, (node.validateChain fuel block.2.header.parentHash).blocks.lookup hash =
          some c → c.validity.isAccepted = true := by
        intro c hc
        rw [hk] at hc
        cases hc
        rfl
      split
      · rename_i post hp
        exact ⟨hg'.executeOn hc' hFresh hp rfl hFork, hc'.executeOn hHash hFork⟩
      · rename_i hp
        exact ⟨hg'.record hFresh rfl hFork (fun _ => ⟨_, hp, rfl⟩) (fun h => by cases h),
          hc'.record hHash hFork⟩
      · exact ⟨hg', hc'⟩
    · exact ⟨hg, hc⟩

/-- A node that starts from a block is grounded. -/
theorem grounded_of_start {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : RecentBlock} {post : Execution.State.State} {total : Nat}
    (h : Node.start config transition anchor post total = some node) : node.Grounded := by
  unfold start at h
  cases hh : anchor.header.hash with
  | error e => simp [hh, Except.toOption] at h
  | ok hash =>
    cases hc : commitsToEmptyBody anchor
    · simp [hh, hc, Except.toOption] at h
    simp only [hh, hc, Except.toOption] at h
    -- The node knows the anchor alone, valid, with totals exactly when it is from before Paris.
    have hOne : ∀ pow, (pow.isSome ↔ anchor.fork < .paris) →
        (⟨config, transition, [(hash, ⟨⟨_, ⟨anchor.header, [], anchor.ommers, fun _ => []⟩⟩, pow,
          .valid post⟩)],
          ⟨hash, ZERO_HASH, ZERO_HASH⟩, none, []⟩ : Node).Grounded := by
      intro pow hp
      have hl : ∀ other b, List.lookup other [(hash, (⟨⟨_, ⟨anchor.header, [], anchor.ommers,
          fun _ => []⟩⟩, pow, .valid post⟩ : KnownBlock))] = some b →
          b = ⟨⟨_, ⟨anchor.header, [], anchor.ommers, fun _ => []⟩⟩, pow, .valid post⟩ := by
        intro other b hb
        by_cases hne : other = hash
        · subst hne
          simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hb
          exact hb.symm
        · have : (other == hash) = false := by simp [hne]
          simp [List.lookup, this] at hb
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro other b hb
        cases hl other b hb
        exact hp
      · intro other b hb _
        cases hl other b hb
        rfl
      · intro other b hb hi
        cases hl other b hb
        cases hi
      · intro other b hb _ hn
        cases hl other b hb
        exact .inr fun other' c hc => by
          cases hl other' c hc
          exact hn
    by_cases hp : anchor.fork < .paris
    · by_cases hd : anchor.header.difficulty ≤ total
      · simp only [hp, hd, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        exact hOne _ (by simp [hp])
      · simp [hp, hd] at h
    · simp only [hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact hOne _ (by simp [hp])

/-- A step of `engine_newPayload` keeps a consistent node grounded. -/
theorem Grounded.newPayloadStep (hg : node.Grounded) (hc : node.Consistent) :
    (node.newPayloadStep version params).2.Grounded := by
  unfold Node.newPayloadStep
  split
  · exact hg
  · exact hg
  · rename_i checked hCheck
    dsimp only
    split
    · exact hg
    · rename_i hash hHash
      split
      · exact hg
      · exact hg
      · rename_i hNotValid hNotInvalid
        -- The payload is neither valid nor invalid, so it is new or accepted.
        have hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true := by
          intro ⟨blk, pow, v⟩ hk
          cases v with
          | valid post => exact absurd hk (hNotValid blk pow post)
          | invalid => exact absurd hk (hNotInvalid blk pow)
          | accepted v' p' => rfl
        -- A checked payload is from Paris on, since some version takes its fork.
        exact hg.onParent hc hFresh ((exists_acceptsFork_iff checked.fork).mp ⟨_, checked.accepted⟩)

/-- The validation of an update keeps a consistent node grounded. -/
theorem Grounded.validateHead (hg : node.Grounded) (hc : node.Consistent) :
    (node.validateHead version params).Grounded := by
  unfold Node.validateHead
  split
  · exact (hg.validateChain hc _ _).1
  · exact hg

/-- A step of `engine_forkchoiceUpdated` keeps a consistent node grounded. -/
theorem Grounded.forkchoiceUpdatedStep (hg : node.Grounded) (hc : node.Consistent) :
    (node.forkchoiceUpdatedStep version params).2.Grounded := by
  have hv := hg.validateHead (version := version) (params := params) hc
  simp only [Node.forkchoiceUpdatedStep]
  split
  · exact hv
  · -- The update changes only the forkchoice state and the known finalized block.
    simp only [Node.updateStep]
    split
    · exact hv.of_blocks rfl rfl
    · exact hv

/-- A step of `engine_forkchoiceUpdated` that builds keeps a consistent node grounded. -/
theorem Grounded.forkchoiceUpdatedBuildStep (hg : node.Grounded) (hc : node.Consistent)
    (builder : Builder) : (node.forkchoiceUpdatedBuildStep builder version params).2.Grounded := by
  -- The build changes neither the known blocks nor the configuration of the transition.
  have ht : (node.forkchoiceUpdatedBuildStep builder version params).2.transition =
      (node.forkchoiceUpdatedStep version params).2.transition := by
    simp only [Node.forkchoiceUpdatedBuildStep]
    split
    · rename_i h
      rw [h]
      exact storeBuild_transition _ _ _ _ _
    · rfl
  exact (hg.forkchoiceUpdatedStep hc).of_blocks
    (forkchoiceUpdatedBuildStep_keeps _ _ _ _).1 ht

/-- Every node that the steps reach from a grounded and consistent node is grounded. -/
theorem Reachable.grounded {start : Node} (hg : start.Grounded) (hc : start.Consistent)
    (hr : Reachable start node) : node.Grounded := by
  induction hr with
  | refl => exact hg
  | newPayload version params hr ih => exact ih.newPayloadStep (hr.consistent hc)
  | forkchoiceUpdated version params hr ih => exact ih.forkchoiceUpdatedStep (hr.consistent hc)
  | forkchoiceUpdatedBuild builder version params hr ih =>
    exact ih.forkchoiceUpdatedBuildStep (hr.consistent hc) builder
  | getPayload setup version id _ ih => exact ih

end Node

end EthLib.Engine
