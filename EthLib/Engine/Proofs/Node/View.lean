module

public import EthLib.Engine.Node.View
public import EthLib.Engine.Proofs.Node

/-!
# Proofs: the chain view of a node holds exactly its valid blocks

Each block of the view is a valid block that the node knows, under its hash.

It is the block that the node keeps, with the state that the node keeps after it.

Each valid block that the node knows is in the view, on the canonical chain or off it.

A node that starts from a block has a view, whose canonical chain is that block alone.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg (TrustedSetup)
open EthLib.Execution.Rpc (BlockRecord ChainView)

namespace Node

variable {node : Node} {networkId : Nat} {setup : TrustedSetup} {v : ChainView}

/-- Each element of a list mapped in the option monad comes from an element of the list. -/
private theorem exists_of_mem_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ {b}, b ∈ l' → ∃ a ∈ l, f a = some b
  | [], l', h, b, hb => by
    simp at h
    subst h
    simp at hb
  | a :: l, l', h, b, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some c =>
      cases hl : List.mapM f l with
      | none => simp [ha, hl] at h
      | some cs =>
        simp only [ha, hl, Option.bind_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨x, hx, hfx⟩ := exists_of_mem_mapM hl hb
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- Each element of a list mapped in the option monad has an image in the result. -/
private theorem exists_mem_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ {a}, a ∈ l → ∃ b ∈ l', f a = some b
  | [], l', h, a, ha => by simp at ha
  | a :: l, l', h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some c =>
      cases hl : List.mapM f l with
      | none => simp [ha, hl] at h
      | some cs =>
        simp only [ha, hl, Option.bind_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨c, List.mem_cons_self, ha⟩
        · obtain ⟨y, hy, hfy⟩ := exists_mem_of_mapM hl hx
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- A key that a lookup finds is a key of the list. -/
private theorem mem_map_fst_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → a ∈ l.map (·.1)
  | [], h => by simp at h
  | (k, x) :: l, h => by
    by_cases hk : a = k
    · simp [hk]
    · have hne : (a == k) = false := by simp [hk]
      simp only [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (mem_map_fst_of_lookup h)

/-- A record of a known valid block is that block, under its hash, with the state after it. -/
theorem validRecord_some {hash : Hash32} {r : BlockRecord} (h : node.validRecord hash = some r) :
    r.hash = hash ∧
      ∃ pow, node.blocks.lookup hash = some ⟨⟨r.fork, r.block⟩, pow, .valid r.state⟩ := by
  unfold validRecord at h
  split at h
  · rename_i fork block pow post hb
    cases hp : node.validState block.header.parentHash with
    | some before =>
      simp only [hp, BlockRecord.ofRun, bind, Except.bind, pure, Except.pure] at h
      cases hr : Execution.Blocks.runBody (node.chainAt block.header.parentHash before) block with
      | error e => simp [hr, Except.toOption] at h
      | ok res =>
        simp only [hr, Except.toOption, Option.some.injEq] at h
        subst h
        exact ⟨rfl, pow, hb⟩
    | none =>
      by_cases he : block.transactions.isEmpty
      · simp only [hp, he, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨rfl, pow, hb⟩
      · simp [hp, he] at h
  · simp at h

/-- The canonical and the side records of a view are the records of their hashes. -/
private theorem mapM_of_view (h : node.view networkId setup = some v) :
    node.canonicalHashes.mapM node.validRecord = some v.canonical ∧
      (node.validHashes.filter (· ∉ node.canonicalHashes)).mapM node.validRecord = some v.side := by
  unfold view at h
  cases hc : node.canonicalHashes.mapM node.validRecord with
  | none => simp [hc] at h
  | some canonical =>
    cases hs : (node.validHashes.filter (· ∉ node.canonicalHashes)).mapM node.validRecord with
    | none =>
      simp only [decide_not] at hs
      simp [hc, hs] at h
    | some side =>
      simp only [hc, hs, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · cases h
      · cases h
        exact ⟨rfl, rfl⟩

/-- The hashes of the records of a list of hashes are those hashes. -/
private theorem map_hash_of_mapM {l : List Hash32} {rs : List BlockRecord}
    (h : l.mapM node.validRecord = some rs) : rs.map (·.hash) = l := by
  induction l generalizing rs with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    rfl
  | cons a l ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨r, hr, rest, hrest, rfl⟩ := h
    simp [(validRecord_some hr).1, ih hrest]

/-- The canonical chain of the view is the chain of the head of the node, oldest first. -/
theorem canonical_hashes_of_view (h : node.view networkId setup = some v) :
    (v.canonical.map (·.hash)).reverse = chainOf node.tree node.forkchoice.headBlockHash := by
  rw [map_hash_of_mapM (mapM_of_view h).1, canonicalHashes, List.reverse_reverse]

/-- Each block of the view is a valid block of the node, under its hash, with the state after it.
-/
theorem lookup_of_mem_view (h : node.view networkId setup = some v) {r : BlockRecord}
    (hr : r ∈ v.canonical ++ v.side) :
    ∃ pow, node.blocks.lookup r.hash = some ⟨⟨r.fork, r.block⟩, pow, .valid r.state⟩ := by
  obtain ⟨hc, hs⟩ := mapM_of_view h
  obtain ⟨hash, hr⟩ : ∃ hash, node.validRecord hash = some r := by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨hash, -, hr⟩ := exists_of_mem_mapM hc hr
      exact ⟨hash, hr⟩
    · obtain ⟨hash, -, hr⟩ := exists_of_mem_mapM hs hr
      exact ⟨hash, hr⟩
  obtain ⟨rfl, hb⟩ := validRecord_some hr
  exact hb

/-- Each valid block of the node is a block of the view. -/
theorem mem_view_of_validState (h : node.view networkId setup = some v) {hash : Hash32}
    {post : Execution.State.State} (hv : node.validState hash = some post) :
    ∃ r ∈ v.canonical ++ v.side, r.hash = hash := by
  obtain ⟨hc, hs⟩ := mapM_of_view h
  obtain ⟨b, hb, -⟩ := validState_eq_some_iff.mp hv
  have hvalid : hash ∈ node.validHashes := by
    unfold validHashes
    simp only [List.mem_filter, hv, Option.isSome_some, and_true]
    exact List.mem_eraseDups.mpr (mem_map_fst_of_lookup hb)
  by_cases hin : hash ∈ node.canonicalHashes
  · obtain ⟨r, hr, hrec⟩ := exists_mem_of_mapM hc hin
    exact ⟨r, List.mem_append_left _ hr, (validRecord_some hrec).1⟩
  · have hside : hash ∈ node.validHashes.filter (· ∉ node.canonicalHashes) :=
      List.mem_filter.mpr ⟨hvalid, by simpa using hin⟩
    obtain ⟨r, hr, hrec⟩ := exists_mem_of_mapM hs hside
    exact ⟨r, List.mem_append_right _ hr, (validRecord_some hrec).1⟩

/-- The view holds exactly the valid blocks of the node: a hash names one exactly when it is valid.
-/
theorem mem_view_iff (h : node.view networkId setup = some v) (hash : Hash32) :
    (∃ r ∈ v.canonical ++ v.side, r.hash = hash) ↔ (node.validState hash).isSome := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨pow, hb⟩ := lookup_of_mem_view h hr
    simp [validState, hb]
  · intro hv
    obtain ⟨post, hp⟩ := Option.isSome_iff_exists.mp hv
    exact mem_view_of_validState h hp

/-- A node that knows one valid block with no transaction as its head views it alone.

The block must not be its own parent. -/
private theorem view_of_single {hash : Hash32} {fork : Fork}
    {block : Execution.Blocks.Block fork Execution.Transactions.Transaction}
    {pow : Option (Nat × Nat)} {post : Execution.State.State}
    (hb : node.blocks = [(hash, ⟨⟨fork, block⟩, pow, .valid post⟩)])
    (hhead : node.forkchoice.headBlockHash = hash) (hparent : block.header.parentHash ≠ hash)
    (htx : block.transactions = []) :
    ∃ v, node.view networkId setup = some v ∧
      v.canonical = [⟨fork, block, hash, post, [], [], none⟩] ∧ v.side = [] := by
  have hv : node.validState hash = some post := by simp [validState, hb]
  have hpv : node.validState block.header.parentHash = none := by
    have hne : (block.header.parentHash == hash) = false := by simp [hparent]
    simp [validState, hb, List.lookup, hne]
  have hcanon : node.canonicalHashes = [hash] := by
    simp [canonicalHashes, chainOf, tree, hb, hhead, ancestors]
  have hvalid : node.validHashes = [hash] := by
    simp [validHashes, hb, hv, List.eraseDups_cons]
  have hrec : node.validRecord hash = some ⟨fork, block, hash, post, [], [], none⟩ := by
    simp [validRecord, hb, hpv, htx]
  unfold view
  simp only [hcanon, hvalid, List.mapM_cons, List.mapM_nil, hrec]
  simp

/-- A node that starts from a block has a view, whose canonical chain is that block alone.

It assumes that the hash of the header of the block is not its own parent hash. -/
theorem view_of_start {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : Execution.Blocks.RecentBlock} {post : Execution.State.State} {total : Nat}
    (h : Node.start config transition anchor post total = some node)
    (hParent : anchor.header.hash ≠ .ok anchor.header.parentHash) :
    ∃ v r, node.view networkId setup = some v ∧ v.canonical = [r] ∧ v.side = [] ∧
      anchor.header.hash = .ok r.hash ∧ r.state = post := by
  unfold start at h
  cases hh : anchor.header.hash with
  | error e => simp [hh, Except.toOption] at h
  | ok hash =>
    cases hc : commitsToEmptyBody anchor
    · simp [hh, hc, Except.toOption] at h
    simp only [hh, hc, Except.toOption] at h
    have hparent : anchor.header.parentHash ≠ hash := by
      rintro rfl
      exact hParent hh
    -- Whatever its total difficulty, the node knows the anchor alone, as its head.
    have hOne : ∀ (n : Node) pow,
        n.blocks = [(hash, ⟨⟨_, ⟨anchor.header, [], anchor.ommers, fun _ => []⟩⟩, pow,
          .valid post⟩)] → n.forkchoice.headBlockHash = hash →
        ∃ v r, n.view networkId setup = some v ∧ v.canonical = [r] ∧ v.side = [] ∧
          anchor.header.hash = .ok r.hash ∧ r.state = post := by
      intro n pow hb hhead
      obtain ⟨v, hv, hcanon, hside⟩ := view_of_single hb hhead hparent rfl
      exact ⟨v, _, hv, hcanon, hside, hh, rfl⟩
    by_cases hp : anchor.fork < .paris
    · by_cases hd : anchor.header.difficulty ≤ total
      · simp only [hp, hd, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        rw [← hh]
        exact hOne _ _ rfl rfl
      · simp [hp, hd] at h
    · simp only [hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      rw [← hh]
      exact hOne _ _ rfl rfl

end Node

end EthLib.Engine
