/- Authors: Matthias Meijers -/

module
public import EthereumXMSSHypertree.HypertreeHash

/-!
# Injectivity of the virtual coordinate and data frame

The unused-domain frame retains every tagged coordinate and every input value. Its word bounds
are local to the actual finite hypertree; unrestricted natural-number serialization is not used.
-/

public section

namespace EthereumXMSSHypertree.ConcreteHypertree

open EthLib.Base EthLib.Cryptography.Xmss EthLib.Cryptography.HashSig

private theorem frameWords_acc (words : List Nat) (initialBytes : ByteArray) :
    words.foldl (fun bytes word => bytes ++ packBytes (uintToBytes 4 word)) initialBytes =
      initialBytes ++ frameWords words := by
  induction words generalizing initialBytes with
  | nil => simp [frameWords]
  | cons word words ih =>
    simp only [List.foldl_cons]
    rw [ih, show frameWords (word :: words) =
      packBytes (uintToBytes 4 word) ++ frameWords words by
        unfold frameWords
        simp only [List.foldl_cons, ByteArray.empty_append]
        exact ih _]
    exact ByteArray.append_assoc

private theorem frameWords_cons (word : Nat) (words : List Nat) :
    frameWords (word :: words) = packBytes (uintToBytes 4 word) ++ frameWords words := by
  simpa only [frameWords, List.foldl_cons, ByteArray.empty_append] using
    frameWords_acc words (packBytes (uintToBytes 4 word))

private theorem frameWords_size (words : List Nat) :
    (frameWords words).size = 4 * words.length := by
  induction words with
  | nil => simp [frameWords]
  | cons word words ih => simp [frameWords_cons, ih, Nat.mul_add, Nat.add_comm]

private theorem frameWords_inj (first second : List Nat) (lengths : first.length = second.length)
    (hfirst : ∀ word ∈ first, word < 256 ^ 4) (hsecond : ∀ word ∈ second, word < 256 ^ 4)
    (h : frameWords first = frameWords second) : first = second := by
  induction first generalizing second with
  | nil => simpa using lengths.symm
  | cons word words ih =>
    cases second with
    | nil => simp at lengths
    | cons other others =>
      rw [frameWords_cons, frameWords_cons] at h
      obtain ⟨hword, htail⟩ := byteArray_append_inj h (by simp)
      have heq := uintToBytes_inj (hfirst word (by simp)) (hsecond other (by simp))
        (packBytes_injective hword)
      have hrest := ih others (by simpa using lengths)
        (fun n hn => hfirst n (by simp [hn])) (fun n hn => hsecond n (by simp [hn])) htail
      simp [heq, hrest]

/-- Every virtual tweak frame occupies exactly six four-byte words. -/
theorem tweakFrame_size (tweak : Tweak) : (tweakFrame tweak).size = 24 := by
  cases tweak <;> simp [tweakFrame, frameWords_size]

/-- All abstract tweak coordinates can be recovered from the fixed-width frame. -/
theorem tweakFrame_injective : Function.Injective tweakFrame := by
  intro first second h
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      have h1 := treeIndex_lt first.1.1
      have h2 := treeIndex_lt second.1.1
      have hs := frameWords_inj _ _ (by rfl)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]
            intro n hn
            rcases hn with h | h | h | h | h | h <;>
            subst n <;> have := first.1.1.1.isLt <;> have := first.1.2.isLt <;>
            have := first.2.1.isLt <;> have := first.2.2.isLt <;> change _ < 4294967296 <;>
            simp only [shape, GXMSS.Hypertree.Shape.branching] at * <;> omega)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]
            intro n hn
            rcases hn with h | h | h | h | h | h <;>
            subst n <;> have := second.1.1.1.isLt <;> have := second.1.2.isLt <;>
            have := second.2.1.isLt <;> have := second.2.2.isLt <;> change _ < 4294967296 <;>
            simp only [shape, GXMSS.Hypertree.Shape.branching] at * <;> omega) h
      simp only [List.cons.injEq] at hs
      apply congrArg Sum.inl
      apply Prod.ext
      · exact Prod.ext (GXMSS.Hypertree.treePosition_ext (Fin.ext hs.2.1) hs.2.2.1)
          (Fin.ext hs.2.2.2.1)
      · exact Prod.ext (Fin.ext hs.2.2.2.2.1) (Fin.ext hs.2.2.2.2.2.1)
    | inr second =>
      have htag := byteArray_append_inj (by simpa only [tweakFrame, frameWords_cons] using h)
        (by simp)
      have htag' := congrArg bytesToUint (packBytes_injective htag.1)
      simp at htag'
  | inr first =>
    cases second with
    | inl second =>
      have htag := byteArray_append_inj (by simpa only [tweakFrame, frameWords_cons] using h)
        (by simp)
      have htag' := congrArg bytesToUint (packBytes_injective htag.1)
      simp at htag'
    | inr second =>
      have h1 := treeIndex_lt first.1
      have h2 := treeIndex_lt second.1
      have hs := frameWords_inj _ _ (by rfl)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]
            intro n hn
            rcases hn with h | h | h | h | h | h <;>
            subst n <;> have := first.1.1.isLt <;> have := first.2.1.isLt <;>
            have := first.2.2.isLt <;> change _ < 4294967296 <;>
            simp only [shape, GXMSS.Hypertree.Shape.branching] at * <;> omega)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]
            intro n hn
            rcases hn with h | h | h | h | h | h <;>
            subst n <;> have := second.1.1.isLt <;> have := second.2.1.isLt <;>
            have := second.2.2.isLt <;> change _ < 4294967296 <;>
            simp only [shape, GXMSS.Hypertree.Shape.branching] at * <;> omega) h
      simp only [List.cons.injEq] at hs
      apply congrArg Sum.inr
      exact Prod.ext (GXMSS.Hypertree.treePosition_ext (Fin.ext hs.2.1) hs.2.2.1)
        (Prod.ext (Fin.ext hs.2.2.2.1) (Fin.ext hs.2.2.2.2.1))

/-- The input tag and payload identify every typed input, including all endpoint values. -/
theorem inputFrame_injective : Function.Injective inputFrame := by
  intro first second h
  cases first <;> cases second <;>
    simp only [inputFrame, ByteArray.append_assoc] at h
  all_goals obtain ⟨htag, hpayload⟩ := byteArray_append_inj h (by rfl)
  case digest.digest first second => exact congrArg Input.digest (packBytes_injective hpayload)
  case pair.pair left right left' right' =>
    obtain ⟨hl, hr⟩ := byteArray_append_inj hpayload (by simp)
    exact congrArg₂ Input.pair (packBytes_injective hl) (packBytes_injective hr)
  case ends.ends first second =>
    have he := FullInputs.packDigests_injective hpayload
    apply congrArg Input.ends
    funext i
    simpa using congrArg (fun values : Vector Digest 58 => values[i]) he
  all_goals
    have hfirst := congrArg (fun bytes : ByteArray => bytes.data[0]!) htag
    contradiction

/-- The complete unused-domain byte frame is injective on all abstract coordinates and inputs. -/
theorem virtualFrame_injective : VirtualFrameInjective := by
  intro first second h
  obtain ⟨ht, hi⟩ := byteArray_append_inj h (by simp [tweakFrame_size])
  exact Prod.ext (tweakFrame_injective ht) (inputFrame_injective hi)

/-- Public parameters and complete virtual calls remain distinct after reserved-address framing. -/
theorem virtualInput_injective :
    Function.Injective (fun call : PublicParam × Tweak × Input =>
      virtualInput call.1 call.2.1 call.2.2) := by
  intro first second h
  obtain ⟨hpp, _, hframe⟩ := thInput_inj h
  exact Prod.ext hpp (virtualFrame_injective hframe)

end EthereumXMSSHypertree.ConcreteHypertree
