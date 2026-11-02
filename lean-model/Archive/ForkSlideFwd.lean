
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkSlideFwd — the consolidated green artifact

READ-ONLY scratch (no source edits, no commit). Zero `sorry`, zero
`Classical.choice`, no `native_decide`; `#print axioms` battery at the tail.

This is the single-file concatenation of `Temp/SlideFwd_Core.lean`,
`Temp/SlideFwd_Chain.lean` and `Temp/SlideFwd_Residual.lean` (same content,
one namespace), so that it compiles with one command and no intermediate
oleans:

```text
lake env lean Orig2/Fork/Local/ForkSlideFwd.lean
```

See `Temp/SlideFwd_Report.md` for the file:line citations.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-
# Temp/SlideFwd_Core — the read-safe window certificate, slides included

READ-ONLY scratch (no source edits, no commit).  Zero `sorry`, zero
`Classical.choice`, no `native_decide`; battery at the tail.

## What is proved

`RaiseLeft.KeepsForward` asks, for EVERY window `γ` preceding an occurrence of
`raise c` in a witness play out of `F`, for the per-position certificate
`RaiseSwaps F c γ`.  It is refuted in general by same-suit pulls
(`RaiseLeft.not_canRaise_of_pull_same_suit`, `Temp/SlideFwd_Report.md`).

Here we prove the **read-safe** instance in full generality, with NO bare-top
and NO empty-tail hypothesis: if every window letter avoids `c` — it is not a
pull or a raise in `c`'s suit, it does not land on `c`, and it is not a slide
headed by `c` — then the certificate holds.

* `ReadSafe c q` is the prose shape (waste letters, which no witness play
  contains, are allowed).
* `readOK_of_readSafe` converts it to `R12.ReadOK` at any reversible letter
  (`R12.ReadOK` is FALSE on waste letters only, and those are never
  reversible).
* `raiseSwaps_of_readSafe` is the induction; it is `R12.raiseSwaps_of_read`
  with the `ReadOK` hypothesis replaced by `ReadSafe`.
* `keepsForward_readsafe_slide` is the target in the user's `R12.ReadOK`
  spelling (its `tabToTab` clause IS "not headed by `c`, not landing on `c`").
* `keepsForward_readsafe_slide_noslide` expands the slide clause explicitly.

## The "segment carries `c`" question

The expected argument worries about a slide headed by ANOTHER card `w ≠ c`
whose moved segment CARRIES `c`, and proposes the crux lemma
`segment_containing_bare_top` (a bare pile top cannot be carried by a segment
headed elsewhere).  **That lemma is not needed**, and its bare-top hypothesis
is not used anywhere: `CommuteStep.step_comm_slide_raise`
(`Orig2/Fork/Local/ForkCommuteSlide.lean:951`) has a dedicated branch for exactly this
case — the raise card top of the slide's source pile, where the raise CHOPS
the run at its own top card (`Orig2/Fork/Local/ForkCommuteSlide.lean:1015-1122`).  Hence
`R12.raise_swap_slide` (`Orig2/Fork/Class/ForkReadBracket.lean:556-582`) is
unconditional, with only `w ≠ c` and `b ≠ Sum.inr c`.  `segment_containing_bare_top`
is therefore recorded below as the (true, but unused) implication it really is.

## The one genuinely needed slide clause

A slide HEADED by `c` is not commutable with `raise c`: after the raise `c`
lies on the foundation and holds no pile, so the slide is dead there.  This is
`R12.no_slide_self_at` (`Orig2/Fork/Class/ForkReadBracket.lean:766`), restated here as
`raise_not_before_own_slide`.  So the S3 clause of `ReadSafe` is essential, not
cosmetic — the empty-tail residual is exactly "no slide of `c` before the
raise", see `Temp/SlideFwd_Chain.lean`.
-/

namespace SlideFwd

open NonforkKit

/- ## §1. The prose predicate -/

/-- **`ReadSafe z q`** — the letter `q` does not touch `z`'s pending raise:
it is not a pull or a raise in `z`'s suit, it does not land on `z`, and it is
not a slide headed by `z`.  The two waste letters cannot occur in a witness
play; they are allowed here so that the predicate is purely syntactic. -/
def ReadSafe (z : Card) (q : Move) : Prop :=
  match q with
  | Move.draw => True
  | Move.wasteToFound _ => True
  | Move.wasteToTab _ _ => True
  | Move.tabToFound w => w.suit ≠ z.suit
  | Move.foundToTab c b => c.suit ≠ z.suit ∧ b ≠ Sum.inr z
  | Move.tabToTab c b => c ≠ z ∧ b ≠ Sum.inr z

theorem readSafe_draw (z : Card) : ReadSafe z Move.draw := trivial

theorem readSafe_raise_of_ne {z w : Card} (h : w.suit ≠ z.suit) :
    ReadSafe z (Move.tabToFound w) := h

theorem readSafe_pull_of_ne {z c : Card} {b : Base}
    (hsu : c.suit ≠ z.suit) (hbz : b ≠ Sum.inr z) :
    ReadSafe z (Move.foundToTab c b) := ⟨hsu, hbz⟩

theorem readSafe_slide_of_ne {z c : Card} {b : Base}
    (hcz : c ≠ z) (hbz : b ≠ Sum.inr z) :
    ReadSafe z (Move.tabToTab c b) := ⟨hcz, hbz⟩

/-- **`ReadSafe` and `R12.ReadOK` agree on every reversible letter.**  They
differ only on the two waste letters, where `ReadOK` is `False` and
`ReadSafe` is `True`; no witness play contains a waste letter. -/
theorem readOK_of_readSafe {st : State} {z : Card} {q : Move}
    (hrev : reversibleAtW st q) (h : ReadSafe z q) : R12.ReadOK z q := by
  cases q with
  | draw => exact trivial
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW st c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW st c b)
  | tabToFound w => exact h
  | foundToTab c b => exact h
  | tabToTab c b => exact h

/- ## §2. The induction -/

/-- **`RaiseSwaps` FROM A READ-SAFE WINDOW.**  Structurally
`R12.raiseSwaps_of_read` (`Orig2/Fork/Class/ForkReadBracket.lean:675`): each window
letter is read-safe, hence `ReadOK` at the state where it fires, hence
survives `CanRaise c` and supplies the two-letter swap datum. -/
theorem raiseSwaps_of_readSafe {Q v : State} {z : Card} {γ β : List Move}
    (hQwf : Q.WF)
    (hplay : ShufflePlayW Q (γ ++ Move.tabToFound z :: β) v)
    (hcan : CanRaise Q z)
    (hread : ∀ q ∈ γ, ReadSafe z q) : RaiseSwaps Q z γ := by
  induction γ generalizing Q v β with
  | nil => exact raiseSwaps_nil Q z
  | cons q γ' ih =>
      rw [List.cons_append] at hplay
      obtain ⟨R, hrevq, hstepq, hplayR⟩ := Bubble.walk_cons_inv hplay
      have hreadq : ReadSafe z q := hread q (List.mem_cons_self ..)
      have hok : R12.ReadOK z q := readOK_of_readSafe hrevq hreadq
      have hcanR : CanRaise R z :=
        R12.canRaise_survives_read hQwf hstepq hrevq hok hcan
      have hhead := R12.local_swap_of_read hQwf hcan hrevq hok
      have hrest : RaiseSwaps R z γ' :=
        ih (step_wf hQwf hstepq) hplayR hcanR
          (fun x hx => hread x (List.mem_cons_of_mem q hx))
      exact R12.raiseSwaps_cons hstepq hhead hrest

/- ## §3. The target -/

/-- **THE TARGET — `KeepsForward` ON READ-SAFE WINDOWS.**  In the user's
`R12.ReadOK` spelling; note that `ReadOK z (tabToTab w b)` is literally
`w ≠ z ∧ b ≠ Sum.inr z`, i.e. the S3 "no slide headed by `c`, no slide landing
on `c`" clause.  No `WF`-of-`u`, no bare-top, no empty-tail, no `NoSlide`
hypothesis is used. -/
theorem keepsForward_readsafe_slide
    {F v : State} {c : Card} {γ β : List Move}
    (hF : F.WF) (hcan : CanRaise F c)
    (hplay : ShufflePlayW F (γ ++ Move.tabToFound c :: β) v)
    (hread : ∀ q ∈ γ, R12.ReadOK c q) :
    RaiseSwaps F c γ :=
  R12.raiseSwaps_of_read hF hplay hcan hread

/-- **THE `htop` HYPOTHESIS OF THE TARGET IS FREE.**  `CanRaise st c` already
says `c` is a pile top (`pileOfTop` searches pile TOPS, i.e. the last face-up
card of a pile), so "nothing above it" is not extra data. -/
theorem pileTop_of_canRaise {st : State} {c : Card} (h : CanRaise st c) :
    ∃ a, st.pileOfTop c = some a :=
  h.2.imp (fun a ha => ha.1)

/-- **THE TARGET, prose spelling.**  `hread` = "no pull/raise in `c`'s suit,
no letter landing on `c`"; `hslide` = "no slide headed by `c` and no slide
landing on `c`".  Together they are exactly `ReadSafe c` on every letter. -/
theorem keepsForward_readsafe_slide_noslide
    {F v : State} {c : Card} {γ β : List Move}
    (hF : F.WF) (hcan : CanRaise F c)
    (hplay : ShufflePlayW F (γ ++ Move.tabToFound c :: β) v)
    (hraise : ∀ w : Card, Move.tabToFound w ∈ γ → w.suit ≠ c.suit)
    (hpull : ∀ (x : Card) (b : Base), Move.foundToTab x b ∈ γ →
      x.suit ≠ c.suit ∧ b ≠ Sum.inr c)
    (hslide : ∀ (w : Card) (b : Base), Move.tabToTab w b ∈ γ →
      w ≠ c ∧ b ≠ Sum.inr c) :
    RaiseSwaps F c γ := by
  refine raiseSwaps_of_readSafe hF hplay hcan ?_
  intro q hq
  cases q with
  | draw => exact trivial
  | wasteToFound x => exact trivial
  | wasteToTab x b => exact trivial
  | tabToFound w => exact hraise w hq
  | foundToTab x b => exact hpull x b hq
  | tabToTab w b => exact hslide w b hq

/- ## §4. The `RaiseSwaps` image and the bubble -/

/-- The window lemma, read-safe spelling. -/
theorem raise_moves_left_readsafe
    {Q v : State} {c : Card} {γ β : List Move}
    (hQ : Q.WF) (hcan : CanRaise Q c)
    (hplay : ShufflePlayW Q (γ ++ Move.tabToFound c :: β) v)
    (hread : ∀ q ∈ γ, ReadSafe c q) :
    ShufflePlayW Q (Move.tabToFound c :: (γ ++ β)) v :=
  RaiseLeft.raise_moves_left_window hplay
    (raiseSwaps_of_readSafe hQ hplay hcan hread)

/- ## §5. The S3 clause is necessary (and the carry clause is not)

Two kernel-checked sanity rows, refining the user's expected argument. -/

/-- **A SLIDE HEADED BY `c` CAN NEVER FOLLOW `raise c`.**  So no `RaiseSwaps`
datum can contain it, and the S3 clause of `ReadSafe` is genuinely required.
This is `R12.no_slide_self_at` in the interface used here. -/
theorem raise_not_before_own_slide {Q : State} {c : Card} {b : Base}
    (hQwf : Q.WF) :
    ¬ ∃ e, ShufflePlayW Q [Move.tabToFound c, Move.tabToTab c b] e :=
  R12.no_slide_self_at hQwf

/-- **ANY WINDOW THAT OPENS WITH A SLIDE OF `c` IS NOT A `RaiseSwaps` DATUM.**
Kernel form of the previous row at the certificate level
(`R12.slide_self_not_mem_of_raiseSwaps`, `Orig2/Fork/Class/ForkReadBracket.lean:795`). -/
theorem no_raiseSwaps_of_slide_self_head {Q : State} {c : Card} {b : Base}
    {rest : List Move} (hQwf : Q.WF)
    (hsw : RaiseSwaps Q c (Move.tabToTab c b :: rest)) : False :=
  R12.slide_self_not_mem_of_raiseSwaps hQwf hsw rfl (Walk.nil Q)

/-- **A SLIDE WHOSE SEGMENT CARRIES THE RAISE CARD NEEDS NO BARE-TOP
HYPOTHESIS.**  `R12.raise_swap_slide` fires with only `w ≠ c` and
`b ≠ Sum.inr c`: the run `fromCard w faceUp` may well contain `c` (as its top
card) — the raise then CHOPS the run at `c`
(`CommuteStep.step_comm_slide_raise`, `Orig2/Fork/Local/ForkCommuteSlide.lean:1015`),
and the two orders still land together.  This is the whole "carries `c`"
case, discharged unconditionally. -/
theorem raiseSwaps_slide_carrying {S : State} {c w : Card} {b : Base}
    (hS : S.WF) (hcan : CanRaise S c) (hwc : w ≠ c) (hbc : b ≠ Sum.inr c)
    (hrev : reversibleAtW S (Move.tabToTab w b)) :
    ∃ e, ShufflePlayW S [Move.tabToFound c, Move.tabToTab w b] e ∧
         S.run [Move.tabToTab w b, Move.tabToFound c] = some e :=
  R12.raise_swap_slide hS hcan hwc hbc hrev

/-- `fromCard` never changes the last card of the list it reads from. -/
theorem lastOf_fromCard_of_mem {c : Card} :
    ∀ {l : List Card}, c ∈ l → lastOf (fromCard c l) = lastOf l
  | [], h => absurd h List.not_mem_nil
  | x :: t, h => by
      by_cases hx : x = c
      · rw [fromCard, ite_eq_left hx]
      · have hct : c ∈ t := by
          rcases List.mem_cons.mp h with h' | h'
          · exact absurd h'.symm hx
          · exact h'
        have htne : t ≠ [] := by
          intro ht
          rw [ht] at hct
          exact List.not_mem_nil hct
        rw [fromCard, ite_eq_right hx,
          show lastOf (x :: t) = lastOf t from by
            cases t with
            | nil => exact absurd rfl htne
            | cons y u => rfl]
        exact lastOf_fromCard_of_mem hct

/-- **THE ACTUAL CONTENT OF `segment_containing_bare_top` (true, unused).**
If `c` is the top of its pile and a slide is headed by a different card `w`
holding in that same pile, then the moved segment carries `c` — i.e. `c` is
the LAST card written at the slide's target (the pile top is the last card of
the pile, and `fromCard` preserves the last card).  This is the shape the
expected argument calls the crux.  It is NOT needed: §5's
`raiseSwaps_slide_carrying` already discharges the case it was meant to
cover, and the bare-top hypothesis (`hpa`, `c` is a pile top) is not consumed
by the slide/raise square at all. -/
theorem segment_carrying_top {st : State} {c w : Card} {a : Anchor}
    (hpa : st.pileOfTop c = some a) (hwa : st.pileHolding w = some a) :
    lastOf (fromCard w (st.piles a).faceUp) = some c := by
  rw [lastOf_fromCard_of_mem (pileHolding_mem hwa)]
  exact (pileOfTop_top hpa).2

end SlideFwd

#print axioms SlideFwd.readOK_of_readSafe
#print axioms SlideFwd.raiseSwaps_of_readSafe
#print axioms SlideFwd.keepsForward_readsafe_slide
#print axioms SlideFwd.pileTop_of_canRaise
#print axioms SlideFwd.keepsForward_readsafe_slide_noslide
#print axioms SlideFwd.raise_moves_left_readsafe
#print axioms SlideFwd.raise_not_before_own_slide
#print axioms SlideFwd.no_raiseSwaps_of_slide_self_head
#print axioms SlideFwd.raiseSwaps_slide_carrying
#print axioms SlideFwd.lastOf_fromCard_of_mem
#print axioms SlideFwd.segment_carrying_top

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-
# Temp/SlideFwd_Chain — the empty-tail chain from the read-safe residual

READ-ONLY scratch (no source edits, no commit).  Zero `sorry`, zero
`Classical.choice`, no `native_decide`; battery at the tail.

## What is proved here

* `KeepsForwardRead` — the `RaiseLeft.KeepsForward` shape restricted to
  READ-SAFE windows — is a THEOREM, not a residual
  (`keepsForwardRead_unconditional`, from `SlideFwd.raiseSwaps_of_readSafe`).
* `EmptyTailReadWindow` — the single geometric residual left: at an
  empty-tail split, the window `raise d ++ γ` preceding an occurrence of
  `raise c` in the pull-free right leg is read-safe for `c`.  This is the
  user's `hread`/`hnoslide` hypothesis, stated once at the split.
* `noEmptyTail_of_readWindow`, `splitBlock_of_readWindow`,
  `satDifferForkWF_of_readWindow` — the whole campaign chain from that
  residual, with NO other change from `RaiseLeft.noEmptyTail_of_keepsForward`.
* `emptyTail_raiseSafe`, `emptyTail_window_auto` (next file) — everything in
  `EmptyTailReadWindow` EXCEPT the "no slide headed by `c`" clause follows
  from `SplitHyp` + `MountainSplit`; the residual is therefore exactly
  "no slide of `c` before the raise", `NoSelfSlide`.
-/

namespace SlideFwd

open NonforkKit
open SplitKit

/- ## §1. `KeepsForward`, read-safe windows only — unconditional -/

/-- **`KeepsForwardRead F c`** — the `RaiseLeft.KeepsForward` shape with the
window restricted to letters that avoid `c`.  Unlike `KeepsForward`, this IS
free: see `keepsForwardRead_unconditional`. -/
def KeepsForwardRead (F : State) (c : Card) : Prop :=
  ∀ (γ β : List Move) (v : State),
    ShufflePlayW F (γ ++ Move.tabToFound c :: β) v →
    (∀ q ∈ γ, ReadSafe c q) → RaiseSwaps F c γ

/-- **THE READ-SAFE RESIDUAL IS NOT A RESIDUAL.**  For every `WF`, `CanRaise`
pair the restricted certificate holds unconditionally. -/
theorem keepsForwardRead_unconditional (F : State) (c : Card)
    (hF : F.WF) (hcan : CanRaise F c) : KeepsForwardRead F c :=
  fun γ β v hplay hread => raiseSwaps_of_readSafe hF hplay hcan hread

/-- The restricted `RaiseLeftAcrossTailLen` shape: bubbling across a
read-safe window. -/
theorem raise_moves_left_of_keepsForwardRead
    {F v : State} {c : Card} {γ β : List Move}
    (hF : F.WF) (hcan : CanRaise F c)
    (hplay : ShufflePlayW F (γ ++ Move.tabToFound c :: β) v)
    (hread : ∀ q ∈ γ, ReadSafe c q) :
    ShufflePlayW F (Move.tabToFound c :: (γ ++ β)) v :=
  raise_bubble γ hplay (keepsForwardRead_unconditional F c hF hcan γ β v hplay hread)

/- ## §2. The split-level residual -/

/-- **`EmptyTailReadWindow` — THE REMAINING RESIDUAL.**  At an empty-tail
split, there is an occurrence of `raise c` in the tail whose window (headed by
the split's own `raise d`) is read-safe for `c`: no pull/raise in `c`'s suit,
no letter landing on `c`, no slide headed by `c`. -/
def EmptyTailReadWindow : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → post = [] →
    ∃ (γ β : List Move),
      tail = γ ++ Move.tabToFound c :: β ∧
      (∀ q ∈ Move.tabToFound d :: γ, ReadSafe c q)

/- ## §3. The empty-tail contradiction -/

/-- **`NoEmptyTail` FROM THE READ-SAFE WINDOW RESIDUAL.**  Identical to
`RaiseLeft.noEmptyTail_of_keepsForward` except that the bubble's window
certificate comes from `KeepsForwardRead` + `EmptyTailReadWindow` instead of
`RaiseLeftAcrossTailLen`. -/
theorem noEmptyTail_of_readWindow
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hwin : EmptyTailReadWindow) :
    BlockKit.NoEmptyTail := by
  intro u v ρ F left right c d b pre post tail h hpost
  have hkeep := h
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  -- the empty-tail window, read-safe by the residual
  obtain ⟨γ, β, htail, hread⟩ :=
    hwin u v ρ F left right c d b pre post tail hkeep hpost
  -- the green facts at the bottom
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hcanF : CanRaise F c := BlockKit.emptyTail_canRaise hkeep hpost
  -- the right leg, written with the split tail
  have hrightD : ShufflePlayW F (Move.tabToFound d :: tail) v := by
    rw [hrightShape] at hright
    exact hright
  rw [htail] at hrightD
  rw [hpost] at hshape
  -- bubble `raise c` to the front of `raise d :: γ`
  have hsw : RaiseSwaps F c (Move.tabToFound d :: γ) :=
    keepsForwardRead_unconditional F c hFwf hcanF (Move.tabToFound d :: γ) β v
      hrightD hread
  have hbubble : ShufflePlayW F (Move.tabToFound c :: (Move.tabToFound d :: γ) ++ β) v :=
    raise_bubble (Move.tabToFound d :: γ) hrightD hsw
  -- the pull's origin
  have hleft' : ShufflePlayW u (pre ++ [Move.foundToTab c b]) F := by
    rw [← hshape]
    simpa using hleft
  obtain ⟨A', hpre, hrest⟩ :=
    ValleyElim.ShufflePlayW_split hleft' pre [Move.foundToTab c b] rfl
  have hstepPull : State.step A' (Move.foundToTab c b) = some F :=
    Elim.step_of_singleton hrest
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hstepRaise : State.step F (Move.tabToFound c) = some A' :=
    step_tabToFound_of_foundToTab hA' hstepPull
  -- the rearranged play, with the adjacent identity pair at the seam
  have hnew : ShufflePlayW u
      (pre ++ Move.foundToTab c b :: Move.tabToFound c ::
        ((Move.tabToFound d :: γ) ++ β)) v := by
    have h := ShufflePlayW_append hleft' hbubble
    simpa [List.append_assoc] using h
  -- delete the pair
  obtain ⟨ρ', hρ'play, hρ'len⟩ :=
    LiveKit.identity_pair_delete (u := u) (v := v)
      (ρ := pre ++ Move.foundToTab c b :: Move.tabToFound c ::
        ((Move.tabToFound d :: γ) ++ β))
      (α := pre) (β := (Move.tabToFound d :: γ) ++ β)
      (m1 := Move.foundToTab c b) (m2 := Move.tabToFound c)
      (A := A') (T := F) hnew rfl hpre ⟨hstepPull, hstepRaise⟩
  -- the lengths agree
  have hlenLeft : left.length = pre.length + 1 := by
    rw [hshape]
    simp
  have hlenRight : right.length = tail.length + 1 := by
    rw [hrightShape]
    simp
  have hlenTail : ((Move.tabToFound d :: γ) ++ β).length = tail.length := by
    rw [htail]
    simp only [List.length_cons, List.length_append] at *
    omega
  have hlenEq :
      (pre ++ Move.foundToTab c b :: Move.tabToFound c ::
        ((Move.tabToFound d :: γ) ++ β)).length = ρ.length := by
    rw [hρ, hshape, hrightShape, htail]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [hlenEq] at hρ'len
  exact absurd hρ'len (Nat.not_lt.mpr (hmin ρ' hρ'play))

/- ## §4. `SplitBlock` and the campaign chain -/

/-- **`SplitBlock` FROM THE READ-SAFE WINDOW RESIDUAL AND THE COVER HALF.** -/
theorem splitBlock_of_readWindow
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hwin : EmptyTailReadWindow) (hcov : BlockKit.TailCovers) :
    SplitBlock :=
  BlockKit.splitBlock_of_parts (noEmptyTail_of_readWindow hl hms hwin) hcov

/-- **THE CAMPAIGN CHAIN FROM THE READ-SAFE WINDOW RESIDUAL.** -/
theorem satDifferForkWF_of_readWindow
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hwin : EmptyTailReadWindow) (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  BlockKit.satDifferForkWF_of_livePair_parts hl
    (noEmptyTail_of_readWindow hl hms hwin) hcov hmin

end SlideFwd

#print axioms SlideFwd.keepsForwardRead_unconditional
#print axioms SlideFwd.raise_moves_left_of_keepsForwardRead
#print axioms SlideFwd.noEmptyTail_of_readWindow
#print axioms SlideFwd.splitBlock_of_readWindow
#print axioms SlideFwd.satDifferForkWF_of_readWindow

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-
# Temp/SlideFwd_Residual — the exact reduced residual: no slide of `c`

READ-ONLY scratch (no source edits, no commit).  Zero `sorry`, zero
`Classical.choice`, no `native_decide`; battery at the tail.

## What is proved

`EmptyTailReadWindow` (`Temp/SlideFwd_Chain.lean`) asks that the empty-tail
window before an occurrence of `raise c` be `ReadSafe c`.  Here it is
DECOMPOSED, clause by clause:

* `emptyTail_window_soft` — from `SplitHyp` + `MountainSplit` + the twin
  identity `d = c.twin`, the FIRST occurrence of `raise c` in the tail has a
  window which is read-safe in EVERY clause except "the slide is not headed by
  `c`":
  - no pull in `c`'s suit: the right leg is pull-free (`MountainSplit`);
  - no raise in `c`'s suit: a raise in `c`'s suit is `raise c`
    (`readSafe_raise_of_canRaise_same_suit`), and the occurrence chosen is the
    FIRST one (`raise_or_slide_onto_first`);
  - no slide landing on `c`: a reversible slide onto `c` would need its mover
    seated on `c.twin`, which is foundational along the pull-free leg
    (`EmptyTail.twin_no_coverSlide`), applied through
    `tailCoverSlide_of_letter`;
  - no pull at all: `MountainSplit`.
* `EmptyTailNoSelfSlide` — the exact residual: the window never contains a
  slide headed by `c`.
* `emptyTailReadWindow_of_noSelfSlide` — the residual implies
  `EmptyTailReadWindow`, hence (chain file) `NoEmptyTail` ⇒ `SplitBlock` ⇒
  `SatDifferForkWF`.

The residual is irreducible: §`raise_not_before_own_slide` shows a slide of
`c` can never be moved past `raise c`, so a window containing one admits no
`RaiseSwaps` datum at all.
-/

namespace SlideFwd

open NonforkKit
open SplitKit

/- ## §1. The soft predicate and the first-occurrence partner -/

/-- **`ReadSafeNoSelfHead z q`** — `ReadSafe z q` with the S3 clause (the
slide is not headed by `z`) dropped from slides.  This isolates the one clause
that is *not* automatic in the empty-tail regime. -/
def ReadSafeNoSelfHead (z : Card) (q : Move) : Prop :=
  match q with
  | Move.tabToTab _ b => b ≠ Sum.inr z
  | _ => ReadSafe z q

theorem readSafe_of_noSelfHead {z : Card} {q : Move}
    (h : ReadSafeNoSelfHead z q)
    (hself : ∀ (w : Card) (b : Base), q = Move.tabToTab w b → w ≠ z) :
    ReadSafe z q := by
  cases q with
  | draw => exact h
  | wasteToFound x => exact h
  | wasteToTab x b => exact h
  | tabToFound x => exact h
  | foundToTab x b => exact h
  | tabToTab w b => exact ⟨hself w b rfl, h⟩

/-- **`NoSlideOf c γ`** — no letter of the window is a slide HEADED by `c`. -/
def NoSlideOf (c : Card) (γ : List Move) : Prop :=
  ∀ (w : Card) (b : Base), Move.tabToTab w b ∈ γ → w ≠ c

/-- **`RaisePartnerFirst l c`** — an occurrence of `raise c` with no earlier
one in the window. -/
def RaisePartnerFirst (l : List Move) (c : Card) : Prop :=
  ∃ (γ δ : List Move), l = γ ++ Move.tabToFound c :: δ ∧
    ∀ q ∈ γ, q ≠ Move.tabToFound c

theorem raisePartnerFirst_cons {m : Move} {ρ : List Move} {c : Card}
    (hm : m ≠ Move.tabToFound c) (h : RaisePartnerFirst ρ c) :
    RaisePartnerFirst (m :: ρ) c := by
  obtain ⟨γ, δ, hγ, hq⟩ := h
  refine ⟨m :: γ, δ, by rw [hγ]; rfl, ?_⟩
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hm
  · exact hq x hx'

/-- **A RAISE IN `c`'s SUIT IS `c`.**  Two `CanRaise` cards of the same suit
sit at the same foundation height, hence are equal.  (The row used inside
`EmptyTail.raise_or_slide_onto`.) -/
theorem readSafe_raise_of_canRaise_same_suit {st : State} {x c : Card}
    (hx : CanRaise st x) (hc : CanRaise st c) (hsu : x.suit = c.suit) :
    x = c := by
  have h1 : x.rank.toIdx = (st.found x.suit).length := by
    simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hx.1
  have h2 : c.rank.toIdx = (st.found c.suit).length := by
    simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hc.1
  have hr : x.rank = c.rank := Rank.toIdx_inj (by rw [h1, h2, hsu])
  cases x with
  | mk xs xr => cases c with | mk cs cr => simp_all

/-- **THE DICHOTOMY WITH A FIRST OCCURRENCE.**  `EmptyTail.raise_or_slide_onto`
with the raise branch sharpened to its first occurrence (which is what makes
the window before the raise raise-free in `c`'s suit).  The proof is the same
induction; only the raise branch and the cons-lifting carry the extra data. -/
theorem raise_or_slide_onto_first {Q W : State} {ρ : List Move} {c : Card}
    (hplay : ShufflePlayW Q ρ W) :
    ∀ (hQ : Q.WF), CanRaise Q c → (∀ m ∈ ρ, ¬ Bubble.IsPull m) →
      RaisePartnerFirst ρ c ∨ EmptyTail.TailCoverSlide Q W ρ c ∨ CanRaise W c := by
  induction hplay with
  | nil st =>
      intro _ hcan _
      exact Or.inr (Or.inr hcan)
  | @cons st s₁ W m ρ' hrev hstep hrest ih =>
      intro hQ hcan hno
      have hnohead : ¬ Bubble.IsPull m := hno m (List.mem_cons_self ..)
      have hnotail : ∀ m' ∈ ρ', ¬ Bubble.IsPull m' :=
        fun m' hm' => hno m' (List.mem_cons_of_mem m hm')
      cases m with
      | draw =>
          have hcan₁ : CanRaise s₁ c := R12.canRaise_survives_draw hstep hcan
          rcases ih (step_wf hQ hstep) hcan₁ hnotail with h | h | h
          · exact Or.inl (raisePartnerFirst_cons (by intro hh; cases hh) h)
          · exact Or.inr (Or.inl (EmptyTail.tailCoverSlide_cons hrev hstep h))
          · exact Or.inr (Or.inr h)
      | wasteToFound x => exact absurd hrev (wasteToFound_not_reversibleAtW st x)
      | wasteToTab x b' => exact absurd hrev (wasteToTab_not_reversibleAtW st x b')
      | foundToTab x b' => exact absurd ⟨x, b', rfl⟩ hnohead
      | tabToFound x =>
          by_cases hsu : x.suit = c.suit
          · -- the letter is a raise in `c`'s suit, hence it IS `raise c`
            have hxcan : CanRaise st x :=
              Bridge.canRaise_of_reversible_raise hQ hrev
            have hx : x = c :=
              readSafe_raise_of_canRaise_same_suit hxcan hcan hsu
            rw [hx]
            exact Or.inl ⟨[], ρ', rfl, by intro q hq; exact absurd hq (by simp)⟩
          · have hxw : x ≠ c := fun h => hsu (by rw [h])
            have hcan₁ : CanRaise s₁ c :=
              R12.canRaise_survives_raise hQ hstep hsu hxw hcan
            have hm : Move.tabToFound x ≠ Move.tabToFound c := by
              intro hh
              have hxc : x = c := by injection hh
              exact hsu (by rw [hxc])
            rcases ih (step_wf hQ hstep) hcan₁ hnotail with h | h | h
            · exact Or.inl (raisePartnerFirst_cons hm h)
            · exact Or.inr (Or.inl (EmptyTail.tailCoverSlide_cons hrev hstep h))
            · exact Or.inr (Or.inr h)
      | tabToTab x b' =>
          by_cases hxc : x = c
          · have hcan₁ : CanRaise s₁ c := by
              have h1 : CanRaise s₁ x :=
                EmptyTail.canRaise_survives_own_slide (c := x) hQ hstep hrev (hxc ▸ hcan)
              exact hxc ▸ h1
            have hm : Move.tabToTab x b' ≠ Move.tabToFound c := by
              intro hh; cases hh
            rcases ih (step_wf hQ hstep) hcan₁ hnotail with h | h | h
            · exact Or.inl (raisePartnerFirst_cons hm h)
            · exact Or.inr (Or.inl (EmptyTail.tailCoverSlide_cons hrev hstep h))
            · exact Or.inr (Or.inr h)
          · by_cases hbase : b' = Sum.inr c
            · subst hbase
              exact Or.inr (Or.inl
                ⟨x, [], ρ', st, s₁, rfl, Walk.nil st, hrev, hstep, hrest⟩)
            · have hcan₁ : CanRaise s₁ c :=
                R12.canRaise_survives_slide hQ hstep hrev hxc hbase hcan
              have hm : Move.tabToTab x b' ≠ Move.tabToFound c := by
                intro hh; cases hh
              rcases ih (step_wf hQ hstep) hcan₁ hnotail with h | h | h
              · exact Or.inl (raisePartnerFirst_cons hm h)
              · exact Or.inr (Or.inl (EmptyTail.tailCoverSlide_cons hrev hstep h))
              · exact Or.inr (Or.inr h)

/- ## §2. A helper row -/

/-- **A SLIDE LANDING ON `c`, FOUND ANYWHERE IN A PLAY, IS A
`TailCoverSlide`.**  Read off the split at its position. -/
theorem tailCoverSlide_of_letter {Q W : State} {ρ : List Move} {c : Card}
    (hplay : ShufflePlayW Q ρ W) :
    ∀ (pre : List Move) {x : Card} (rest : List Move),
      ρ = pre ++ Move.tabToTab x (Sum.inr c) :: rest →
      EmptyTail.TailCoverSlide Q W ρ c := by
  induction hplay with
  | nil st =>
      intro pre x rest h
      cases pre with
      | nil => exact absurd h (by simp)
      | cons a as => exact absurd h (by simp)
  | @cons st s₁ W m ρ' hrev hstep hrest ih =>
      intro pre x rest h
      cases pre with
      | nil =>
          simp only [List.nil_append] at h
          injection h with hm hrest'
          subst hm
          subst hrest'
          exact ⟨x, [], ρ', st, s₁, rfl, Walk.nil st, hrev, hstep, hrest⟩
      | cons a as =>
          simp only [List.cons_append] at h
          injection h with ha htail
          subst ha
          exact EmptyTail.tailCoverSlide_cons hrev hstep
            (ih as (x := x) (rest := rest) htail)

/- ## §3. The window, minus one clause -/

/-- **THE WINDOW IS READ-SAFE EXCEPT FOR SLIDES HEADED BY `c`.**  At an
empty-tail split the FIRST `raise c` of the pull-free right leg has a window
which satisfies every clause of `ReadSafe c` except the S3 head clause. -/
theorem emptyTail_window_soft
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = [])
    (hms : MountainKit.MountainSplit left right) (htwin : d = c.twin) :
    ∃ (γ β : List Move),
      tail = γ ++ Move.tabToFound c :: β ∧
      (∀ q ∈ γ, q ≠ Move.tabToFound c) ∧
      (∀ q ∈ Move.tabToFound d :: γ, ReadSafeNoSelfHead c q) := by
  have hkeep := h
  obtain ⟨huwf, -, hsv, -, -, -, -, hleft, hright, hshape, hfree, hrightShape⟩ := h
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hcanF : CanRaise F c := BlockKit.emptyTail_canRaise hkeep hpost
  have hnopullRight : ∀ m ∈ right, ¬ Bubble.IsPull m := hms.2
  have hnopullTail : ∀ m ∈ tail, ¬ Bubble.IsPull m := by
    intro m hm hpull
    exact hnopullRight m (by rw [hrightShape]; exact List.mem_cons_of_mem _ hm) hpull
  rw [hrightShape] at hright
  obtain ⟨G, hstep, htail⟩ : ∃ G : State,
      State.step F (Move.tabToFound d) = some G ∧ ShufflePlayW G tail v := by
    cases hright with
    | cons _ hs hrest => exact ⟨_, hs, hrest⟩
  have hsu : d.suit ≠ c.suit := by
    rw [htwin]; exact EmptyTail.twin_suit_ne c.suit
  have hdw : d ≠ c := by
    rw [htwin]; exact SplitKit.card_twin_ne c
  have hcanG : CanRaise G c :=
    R12.canRaise_survives_raise hFwf hstep hsu hdw hcanF
  have hGwf : G.WF := step_wf hFwf hstep
  have hfoundG : ∃ σ, c.twin ∈ G.found σ := by
    obtain ⟨-, ap, hpa, hs⟩ := step_tabToFound_inv hstep
    have hs2 : G = raiseSt F d ap := hs
    refine ⟨d.suit, ?_⟩
    rw [hs2, raiseSt_found_apply, ite_eq_left rfl, htwin]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  rcases raise_or_slide_onto_first htail hGwf hcanG hnopullTail with
    hpart | hcov | hcanV
  · obtain ⟨γ, β, htailEq, hfirst⟩ := hpart
    refine ⟨γ, β, htailEq, hfirst, ?_⟩
    -- the head letter
    have hhead : ReadSafeNoSelfHead c (Move.tabToFound d) := hsu
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hqγ
    · exact hhead
    · -- a window letter
      obtain ⟨γ₁, γ₂, hγ⟩ := RaiseLeft.exists_split_mem hqγ
      have htailSplit : tail = γ₁ ++ q :: (γ₂ ++ Move.tabToFound c :: β) := by
        rw [htailEq, hγ]
        simp only [List.cons_append, List.append_assoc]
      have hplaySplit : ShufflePlayW G (γ₁ ++ q :: (γ₂ ++ Move.tabToFound c :: β)) v :=
        htailSplit ▸ htail
      obtain ⟨mid, hpre, hrestPlay⟩ := Bubble.walk_split γ₁ hplaySplit
      obtain ⟨mid', hrevq, hstepq, hrestTail⟩ := Bubble.walk_cons_inv hrestPlay
      have hmidwf : mid.WF := SatDifferCensus.ShufflePlayW.wf_end hpre hGwf
      have hnomem : Move.tabToFound c ∉ γ₁ := by
        intro hm
        exact hfirst _ (by rw [hγ]; exact List.mem_append_left _ hm) rfl
      have hcanMid : CanRaise mid c :=
        RaiseLeft.canRaise_mid_of_no_raise_before (G := G) (ρ := tail) (c := c)
          hGwf hcanG hnopullTail hfoundG γ₁ mid q
          (γ₂ ++ Move.tabToFound c :: β) htailSplit.symm hpre hnomem
      cases q with
      | draw => exact trivial
      | wasteToFound x => exact trivial
      | wasteToTab x b' => exact trivial
      | tabToFound x =>
          have hxcan : CanRaise mid x :=
            Bridge.canRaise_of_reversible_raise hmidwf hrevq
          by_cases hsux : x.suit = c.suit
          · exfalso
            have hxc : x = c :=
              readSafe_raise_of_canRaise_same_suit hxcan hcanMid hsux
            subst hxc
            exact hfirst _ hqγ rfl
          · exact hsux
      | foundToTab x b' =>
          exfalso
          have hmem : Move.foundToTab x b' ∈ tail := by
            rw [htailEq, hγ]
            exact List.mem_append_left _
              (List.mem_append_right γ₁ (List.mem_cons_self ..))
          exact hnopullTail _ hmem ⟨x, b', rfl⟩
      | tabToTab x b' =>
          intro hb
          subst hb
          exact (EmptyTail.twin_no_coverSlide hGwf htail hnopullTail hfoundG)
            (tailCoverSlide_of_letter htail γ₁ (x := x)
              (rest := γ₂ ++ Move.tabToFound c :: β) htailSplit)
  · exact absurd hcov (EmptyTail.twin_no_coverSlide hGwf htail hnopullTail hfoundG)
  · exact absurd hcanV (ValleyElim.no_raise_of_saturated hsv c)

/- ## §4. The exact residual -/

/-- **`EmptyTailNoSelfSlide` — THE EXACT REMAINING RESIDUAL.**  At an
empty-tail split, the window preceding the first `raise c` of the tail
contains no slide HEADED by `c`.

`emptyTailReadWindow_of_noSelfSlide` / `emptyTailNoSelfSlide_of_readWindow`
below show that this is EXACTLY `EmptyTailReadWindow`: no clause of
`ReadSafe` beyond this one is owed by the split geometry
(`emptyTail_window_soft`).  It cannot be dropped: a window containing
`Move.tabToTab c b` before `raise c` admits no `RaiseSwaps` datum, because
`[raise c, tabToTab c b]` is never a play
(`SlideFwd.raise_not_before_own_slide`) and no certificate can open with it
(`SlideFwd.no_raiseSwaps_of_slide_self_head`). -/
def EmptyTailNoSelfSlide : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move) (γ β : List Move),
    SplitHyp u v ρ F left right c d b pre post tail → post = [] →
    tail = γ ++ Move.tabToFound c :: β →
    (∀ q ∈ γ, q ≠ Move.tabToFound c) →
    NoSlideOf c γ

/-- **THE FIRST-OCCURRENCE DECOMPOSITION IS UNIQUE.**  If `m` occurs in both
given splits at the displayed position and is absent from both prefixes, the
prefixes agree. -/
theorem first_decomp_unique {m : Move} :
    ∀ {γ₁ β₁ γ₂ β₂ : List Move},
      γ₁ ++ m :: β₁ = γ₂ ++ m :: β₂ →
      (∀ q ∈ γ₁, q ≠ m) → (∀ q ∈ γ₂, q ≠ m) → γ₁ = γ₂
  | [], _, [], _, _, _, _ => rfl
  | [], _, a :: as, _, heq, _, h₂ => by
      simp only [List.nil_append, List.cons_append] at heq
      exact absurd ((List.cons.inj heq).1).symm (h₂ a (List.mem_cons_self ..))
  | a :: as, _, [], _, heq, h₁, _ => by
      simp only [List.nil_append, List.cons_append] at heq
      exact absurd ((List.cons.inj heq).1) (h₁ a (List.mem_cons_self ..))
  | a :: as, β₁, a' :: as', β₂, heq, h₁, h₂ => by
      simp only [List.cons_append] at heq
      have haa : a = a' := (List.cons.inj heq).1
      have htl : as ++ m :: β₁ = as' ++ m :: β₂ := (List.cons.inj heq).2
      subst haa
      rw [first_decomp_unique htl
        (fun q hq => h₁ q (List.mem_cons_of_mem a hq))
        (fun q hq => h₂ q (List.mem_cons_of_mem a hq))]

/-- **THE RESIDUAL SUFFICES.** -/
theorem emptyTailReadWindow_of_noSelfSlide
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hres : EmptyTailNoSelfSlide) :
    EmptyTailReadWindow := by
  intro u v ρ F left right c d b pre post tail h hpost
  have htwin : d = c.twin := EmptyTail.twin_of_livePair_emptyTail hl h hpost
  obtain ⟨γ, β, htail, hfirst, hsoft⟩ :=
    emptyTail_window_soft h hpost
      (hms u v ρ F left right c d b pre post tail h) htwin
  refine ⟨γ, β, htail, ?_⟩
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hqγ
  · exact hsoft _ (List.mem_cons_self ..)
  · have hs := hsoft q (List.mem_cons_of_mem _ hqγ)
    have hns : NoSlideOf c γ :=
      hres u v ρ F left right c d b pre post tail γ β h hpost htail hfirst
    exact readSafe_of_noSelfHead hs (fun w b' hqeq =>
      hns w b' (hqeq ▸ hqγ))

/-- **THE RESIDUAL IS EXACT**: `EmptyTailReadWindow` implies it, so nothing
but the self-slide clause is owed. -/
theorem emptyTailNoSelfSlide_of_readWindow (h : EmptyTailReadWindow) :
    EmptyTailNoSelfSlide := by
  intro u v ρ F left right c d b pre post tail γ β hsp hpost htail hfirst
  obtain ⟨γ', β', htail', hread⟩ :=
    h u v ρ F left right c d b pre post tail hsp hpost
  -- `ReadSafe c (raise c)` is false, so `γ'` is also first-occurrence
  have hfirst' : ∀ q ∈ γ', q ≠ Move.tabToFound c := by
    intro q hq hqeq
    subst hqeq
    exact (hread _ (List.mem_cons_of_mem _ hq)) rfl
  have hγγ : γ = γ' :=
    first_decomp_unique (by rw [← htail, ← htail']) hfirst hfirst'
  intro w bw hmem
  have hmem' : Move.tabToTab w bw ∈ γ' := by rw [← hγγ]; exact hmem
  exact (hread _ (List.mem_cons_of_mem _ hmem')).1

/- ## §5. The chain from the exact residual -/

/-- **`NoEmptyTail` FROM THE EXACT RESIDUAL.** -/
theorem noEmptyTail_of_noSelfSlide
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hres : EmptyTailNoSelfSlide) :
    BlockKit.NoEmptyTail :=
  noEmptyTail_of_readWindow hl hms (emptyTailReadWindow_of_noSelfSlide hl hms hres)

/-- **`SplitBlock` FROM THE EXACT RESIDUAL AND THE COVER HALF.** -/
theorem splitBlock_of_noSelfSlide
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hres : EmptyTailNoSelfSlide) (hcov : BlockKit.TailCovers) :
    SplitBlock :=
  splitBlock_of_readWindow hl hms
    (emptyTailReadWindow_of_noSelfSlide hl hms hres) hcov

/-- **THE CAMPAIGN CHAIN FROM THE EXACT RESIDUAL.** -/
theorem satDifferForkWF_of_noSelfSlide
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hres : EmptyTailNoSelfSlide) (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_readWindow hl hms
    (emptyTailReadWindow_of_noSelfSlide hl hms hres) hcov hmin

end SlideFwd

#print axioms SlideFwd.readSafe_of_noSelfHead
#print axioms SlideFwd.raisePartnerFirst_cons
#print axioms SlideFwd.raise_or_slide_onto_first
#print axioms SlideFwd.readSafe_raise_of_canRaise_same_suit
#print axioms SlideFwd.tailCoverSlide_of_letter
#print axioms SlideFwd.emptyTail_window_soft
#print axioms SlideFwd.first_decomp_unique
#print axioms SlideFwd.emptyTailReadWindow_of_noSelfSlide
#print axioms SlideFwd.emptyTailNoSelfSlide_of_readWindow
#print axioms SlideFwd.noEmptyTail_of_noSelfSlide
#print axioms SlideFwd.splitBlock_of_noSelfSlide
#print axioms SlideFwd.satDifferForkWF_of_noSelfSlide
