import Orig2.ForkNonfork
import Orig2.ForkEmptyTail
import Orig2.ForkLivePair
import Orig2.ForkTailCover

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkRaiseLeft — `RaiseLeftAcrossTail`, its residual, and the
empty-tail contradiction

READ-ONLY scratch (no source edits, no commit).  Zero `sorry`, zero
`Classical.choice`, no `native_decide`; battery at the tail.

## The campaign step this card closes

At an empty-tail split (`post = []`) of a minimal play:

```text
  the turn is          pull c ; raise d      with d = c.twin   (twin_of_livePair_emptyTail)
  `raise c` EXISTS in the tail, unconditionally               (twin_raisePartner)
  the raise bubbles to the FRONT of the tail                  (§2, §3)
  ⇒ `pull c ; raise c` is an adjacent IdentityPair            (LiveKit.pull_raise_identity_pair)
  ⇒ a strictly shorter play exists                            (LiveKit.identity_pair_delete)
  ⇒ contradicts shortest-ness                                 (SplitHyp's hmin)
  ⇒ NoEmptyTail ⇒ (with TailCovers) SplitBlock ⇒ SatDifferForkWF.
```

The bubble itself is `NonforkKit.raise_bubble` (`Orig2/ForkNonfork.lean:101`),
which needs neither `WF` nor `NoSlide`: everything the bubble consumes is the
per-position certificate `RaiseSwaps`.

## What is unconditional here

* §2 `raise_moves_left_window` — the bubble, given the certificate.
* §5 `raise_moves_left_one_raise` / `raise_moves_left_of_raises` — the TARGET,
  unconditionally, for windows of raises of suits other than `c`'s (the
  per-position datum is `raise_swap_raise`).
* §4 `noEmptyTail_of_keepsForward`, `splitBlock_of_keepsForward`,
  `satDifferForkWF_of_keepsForward` — the whole empty-tail chain, from the
  NAMED residual `KeepsForward` (§3) and `BlockKit.TailCovers`.

## The residual, and why it is a residual

`KeepsForward F c` asks, for every window `γ` preceding an occurrence of
`raise c` in a witness play out of `F`, for the certificate `RaiseSwaps F c γ`.
Obligation (iii) of the left-bubble — "the window letter `q` is legal at the
raise's IMAGE" — is NOT a consequence of legality at the origin.  §6 proves
both halves of the obstruction exactly:

* a pull of a card of `c`'s suit kills `c`'s `nextUp` at its landing
  (`nextUp_false_of_pull_same_suit`), so `mid.run [q, raise c]` does not exist
  there (`not_canRaise_of_pull_same_suit`);
* after `raise c` the foundation top of `c`'s suit IS `c`
  (`foundTop_raiseSt_self`), so the swapped word `[raise c, pull x b]` does not
  exist either (`step_foundToTab_raiseSt_same_suit`).

So the residual is genuinely non-removable in this form; §5 shows it is
nevertheless discharged on the raise-only windows, and `RaiseSwaps` is never
vacuous where `RaiseLeftAcrossTail` is needed in that regime.
-/

namespace RaiseLeft

open SplitKit
open NonforkKit

/-! ## §0. List algebra -/

theorem exists_split_mem {l : List Move} {a : Move} (h : a ∈ l) :
    ∃ pre post : List Move, l = pre ++ a :: post := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons b t ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨[], t, rfl⟩
      · obtain ⟨pre, post, hp⟩ := ih h'
        exact ⟨b :: pre, post, by rw [hp]; rfl⟩

theorem length_window (γ β : List Move) (c : Card) :
    (γ ++ β).length + 1 = (γ ++ Move.tabToFound c :: β).length := by
  simp only [List.length_append, List.length_cons]
  omega

/-- `chop` drops exactly one card. -/
theorem length_chop (l : List Card) : (chop l).length = l.length - 1 := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      cases t with
      | nil => rfl
      | cons y u =>
          simp only [chop, List.length_cons] at ih ⊢
          omega

/-! ## §1. The target statements -/

/-- **THE TARGET**: a raise occurrence can be moved to the FRONT of the tail
of a witness play, at the same total length, whenever it is raisable at the
start. -/
def RaiseLeftAcrossTail : Prop :=
  ∀ (F v : State) (c : Card) (tail : List Move),
    F.WF → CanRaise F c → ShufflePlayW F tail v → Move.tabToFound c ∈ tail →
      ∃ tail' : List Move, ShufflePlayW F (Move.tabToFound c :: tail') v

/-- **THE LENGTH-PRESERVING FORM**: exactly what feeds
`LiveKit.identity_pair_delete` (`Orig2/ForkLivePair.lean:291`) at an
empty-tail split. -/
def RaiseLeftAcrossTailLen : Prop :=
  ∀ (F v : State) (c : Card) (tail : List Move),
    F.WF → CanRaise F c → ShufflePlayW F tail v → Move.tabToFound c ∈ tail →
      ∃ tail' : List Move, ShufflePlayW F (Move.tabToFound c :: tail') v ∧
        tail'.length + 1 = tail.length

theorem raiseLeft_of_len (h : RaiseLeftAcrossTailLen) : RaiseLeftAcrossTail :=
  fun F v c tail hF hc hp hm => by
    obtain ⟨t', hp', _⟩ := h F v c tail hF hc hp hm
    exact ⟨t', hp'⟩

/-! ## §2. The window lemma -/

/-- **THE WINDOW LEMMA.**  `raise c` moves to the front of the window `γ` in
`γ ++ raise c :: β`, once the per-position certificate `RaiseSwaps` holds.
This is `NonforkKit.raise_bubble` (`Orig2/ForkNonfork.lean:101`), which needs
neither `WF` nor `NoSlide`. -/
theorem raise_moves_left_window {Q v : State} {c : Card} {γ β : List Move}
    (hplay : ShufflePlayW Q (γ ++ Move.tabToFound c :: β) v)
    (hsw : RaiseSwaps Q c γ) :
    ShufflePlayW Q (Move.tabToFound c :: (γ ++ β)) v :=
  raise_bubble γ hplay hsw

/-! ## §3. The named residual -/

/-- **`KeepsForward F c` — THE RESIDUAL.**  Every window `γ` that precedes an
occurrence of `raise c` in a witness play out of `F` satisfies the
per-position swap certificate.  At a position `mid` of `γ` reached by a
prefix, with next letter `q`, this asks for both
`mid --raise c--> · --q--> e` as a witness play and
`mid --q--> · --raise c--> e`.

The obstruction (§6) is obligation (iii): `q` legal at the raise's IMAGE. -/
def KeepsForward (F : State) (c : Card) : Prop :=
  ∀ (γ β : List Move) (v : State),
    ShufflePlayW F (γ ++ Move.tabToFound c :: β) v → RaiseSwaps F c γ

/-- **THE RESIDUAL IMPLIES THE TARGET.** -/
theorem raise_moves_left_of_keepsForward
    (h : ∀ (F : State) (c : Card), F.WF → CanRaise F c → KeepsForward F c) :
    RaiseLeftAcrossTailLen := by
  intro F v c tail hF hc hp hm
  obtain ⟨γ, β, hsplit⟩ := exists_split_mem hm
  rw [hsplit] at hp
  refine ⟨γ ++ β, raise_moves_left_window hp (h F c hF hc γ β v hp), ?_⟩
  rw [hsplit]
  exact length_window γ β c

/-! ## §4. The empty-tail contradiction and the campaign chain -/

/-- **`NoEmptyTail` FROM THE RAISE BUBBLE.**  At an empty-tail split of a
shortest play, the bottom is the both-raisable twin pair; the raise `raise c`
must occur in the (pull-free) tail, and bubbling it to the FRONT of
`raise d :: tail` makes `pull c ; raise c` adjacent.  That pair is an
identity pair, so the play strictly shortens — impossible. -/
theorem noEmptyTail_of_keepsForward
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hrt : RaiseLeftAcrossTailLen) :
    BlockKit.NoEmptyTail := by
  intro u v ρ F left right c d b pre post tail h hpost
  have hkeep := h
  obtain ⟨huwf, hsu, hsv, hplay, hsplitAt, hmin, hρ, hleft, hright, hshape,
    hfree, hrightShape⟩ := h
  -- the empty-tail bottom is the twin pair
  have htwin : d = c.twin := EmptyTail.twin_of_livePair_emptyTail hl hkeep hpost
  -- and the raise partner `raise c` occurs in the pull-free tail
  have hpart : EmptyTail.RaisePartner tail c :=
    EmptyTail.twin_raisePartner hkeep hpost
      (hms u v ρ F left right c d b pre post tail hkeep) htwin
  obtain ⟨γ, β, htail⟩ := hpart
  -- the green facts at the bottom
  have hFwf : F.WF := SatDifferCensus.ShufflePlayW.wf_end hleft huwf
  have hcanF : CanRaise F c := BlockKit.emptyTail_canRaise hkeep hpost
  -- the right leg, written with the split tail
  have hrightD : ShufflePlayW F (Move.tabToFound d :: tail) v := by
    rw [hrightShape] at hright
    exact hright
  rw [htail] at hrightD
  rw [hpost] at hshape
  -- bubble `raise c` to the front
  have hmem : Move.tabToFound c ∈
      Move.tabToFound d :: (γ ++ Move.tabToFound c :: β) :=
    List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self ..))
  obtain ⟨tail', htail'play, htail'len⟩ :=
    hrt F v c (Move.tabToFound d :: (γ ++ Move.tabToFound c :: β))
      hFwf hcanF hrightD hmem
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
      (pre ++ Move.foundToTab c b :: Move.tabToFound c :: tail') v := by
    have h := ShufflePlayW_append hleft' htail'play
    simpa [List.append_assoc] using h
  -- delete the pair
  obtain ⟨ρ', hρ'play, hρ'len⟩ :=
    LiveKit.identity_pair_delete (u := u) (v := v)
      (ρ := pre ++ Move.foundToTab c b :: Move.tabToFound c :: tail')
      (α := pre) (β := tail')
      (m1 := Move.foundToTab c b) (m2 := Move.tabToFound c)
      (A := A') (T := F) hnew rfl hpre ⟨hstepPull, hstepRaise⟩
  -- the lengths agree
  have hlenLeft : left.length = pre.length + 1 := by
    rw [hshape]
    simp
  have hlenRight : right.length = tail.length + 1 := by
    rw [hrightShape]
    simp
  have hlenTail : tail'.length = tail.length := by
    have hh := htail'len
    rw [htail]
    simp only [List.length_cons, List.length_append] at hh ⊢
    omega
  have hlenEq :
      (pre ++ Move.foundToTab c b :: Move.tabToFound c :: tail').length = ρ.length := by
    rw [hρ]
    simp only [List.length_append, List.length_cons]
    omega
  rw [hlenEq] at hρ'len
  exact absurd hρ'len (Nat.not_lt.mpr (hmin ρ' hρ'play))

/-- **`SplitBlock` FROM THE COVER HALF AND THE RESIDUAL.** -/
theorem splitBlock_of_keepsForward
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hrt : RaiseLeftAcrossTailLen) (hcov : BlockKit.TailCovers) :
    SplitBlock :=
  BlockKit.splitBlock_of_parts (noEmptyTail_of_keepsForward hl hms hrt) hcov

/-- **THE CAMPAIGN CHAIN.**  `SplitLivePair` + the mountain split + the
raise residual + the cover half + shortest-play existence give
`SatDifferForkWF`. -/
theorem satDifferForkWF_of_keepsForward
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hrt : RaiseLeftAcrossTailLen) (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  BlockKit.satDifferForkWF_of_livePair_parts hl
    (noEmptyTail_of_keepsForward hl hms hrt) hcov hmin

/-- The same chain, stated with the pointwise window residual `KeepsForward`. -/
theorem satDifferForkWF_of_keepsForwardWin
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (h : ∀ (F : State) (c : Card), F.WF → CanRaise F c → KeepsForward F c)
    (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  satDifferForkWF_of_keepsForward hl hms
    (raise_moves_left_of_keepsForward h) hcov hmin

/-! ## §5. Unconditional instances of the target

Two genuine discharges of the residual, and of the target itself. -/

/-- **THE TARGET, UNCONDITIONALLY, FOR A ONE-RAISE WINDOW.**  A window
consisting of a single raise of a DIFFERENT suit is a `RaiseSwaps` datum
(`NonforkKit.raiseSwaps_single_raise`, `Orig2/ForkNonfork.lean:319`). -/
theorem raise_moves_left_one_raise
    {Q v : State} {c w : Card} {β : List Move}
    (hQ : Q.WF) (hc : CanRaise Q c) (hw : CanRaise Q w) (hsu : c.suit ≠ w.suit)
    (hplay : ShufflePlayW Q (Move.tabToFound w :: Move.tabToFound c :: β) v) :
    ∃ tail' : List Move, ShufflePlayW Q (Move.tabToFound c :: tail') v ∧
      tail'.length + 1 = (Move.tabToFound w :: Move.tabToFound c :: β).length := by
  obtain ⟨E, htwo, -⟩ :=
    ValleyElim.ShufflePlayW_split hplay [Move.tabToFound w, Move.tabToFound c] β rfl
  have hsw : RaiseSwaps Q c [Move.tabToFound w] :=
    raiseSwaps_single_raise hQ hc hw hsu htwo
  refine ⟨Move.tabToFound w :: β, raise_bubble [Move.tabToFound w] hplay hsw, ?_⟩
  simp only [List.length_cons]

/-- **THE RESIDUAL HOLDS ON A WINDOW OF RAISES IN OTHER SUITS.**  Induct over
the window: at each position `raise w` (with `w.suit ≠ c.suit`) the state is
`WF`, both `c` and `w` are raisable, and `raise_swap_raise`
(`Orig2/ForkNonfork.lean:276`) supplies exactly the two-conjunct datum
`RaiseSwaps` asks for; `R12.canRaise_survives_raise` keeps `CanRaise c`. -/
theorem raiseSwaps_of_raises :
    ∀ (γ : List Move) {Q v : State} {c : Card} {β : List Move},
      Q.WF → CanRaise Q c →
      (∀ m ∈ γ, ∃ w : Card, m = Move.tabToFound w ∧ w.suit ≠ c.suit) →
      ShufflePlayW Q (γ ++ Move.tabToFound c :: β) v →
      RaiseSwaps Q c γ := by
  intro γ
  induction γ with
  | nil =>
      intro Q v c β _ _ _ _
      exact raiseSwaps_nil Q c
  | cons a as ih =>
      intro Q v c β hQ hc hall hplay
      obtain ⟨w, rfl, hsu⟩ := hall a (List.mem_cons_self ..)
      have hall' : ∀ m ∈ as, ∃ w : Card, m = Move.tabToFound w ∧ w.suit ≠ c.suit :=
        fun m hm => hall m (List.mem_cons_of_mem (Move.tabToFound w) hm)
      obtain ⟨s1, hrev_a, hstep_a, hrest⟩ := Bubble.walk_cons_inv hplay
      have hs1wf : s1.WF := step_wf hQ hstep_a
      have hw : CanRaise Q w := Bridge.canRaise_of_reversible_raise hQ hrev_a
      have hwc : w ≠ c := fun h => hsu (by rw [h])
      have hc1 : CanRaise s1 c :=
        R12.canRaise_survives_raise hQ hstep_a hsu hwc hc
      have hsw_as : RaiseSwaps s1 c as := ih hs1wf hc1 hall' hrest
      obtain ⟨e0, hswap0, hrun0⟩ := raise_swap_raise hQ hc hw (Ne.symm hsu)
      intro pre mid q rest hsplit hpre
      cases pre with
      | nil =>
          simp only [List.nil_append] at hsplit
          injection hsplit with hq hrest'
          subst hq
          subst hrest'
          have hmid : mid = Q := by
            have h := Walk_run (fun st m => reversibleAtW st m) hpre
            exact Option.some.inj (h.symm.trans rfl)
          subst hmid
          exact ⟨e0, hswap0, hrun0⟩
      | cons a' pre' =>
          simp only [List.cons_append] at hsplit
          injection hsplit with ha' htl
          subst ha'
          obtain ⟨m1, hrev1, hstep1, hpre'⟩ := Bubble.walk_cons_inv hpre
          have hm1 : m1 = s1 := Option.some.inj (hstep1.symm.trans hstep_a)
          subst hm1
          exact hsw_as pre' mid q rest htl hpre'

/-- **THE TARGET, UNCONDITIONALLY, ON A RAISE WINDOW.** -/
theorem raise_moves_left_of_raises {Q v : State} {c : Card} {γ β : List Move}
    (hQ : Q.WF) (hc : CanRaise Q c)
    (hall : ∀ m ∈ γ, ∃ w : Card, m = Move.tabToFound w ∧ w.suit ≠ c.suit)
    (hplay : ShufflePlayW Q (γ ++ Move.tabToFound c :: β) v) :
    ShufflePlayW Q (Move.tabToFound c :: (γ ++ β)) v :=
  raise_bubble γ hplay (raiseSwaps_of_raises γ hQ hc hall hplay)

/-- **`KeepsForward`, DISCHARGED FOR RAISE-ONLY WINDOWS.** -/
theorem keepsForward_of_raise_letters {F : State} {c : Card}
    (hF : F.WF) (hc : CanRaise F c)
    (hall : ∀ (γ β : List Move) (v : State),
      ShufflePlayW F (γ ++ Move.tabToFound c :: β) v →
      ∀ m ∈ γ, ∃ w : Card, m = Move.tabToFound w ∧ w.suit ≠ c.suit) :
    KeepsForward F c :=
  fun γ β v hplay => raiseSwaps_of_raises γ hF hc (hall γ β v hplay) hplay

/-! ## §6. The exact obstruction — why the residual is a residual -/

/-- **A PULL OF `c`'s SUIT KILLS `c`'s `nextUp`.**  The pull removes the
foundation top (so the foundation is nonempty and `chop` drops one card),
while `c`'s next-up rank stays put. -/
theorem not_nextUp_of_pull_same_suit {st w : State} {c x : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab x b) = some w)
    (hx : x.suit = c.suit) (hnext : st.nextUp c = true) :
    ¬ (w.nextUp c = true) := by
  obtain ⟨c', hft, hc', hcp, hs⟩ := step_foundToTab_inv hstep
  have hnextIdx : c.rank.toIdx = (st.found c.suit).length := by
    simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hnext
  have hxmem : x ∈ st.found x.suit := by
    rw [hc'] at hft
    exact lastOf_mem (l := st.found x.suit) (by simpa [State.foundTop] using hft)
  have hposx : 1 ≤ (st.found x.suit).length := by
    cases hf : st.found x.suit with
    | nil => rw [hf] at hxmem; exact absurd hxmem List.not_mem_nil
    | cons y t => simp
  have hpos : 1 ≤ (st.found c.suit).length := by
    rw [← hx]
    exact hposx
  have hfoundW : w.found c.suit = chop (st.found c.suit) := by
    rw [hs, putCard_found, ← hx, setFound_found_self]
  have hlen : (w.found c.suit).length = (st.found c.suit).length - 1 := by
    rw [hfoundW, length_chop]
  intro hw
  have h2 : c.rank.toIdx = (w.found c.suit).length := by
    simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hw
  rw [hlen] at h2
  omega

/-- **THE OBSTRUCTION (ii)**: a pull of a card of `c`'s suit destroys `c`'s
vanilla raisability at its landing, so `mid.run [q, raise c]` fails there. -/
theorem not_canRaise_of_pull_same_suit {st w : State} {c x : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab x b) = some w)
    (hx : x.suit = c.suit) (hcan : CanRaise st c) :
    ¬ CanRaise w c := by
  intro hw
  exact not_nextUp_of_pull_same_suit hstep hx hcan.1 hw.1

/-- **AFTER `raise c` THE FOUNDATION TOP OF `c`'s SUIT IS `c`.** -/
theorem foundTop_raiseSt_self (u : State) (c : Card) (a : Anchor) :
    (raiseSt u c a).foundTop c.suit = some c := by
  simp [State.foundTop, raiseSt_found_apply, lastOf_snoc]

/-- **THE OBSTRUCTION (iii)**: at the raise's IMAGE, a pull of a DIFFERENT card
of `c`'s suit no longer fires — the foundation top of that suit is now `c`.
So the swapped word `[raise c, pull x b]` cannot exist. -/
theorem step_foundToTab_raiseSt_same_suit (S : State) (c x : Card) (a : Anchor)
    (b : Base) (hx : x.suit = c.suit) (hxc : x ≠ c) :
    State.step (raiseSt S c a) (Move.foundToTab x b) = none := by
  rw [step_foundToTab_eq]
  have htop : (raiseSt S c a).foundTop x.suit = some c := by
    rw [hx]; exact foundTop_raiseSt_self S c a
  rw [htop]
  have hdec : decide (c = x) = false :=
    decide_false_of_not (fun h => hxc h.symm)
  simp [hdec]

/-! ## §7. Obligation (i) is FREE in the empty-tail twin regime

In the empty-tail case the right leg is PULL-FREE and `c.twin` sits in the
foundation (it was raised at the head of the leg), so no slide can land on `c`
(`EmptyTail.twin_no_coverSlide`).  Hence `raise_or_slide_onto` gives
`CanRaise c` at EVERY prefix state of the window — the first obligation of the
bubble costs nothing there. -/

theorem raisePartner_mem {l : List Move} {c : Card}
    (h : EmptyTail.RaisePartner l c) : Move.tabToFound c ∈ l := by
  obtain ⟨γ, δ, hγ⟩ := h
  rw [hγ]
  exact List.mem_append_right _ (List.mem_cons_self ..)

/-- **OBLIGATION (i) IS FREE.**  Along a pull-free window whose origin has
`c.twin` in the foundation, at every prefix state before the first `raise c`
the card `c` is still vanilla-raisable. -/
theorem canRaise_mid_of_no_raise_before
    {G : State} {ρ : List Move} {c : Card}
    (hG : G.WF) (hcan : CanRaise G c)
    (hnopull : ∀ m ∈ ρ, ¬ Bubble.IsPull m)
    (hfoundTwin : ∃ σ, c.twin ∈ G.found σ) :
    ∀ (pre : List Move) (mid : State) (q : Move) (rest : List Move),
      pre ++ q :: rest = ρ → ShufflePlayW G pre mid →
      Move.tabToFound c ∉ pre → CanRaise mid c := by
  intro pre mid q rest hsplit hpre hnomem
  have hnopullPre : ∀ m ∈ pre, ¬ Bubble.IsPull m := by
    intro m hm hp
    exact hnopull m (by rw [← hsplit]; exact List.mem_append_left _ hm) hp
  rcases EmptyTail.raise_or_slide_onto hpre hG hcan hnopullPre with h | h | h
  · exact absurd (raisePartner_mem h) hnomem
  · exact absurd h (EmptyTail.twin_no_coverSlide hG hpre hnopullPre hfoundTwin)
  · exact h

/-! ## §8. The forward half of the certificate

`RaiseSwaps` asks for BOTH orders; `Bubble.bubble_raise_left`
(`Orig2/ForkBubble.lean:207`) asks only for the forward word `raise c ; q`, at
the price of slide-freedom on the window.  Obligation (i) being free (§7), the
forward half is what an empty-tail residual really has to pay for. -/

/-- **THE FORWARD HALF** of the per-position certificate. -/
def SwapsForward (Q : State) (c : Card) (γ : List Move) : Prop :=
  ∀ (pre : List Move) (mid : State) (q : Move) (rest : List Move),
    pre ++ q :: rest = γ → ShufflePlayW Q pre mid →
    ∃ e, ShufflePlayW mid [Move.tabToFound c, q] e

theorem raiseSwaps_imp_forward {Q : State} {c : Card} {γ : List Move}
    (h : RaiseSwaps Q c γ) : SwapsForward Q c γ :=
  fun pre mid q rest hsplit hpre => (h pre mid q rest hsplit hpre).imp fun _ h' => h'.1

/-- **THE WINDOW LEMMA, FORWARD FORM.**  Slide-free windows only; the price the
weaker (`RaiseSwaps`-free) residual pays. -/
theorem raise_moves_left_window_noslide
    {Q v : State} {c : Card} {γ β : List Move}
    (hQ : Q.WF)
    (hnsl : ∀ m ∈ γ, CommuteStep.NoSlide m)
    (hplay : ShufflePlayW Q (γ ++ Move.tabToFound c :: β) v)
    (hfw : SwapsForward Q c γ) :
    ShufflePlayW Q (Move.tabToFound c :: (γ ++ β)) v :=
  Bubble.bubble_raise_left γ hQ hnsl
    (Bubble.noSlide_of_isRaise ⟨c, rfl⟩) hplay hfw

end RaiseLeft

/-! ## §7. Battery -/

#print axioms RaiseLeft.exists_split_mem
#print axioms RaiseLeft.length_window
#print axioms RaiseLeft.length_chop
#print axioms RaiseLeft.raiseLeft_of_len
#print axioms RaiseLeft.raise_moves_left_window
#print axioms RaiseLeft.raise_moves_left_of_keepsForward
#print axioms RaiseLeft.noEmptyTail_of_keepsForward
#print axioms RaiseLeft.splitBlock_of_keepsForward
#print axioms RaiseLeft.satDifferForkWF_of_keepsForward
#print axioms RaiseLeft.satDifferForkWF_of_keepsForwardWin
#print axioms RaiseLeft.raise_moves_left_one_raise
#print axioms RaiseLeft.raiseSwaps_of_raises
#print axioms RaiseLeft.raise_moves_left_of_raises
#print axioms RaiseLeft.keepsForward_of_raise_letters
#print axioms RaiseLeft.not_nextUp_of_pull_same_suit
#print axioms RaiseLeft.not_canRaise_of_pull_same_suit
#print axioms RaiseLeft.foundTop_raiseSt_self
#print axioms RaiseLeft.step_foundToTab_raiseSt_same_suit
#print axioms RaiseLeft.raisePartner_mem
#print axioms RaiseLeft.canRaise_mid_of_no_raise_before
#print axioms RaiseLeft.raiseSwaps_imp_forward
#print axioms RaiseLeft.raise_moves_left_window_noslide
