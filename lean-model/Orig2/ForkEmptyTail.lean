import Orig2.ForkNormalizeTail
import Orig2.ForkReadBracket
import Orig2.ForkMountain
import Orig2.ForkMechanism

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2.ForkEmptyTail — the empty-tail case of `SplitKit.SplitBlock`

READ-ONLY scratch card (no source edits, no commit).  Zero `sorry`, zero
`Classical.choice`, zero `native_decide`.

## Contents

1. **§1 — the residual carries no reordering content.**
   `BlockKit.EmptyTailPartners` (`Orig2/ForkNormalizeTail.lean:44`) follows
   from two pure OCCURRENCE statements: a `pull d` inside `pre`, and a
   `raise c` inside `tail`.  `emptyTailPartners_of_occurrences` assembles the
   normalizer's decomposition from the two occurrences by list algebra
   alone.  So the whole content of the residual is *existence*.

2. **§2 — `CanRaise` persistence.**  A `ReadOK c` letter
   (`Orig2/ForkReadBracket.lean:589`) keeps `CanRaise c` (`R12`'s survival
   rows), and a reversible slide of `c` itself keeps it too
   (`canRaise_survives_own_slide`).  Hence along a PULL-FREE play
   (`MountainKit.MountainSplit`'s right leg) `CanRaise c` can only be
   destroyed by `raise c` or by a slide LANDING on `c`
   (`raise_or_slide_onto`).  This is the exact "the cover may live in the
   tail" dichotomy.
3. **§3 — the twin case.**  If `d = c.twin`, the cover-slide branch is
   impossible: a reversible slide onto `c` needs its mover to sit on
   `c.twin` (`Mech.mover_seat_twin_of_slide_into_card`), but `c.twin` is
   raised at the first letter of the right leg and the tail is pull-free, so
   `c.twin` stays in the foundation and can never carry a mover
   (`mem_found_unique`).  Hence **the raise partner `raise c` exists
   unconditionally in the twin case** (`twin_raisePartner`).

4. **§4 — the assembled reductions.**
   `SplitLivePair` confines the bottom's live set to `{d, d.twin}`; `c` is
   live at the bottom and `c ≠ d`, so in the empty-tail case `d = c.twin`
   *unconditionally* (`twin_of_livePair_emptyTail`).  Combined with §3 this
   makes the raise half of `BlockKit.EmptyTailPartners` free, leaving only the
   `pull d` occurrence (`emptyTailPartners_of_livePair_pull`), and gives the
   reduction chain `… → NoEmptyTail → SplitBlock → SatDifferForkWF`.

5. **§5 — where the pull partner comes from.**
   `pullPartner_of_found` : the pull occurrence is exactly what "`d` was in
   `u`'s foundation" produces.  There is no other source: the pull-free tail
   can never pull, and a pull of `d` after the split's own pull would be
   outside `pre`.

## The honest boundary

`NoEmptyTail` itself is NOT proved.  §4 shows the empty-tail case *is* the
twin case (`d = c.twin`), so §3 rules out the tail-cover branch entirely; what
remains is the `pull d` occurrence, which `pullPartner_of_found` shows needs
`d ∈ u.found`.  That is not a consequence of `SplitHyp`'s hypotheses: the
census (`Temp/EmptyTail_probe.py`, 658 canonical splits of unit-shortest
saturated→saturated plays) finds **0** plays in which `d` is pulled at all,
while `d = c.twin` in 658/658.  So `EmptyTailPartners` is the wrong residual
for the empty-tail corner: it demands a letter the plays do not contain.  The
corner has to be *handled* (the bottom is the both-raisable twin pair, exactly
the `BlockMin` relaxed route), not excluded through the normalizer.
See `Temp/EmptyTail_Report.md`.
-/

open ValleyElim
open CommuteStep
open SplitKit

namespace EmptyTail

/-! ## §1. The residual is two occurrence statements -/

/-- A `pull d` inside `pre` (the letters before the split's own pull). -/
def PullPartner (pre : List Move) (d : Card) : Prop :=
  ∃ (α β : List Move) (bd : Base), pre = α ++ Move.foundToTab d bd :: β

/-- A `raise c` inside `tail` (the letters after the split's own raise). -/
def RaisePartner (tail : List Move) (c : Card) : Prop :=
  ∃ (γ δ : List Move), tail = γ ++ Move.tabToFound c :: δ

/-- The normalizer's decomposition, written once. -/
def PartnerDecomp (ρ : List Move) (c d : Card) (b : Base) : Prop :=
  ∃ (α β γ δ ε : List Move) (bd : Base),
    ρ = α ++ [Move.foundToTab d bd] ++ β ++
        [Move.foundToTab c b, Move.tabToFound d] ++ γ ++
        [Move.tabToFound c] ++ δ ++ ε

/-- **THE RESIDUAL IS EXISTENCE ONLY.**  The two occurrences that
`BlockKit.EmptyTailPartners` asks for assemble the normalizer's decomposition
by list algebra; no reordering condition hides inside the residual. -/
theorem emptyTailPartners_of_occurrences
    (hpull : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail → post = [] →
      PullPartner pre d)
    (hraise : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail → post = [] →
      RaisePartner tail c) :
    BlockKit.EmptyTailPartners := by
  intro u v ρ F left right c d b pre post tail hsplit hpost
  obtain ⟨α, β, bd, hpre⟩ := hpull u v ρ F left right c d b pre post tail hsplit hpost
  obtain ⟨γ, δ, htail⟩ := hraise u v ρ F left right c d b pre post tail hsplit hpost
  obtain ⟨-, -, -, -, -, -, hρ, -, -, hshape, -, hrightShape⟩ := hsplit
  refine ⟨α, β, γ, δ, [], bd, ?_⟩
  rw [hρ, hshape, hrightShape, hpre, htail, hpost]
  simp only [List.cons_append, List.nil_append, List.append_nil,
    List.append_assoc]

/-- The empty-tail split's play as an explicit word (the shape the two
occurrence statements live on). -/
theorem emptyTail_play_shape
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = []) :
    ρ = pre ++ Move.foundToTab c b :: Move.tabToFound d :: tail := by
  obtain ⟨-, -, -, -, -, -, hρ, -, -, hshape, -, hrightShape⟩ := h
  rw [hρ, hshape, hrightShape, hpost]
  simp

/-! ## §2. `CanRaise` persistence -/

/-- **A `ReadOK` letter keeps `CanRaise`.**  Direct induction on the
witness play using `R12.canRaise_survives_read`
(`Orig2/ForkReadBracket.lean:628`). -/
theorem canRaise_persists_readok {st w : State} {ρ : List Move} {z : Card}
    (h : ShufflePlayW st ρ w) :
    ∀ (hst : st.WF), CanRaise st z → (∀ m ∈ ρ, R12.ReadOK z m) →
      CanRaise w z := by
  induction h with
  | nil st => intro _ hcan _; exact hcan
  | @cons st s₁ W m ρ' hrev hstep hrest ih =>
      intro hst hcan hok
      exact ih (step_wf hst hstep)
        (R12.canRaise_survives_read hst hstep hrev
          (hok m (List.mem_cons_self ..)) hcan)
        (fun m' hm' => hok m' (List.mem_cons_of_mem m hm'))

/-- The `chop` of two nonempty lists is nonempty. -/
theorem chop_append_ne_nil {l₁ l₂ : List Card} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    chop (l₁ ++ l₂) ≠ [] := by
  cases l₁ with
  | nil => exact absurd rfl h₁
  | cons x t =>
      cases t with
      | nil =>
          cases l₂ with
          | nil => exact absurd rfl h₂
          | cons y u => intro hc; cases hc
      | cons y u => intro hc; cases hc

/-- **A REVERSIBLE SLIDE OF `c` ITSELF KEEPS `c` RAISABLE.**  `c` is a pile
top, so the slide relocates the singleton run above `c`; its `nextUp` is
untouched (`slideSt_found`), it still tops the target pile
(`slideSt_pileOfTop_source`), and the seat clause survives (a nonempty target
run gives a `chop`, an empty target gives a bare king because the slide was
licenced). -/
theorem canRaise_survives_own_slide {st s' : State} {c : Card} {b : Base}
    (hst : st.WF) (hstep : State.step st (Move.tabToTab c b) = some s')
    (hrev : reversibleAtW st (Move.tabToTab c b)) (h : CanRaise st c) :
    CanRaise s' c := by
  obtain ⟨hnext, a, hpa, -⟩ := h
  obtain ⟨aD, k, hholdD, hcp, hk, hak, hface, hrunv, hcell⟩ :=
    CommuteStep.slide_data hst hrev
  have hhold : st.pileHolding c = some a :=
    Drain.pileHolding_of_pileOfTop hst hpa
  have haD : aD = a := Option.some.inj (hholdD.symm.trans hhold)
  have hpaD : st.pileOfTop c = some aD := by rw [haD]; exact hpa
  obtain ⟨a', hh, hcp', hne', hs⟩ := CommuteStep.step_tabToTab_slideSt hstep
  have ha' : a' = aD := Option.some.inj (hh.symm.trans hholdD)
  have hsD : s' = CommuteStep.slideSt st c b aD := by rw [hs, ha']
  have hnext' : s'.nextUp c = st.nextUp c := by
    rw [hsD]
    unfold State.nextUp State.foundHeight
    rw [CommuteStep.slideSt_found]
  have htop' : s'.pileOfTop c = some k := by
    rw [hsD]
    exact CommuteStep.slideSt_pileOfTop_source hst hcp hk hak hrunv hcell hpaD
  have hseat' : chop (s'.piles k).faceUp ≠ [] ∨
      ((s'.piles k).hidden = [] ∧ c.rank = Rank.king) := by
    rw [hsD, CommuteStep.slideSt_piles_target hst hcp hk hak hcell]
    cases b with
    | inl j =>
        obtain ⟨hemp, hking⟩ := canPlace_inl hcp
        obtain ⟨hhid, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
        have hjk : j = k := Option.some.inj hk
        subst hjk
        exact Or.inr ⟨hhid, hking⟩
    | inr z =>
        obtain ⟨kk, hz, -⟩ := canPlace_inr hcp
        have hkk : k = kk := by
          have h1 : CommuteStep.tgt st (Sum.inr z) = some kk := hz
          rw [hk] at h1
          exact Option.some.inj h1
        refine Or.inl ?_
        apply chop_append_ne_nil
        · intro hnil
          have hmem : z ∈ (st.piles k).faceUp := by
            have := lastOf_mem (pileOfTop_top hz).2
            rw [hkk]
            exact this
          rw [hnil] at hmem
          exact List.not_mem_nil hmem
        · exact hrunv
  exact ⟨by rw [hnext']; exact hnext, k, htop', hseat'⟩

/-- **FOUNDATION MEMBERSHIP IS MONOTONE ALONG A PULL-FREE PLAY.** -/
theorem found_mem_of_no_pull {a b : State} {ρ : List Move} {c : Card} {σ : Suit}
    (h : ShufflePlayW a ρ b) :
    ∀ (hm : c ∈ a.found σ), (∀ m ∈ ρ, ¬ Bubble.IsPull m) →
      ∃ σ', c ∈ b.found σ' := by
  induction h with
  | nil st => intro hm _; exact ⟨σ, hm⟩
  | @cons st s₁ W m ρ' hrev hstep hrest ih =>
      intro hm hno
      have htail : ∀ m' ∈ ρ', ¬ Bubble.IsPull m' :=
        fun m' hm' => hno m' (List.mem_cons_of_mem m hm')
      have hmhead : ¬ Bubble.IsPull m := hno m (List.mem_cons_self ..)
      cases m with
      | draw =>
          exact ih (by rw [stepDraw_found hstep]; exact hm) htail
      | wasteToFound x =>
          exact absurd hrev (wasteToFound_not_reversibleAtW st x)
      | wasteToTab x b' =>
          exact absurd hrev (wasteToTab_not_reversibleAtW st x b')
      | foundToTab x b' => exact absurd ⟨x, b', rfl⟩ hmhead
      | tabToFound x =>
          obtain ⟨-, ap, hpa, hs⟩ := step_tabToFound_inv hstep
          have hs2 : s₁ = raiseSt st x ap := hs
          refine ih ?_ htail
          rw [hs2, raiseSt_found_apply]
          by_cases hσ : σ = x.suit
          · rw [ite_eq_left hσ, ← hσ]
            exact List.mem_append.mpr (Or.inl hm)
          · rw [ite_eq_right hσ]
            exact hm
      | tabToTab x b' =>
          obtain ⟨ap, -, -, -, hs⟩ := step_tabToTab_inv hstep
          have hs2 : s₁ = CommuteStep.slideSt st x b' ap := hs
          refine ih ?_ htail
          rw [hs2, CommuteStep.slideSt_found]
          exact hm

/-- **THE COVER-SLIDE EVENT IN THE TAIL** — a slide whose target is the card
`c` itself, with the witness play split around it. -/
def TailCoverSlide (Q W : State) (ρ : List Move) (c : Card) : Prop :=
  ∃ (x : Card) (s1 s2 : List Move) (A Z : State),
    ρ = s1 ++ Move.tabToTab x (Sum.inr c) :: s2 ∧
    ShufflePlayW Q s1 A ∧
    reversibleAtW A (Move.tabToTab x (Sum.inr c)) ∧
    State.step A (Move.tabToTab x (Sum.inr c)) = some Z ∧
    ShufflePlayW Z s2 W

theorem raisePartner_cons {m : Move} {ρ : List Move} {c : Card}
    (h : RaisePartner ρ c) : RaisePartner (m :: ρ) c := by
  obtain ⟨γ, δ, hγδ⟩ := h
  exact ⟨m :: γ, δ, by rw [hγδ]; rfl⟩

theorem tailCoverSlide_cons {Q s₁ W : State} {m : Move} {ρ : List Move} {c : Card}
    (hrev : reversibleAtW Q m) (hstep : State.step Q m = some s₁)
    (h : TailCoverSlide s₁ W ρ c) : TailCoverSlide Q W (m :: ρ) c := by
  obtain ⟨x, s1, s2, A, Z, hρ, hA, hrevA, hstepA, hZ⟩ := h
  exact ⟨x, m :: s1, s2, A, Z, by rw [hρ]; rfl,
    Walk.cons hrev hstep hA, hrevA, hstepA, hZ⟩

/-- **THE EMPTY-TAIL DICHOTOMY.**  Along a PULL-FREE witness play, starting
from a state where `c` is raisable, exactly one of three things happens:

* some letter is `raise c` (`RaisePartner`) — the witness's raise partner;
* some slide LANDS on `c` (`TailCoverSlide`) — the mechanism's cover event,
  which may live anywhere in the tail;
* `c` is still raisable at the far end (`CanRaise W c`).

The pull-free hypothesis is essential: a pull in `c`'s suit would drop the
foundation and destroy `c`'s `nextUp` without raising `c`.  In the campaign
it is `MountainKit.MountainSplit`'s right leg. -/
theorem raise_or_slide_onto {Q W : State} {ρ : List Move} {c : Card}
    (hplay : ShufflePlayW Q ρ W) :
    ∀ (hQ : Q.WF), CanRaise Q c → (∀ m ∈ ρ, ¬ Bubble.IsPull m) →
      RaisePartner ρ c ∨ TailCoverSlide Q W ρ c ∨ CanRaise W c := by
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
          · exact Or.inl (raisePartner_cons h)
          · exact Or.inr (Or.inl (tailCoverSlide_cons hrev hstep h))
          · exact Or.inr (Or.inr h)
      | wasteToFound x => exact absurd hrev (wasteToFound_not_reversibleAtW st x)
      | wasteToTab x b' => exact absurd hrev (wasteToTab_not_reversibleAtW st x b')
      | foundToTab x b' => exact absurd ⟨x, b', rfl⟩ hnohead
      | tabToFound x =>
          by_cases hsu : x.suit = c.suit
          · -- the letter is a raise in `c`'s suit, hence it IS `raise c`
            have hxcan : CanRaise st x :=
              Bridge.canRaise_of_reversible_raise hQ hrev
            have hx : x = c := by
              have h1 : x.rank.toIdx = (st.found x.suit).length := by
                simpa [State.nextUp, State.foundHeight] using
                  of_decide_eq_true hxcan.1
              have h2 : c.rank.toIdx = (st.found c.suit).length := by
                simpa [State.nextUp, State.foundHeight] using
                  of_decide_eq_true hcan.1
              have hr : x.rank = c.rank := by
                apply Rank.toIdx_inj
                rw [h1, h2, hsu]
              cases x with
              | mk xs xr =>
                  cases c with
                  | mk cs cr => simp_all
            rw [hx]
            exact Or.inl ⟨[], ρ', rfl⟩
          · have hxw : x ≠ c := fun h => hsu (by rw [h])
            have hcan₁ : CanRaise s₁ c :=
              R12.canRaise_survives_raise hQ hstep hsu hxw hcan
            rcases ih (step_wf hQ hstep) hcan₁ hnotail with h | h | h
            · exact Or.inl (raisePartner_cons h)
            · exact Or.inr (Or.inl (tailCoverSlide_cons hrev hstep h))
            · exact Or.inr (Or.inr h)
      | tabToTab x b' =>
          by_cases hxc : x = c
          · -- `c`'s own slide keeps it raisable
            have hcan₁ : CanRaise s₁ c := by
              have h1 : CanRaise s₁ x :=
                canRaise_survives_own_slide (c := x) hQ hstep hrev (hxc ▸ hcan)
              exact hxc ▸ h1
            rcases ih (step_wf hQ hstep) hcan₁ hnotail with h | h | h
            · exact Or.inl (raisePartner_cons h)
            · exact Or.inr (Or.inl (tailCoverSlide_cons hrev hstep h))
            · exact Or.inr (Or.inr h)
          · by_cases hbase : b' = Sum.inr c
            · -- the slide lands on `c`: the cover event, at the head
              subst hbase
              exact Or.inr (Or.inl
                ⟨x, [], ρ', st, s₁, rfl, Walk.nil st, hrev, hstep, hrest⟩)
            · have hcan₁ : CanRaise s₁ c :=
                R12.canRaise_survives_slide hQ hstep hrev hxc hbase hcan
              rcases ih (step_wf hQ hstep) hcan₁ hnotail with h | h | h
              · exact Or.inl (raisePartner_cons h)
              · exact Or.inr (Or.inl (tailCoverSlide_cons hrev hstep h))
              · exact Or.inr (Or.inr h)

/-! ## §3. The twin case supplies the raise partner -/

/-- `Suit.twin` is a different suit. -/
theorem twin_suit_ne (s : Suit) : s.twin ≠ s := Suit.twin_ne s

/-- **THE TWIN CASE HAS NO COVER SLIDE.**  After `raise c.twin`, the card
`c.twin` sits in the foundation; the tail is pull-free, so it stays there.
But a reversible slide landing on `c` would need its mover seated directly on
`c.twin` (`Mech.mover_seat_twin_of_slide_into_card`), and a foundational card
lies on no pile (`mem_found_unique`). -/
theorem twin_no_coverSlide {G v : State} {tail : List Move} {c : Card}
    (hG : G.WF) (hplay : ShufflePlayW G tail v)
    (hnopull : ∀ m ∈ tail, ¬ Bubble.IsPull m)
    (hfound : ∃ σ, c.twin ∈ G.found σ) :
    ¬ TailCoverSlide G v tail c := by
  rintro ⟨x, s1, s2, A, Z, htail, hplay1, hrevA, hstepA, -⟩
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hplay1 hG
  -- the twin-source law: `x` sits directly on `c.twin` at `A`
  have hseat : seatOf A x = some (Sum.inr c.twin) :=
    Mech.mover_seat_twin_of_slide_into_card hAwf hstepA hrevA
  -- extract the pile membership from the seat read
  have hmemPile : ∃ a, c.twin ∈ (A.piles a).faceUp := by
    obtain ⟨a, -, -, hlast⟩ := tfc_seatOf_of_inr hseat
    exact ⟨a, mem_below _ (lastOf_mem hlast)⟩
  -- and its foundation membership survives the pull-free prefix
  have hnopull1 : ∀ m ∈ s1, ¬ Bubble.IsPull m := by
    intro m hm hpull
    exact hnopull m (by rw [htail]; exact List.mem_append_left _ hm) hpull
  obtain ⟨σ, hfoundσ⟩ := hfound
  obtain ⟨σ', hfoundA⟩ := found_mem_of_no_pull hplay1 hfoundσ hnopull1
  obtain ⟨a, hmem⟩ := hmemPile
  exact ((mem_found_unique hAwf hfoundA).1 a).2 hmem

/-- **THE TWIN CASE SUPPLIES THE RAISE PARTNER.**  With `d = c.twin` and the
right leg pull-free (`MountainKit.MountainSplit`), the tail must contain
`raise c`.  (Only the raise partner is forced; the `pull d` partner is a
separate obligation.) -/
theorem twin_raisePartner
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail)
    (hpost : post = [])
    (hms : MountainKit.MountainSplit left right)
    (htwin : d = c.twin) :
    RaisePartner tail c := by
  have hkeep := h
  obtain ⟨huwf, -, hsv, -, -, -, -, hleft, hright, -, -, hrightShape⟩ := h
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
    rw [htwin]; exact twin_suit_ne c.suit
  have hdw : d ≠ c := by
    rw [htwin]; exact SplitKit.card_twin_ne c
  have hcanG : CanRaise G c :=
    R12.canRaise_survives_raise hFwf hstep hsu hdw hcanF
  have hGwf : G.WF := step_wf hFwf hstep
  -- `c.twin` is founded by the raise at the head of the right leg
  have hfoundG : ∃ σ, c.twin ∈ G.found σ := by
    obtain ⟨-, ap, hpa, hs⟩ := step_tabToFound_inv hstep
    have hs2 : G = raiseSt F d ap := hs
    refine ⟨d.suit, ?_⟩
    rw [hs2, raiseSt_found_apply, ite_eq_left rfl, htwin]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  rcases raise_or_slide_onto htail hGwf hcanG hnopullTail with hraise | hcov | hcanV
  · exact hraise
  · exact absurd hcov (twin_no_coverSlide hGwf htail hnopullTail hfoundG)
  · exact absurd hcanV (ValleyElim.no_raise_of_saturated hsv c)

/-! ## §4. The empty-tail case under the campaign's standing inputs -/

/-- **THE EMPTY-TAIL RAISE CARD IS THE PULL CARD'S TWIN.**  `SplitLivePair`
confines the bottom's live set to `{d, d.twin}`; `c` is live there
(`emptyTail_canRaise`) and `c ≠ d` (`emptyTail_turn_ne`), so `c = d.twin`.
No block clause is used. -/
theorem twin_of_livePair_emptyTail
    (hl : SplitLivePair)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = []) :
    d = c.twin := by
  have hpair : TwinLivePair F d := hl u v ρ F left right c d b pre post tail h
  have hcanF : CanRaise F c := BlockKit.emptyTail_canRaise h hpost
  have hcd : c ≠ d := BlockKit.emptyTail_turn_ne h hpost
  rcases (hpair c).mp (CanRaiseS.now c hcanF) with hce | hce
  · exact absurd hce hcd
  · calc d = d.twin.twin := (card_twin_twin d).symm
      _ = c.twin := by rw [← hce]

/-- **THE RAISE PARTNER IS FREE UNDER `SplitLivePair` + THE MOUNTAIN SPLIT.**
The empty-tail raise card is `c.twin` (§ above), so §3 applies. -/
theorem emptyTail_raisePartner_of_livePair
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = []) :
    RaisePartner tail c :=
  twin_raisePartner h hpost
    (hms u v ρ F left right c d b pre post tail h)
    (twin_of_livePair_emptyTail hl h hpost)

/-- **THE PULLED DECOMPOSITION FROM THE PULL OCCURRENCE.**  §1's assembly,
with the raise partner supplied by §3. -/
theorem emptyTailPartnerDecomp_of_pull
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = [])
    (hms : MountainKit.MountainSplit left right) (htwin : d = c.twin)
    (hpull : PullPartner pre d) :
    PartnerDecomp ρ c d b := by
  obtain ⟨α, β, bd, hpre⟩ := hpull
  obtain ⟨γ, δ, htail⟩ := twin_raisePartner h hpost hms htwin
  obtain ⟨-, -, -, -, -, -, hρ, -, -, hshape, -, hrightShape⟩ := h
  refine ⟨α, β, γ, δ, [], bd, ?_⟩
  rw [hρ, hshape, hrightShape, hpre, htail, hpost]
  simp only [List.cons_append, List.nil_append, List.append_nil,
    List.append_assoc]

/-- **THE WHOLE EMPTY-TAIL RESIDUAL IS THE PULL OCCURRENCE.**  Under the
campaign's standing `SplitLivePair` and mountain (`M1`) inputs, the raise half
of `BlockKit.EmptyTailPartners` is automatic; only the `pull d` occurrence in
`pre` has to be supplied. -/
theorem emptyTailPartners_of_livePair_pull
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hpull : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail → post = [] →
      PullPartner pre d) :
    BlockKit.EmptyTailPartners :=
  emptyTailPartners_of_occurrences hpull
    (fun u v ρ F left right c d b pre post tail h hpost =>
      emptyTail_raisePartner_of_livePair hl hms h hpost)

/-- **`NoEmptyTail` FROM THE PULL OCCURRENCE + A NORMALIZER.** -/
theorem noEmptyTail_of_livePair_pull
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hpull : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail → post = [] →
      PullPartner pre d)
    (hnorm : LocatorCorrected.CrossingBracketNormalizer) :
    BlockKit.NoEmptyTail :=
  BlockKit.noEmptyTail_of_partners_normalizer
    (emptyTailPartners_of_livePair_pull hl hms hpull) hnorm

/-- **`SplitBlock` FROM THE PULL OCCURRENCE, A NORMALIZER AND THE COVER
HALF.** -/
theorem splitBlock_of_livePair_pull
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hpull : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail → post = [] →
      PullPartner pre d)
    (hnorm : LocatorCorrected.CrossingBracketNormalizer)
    (hcov : BlockKit.TailCovers) :
    SplitBlock :=
  BlockKit.splitBlock_of_parts
    (noEmptyTail_of_livePair_pull hl hms hpull hnorm) hcov

/-- **THE CAMPAIGN CHAIN FROM THE PULL OCCURRENCE.**  All the other inputs
(`SplitLivePair`, the cover half, shortest-play existence) are the campaign's
standing ones. -/
theorem satDifferForkWF_of_livePair_pull
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hpull : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail → post = [] →
      PullPartner pre d)
    (hnorm : LocatorCorrected.CrossingBracketNormalizer)
    (hcov : BlockKit.TailCovers)
    (hmin : ValleyElim.ShortestPlayExists) :
    SatDifferForkWF :=
  BlockKit.satDifferForkWF_of_livePair_parts hl
    (noEmptyTail_of_livePair_pull hl hms hpull hnorm) hcov hmin

/-! ## §5. Where the pull partner comes from -/

/-- **FOUNDED AT THE ORIGIN AND NOT AT THE END ⟹ A PULL OF IT OCCURS.**  The
exact first-move analysis of `found_mem_of_no_pull`: membership in the
foundations is preserved by draws, raises and slides, and is only lost by a
pull of the card itself. -/
theorem inFound_or_pull {u F : State} {ρ : List Move} {d : Card}
    (hplay : ShufflePlayW u ρ F) :
    ∀ (σ : Suit), d ∈ u.found σ →
      (∃ σ', d ∈ F.found σ') ∨
      ∃ (α β : List Move) (b : Base), ρ = α ++ Move.foundToTab d b :: β := by
  induction hplay with
  | nil st => intro σ hm; exact Or.inl ⟨σ, hm⟩
  | @cons st s₁ W m ρ' hrev hstep hrest ih =>
      intro σ hm
      cases m with
      | draw =>
          rcases ih σ (by rw [stepDraw_found hstep]; exact hm) with h | h
          · exact Or.inl h
          · obtain ⟨α, β, b, hα⟩ := h
            exact Or.inr ⟨Move.draw :: α, β, b, by rw [hα]; rfl⟩
      | wasteToFound x => exact absurd hrev (wasteToFound_not_reversibleAtW st x)
      | wasteToTab x b => exact absurd hrev (wasteToTab_not_reversibleAtW st x b)
      | tabToFound x =>
          obtain ⟨-, ap, hpa, hs⟩ := step_tabToFound_inv hstep
          have hs2 : s₁ = raiseSt st x ap := hs
          rcases ih σ (by
            rw [hs2, raiseSt_found_apply]
            by_cases hσ : σ = x.suit
            · rw [ite_eq_left hσ, ← hσ]
              exact List.mem_append.mpr (Or.inl hm)
            · rw [ite_eq_right hσ]
              exact hm) with h | h
          · exact Or.inl h
          · obtain ⟨α, β, b, hα⟩ := h
            exact Or.inr ⟨Move.tabToFound x :: α, β, b, by rw [hα]; rfl⟩
      | tabToTab x b =>
          obtain ⟨ap, -, -, -, hs⟩ := step_tabToTab_inv hstep
          have hs2 : s₁ = CommuteStep.slideSt st x b ap := hs
          rcases ih σ (by rw [hs2, CommuteStep.slideSt_found]; exact hm) with h | h
          · exact Or.inl h
          · obtain ⟨α, β, b', hα⟩ := h
            exact Or.inr ⟨Move.tabToTab x b :: α, β, b', by rw [hα]; rfl⟩
      | foundToTab x b =>
          obtain ⟨c', hft, hceq, hcp, hs⟩ := step_foundToTab_inv hstep
          have htop : lastOf (st.found x.suit) = some x := by
            rw [hceq] at hft
            exact hft
          by_cases hxd : x = d
          · refine Or.inr ⟨[], ρ', b, ?_⟩
            simp [hxd]
          · have hdx : d ≠ x := fun h => hxd h.symm
            rcases ih σ (by
              rw [hs, putCard_found]
              show d ∈ (st.setFound x.suit (chop (st.found x.suit))).found σ
              simp only [State.setFound]
              by_cases hσ : σ = x.suit
              · rw [ite_eq_left hσ]
                rw [hσ] at hm
                have hsplit := lastOf_chop htop
                rw [hsplit] at hm
                rcases List.mem_append.mp hm with h | h
                · exact h
                · exact absurd (List.mem_singleton.mp h) hdx
              · rw [ite_eq_right hσ]
                exact hm) with h | h
            · exact Or.inl h
            · obtain ⟨α, β, b', hα⟩ := h
              exact Or.inr ⟨Move.foundToTab x b :: α, β, b', by rw [hα]; rfl⟩

/-- **THE PULL PARTNER EXISTS WHENEVER `d` WAS FOUNDED AT THE ORIGIN.**  This
is the exact positive content of `EmptyTail.PullPartner`: `d` sits in `u`'s
foundation and on the tableau at `F`, so some letter moved it off the
foundation — and it is a pull of `d`. -/
theorem pullPartner_of_found
    {u F : State} {pre : List Move} {d : Card} {σ : Suit} {a : Anchor}
    (hpre : ShufflePlayW u pre F) (hfound : d ∈ u.found σ)
    (htab : d ∈ (F.piles a).faceUp) (hFwf : F.WF) :
    PullPartner pre d := by
  rcases inFound_or_pull hpre σ hfound with ⟨σ', hf⟩ | ⟨α, β, b, hα⟩
  · exact absurd hf (fun hf => ((mem_found_unique hFwf hf).1 a).2 htab)
  · exact ⟨α, β, b, hα⟩

/-- **THE EMPTY-TAIL PULL PARTNER FROM `d` FOUNDED AT `u`.**  In the split's
own data: `d` is raisable at `F` (green), so it lies on a pile there; if `d`
was founded at `u`, the pull partner is supplied by `pullPartner_of_found`. -/
theorem emptyTail_pullPartner_of_found
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = [])
    (hfound : ∃ σ, d ∈ u.found σ) :
    PullPartner pre d := by
  have hkeep := h
  obtain ⟨huwf, -, -, -, -, -, -, hleft, -, hshape, -, -⟩ := h
  obtain ⟨A', hpre, hcanA'd⟩ := BlockKit.emptyTail_canRaise_before hkeep hpost
  have hA' : A'.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨σ, hσ⟩ := hfound
  obtain ⟨-, a, hpa, -⟩ := hcanA'd
  exact pullPartner_of_found hpre hσ (lastOf_mem (pileOfTop_top hpa).2) hA'

/-- **THE REDUCED RESIDUAL: `d` FOUNDED AT THE ORIGIN.**  Under
`SplitLivePair` + `M1`, the empty-tail half of `BlockKit.SplitBlock` follows
from the single state-level occurrence condition "`d` lies in `u`'s
foundation". -/
theorem emptyTailPartners_of_livePair_founded
    (hl : SplitLivePair)
    (hms : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail →
      MountainKit.MountainSplit left right)
    (hfound : ∀ (u v : State) (ρ : List Move) (F : State)
      (left right : List Move) (c d : Card) (b : Base)
      (pre post tail : List Move),
      SplitHyp u v ρ F left right c d b pre post tail → post = [] →
      ∃ σ, d ∈ u.found σ) :
    BlockKit.EmptyTailPartners :=
  emptyTailPartners_of_livePair_pull hl hms
    (fun u v ρ F left right c d b pre post tail h hpost =>
      emptyTail_pullPartner_of_found h hpost
        (hfound u v ρ F left right c d b pre post tail h hpost))

/-- **THE CORRECTED EMPTY-TAIL RESIDUAL.**  Under `SplitLivePair` an
empty-tail split bottom is exactly the both-raisable twin pair: `d = c.twin`
with both `c` and `d` vanilla-raisable there.  This is the hypothesis shape of
`BlockMin`'s `BothRaisableBlock` (`Temp/BlockMin_Main.lean:241`), i.e. the
relaxed route consumes it directly — no partner letters needed. -/
theorem emptyTail_bothRaisable_twin
    (hl : SplitLivePair)
    {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base}
    {pre post tail : List Move}
    (h : SplitHyp u v ρ F left right c d b pre post tail) (hpost : post = []) :
    d = c.twin ∧ CanRaise F c ∧ CanRaise F d := by
  obtain ⟨-, -, hcanD, -⟩ := splitHyp_green h
  exact ⟨twin_of_livePair_emptyTail hl h hpost,
    BlockKit.emptyTail_canRaise h hpost, hcanD⟩

/-! ## §6. Battery -/

#print axioms EmptyTail.emptyTailPartners_of_occurrences
#print axioms EmptyTail.emptyTail_play_shape
#print axioms EmptyTail.canRaise_persists_readok
#print axioms EmptyTail.canRaise_survives_own_slide
#print axioms EmptyTail.found_mem_of_no_pull
#print axioms EmptyTail.raise_or_slide_onto
#print axioms EmptyTail.twin_no_coverSlide
#print axioms EmptyTail.twin_raisePartner
#print axioms EmptyTail.twin_of_livePair_emptyTail
#print axioms EmptyTail.emptyTail_raisePartner_of_livePair
#print axioms EmptyTail.emptyTailPartnerDecomp_of_pull
#print axioms EmptyTail.emptyTailPartners_of_livePair_pull
#print axioms EmptyTail.noEmptyTail_of_livePair_pull
#print axioms EmptyTail.splitBlock_of_livePair_pull
#print axioms EmptyTail.satDifferForkWF_of_livePair_pull
#print axioms EmptyTail.inFound_or_pull
#print axioms EmptyTail.pullPartner_of_found
#print axioms EmptyTail.emptyTail_pullPartner_of_found
#print axioms EmptyTail.emptyTailPartners_of_livePair_founded
#print axioms EmptyTail.emptyTail_bothRaisable_twin

end EmptyTail
