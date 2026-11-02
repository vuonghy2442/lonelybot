import Orig2.Fork.Split.ForkLandingLocal

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkNoMate — the containment clause in the raise vocabulary

Scratch card.  READ-ONLY on `Orig2/` (no source edit, no commit).  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; axiom battery at the tail.

## What this card establishes

1. **`MateRaiseFree ↔ LandingThirdSuitFree`** (`mateRaiseFree_iff_containment`):
   in the raise vocabulary the containment residual is *not* weaker — every
   model of the raise-exclusion is a model of the containment and conversely
   (the converse is `Direct.split_survivor_bad_raise`).  So `MateRaiseFree` is
   a restatement, not a reduction.

2. **The load-bearing clause** (`LandKit.canRaiseS_below_form`'s last
   conjunct): `fromCard c faceUp = [c] ∨ st.pileOfTop c.twin ≠ none`.  The
   hatch disjunct `st.pileOfTop c.twin ≠ none` is controlled by `e.twin`'s
   *seat*, and it is precisely the predicate that `tabToFound e.twin` topples.
   - `hatch_of_not_clear`: if the seat clause fails, the hatch carries `e`;
   - `canRaiseS_survives_twin_raise_of_clear`: if the seat clause carries `e`,
     `raise e.twin` is *harmless* (e's pile is untouched: the twin tops a
     different pile);
   - `kill_shape_of_twin_raise`: if `raise e.twin` kills `e`, then the hatch
     carried it and the seat clause did not.

3. **The mechanism, exact** (`violation_is_third_twin_bracket`): a violating
   split carries a *third-suit twin bracket* — an earlier pull `pull z` in
   `pre` with `e ∈ {z, z.twin}`, and a raise of the other member of
   `{z, z.twin}` in `right`.  By `Direct.split_pull_card_bad_raise` the same
   split *also* carries the `{c, c.twin}` bracket, so a violating split has
   **two disjoint pull/raise twin pairs** while the census's minimal splits
   carry exactly one (the `{c, c.twin}` pair).

4. **The fourth suit's ledger** (`fourth_suit_pull_accounting`,
   `third_suit_frozen_rung`): raising `e.twin` forces the fourth suit
   (`e.suit.twin`) to be *pulled in the left leg* at least as often as its
   height at `u` exceeds `e.rank`, and to *climb in the right leg*; meanwhile
   the third suit's rung is frozen at `e.rank` all the way to `v`.  These are
   exact and contradiction-free: the rung/unimodality accounting does **not**
   refute the violation.

5. **The residual, named**: `MateRaiseFree` (`Direct`, equivalent to the
   containment) and `NoThirdTwinBracket` (the bracket-pair form, *strictly
   stronger* — a sufficient condition, not a reduction).
-/

namespace NoMate

open ValleyElim
open Bubble

/-! ## §0. Membership to occurrence -/

/-- A letter of a list is an occurrence (`Direct.Occurs`). -/
theorem occurs_of_mem {m : Move} {l : List Move} (h : m ∈ l) : Direct.Occurs m l := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact Direct.occurs_head _ t
      · exact Direct.occurs_cons (ih h')

/-! ## §1. Suit geometry: the twin's seat is the FOURTH suit -/
/-- The twin keeps the rank and moves to the same-colour twin suit. -/
theorem twin_suit_eq (c : Card) : c.twin.suit = c.suit.twin := rfl

theorem twin_suit_ne_self (c : Card) : c.twin.suit ≠ c.suit := by
  intro h
  exact Suit.twin_ne c.suit (by rw [twin_suit_eq] at h; exact h)

theorem suit_twin_inj {a b : Suit} (h : a.twin = b.twin) : a = b := by
  have h2 : a.twin.twin = b.twin.twin := congrArg Suit.twin h
  simpa using h2

theorem card_twin_ne_self (c : Card) : c.twin ≠ c := by
  intro h
  exact twin_suit_ne_self c (by rw [h])

/-- **THE FOURTH SUIT.**  If `e` is a third-suit card relative to the split's
pull card `c`, then `e.twin` sits in the *fourth* suit: different from `c`'s
suit, from `c.twin`'s suit, and from `e`'s own suit. -/
theorem fourth_suit_facts {c e : Card} (h1 : e.suit ≠ c.suit)
    (h2 : e.suit ≠ c.twin.suit) :
    e.twin.suit ≠ c.suit ∧ e.twin.suit ≠ c.twin.suit ∧
      e.twin.suit ≠ e.suit := by
  have he1 : e.twin.suit = e.suit.twin := rfl
  have hc1 : c.twin.suit = c.suit.twin := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply h2
    have hh : e.suit.twin = c.suit := h
    have h3 : e.suit = c.suit.twin := by simpa using congrArg Suit.twin hh
    rw [h3]
    rfl
  · intro h
    apply h1
    exact suit_twin_inj h
  · intro h
    exact Suit.twin_ne e.suit h

/-! ## §2. Which clause of `canRaiseS_below_form` is load-bearing -/

/-- The licence clause that `e.twin`'s **seat** controls: the twin tops some
pile.  This is the second disjunct of `LandKit.canRaiseS_below_form`'s last
conjunct, and it is exactly the predicate that `tabToFound e.twin` topples. -/
def Hatch (st : State) (e : Card) : Prop := st.pileOfTop e.twin ≠ none

/-- The *other* licence clause: `e` is the top of its pile (nothing above it)
with its seat below.  This is the first disjunct of
`LandKit.canRaiseS_below_form`'s last conjunct, together with the seat
clause. -/
def ClearLicence (st : State) (e : Card) : Prop :=
  ∃ a : Anchor, e ∈ (st.piles a).faceUp ∧
    (below e (st.piles a).faceUp ≠ [] ∨
      ((st.piles a).hidden = [] ∧ e.rank = Rank.king)) ∧
    fromCard e (st.piles a).faceUp = [e]

/-- `fromCard e faceUp = [e]` pins `e` as the pile's **top** card. -/
theorem top_of_fromCard_singleton {st : State} {a : Anchor} {e : Card}
    (hmem : e ∈ (st.piles a).faceUp)
    (h : fromCard e (st.piles a).faceUp = [e]) :
    (st.piles a).top = some e := by
  obtain ⟨z, hz⟩ := lastOf_exists (l := (st.piles a).faceUp) (by
    intro hnil
    rw [hnil] at hmem
    exact absurd hmem List.not_mem_nil)
  have hzmem : z ∈ fromCard e (st.piles a).faceUp :=
    tfc_lastOf_mem_fromCard _ _ hmem z hz
  rw [h, List.mem_singleton] at hzmem
  rw [Pile.top, hz, hzmem]

/-- The seat clause plus `nextUp` is the flat characterisation's licence. -/
theorem canRaiseS_of_clearLicence {st : State} (hwf : st.WF) {e : Card}
    (hnext : st.nextUp e = true) (h : ClearLicence st e) : CanRaiseS st e := by
  obtain ⟨a, hmem, hseat, hclear⟩ := h
  exact (LandKit.canRaiseS_below_form hwf).mpr
    ⟨hnext, a, hmem, hseat, Or.inl hclear⟩

/-- **IF THE SEAT CLAUSE FAILS, THE HATCH IS THE LICENCE.**  This is the exact
clause attribution: at a state where `e` is S-live and *not* clear, the flat
characterisation's last conjunct is carried by `st.pileOfTop e.twin ≠ none`. -/
theorem hatch_of_not_clear {st : State} (hwf : st.WF) {e : Card}
    (he : CanRaiseS st e) (hnc : ¬ ClearLicence st e) : Hatch st e := by
  obtain ⟨-, a, hmem, hseat, hdisj⟩ := (LandKit.canRaiseS_below_form hwf).mp he
  rcases hdisj with h | h
  · exact absurd ⟨a, hmem, hseat, h⟩ hnc
  · exact h

/-- **THE SEAT LICENCE MAKES THE TWIN RAISE HARMLESS.**  If `e` is carried by
`fromCard e faceUp = [e]` (so `e` is a pile top), then `raise e.twin` cannot
touch `e`'s pile: the twin tops a *different* pile, so the ends agree.  This
is the complement of `Direct.canRaiseS_survives_raise_of_ne`, which covers
every raise except the two rank-mates. -/
theorem canRaiseS_survives_twin_raise_of_clear {st st' : State} {e : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound e.twin) = some st')
    (he : CanRaiseS st e) (hc : ClearLicence st e) :
    CanRaiseS st' e := by
  obtain ⟨a, hmem, hseat, hclear⟩ := hc
  obtain ⟨-, a0, hpa0, -⟩ := step_tabToFound_inv hstep
  have hnext : st.nextUp e = true := ((LandKit.canRaiseS_below_form hwf).mp he).1
  have hnext' : st'.nextUp e = true :=
    SafeTransport.nextUp_tabToFound_ne hstep (twin_suit_ne_self e) hnext
  have ha : a ≠ a0 := by
    intro hEq
    have htop : (st.piles a).top = some e := top_of_fromCard_singleton hmem hclear
    have htop' : (st.piles a).top = some e.twin := by
      rw [hEq]
      exact (pileOfTop_eq_some_iff hwf).mp hpa0
    exact card_twin_ne_self e (Option.some.inj (htop.symm.trans htop')).symm
  have hpile : st'.piles a = st.piles a :=
    SafeTransport.piles_tabToFound_ne hstep hpa0 ha
  exact (LandKit.canRaiseS_below_form (step_wf hwf hstep)).mpr
    ⟨hnext', a, by rw [hpile]; exact hmem, by rw [hpile]; exact hseat,
      Or.inl (by rw [hpile]; exact hclear)⟩

/-- **THE KILL SHAPE.**  If `raise e.twin` kills `e`'s S-licence, then the
hatch carried it and the seat clause did not: `e.twin`'s *seat* is the
load-bearing datum, and the killed `e` is *buried* (not a pile top with its
seat below). -/
theorem kill_shape_of_twin_raise {st st' : State} {e : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound e.twin) = some st')
    (he : CanRaiseS st e) (hkill : ¬ CanRaiseS st' e) :
    Hatch st e ∧ ¬ ClearLicence st e := by
  refine ⟨?_, ?_⟩
  · obtain ⟨-, a0, hpa0, -⟩ := step_tabToFound_inv hstep
    unfold Hatch
    rw [hpa0]
    exact fun h => nomatch h
  · intro hc
    exact hkill (canRaiseS_survives_twin_raise_of_clear hwf hstep he hc)

/-! ## §3. The residual is a restatement, not a reduction -/

/-- **`MateRaiseFree` FOLLOWS FROM THE CONTAINMENT** (no mountain hypothesis,
no minimality): the containment gives `False` at the very instance, so both
occurrence exclusions are vacuous. -/
theorem mateRaiseFree_of_containment (h : Landing.LandingThirdSuitFree) :
    Direct.MateRaiseFree := by
  intro u v ρ F left right c d b pre post tail hs hms A' B hpre hstep e he h1 h2
  exact ⟨fun _ => h u v ρ F left right c d b pre post tail hs A' B hpre hstep e he h1 h2,
    fun _ => h u v ρ F left right c d b pre post tail hs A' B hpre hstep e he h1 h2⟩

/-- **THE VERDICT.**  Given the mountain shape at splits, the raise-exclusion
`MateRaiseFree` and the containment clause are the *same* proposition.  The
forward direction is `Direct.landingThirdSuitFree_of_mateRaiseFree`; the
backward direction is the previous theorem.  Hence no strictly smaller
raise-language residual exists: any model of the containment satisfies the
raise-exclusion, and vice versa. -/
theorem mateRaiseFree_iff_containment (hmt : Direct.MountainAtSplits) :
    Direct.MateRaiseFree ↔ Landing.LandingThirdSuitFree :=
  ⟨Direct.landingThirdSuitFree_of_mateRaiseFree hmt, mateRaiseFree_of_containment⟩

/-! ## §4. The mechanism: the violation is a THIRD-SUIT TWIN BRACKET -/

/-- `pre` is free-or-pull: it sits in the raise-free left leg. -/
theorem freeOrPull_of_pre
    {u F : State} {left pre post : List Move} {c : Card} {b : Base}
    (hleft : ShufflePlayW u left F)
    (hshape : left = pre ++ Move.foundToTab c b :: post)
    (hnr : ∀ m ∈ left, ¬ IsRaise m) :
    ∀ m ∈ pre, LandKit.FreeOrPull m := by
  intro m hm
  have hmleft : m ∈ left := by
    rw [hshape]
    exact List.mem_append_left _ hm
  rcases MountainKit.free_or_pull_or_raise_of_play hleft m hmleft with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (hnr m hmleft)

/-- **THE VIOLATION IS A THIRD-SUIT TWIN BRACKET.**  At a split, a third-suit
card `e` S-live at the pull's landing is (i) the card of an EARLIER PULL `z`
in `pre`, or `z`'s twin (`LandKit.landing_third_suit_earlier_pull`), and
(ii) the pull-free right leg raises a rank-mate of `e`
(`Direct.split_survivor_bad_raise`).  Since `e ∈ {z, z.twin}`, the pair
`{z, z.twin}` is both **pulled** (left leg) and **rank-mate raised** (right
leg): a cross-twin bracket, on a suit pair disjoint from `{c, c.twin}`. -/
theorem violation_third_twin_bracket
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) (he1 : e.suit ≠ c.suit)
    (he2 : e.suit ≠ c.twin.suit) :
    ∃ (α : List Move) (z : Card) (bz : Base) (β : List Move),
      pre = α ++ Move.foundToTab z bz :: β ∧
        (e = z ∨ e = z.twin) ∧
        (Direct.Occurs (Move.tabToFound e) right ∨
          Direct.Occurs (Move.tabToFound e.twin) right) ∧
        z.suit ≠ c.suit ∧ z.suit ≠ c.twin.suit := by
  have hk := h
  obtain ⟨huwf, hsu, -, -, -, -, -, hleft, hright, hshape, hfree, -⟩ := h
  have hec : e ≠ c := fun hh => he1 (by rw [hh])
  have het : e ≠ c.twin := fun hh => he2 (by rw [hh])
  obtain ⟨α, z, bz, β, hpreEq, hez⟩ :=
    LandKit.landing_third_suit_earlier_pull hpre huwf hsu
      (freeOrPull_of_pre hleft hshape hms.1) hstep he hec het
  have hraise := Direct.split_survivor_bad_raise hk hms hpre hstep he
  have hz1 : z.suit ≠ c.suit := by
    rcases hez with h1 | h1
    · rw [← h1]; exact he1
    · have hzz : z = e.twin := by rw [h1, card_twin_twin]
      rw [hzz]
      exact (fourth_suit_facts he1 he2).1
  have hz2 : z.suit ≠ c.twin.suit := by
    rcases hez with h1 | h1
    · rw [← h1]; exact he2
    · have hzz : z = e.twin := by rw [h1, card_twin_twin]
      rw [hzz]
      exact (fourth_suit_facts he1 he2).2.1
  exact ⟨α, z, bz, β, hpreEq, hez, hraise, hz1, hz2⟩

/-- **A VIOLATING SPLIT CARRIES TWO TWIN BRACKETS.**  The `{c, c.twin}` pair is
pulled (`foundToTab c b` in `left`) and rank-mate raised (`right` raises `c`
or `c.twin`, `Direct.split_pull_card_bad_raise`); the third-suit pair
`{z, z.twin}` of `violation_third_twin_bracket` is also pulled and raised.
The two pairs are disjoint (`z ≠ c`, `z ≠ c.twin`).  This is the exact
"bracket imbalance" of a violation — but it is **not** a contradiction with
minimality: a third-suit pull/raise pair already occurs in the census's
minimal `P4_s1` split (`Temp/SplitProbe_witnesses_out.txt:3-4`: `pull 4H` in
`pre`, `raise 4H` in `right`) with no survivor at the landing.  See
`Temp/NoMate_Report.md` §5. -/
theorem two_twin_brackets_of_violation
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (h : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (hms : MountainKit.MountainSplit left right)
    {A' B : State} (hpre : ShufflePlayW u pre A')
    (hstep : State.step A' (Move.foundToTab c b) = some B)
    {e : Card} (he : CanRaiseS B e) (he1 : e.suit ≠ c.suit)
    (he2 : e.suit ≠ c.twin.suit) :
    (∃ (α : List Move) (z : Card) (bz : Base) (β : List Move),
        pre = α ++ Move.foundToTab z bz :: β ∧
          (e = z ∨ e = z.twin) ∧ z.suit ≠ c.suit ∧
          z.suit ≠ c.twin.suit ∧ z ≠ c ∧ z ≠ c.twin ∧
          (Direct.Occurs (Move.tabToFound e) right ∨
            Direct.Occurs (Move.tabToFound e.twin) right)) ∧
      Direct.Occurs (Move.foundToTab c b) left ∧
      (Direct.Occurs (Move.tabToFound c) right ∨
        Direct.Occurs (Move.tabToFound c.twin) right) := by
  have hk := h
  obtain ⟨-, -, -, -, -, -, -, -, -, hshape, -, -⟩ := hk
  obtain ⟨α, z, bz, β, hpreEq, hez, hraise, hz1, hz2⟩ :=
    violation_third_twin_bracket h hms hpre hstep he he1 he2
  have hzc : z ≠ c := fun hh => hz1 (by rw [hh])
  have hzt : z ≠ c.twin := fun hh => hz2 (by rw [hh])
  have hcpull : Direct.Occurs (Move.foundToTab c b) left := by
    rw [hshape]
    exact Direct.occurs_append_right (Direct.occurs_head _ post)
  have hcpair := Direct.split_pull_card_bad_raise h hms hpre hstep
  exact ⟨⟨α, z, bz, β, hpreEq, hez, hz1, hz2, hzc, hzt, hraise⟩, hcpull, hcpair⟩

/-! ## §5. The fourth suit's ledger (why the rung route does not close) -/

/-- **A RAISE OF `x` ANYWHERE IN A PULL-FREE LEG PINS ITS SUIT'S START RUNG.**
The leg's `x.suit` rung at the start is at most `x.rank`: the raise is legal
only at rung `x.rank`, and a pull-free leg never lowers a rung. -/
theorem rung_le_of_occurs_raise {F v : State} {right : List Move} {x : Card}
    (hplay : ShufflePlayW F right v)
    (hnopull : ∀ m ∈ right, ¬ IsPull m)
    (hocc : Direct.Occurs (Move.tabToFound x) right) :
    rungAt F x.suit ≤ x.rank.toIdx := by
  induction hplay with
  | nil st =>
      obtain ⟨s₁, s₂, hs⟩ := hocc
      simp at hs
  | @cons st s₁ W m rest hrev hstep hrest ih =>
      have hnp : ∀ m' ∈ rest, ¬ IsPull m' :=
        fun m' hm' => hnopull m' (List.mem_cons_of_mem m hm')
      obtain ⟨s₁', s₂', hs⟩ := hocc
      cases s₁' with
      | nil =>
          rw [List.nil_append] at hs
          injection hs with hm _
          subst hm
          have hnext : st.nextUp x = true := (step_tabToFound_inv hstep).1
          have hrank : rungAt st x.suit = x.rank.toIdx := by
            have h := of_decide_eq_true hnext
            unfold State.nextUp State.foundHeight at h
            unfold rungAt
            omega
          exact Nat.le_of_eq hrank
      | cons a t =>
          rw [List.cons_append] at hs
          injection hs with _ htl
          have hocc' : Direct.Occurs (Move.tabToFound x) rest := ⟨t, s₂', htl⟩
          have hIH : rungAt s₁ x.suit ≤ x.rank.toIdx := ih hnp hocc'
          have hstep_le : rungAt st x.suit ≤ rungAt s₁ x.suit := by
            have hsingle : ShufflePlayW st [m] s₁ := Walk.cons hrev hstep (Walk.nil s₁)
            exact MountainKit.rungAt_le_of_no_pull (σ := x.suit) hsingle
              (by
                intro m' hm'
                rw [List.mem_singleton] at hm'
                have hm'mem : m' ∈ m :: rest := by
                  rw [List.mem_cons]
                  exact Or.inl hm'
                exact hnopull m' hm'mem)
          omega

/-- **THE FOURTH SUIT IS PULLED IN THE LEFT LEG.**  If the right leg raises
`e.twin` while `e` is the third-suit frontier (`rungAt F e.suit = e.rank`),
then the fourth suit's height at `u` is accounted for by left-leg pulls of
that suit up to `e.rank`:

`rungAt u e.twin.suit ≤ pullsOf left e.twin.suit + e.rank.toIdx`.

So raising `e.twin` requires the fourth suit to be pulled in the left leg --
exactly the bracket `violation_third_twin_bracket` exhibits. -/
theorem fourth_suit_pull_accounting {u v F : State} {left right : List Move}
    {c e : Card} {b : Base} {d : Card} {tail : List Move}
    (hleft : ShufflePlayW u left F) (hright : ShufflePlayW F right v)
    (hms : MountainKit.MountainSplit left right)
    (hocc : Direct.Occurs (Move.tabToFound e.twin) right) :
    rungAt u e.twin.suit ≤ pullsOf left e.twin.suit + e.rank.toIdx := by
  have h4 : rungAt F e.twin.suit ≤ e.rank.toIdx := by
    have h := rung_le_of_occurs_raise hright hms.2 hocc
    rwa [Card.twin_rank] at h
  have hacc : pullsOf left e.twin.suit =
      rungAt u e.twin.suit - rungAt F e.twin.suit :=
    MountainKit.pullsOf_eq_sub_of_no_raise hleft hms.1
  omega

/-- **THE THIRD SUIT IS FROZEN AT `e.rank`.**  If the right leg raises no card
of `e`'s suit (the frozen hypothesis), the third suit's rung at the far
endpoint is still `e.rank`: the kill happened without touching `e`'s own
suit. -/
theorem third_suit_frozen_rung {F v : State} {right : List Move} {e : Card}
    (hright : ShufflePlayW F right v)
    (hnopull : ∀ m ∈ right, ¬ IsPull m)
    (hno : ∀ x : Card, Direct.Occurs (Move.tabToFound x) right → x.suit ≠ e.suit)
    (hr : rungAt F e.suit = e.rank.toIdx) :
    rungAt v e.suit = e.rank.toIdx := by
  have hz : raisesOf right e.suit = 0 := by
    rcases Nat.eq_zero_or_pos (raisesOf right e.suit) with hz0 | hpos
    · exact hz0
    · obtain ⟨x, hxs, hmem⟩ := LedgerKit.raisesOf_pos_iff.mp hpos
      have hocc : Direct.Occurs (Move.tabToFound x) right := occurs_of_mem hmem
      exact absurd hxs (hno x hocc)
  have hacc : raisesOf right e.suit = rungAt v e.suit - rungAt F e.suit :=
    MountainKit.raisesOf_eq_sub_of_no_pull hright hnopull
  have hle : rungAt F e.suit ≤ rungAt v e.suit :=
    MountainKit.rungAt_le_of_no_pull hright hnopull
  omega

/-! ## §6. The fork lane settles this lane -/

/-- **`TwinLiveAtBottom`** — the fork lane's clause, stated as the input this
card consumes: at every split, the bottom's S-live set is exactly the twin
pair of the pull card.  (This is the content of `TwinLivePair F c`; the
siting/pin/block lane supplies it.) -/
def TwinLiveAtBottom : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State) (left right : List Move)
    (c d : Card) (b : Base) (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail → TwinLivePair F c

/-- **THE FORK LANE IMPLIES THE CONTAINMENT** (`Landing.landingLivePair_of_twinLivePair_F`
transported along the free tail).  No mountain shape, no minimality, no raise
vocabulary: the containment is a consequence of the bottom's live pair. -/
theorem containment_of_twinLiveAtBottom (h : TwinLiveAtBottom) :
    Landing.LandingThirdSuitFree := by
  intro u v ρ F left right c d b pre post tail hs A' B hpre hstep e he h1 h2
  have hk := hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfree, -⟩ := hs
  obtain ⟨hpost, hBwf⟩ := Landing.post_play_of_landing hk hpre hstep
  have hland := Landing.landingLivePair_of_twinLivePair_F hBwf hpost hfree
    (h u v ρ F left right c d b pre post tail hk)
  rcases hland.2 e he with h' | h'
  · exact h1 h'
  · exact h2 h'

/-- **THE FORK LANE THEREFORE SETTLES THE RAISE RESIDUAL TOO.**  Composing the
previous theorem with `mateRaiseFree_of_containment`.  So the raise-exclusion
this card isolates is *not* an independent obligation: the bottom's live pair
implies it outright. -/
theorem mateRaiseFree_of_twinLiveAtBottom (h : TwinLiveAtBottom) :
    Direct.MateRaiseFree :=
  mateRaiseFree_of_containment (containment_of_twinLiveAtBottom h)

end NoMate

#print axioms NoMate.twin_suit_ne_self
#print axioms NoMate.fourth_suit_facts
#print axioms NoMate.top_of_fromCard_singleton
#print axioms NoMate.canRaiseS_of_clearLicence
#print axioms NoMate.hatch_of_not_clear
#print axioms NoMate.canRaiseS_survives_twin_raise_of_clear
#print axioms NoMate.kill_shape_of_twin_raise
#print axioms NoMate.mateRaiseFree_of_containment
#print axioms NoMate.mateRaiseFree_iff_containment
#print axioms NoMate.freeOrPull_of_pre
#print axioms NoMate.violation_third_twin_bracket
#print axioms NoMate.two_twin_brackets_of_violation
#print axioms NoMate.rung_le_of_occurs_raise
#print axioms NoMate.fourth_suit_pull_accounting
#print axioms NoMate.third_suit_frozen_rung
#print axioms NoMate.occurs_of_mem
#print axioms NoMate.containment_of_twinLiveAtBottom
#print axioms NoMate.mateRaiseFree_of_twinLiveAtBottom
