import Orig2.TwinCargoKernel
import Orig2.SeatMateStack
import Orig2.Integrity
import Orig2.TwinDetourArbitraryMid

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2.TwinForcedCancel — forced cancellation of the other twin and the
`p`-excursion

The single raise-pull detour of the pair `{x, x.twin}` is

```
raise y  ++  mid  ++  pull y b
```

with `y ∈ {x, x.twin}`, `y` seated on the card parent `p` at the source,
and `mid` pair-free.  Write `q = y.twin` for the other twin; at the
source `q` sits on `p.twin`.

This card proves the two forced-cancellation rows on which the identity
detour rests.

* **The other twin is pinned.**  While `y` is off the tableau, a
  pair-free middle can only move `q` between the two fitting parents
  `p.twin` and `p` (`tfc_fitting_parent`).  If the final pull of `y` is
  onto `p`, then `p` is a pile top at the end; a `q` sitting on `p`
  would cover it (`tfc_seat_parent`), so `q` must be back on `p.twin`.
  This is `otherTwin_forced_identity` (with the intermediate invariant
  `otherTwin_seat_cases`).

* **A `p`-excursion cancels.**  `lastPull_base_eq_parent_or_twin` forces
  the pull target of a raised `p` to be its original card parent `r` or
  `r.twin`.  On `r` the raise-pull pair is a state-level loop
  (`TwinCargoKernel.raise_pull_self_eq`); on `r.twin` the whole
  excursion is exactly one `tabToTab` slide of `p` carrying its run
  (`TwinCargoKernel.raise_pull_twin_step_eq`).  Both are pair-free from
  the excursion's endpoint back to its source: `p_excursion_cancels`.

The sufficient residual isolated by this reduction is `PullLift`:
attaching `y` to `p` is functorial along a pair-free orbit between two
states where `p` is a pile top and `y` lies on its foundation.  The file
proves that this residual implies the mandatory identity row
(`singleDetour_identity_arbitraryMid_of_pullLift`) and the old residual
`TwinDetourArbitraryMid.SingleDetourIdentityArbitraryMid`
(`singleDetourIdentityArbitraryMid_of_pullLift`).

For the exchange detour the file proves the forced swap seats
(`otherTwin_forced_exchange`, `singleDetour_exchange_endpoint_seats`):
the only surviving middle is the slide of `q` from `p.twin` to `p`.

Zero `sorry`, zero `Classical.choice`, no new axioms.
-/

open State

namespace TwinForcedCancel

/-! ## §0. Walk kit -/

/-- Split a witness walk at a list prefix. -/
theorem walk_split {P : State → Move → Prop} :
    ∀ {s s' : State} {A B : List Move},
      Walk P s (A ++ B) s' → ∃ u, Walk P s A u ∧ Walk P u B s' := by
  intro s s' A B
  induction A generalizing s with
  | nil =>
      intro h
      exact ⟨s, .nil s, by simpa using h⟩
  | cons m rest ih =>
      intro h
      cases h with
      | cons hlet hstep hrest =>
          obtain ⟨u, hA, hB⟩ := ih hrest
          exact ⟨u, .cons hlet hstep hA, hB⟩

/-- Expose the first letter of a witness walk. -/
theorem walk_cons_inv {P : State → Move → Prop} {st s' : State}
    {m : Move} {ρ : List Move} (h : Walk P st (m :: ρ) s') :
    ∃ s1, P st m ∧ State.step st m = some s1 ∧ Walk P s1 ρ s' := by
  cases h with
  | cons hlet hstep hrest => exact ⟨_, hlet, hstep, hrest⟩

/-! ## §1. Seat and pile-top kit -/

/-- A foundation card is off the tableau, hence unseated. -/
theorem seatOf_none_of_mem_found {s : State} (hwf : s.WF) {c : Card}
    (h : c ∈ s.found c.suit) : seatOf s c = none := by
  apply tfc_seatOf_none
  apply tfc_pileHolding_none
  intro a hmem
  exact ((mem_found_unique hwf h).1 a).2 hmem

/-- A pile top is seated. -/
theorem seatOf_ne_none_of_pileOfTop {s : State} {c : Card} {a : Anchor}
    (h : s.pileOfTop c = some a) : seatOf s c ≠ none := by
  intro hse
  have hhold : s.pileHolding c = none := holdNone_of_seatNone hse
  exact (tfc_not_mem_faceUp_of_holdNone hhold a)
    (lastOf_mem (tfc_pileOfTop_top h).2)

/-- A member of a list other than its last element lies in the chop. -/
theorem mem_chop_of_mem_ne_last {l : List Card} {y c : Card}
    (hy : y ∈ l) (hlast : lastOf l = some c) (hyc : y ≠ c) : y ∈ chop l := by
  obtain ⟨front, hfront⟩ := lastOf_eq_snoc hlast
  rw [hfront] at hy ⊢
  rw [chop_snoc]
  rcases List.mem_append.mp hy with h | h
  · exact h
  · exact absurd (List.mem_singleton.mp h) hyc

/-- Foundation membership survives a pair-free letter. -/
theorem found_mem_pairFree_step {x y : Card} {u v : State} {m : Move}
    (hstep : State.step u m = some v)
    (hmem : y ∈ u.found y.suit)
    (hno : NotFoundPair x m) (hy : y = x ∨ y = x.twin) :
    y ∈ v.found y.suit := by
  cases m with
  | draw =>
      rw [← (chart_draw hstep).2.1 y.suit]
      exact hmem
  | wasteToFound c =>
      obtain ⟨-, z, zs, hw, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      by_cases hcs : c.suit = y.suit
      · have hmem' : y ∈ u.found c.suit := by rw [hcs]; exact hmem
        rw [show y.suit = c.suit from hcs.symm, setFound_found_self,
          List.mem_append]
        exact Or.inl hmem'
      · rw [setFound_found_ne (fun h => hcs h.symm)]
        exact hmem
  | wasteToTab c b =>
      obtain ⟨-, z, zs, hw, hs⟩ := step_wasteToTab_inv hstep
      rw [hs, putCard_found]
      exact hmem
  | tabToFound c =>
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      by_cases hcs : c.suit = y.suit
      · have hmem' : y ∈ u.found c.suit := by rw [hcs]; exact hmem
        rw [show y.suit = c.suit from hcs.symm, setFound_found_self,
          List.mem_append]
        exact Or.inl hmem'
      · rw [setFound_found_ne (fun h => hcs h.symm)]
        exact hmem
  | foundToTab c b =>
      obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
      have hyc : y ≠ c := by
        intro hyc
        rcases hy with hx | hxt
        · exact hno.2.2.1 b (by rw [← hyc, hx])
        · exact hno.2.2.2 b (by rw [← hyc, hxt])
      rw [hs, putCard_found]
      by_cases hcs : c.suit = y.suit
      · rw [show y.suit = c.suit from hcs.symm, setFound_found_self]
        have hmem' : y ∈ u.found c.suit := by rw [hcs]; exact hmem
        have hlast_c : lastOf (u.found c.suit) = some c := by
          show u.foundTop c.suit = some c
          rw [htop, hc'c]
        exact mem_chop_of_mem_ne_last hmem' hlast_c hyc
      · rw [setFound_found_ne (fun h => hcs h.symm)]
        exact hmem
  | tabToTab c b =>
      obtain ⟨a, hhold, hcp, hfromne, hs⟩ := step_tabToTab_inv hstep
      rw [hs, putRun_found, setPile_found]
      exact hmem

/-- Foundation membership survives a pair-free play. -/
theorem found_mem_pairFree_play {x y : Card} (hy : y = x ∨ y = x.twin) :
    ∀ {s t : State} {play : List Move},
      ShufflePlayW s play t →
      (∀ m ∈ play, NotFoundPair x m) →
      y ∈ s.found y.suit → y ∈ t.found y.suit := by
  intro s t play
  induction play generalizing s with
  | nil =>
      intro hplay _ hmem
      cases hplay
      exact hmem
  | cons m rest ih =>
      intro hplay hno hmem
      obtain ⟨s1, hrev, hstep, hrest⟩ := walk_cons_inv hplay
      exact ih hrest
        (fun n hn => hno n (List.mem_cons_of_mem m hn))
        (found_mem_pairFree_step hstep hmem (hno m (by simp)) hy)

/-- Fitting the twin parent implies fitting the parent. -/
theorem canSitOn_parent_of_twin {q p : Card}
    (h : canSitOn q p.twin = true) : canSitOn q p = true := by
  have h' : canSitOn q p.twin = canSitOn q p := canSitOn_twin_right q p
  rwa [h'] at h

/-- A card fitting some card parent is not a king. -/
theorem canSitOn_not_king {c z : Card} (h : canSitOn c z = true) :
    c.rank ≠ Rank.king := by
  obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp h
  intro hk
  have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
  have hlt := Rank.toIdx_lt z.rank
  omega

/-- At a state where `q` sits on `p` or `p.twin`, the static fit under
`p.twin` holds. -/
theorem canSitOn_p_twin_of_seat_cases {s : State} (hwf : s.WF) {q p : Card}
    (h : seatOf s q = some (Sum.inr p.twin) ∨
      seatOf s q = some (Sum.inr p)) :
    canSitOn q p.twin = true := by
  rcases h with h | h
  · obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr h
    exact (tfc_seat_parent hwf hhold hlast).1
  · obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr h
    have hp : canSitOn q p = true := (tfc_seat_parent hwf hhold hlast).1
    have ht : canSitOn q p.twin = canSitOn q p := canSitOn_twin_right q p
    rwa [ht]

/-! ## §2. The other twin's only two seats -/

/-- **The one-letter invariant.**  A pair-free reversible letter cannot
move `q` off the pair of fitting parents `{p, p.twin}`.  The only letter
that moves `q` at all is a slide of `q` itself, whose card-parent target
is pinned by `tfc_fitting_parent`; a slide onto an empty pile is
excluded because `q` fits `p` and therefore is not a king. -/
theorem otherTwin_step_cases
    {x q p : Card} {u v : State} {m : Move}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m) (hm : NotFoundPair x m)
    (hq : q = x ∨ q = x.twin)
    (hfit : canSitOn q p = true)
    (hseat : seatOf u q = some (Sum.inr p.twin) ∨
      seatOf u q = some (Sum.inr p)) :
    seatOf v q = some (Sum.inr p.twin) ∨
      seatOf v q = some (Sum.inr p) := by
  have hse_ne : seatOf u q ≠ none := by
    rcases hseat with h | h <;> rw [h] <;> simp
  cases m with
  | draw =>
      simpa [(chart_draw hstep).1 q] using hseat
  | wasteToFound c =>
      exact absurd hrev (wasteToFound_not_reversibleAtW u c)
  | wasteToTab c b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u c b)
  | tabToFound c =>
      have hcq : c ≠ q := by
        intro hcq
        rcases hq with hx | hx
        · exact hm.1 (by rw [hcq, hx])
        · exact hm.2.1 (by rw [hcq, hx])
      have h := raise_seat_change_of_seated hstep hrev hse_ne (Ne.symm hcq)
      rw [h]
      exact hseat
  | foundToTab c b =>
      have hcq : c ≠ q := by
        intro hcq
        rcases hq with hx | hx
        · exact hm.2.2.1 b (by rw [hcq, hx])
        · exact hm.2.2.2 b (by rw [hcq, hx])
      have h := pull_seat_change hstep q (Ne.symm hcq)
      rw [h]
      exact hseat
  | tabToTab c b =>
      by_cases hcq : c = q
      · subst c
        obtain ⟨a, hhold, hcp, hfromne, hshape⟩ := step_tabToTab_inv hstep
        have hseat_v : seatOf v q = some b := by
          have h := tfc_seat_point_edit hwf hstep hrev q
          rwa [ite_eq_left rfl] at h
        cases b with
        | inl a' =>
            have hking : q.rank = Rank.king := (canPlace_inl hcp).2
            exact absurd hking (canSitOn_not_king hfit)
        | inr z =>
            obtain ⟨k, hloc, hfitq⟩ := canPlace_inr hcp
            rcases tfc_fitting_parent (c := q) (w := p) (z := z) hfit hfitq with
              hzp | hzp
            · right
              rwa [← hzp] at hseat_v
            · left
              have hz : z = p.twin := by
                have h := congrArg Card.twin hzp
                rw [tfc_card_twin_twin] at h
                exact h.symm
              rwa [hz] at hseat_v
      · have h := tfc_seat_point_edit hwf hstep hrev q
        rw [ite_eq_right (Ne.symm hcq)] at h
        rw [h]
        exact hseat

/-- **The other twin's seat invariant.**  Along a pair-free middle
starting with `q` on `p.twin` (or already on `p`), the other twin only
ever sits on `p.twin` or `p`. -/
theorem otherTwin_seat_cases
    {x y q p : Card} {s1 s2 : State} {mid : List Move}
    (hy : y = x ∨ y = x.twin) (hq : q = y.twin)
    (hwf1 : s1.WF)
    (hmid : ShufflePlayW s1 mid s2)
    (hno : ∀ m ∈ mid, NotFoundPair x m)
    (hseatQ : seatOf s1 q = some (Sum.inr p.twin) ∨
      seatOf s1 q = some (Sum.inr p)) :
    seatOf s2 q = some (Sum.inr p.twin) ∨
      seatOf s2 q = some (Sum.inr p) := by
  have hqpair : q = x ∨ q = x.twin := by
    rcases hy with hyx | hyt
    · right
      rw [hq, hyx]
    · left
      rw [hq, hyt, tfc_card_twin_twin]
  revert hseatQ hwf1
  induction hmid with
  | nil =>
      intro hwf1 hseatQ
      exact hseatQ
  | @cons s0 s1' W m ρ hrev hstep hrest ih =>
      intro hwf1 hseatQ
      have hm : NotFoundPair x m := hno m (by simp)
      have hfitTwin := canSitOn_p_twin_of_seat_cases (s := s0) (q := q) (p := p)
        hwf1 hseatQ
      have hfit : canSitOn q p = true := canSitOn_parent_of_twin hfitTwin
      have hstepCases := otherTwin_step_cases (u := s0) (v := s1') (m := m)
        hwf1 hstep hrev hm hqpair hfit hseatQ
      exact ih (fun n hn => hno n (List.mem_cons_of_mem m hn))
        (step_wf hwf1 hstep) hstepCases

/-! ## §3. Forced identity and forced exchange of the other twin -/

/-- **Other-twin forced cancellation (identity).**  If the final pull of
`y` is onto `p`, then `p` is a pile top at the endpoint.  The other twin
`q` can then only be on `p.twin`: on `p` it would cover `p`, making
`s2.pileOfTop p` empty.  Consequently `p.twin` is not a pile top either
(it is covered by `q`). -/
theorem otherTwin_forced_identity
    {x y q p : Card} {a : Anchor} {s1 s2 : State} {mid : List Move}
    (hy : y = x ∨ y = x.twin) (hq : q = y.twin)
    (hwf1 : s1.WF)
    (hmid : ShufflePlayW s1 mid s2)
    (hno : ∀ m ∈ mid, NotFoundPair x m)
    (hseatQ : seatOf s1 q = some (Sum.inr p.twin))
    (hpTop : s2.pileOfTop p = some a) :
    seatOf s2 q = some (Sum.inr p.twin) ∧ s2.pileOfTop p.twin = none := by
  have hcases := otherTwin_seat_cases hy hq hwf1 hmid hno (Or.inl hseatQ)
  have hwf2 : s2.WF := run_wf hwf1 (Walk_run _ hmid)
  rcases hcases with hleft | hright
  · refine ⟨hleft, ?_⟩
    obtain ⟨b, hhold, -, hlast⟩ := tfc_seatOf_of_inr hleft
    exact (tfc_seat_parent hwf2 hhold hlast).2
  · exfalso
    obtain ⟨b, hhold, -, hlast⟩ := tfc_seatOf_of_inr hright
    have hpnone := (tfc_seat_parent hwf2 hhold hlast).2
    rw [hpTop] at hpnone
    cases hpnone

/-- **Other-twin forced cancellation (exchange).**  If the final pull of
`y` is onto `p.twin`, then `p.twin` is a pile top at the endpoint, so
`q` cannot still be on `p.twin`; the invariant leaves only `p`. -/
theorem otherTwin_forced_exchange
    {x y q p : Card} {a : Anchor} {s1 s2 : State} {mid : List Move}
    (hy : y = x ∨ y = x.twin) (hq : q = y.twin)
    (hwf1 : s1.WF)
    (hmid : ShufflePlayW s1 mid s2)
    (hno : ∀ m ∈ mid, NotFoundPair x m)
    (hseatQ : seatOf s1 q = some (Sum.inr p.twin))
    (hpTopTwin : s2.pileOfTop p.twin = some a) :
    seatOf s2 q = some (Sum.inr p) ∧ s2.pileOfTop p = none := by
  have hcases := otherTwin_seat_cases hy hq hwf1 hmid hno (Or.inl hseatQ)
  have hwf2 : s2.WF := run_wf hwf1 (Walk_run _ hmid)
  rcases hcases with hleft | hright
  · exfalso
    obtain ⟨b, hhold, -, hlast⟩ := tfc_seatOf_of_inr hleft
    have hpnone := (tfc_seat_parent hwf2 hhold hlast).2
    rw [hpTopTwin] at hpnone
    cases hpnone
  · refine ⟨hright, ?_⟩
    obtain ⟨b, hhold, -, hlast⟩ := tfc_seatOf_of_inr hright
    exact (tfc_seat_parent hwf2 hhold hlast).2

/-! ## §4. The `p`-excursion -/

/-- A raise of a card seated on a card parent makes that parent the pile
top of the same pile. -/
theorem raise_makes_parent_top
    {u s1 : State} {y p : Card}
    (hwf : u.WF) (hseat : seatOf u y = some (Sum.inr p))
    (hraise : State.step u (Move.tabToFound y) = some s1) :
    ∃ a, s1.pileOfTop p = some a := by
  obtain ⟨a, hhold, hbelow_ne, hlast⟩ := tfc_seatOf_of_inr hseat
  obtain ⟨-, a₀, hpa₀, hs1⟩ := step_tabToFound_inv hraise
  have htop₀ : (u.piles a₀).top = some y := (tfc_pileOfTop_top hpa₀).2
  have hhold₀ : u.pileHolding y = some a₀ :=
    (pileHolding_eq_some_iff hwf).mpr (Pile.mem_of_top htop₀)
  have ha₀ : a₀ = a := pileHolding_inj hhold₀ hhold
  subst a₀
  have hface : (u.piles a).faceUp = chop (u.piles a).faceUp ++ [y] :=
    lastOf_chop (tfc_pileOfTop_top hpa₀).2
  have hnodup : (u.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
  have hy_not_chop : y ∉ chop (u.piles a).faceUp := by
    rw [hface] at hnodup
    exact List.snoc_nodup_notMem _ _ hnodup
  have hbelow_eq : below y (u.piles a).faceUp = chop (u.piles a).faceUp := by
    conv => lhs; rw [hface]
    exact below_snoc_not_mem hy_not_chop
  have hlast_chop : lastOf (chop (u.piles a).faceUp) = some p := by
    rw [← hbelow_eq]
    exact hlast
  have hchop_ne : chop (u.piles a).faceUp ≠ [] := by
    intro hnil
    rw [hnil] at hlast_chop
    nomatch hlast_chop
  have hs1_pa : s1.piles a =
      Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp) := by
    rw [hs1]
    simp only [ite_true]
  refine ⟨a, ?_⟩
  rw [pileOfTop_eq_some_iff (step_wf hwf hraise)]
  show lastOf (s1.piles a).faceUp = some p
  rw [hs1_pa, afterRunRemoved_faceUp_ne hchop_ne]
  exact hlast_chop

/-- A slide of a card seated on a card parent towards the parent's twin
is reversible (the chop below the card is nonempty). -/
theorem reversibleAtW_slide_twin_of_seated
    {s t : State} {p r : Card}
    (hwf : s.WF) (hseat : seatOf s p = some (Sum.inr r))
    (hslide : State.step s (Move.tabToTab p (Sum.inr r.twin)) = some t) :
    reversibleAtW s (Move.tabToTab p (Sum.inr r.twin)) := by
  obtain ⟨a, hhold, hbelow_ne, hlast⟩ := tfc_seatOf_of_inr hseat
  obtain ⟨a', hhold', hcp, hfromne, hshape⟩ := step_tabToTab_inv hslide
  have ha : a' = a := pileHolding_inj hhold' hhold
  subst a'
  have hR : tabToTabR s p (Sum.inr r.twin) = true := by
    cases hbl : below p (s.piles a).faceUp with
    | nil => exact absurd hbl hbelow_ne
    | cons w ws => simp [tabToTabR, hhold, hcp, hbl]
  exact (tabToTabR_iff_reversibleAtW hwf p (Sum.inr r.twin)).mp hR

/-- **The `p`-excursion returns exactly.**  Pulling `p` back onto its
original card parent `r` restores the state before the raise. -/
theorem p_excursion_return_eq
    {s s1 t : State} {p r : Card}
    (hwf : s.WF) (hseat : seatOf s p = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound p) = some s1)
    (hpull : State.step s1 (Move.foundToTab p (Sum.inr r)) = some t) :
    t = s :=
  TwinCargoKernel.raise_pull_self_eq hwf hseat hraise hpull

/-- **The `p`-excursion exchange is a slide.**  Pulling `p` onto the twin
`r.twin` of its original parent is literally the slide of `p`'s run onto
`r.twin`, taken at the state before the raise. -/
theorem p_excursion_exchange_slide
    {s s1 t : State} {p r : Card}
    (hwf : s.WF) (hseat : seatOf s p = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound p) = some s1)
    (hpull : State.step s1 (Move.foundToTab p (Sum.inr r.twin)) = some t) :
    State.step s (Move.tabToTab p (Sum.inr r.twin)) = some t :=
  TwinCargoKernel.raise_pull_twin_step_eq hwf hseat hraise hpull

/-- **The `p`-excursion cancels.**  A raise of `p` off its card parent
`r` followed by a pull of `p` back is pair-free orbit to its source in
both forced cases:

* onto `r`: the raise-pull pair is the state-level loop
  `raise_pull_self_eq`;
* onto `r.twin`: the pair is exactly one `tabToTab` slide of `p`'s run
  (`raise_pull_twin_step_eq`), and the slide is pair-free and reversible.

`lastPull_base_eq_parent_or_twin` supplies this dichotomy for every pull
of a card that started on a card parent. -/
theorem p_excursion_cancels
    {x p r : Card} {s s1 t : State} {b : Base}
    (hwf : s.WF)
    (hseat : seatOf s p = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound p) = some s1)
    (hpull : State.step s1 (Move.foundToTab p b) = some t)
    (hb : b = Sum.inr r ∨ b = Sum.inr r.twin) :
    PairFreeOrbit x t s := by
  rcases hb with hb | hb
  · subst hb
    have ht : t = s := p_excursion_return_eq hwf hseat hraise hpull
    rw [ht]
    exact pairFreeOrbit_refl x s
  · subst hb
    have hslide : State.step s (Move.tabToTab p (Sum.inr r.twin)) = some t :=
      p_excursion_exchange_slide hwf hseat hraise hpull
    have hrev := reversibleAtW_slide_twin_of_seated hwf hseat hslide
    have hwalk : ShufflePlayW s [Move.tabToTab p (Sum.inr r.twin)] t :=
      Walk.cons hrev hslide (Walk.nil t)
    have hno : ∀ m ∈ [Move.tabToTab p (Sum.inr r.twin)], NotFoundPair x m := by
      intro m hm
      rw [List.mem_singleton] at hm
      subst hm
      exact ⟨by simp, by simp, fun b => by simp, fun b => by simp⟩
    exact TwinDetourArbitraryMid.pairFreeReversal_unseated hwf hwalk hno

/-! ## §5. The exact identity residual: attaching `y` to `p` -/

/-- **`PullLift x y p`** — the attachment lift.  If `y` is unseated at
both `s1` and `s2`, `p` is a pile top at both, and `s2` is pair-free
orbit to `s1`, then attaching `y` on `p` at both endpoints is pair-free
orbit in the same direction.

This is the precise remaining geometric obligation of the arbitrary
middle: the pair-free middle has already been reversed by
`pairFreeReversal_unseated`; what is missing is transporting that
reversal across the presence of `y` on `p` (the `p`-excursions are
handled by `p_excursion_cancels`). -/
def PullLift (x y p : Card) : Prop :=
  ∀ {s1 s2 : State} {ρ : List Move},
    s1.WF → s2.WF →
    seatOf s1 y = none → seatOf s2 y = none →
    y ∈ s1.found y.suit → y ∈ s2.found y.suit →
    (∃ a, s1.pileOfTop p = some a) →
    (∃ b, s2.pileOfTop p = some b) →
    canSitOn y p = true →
    ShufflePlayW s2 ρ s1 →
    (∀ m ∈ ρ, NotFoundPair x m) →
    PairFreeOrbit x (TwinRaiseCommute.pulledAt s2 y (Sum.inr p))
      (TwinRaiseCommute.pulledAt s1 y (Sum.inr p))

/-- **The identity detour from the attachment lift.**  The raise and the
final pull are state-level inverses of `pulledAt` (via
`raise_pull_self_eq`), and the pair-free middle is reversed by
`pairFreeReversal_unseated`; `PullLift` then attaches `y` to `p` at both
ends. -/
theorem singleDetour_identity_arbitraryMid_of_pullLift
    {u v : State} {x y : Card} {p : Card} {mid : List Move}
    (hlift : PullLift x y p)
    (hwf : u.WF)
    (hy : y = x ∨ y = x.twin)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hplay : ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p)]) v)
    (hnoMid : ∀ m ∈ mid, NotFoundPair x m) :
    PairFreeOrbit x v u := by
  obtain ⟨s1, hrevR, hraise, hrest⟩ := walk_cons_inv hplay
  obtain ⟨s2, hmid, hpullwalk⟩ := walk_split hrest
  obtain ⟨v', hrevP, hpull, hnil⟩ := walk_cons_inv hpullwalk
  cases hnil
  have hwf1 : s1.WF := step_wf hwf hraise
  have hwf2 : s2.WF := run_wf hwf1 (Walk_run _ hmid)
  have hseatY1 : seatOf s1 y = none :=
    TwinSpliceComm.seatOf_tabToFound_mover_none hwf hraise
  have hseatY2 : seatOf s2 y = none :=
    pairFree_play_seat_none hwf1 hmid hnoMid hy hseatY1
  obtain ⟨a0, hhold0, -, hlast0⟩ := tfc_seatOf_of_inr hseatY
  have hfit : canSitOn y p = true := (tfc_seat_parent hwf hhold0 hlast0).1
  have hpTop1 : ∃ a, s1.pileOfTop p = some a :=
    raise_makes_parent_top hwf hseatY hraise
  have hpTop2 : ∃ a, s2.pileOfTop p = some a := by
    obtain ⟨c', htop, hc', hcp, hshape⟩ := step_foundToTab_inv hpull
    obtain ⟨k, hloc, hfitq⟩ := canPlace_inr hcp
    exact ⟨k, hloc⟩
  obtain ⟨hnext, aR, hpaR, hs1shape⟩ := step_tabToFound_inv hraise
  have htrio := tabToFound_found_trio (st := u) (s₁ := s1) (c := y) (a := aR)
    hs1shape
  have hs1_foundTop : s1.foundTop y.suit = some y := htrio.2.2
  have hfound1 : y ∈ s1.found y.suit := lastOf_mem hs1_foundTop
  have hfound2 : y ∈ s2.found y.suit :=
    found_mem_pairFree_play hy hmid hnoMid hfound1
  obtain ⟨ρ, hρ, hnoρ⟩ :=
    TwinDetourArbitraryMid.pairFreeReversal_unseated hwf1 hmid hnoMid
  have hL := hlift hwf1 hwf2 hseatY1 hseatY2 hfound1 hfound2
    hpTop1 hpTop2 hfit hρ hnoρ
  have hv : v = TwinRaiseCommute.pulledAt s2 y (Sum.inr p) := by
    obtain ⟨c', htop, hc', hcp, hshape⟩ := step_foundToTab_inv hpull
    simpa [TwinRaiseCommute.pulledAt] using hshape
  obtain ⟨aP, hs1_top⟩ := hpTop1
  have hcp1 : s1.canPlace y (Sum.inr p) = true :=
    tfa_canPlace_inr (st := s1) (c := y) (z := p) (k := aP) hs1_top hfit
  have hstep1 : State.step s1 (Move.foundToTab y (Sum.inr p)) =
      some (TwinRaiseCommute.pulledAt s1 y (Sum.inr p)) := by
    simpa [TwinRaiseCommute.pulledAt] using
      step_foundToTab_splice (st := s1) (c := y) (b := Sum.inr p)
        hs1_foundTop hcp1
  have hu' : TwinRaiseCommute.pulledAt s1 y (Sum.inr p) = u :=
    TwinCargoKernel.raise_pull_self_eq hwf hseatY hraise hstep1
  have hu : u = TwinRaiseCommute.pulledAt s1 y (Sum.inr p) := hu'.symm
  simpa [hv, hu] using hL

/-- **The old identity residual follows from the attachment lift.** -/
theorem singleDetourIdentityArbitraryMid_of_pullLift {x : Card}
    (h : ∀ y p, PullLift x y p) :
    TwinDetourArbitraryMid.SingleDetourIdentityArbitraryMid x := by
  intro u v y p mid hwf hx hxt hy hseatY hplay hnoMid hvx hvt
  exact singleDetour_identity_arbitraryMid_of_pullLift (h y p)
    hwf hy hseatY hplay hnoMid

/-! ## §6. Endpoint seats of the two detours -/

/-- **The identity detour's pair seats.**  The other twin is forced back
to `p.twin`, and `y` itself is pulled onto `p`. -/
theorem singleDetour_identity_endpoint_seats
    {u v : State} {x y q : Card} {p : Card} {mid : List Move}
    (hy : y = x ∨ y = x.twin) (hq : q = y.twin)
    (hwf : u.WF)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hseatQ : seatOf u q = some (Sum.inr p.twin))
    (hplay : ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p)]) v)
    (hnoMid : ∀ m ∈ mid, NotFoundPair x m) :
    seatOf v y = some (Sum.inr p) ∧ seatOf v q = some (Sum.inr p.twin) := by
  obtain ⟨s1, hrevR, hraise, hrest⟩ := walk_cons_inv hplay
  obtain ⟨s2, hmid, hpullwalk⟩ := walk_split hrest
  obtain ⟨v', hrevP, hpull, hnil⟩ := walk_cons_inv hpullwalk
  cases hnil
  have hwf1 : s1.WF := step_wf hwf hraise
  have hwf2 : s2.WF := run_wf hwf1 (Walk_run _ hmid)
  have hqy : q ≠ y := by
    rw [hq]
    exact card_twin_ne y
  have hseatQ1 : seatOf s1 q = some (Sum.inr p.twin) := by
    have h := raise_seat_change_of_seated hraise hrevR
      (by rw [hseatQ]; simp) (hqy)
    rw [h] 
    exact hseatQ
  have hpTop : ∃ a, s2.pileOfTop p = some a := by
    obtain ⟨c', htop, hc', hcp, hshape⟩ := step_foundToTab_inv hpull
    obtain ⟨k, hloc, hfitq⟩ := canPlace_inr hcp
    exact ⟨k, hloc⟩
  obtain ⟨aP, hpTopS⟩ := hpTop
  have hforced := otherTwin_forced_identity hy hq hwf1 hmid hnoMid
    hseatQ1 hpTopS
  have hyv : seatOf v y = some (Sum.inr p) :=
    TwinSpliceComm.seatOf_foundToTab_mover hwf2 hpull
  have hqv : seatOf v q = seatOf s2 q :=
    pull_seat_change hpull q (hqy)
  exact ⟨hyv, hqv.trans hforced.1⟩

/-- **The exchange detour's pair seats.**  The other twin is forced onto
`p` (it left `p.twin` for `p` and cannot return), while `y` is pulled
onto `p.twin`. -/
theorem singleDetour_exchange_endpoint_seats
    {u v : State} {x y q : Card} {p : Card} {mid : List Move}
    (hy : y = x ∨ y = x.twin) (hq : q = y.twin)
    (hwf : u.WF)
    (hseatY : seatOf u y = some (Sum.inr p))
    (hseatQ : seatOf u q = some (Sum.inr p.twin))
    (hplay : ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p.twin)]) v)
    (hnoMid : ∀ m ∈ mid, NotFoundPair x m) :
    seatOf v y = some (Sum.inr p.twin) ∧ seatOf v q = some (Sum.inr p) := by
  obtain ⟨s1, hrevR, hraise, hrest⟩ := walk_cons_inv hplay
  obtain ⟨s2, hmid, hpullwalk⟩ := walk_split hrest
  obtain ⟨v', hrevP, hpull, hnil⟩ := walk_cons_inv hpullwalk
  cases hnil
  have hwf1 : s1.WF := step_wf hwf hraise
  have hwf2 : s2.WF := run_wf hwf1 (Walk_run _ hmid)
  have hqy : q ≠ y := by
    rw [hq]
    exact card_twin_ne y
  have hseatQ1 : seatOf s1 q = some (Sum.inr p.twin) := by
    have h := raise_seat_change_of_seated hraise hrevR
      (by rw [hseatQ]; simp) (hqy)
    rw [h]
    exact hseatQ
  have hpTopTwin : ∃ a, s2.pileOfTop p.twin = some a := by
    obtain ⟨c', htop, hc', hcp, hshape⟩ := step_foundToTab_inv hpull
    obtain ⟨k, hloc, hfitq⟩ := canPlace_inr hcp
    exact ⟨k, hloc⟩
  obtain ⟨aT, hpTopTwinS⟩ := hpTopTwin
  have hforced := otherTwin_forced_exchange hy hq hwf1 hmid hnoMid
    hseatQ1 hpTopTwinS
  have hyv : seatOf v y = some (Sum.inr p.twin) :=
    TwinSpliceComm.seatOf_foundToTab_mover hwf2 hpull
  have hqv : seatOf v q = seatOf s2 q :=
    pull_seat_change hpull q (hqy)
  exact ⟨hyv, hqv.trans hforced.1⟩

/-! ## §7. Audit -/

#print axioms walk_split
#print axioms walk_cons_inv
#print axioms seatOf_none_of_mem_found
#print axioms seatOf_ne_none_of_pileOfTop
#print axioms mem_chop_of_mem_ne_last
#print axioms found_mem_pairFree_step
#print axioms found_mem_pairFree_play
#print axioms canSitOn_parent_of_twin
#print axioms canSitOn_not_king
#print axioms canSitOn_p_twin_of_seat_cases
#print axioms otherTwin_step_cases
#print axioms otherTwin_seat_cases
#print axioms otherTwin_forced_identity
#print axioms otherTwin_forced_exchange
#print axioms raise_makes_parent_top
#print axioms reversibleAtW_slide_twin_of_seated
#print axioms p_excursion_return_eq
#print axioms p_excursion_exchange_slide
#print axioms p_excursion_cancels
#print axioms PullLift
#print axioms singleDetour_identity_arbitraryMid_of_pullLift
#print axioms singleDetourIdentityArbitraryMid_of_pullLift
#print axioms singleDetour_identity_endpoint_seats
#print axioms singleDetour_exchange_endpoint_seats

/-! ## §8. Report

### Proved unconditionally

* `otherTwin_step_cases` and `otherTwin_seat_cases`: while the middle is
  pair-free, the other twin `q` can occupy only `p.twin` or `p`.  The only
  letter that moves `q` is a slide of `q`; its card-parent target is
  pinned to `{p, p.twin}` by `tfc_fitting_parent`, and an empty-pile
  target is excluded because `q` fits `p` and therefore is not a king.

* `found_mem_pairFree_step` and `found_mem_pairFree_play`: a card already
  on its foundation stays there through a pair-free play (the pull of that
  very card is excluded).  This keeps the attachment `pulledAt` faithful:
  `PullLift` assumes `y` really lies on its foundation at both ends.

* `otherTwin_forced_identity`: if the final pull is onto `p` (so `p` is
  a pile top at the end), then `q` is on `p.twin` and `p.twin` is not a
  pile top.  `q` on `p` would cover `p` by `tfc_seat_parent`.

* `otherTwin_forced_exchange`: if the final pull is onto `p.twin` (so
  `p.twin` is a pile top at the end), then `q` is on `p` and `p` is not
  a pile top.  This is the forced swap configuration.

* `raise_makes_parent_top`: raising a card seated on `p` makes `p` the
  top of the same pile.

* `reversibleAtW_slide_twin_of_seated`: the slide of a card seated on a
  card parent `r` towards `r.twin` is reversible (its chop below the
  card is nonempty).

* `p_excursion_return_eq`: the return-to-`r` excursion restores the state
  exactly.

* `p_excursion_exchange_slide`: the exchange-to-`r.twin` excursion is
  literally the single slide of `p`'s run.

* `p_excursion_cancels`: a raise of `p` off its card parent `r` followed
  by a pull of `p` back onto `r` or `r.twin` is pair-free orbit to its
  source.  On `r` it is the state-level loop
  `TwinCargoKernel.raise_pull_self_eq`; on `r.twin` it is the single
  `tabToTab` slide computed by `TwinCargoKernel.raise_pull_twin_step_eq`.

* `singleDetour_identity_endpoint_seats` and
  `singleDetour_exchange_endpoint_seats`: the endpoint pair seats of the
  two detours are the identity and swap configurations respectively.

* `singleDetour_identity_arbitraryMid_of_pullLift`: the mandatory
  identity row follows from `PullLift x y p`.

* `singleDetourIdentityArbitraryMid_of_pullLift`: consequently
  `TwinDetourArbitraryMid.SingleDetourIdentityArbitraryMid x` follows
  from `∀ y p, PullLift x y p`.

### Exact remaining identity obligation

The sufficient residual isolated by this reduction is the attachment
lift, stated above as `PullLift x y p`:

```
def PullLift (x y p : Card) : Prop :=
  ∀ {s1 s2 : State} {ρ : List Move},
    s1.WF → s2.WF →
    seatOf s1 y = none → seatOf s2 y = none →
    y ∈ s1.found y.suit → y ∈ s2.found y.suit →
    (∃ a, s1.pileOfTop p = some a) →
    (∃ b, s2.pileOfTop p = some b) →
    canSitOn y p = true →
    ShufflePlayW s2 ρ s1 →
    (∀ m ∈ ρ, NotFoundPair x m) →
    PairFreeOrbit x (TwinRaiseCommute.pulledAt s2 y (Sum.inr p))
      (TwinRaiseCommute.pulledAt s1 y (Sum.inr p))
```

The `p`-raise/pull subcases of this lift are discharged by
`p_excursion_cancels`; the `q`-excursion subcases are pinned by
`otherTwin_seat_cases`.  What remains is the functoriality of attaching
`y` on `p` across the pair-free middle.

### Exact remaining exchange obligation

For the exchange detour the forced seat analysis is complete
(`otherTwin_forced_exchange`, `singleDetour_exchange_endpoint_seats`),
but the state-level conclusion is still the residual of
`Orig2/TwinDetourArbitraryMid.lean`:

```
def SingleDetourExchangeArbitraryMid (x : Card) : Prop :=
  ∀ {u v : State} {y : Card} {p : Card} {mid : List Move},
    u.WF →
    (∃ z, seatOf u x = some (Sum.inr z)) →
    (∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) →
    (y = x ∨ y = x.twin) →
    seatOf u y = some (Sum.inr p) →
    ShufflePlayW u
      (Move.tabToFound y :: mid ++ [Move.foundToTab y (Sum.inr p.twin)]) v →
    (∀ m ∈ mid, NotFoundPair x m) →
    (∃ w, seatOf v x = some (Sum.inr w)) →
    (∃ w' : Card, seatOf v x.twin = some (Sum.inr w'.twin)) →
    PairFreeOrbit x v (u.spliceTwinRuns x)
```

The forced-seat rows identify the surviving middle as the slide of `q`
from `p.twin` to `p`; the canonical instance is
`TwinDetourArbitraryMid.singleDetour_exchange_canonical`.

### Axioms

Every exported head is audited above.  The footprint is the Lean
kernel's standard `propext` / `Quot.sound`; there is no `sorryAx`, no
`Classical.choice`, and no new axiom.
-/

end TwinForcedCancel
