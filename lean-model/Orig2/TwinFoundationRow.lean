import Orig2.TwinPullLift

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000

/-!
# Orig2.TwinFoundationRow — the same-suit foundation-row excursion

While `y` is unseated and is the top of the foundation row of `y.suit`, a
pair-free middle may raise another card `c` with `c.suit = y.suit`.  Because
`c` is `nextUp`, it is exactly the next rank of the row, so the raise puts
`c` on top of `y` and changes the foundation top from `y` to `c`.  This card
proves the exact excursion rows:

* the raise makes `c` the foundation top (`sameSuit_raise_foundTop`) and
  blocks every pull of `y` while `c` is still above it
  (`sameSuit_raise_blocks_pull`);
* pulling `c` back onto its original card parent restores the source
  exactly (`sameSuit_excursion_parent_eq`);
* pulling `c` back onto the parent's twin is literally one `tabToTab`
  slide/cargo letter (`sameSuit_excursion_twin_slide`,
  `sameSuit_excursion_twin_cargoLeg`);
* the pull target is forced to be the original parent or the parent's twin
  (`cardParent_pull_target_forced`), and the whole excursion is a pair-free
  orbit from its endpoint back to its source, for every pair `x`
  (`cardParent_raise_pull_cancels`, `sameSuit_excursion_pairFreeOrbit`);
* at an attachment context `Ctx s y p`, the twin arm is again an attachment
  context (`sameSuit_excursion_twin_ctx`), so the excursion does not break
  the attachment context.

The bundled strongest row of the file is
`sameSuit_foundationRow_cancels`.

All proofs are `sorry`-free, `Classical.choice`-free, and use no new axioms.
-/

open State

namespace TwinFoundationRow

/-! ## §0. Same-suit bookkeeping -/

/-- The twin of a card has the twin suit. -/
theorem twin_suit (c : Card) : c.twin.suit = c.suit.twin := rfl

/-- A same-suit card distinct from `y` is off the twin pair containing `y`. -/
theorem sameSuit_off_pair {x y c : Card}
    (hy : y = x ∨ y = x.twin)
    (hcSuit : c.suit = y.suit) (hcy : c ≠ y) :
    c ≠ x ∧ c ≠ x.twin := by
  constructor
  · intro hcx
    rcases hy with hyx | hyt
    · exact hcy (hcx.trans hyx.symm)
    · have h : x.suit = x.suit.twin := by
        rw [hcx] at hcSuit
        rw [hyt] at hcSuit
        exact hcSuit
      exact Suit.twin_ne x.suit h.symm
  · intro hcxt
    rcases hy with hyx | hyt
    · have h : x.suit.twin = x.suit := by
        rw [hcxt] at hcSuit
        rw [hyx] at hcSuit
        exact hcSuit
      exact Suit.twin_ne x.suit h
    · exact hcy (hcxt.trans hyt.symm)

/-- The same-suit raise letter is pair-free for a pair containing `y`. -/
theorem sameSuit_raise_notFoundPair {x y c : Card}
    (hy : y = x ∨ y = x.twin)
    (hcSuit : c.suit = y.suit) (hcy : c ≠ y) :
    NotFoundPair x (Move.tabToFound c) := by
  obtain ⟨hcx, hcxt⟩ := sameSuit_off_pair hy hcSuit hcy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    injection h with h1
    exact hcx h1
  · intro h
    injection h with h1
    exact hcxt h1
  · intro b h
    cases h
  · intro b h
    cases h

/-- The same-suit pull letter is pair-free for a pair containing `y`. -/
theorem sameSuit_pull_notFoundPair {x y c : Card} {b : Base}
    (hy : y = x ∨ y = x.twin)
    (hcSuit : c.suit = y.suit) (hcy : c ≠ y) :
    NotFoundPair x (Move.foundToTab c b) := by
  obtain ⟨hcx, hcxt⟩ := sameSuit_off_pair hy hcSuit hcy
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro b' h
    injection h with h1 h2
    exact hcx h1
  · intro b' h
    injection h with h1 h2
    exact hcxt h1

/-! ## §1. The raise changes the foundation top -/

/-- A successful raise appends the raised card to its foundation row. -/
theorem raise_found_self {s s1 : State} {c : Card}
    (hraise : State.step s (Move.tabToFound c) = some s1) :
    s1.found c.suit = s.found c.suit ++ [c] := by
  obtain ⟨-, a, -, hs1⟩ := step_tabToFound_inv hraise
  rw [hs1]
  exact setFound_found_self

/-- **The same-suit raise makes `c` the foundation top.** -/
theorem sameSuit_raise_foundTop {s s1 : State} {c y : Card}
    (hcSuit : c.suit = y.suit)
    (hraise : State.step s (Move.tabToFound c) = some s1) :
    s1.foundTop y.suit = some c := by
  obtain ⟨-, a, -, hs1⟩ := step_tabToFound_inv hraise
  change lastOf (s1.found y.suit) = some c
  rw [hs1, hcSuit, setFound_found_self]
  exact lastOf_snoc

/-- After the same-suit raise, `c` sits above `y` in the foundation row. -/
theorem sameSuit_raise_above {s s1 : State} {c y : Card}
    (hcSuit : c.suit = y.suit)
    (hraise : State.step s (Move.tabToFound c) = some s1) :
    s1.found y.suit = s.found y.suit ++ [c] := by
  have h := raise_found_self hraise
  rwa [hcSuit] at h

/-- **The final pull of `y` is blocked whenever `y` is not the foundation
top.** -/
theorem foundToTab_none_of_foundTop_ne {st : State} {y : Card} {b : Base}
    (h : st.foundTop y.suit ≠ some y) :
    State.step st (Move.foundToTab y b) = none := by
  cases ht : st.foundTop y.suit with
  | none =>
      simp [State.step, ht]
  | some c =>
      have hcy : c ≠ y := by
        intro hEq
        exact h (by rw [ht, hEq])
      have hdec : decide (c = y) = false := decide_false_of_not hcy
      simp [State.step, ht, hdec]

/-- **The same-suit raise blocks the final pull of `y`.**  While `c` is on
the foundation above `y`, no pull of `y` can fire. -/
theorem sameSuit_raise_blocks_pull {s s1 : State} {c y : Card}
    (hcSuit : c.suit = y.suit) (hcy : c ≠ y)
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (b : Base) :
    State.step s1 (Move.foundToTab y b) = none := by
  apply foundToTab_none_of_foundTop_ne
  rw [sameSuit_raise_foundTop hcSuit hraise]
  intro hEq
  exact hcy (Option.some.inj hEq)

/-- A successful final pull of `y` forces `y` to be the foundation top. -/
theorem foundTop_of_foundToTab_some {st t : State} {y : Card} {b : Base}
    (h : State.step st (Move.foundToTab y b) = some t) :
    st.foundTop y.suit = some y := by
  obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv h
  rw [hc'c] at htop
  exact htop

/-- No final pull of `y` can fire at the state where the same-suit card
`c` has just been raised above it. -/
theorem sameSuit_raise_not_finalPull {s s1 : State} {c y : Card}
    (hcSuit : c.suit = y.suit) (hcy : c ≠ y)
    (hraise : State.step s (Move.tabToFound c) = some s1) :
    ∀ b t, State.step s1 (Move.foundToTab y b) ≠ some t := by
  intro b t h
  rw [sameSuit_raise_blocks_pull hcSuit hcy hraise b] at h
  cases h

/-! ## §2. The pull target is forced to the parent or its twin -/

/-- A card seated `.inr` on a card parent is not a king. -/
theorem seated_inr_rank_ne_king {s : State} {c r : Card}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r)) :
    c.rank ≠ Rank.king := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hfit : canSitOn c r = true := (tfc_seat_parent hwf hhold hlast).1
  intro hking
  have hlt := ((canSitOn_eq c r).mp hfit).1
  have hidx : c.rank.toIdx = 12 := by rw [hking]; rfl
  have hlt' := Rank.toIdx_lt r.rank
  omega

/-- **The pull of a card seated on a card parent is forced to that parent
or its twin.**  The empty-pile arm is excluded because the card is not a
king, and the card-parent arm is pinned by `tfc_fitting_parent`. -/
theorem cardParent_pull_target_forced {s s1 t : State} {c r : Card} {b : Base}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r))
    (hpull : State.step s1 (Move.foundToTab c b) = some t) :
    b = Sum.inr r ∨ b = Sum.inr r.twin := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hfitC : canSitOn c r = true := (tfc_seat_parent hwf hhold hlast).1
  obtain ⟨-, -, -, hcp, -⟩ := step_foundToTab_inv hpull
  cases b with
  | inl a' =>
      have hking : c.rank = Rank.king := (canPlace_inl hcp).2
      exact absurd hking (seated_inr_rank_ne_king hwf hseat)
  | inr z =>
      obtain ⟨k, hk, hfitZ⟩ := canPlace_inr hcp
      rcases tfc_fitting_parent hfitC hfitZ with h | h
      · exact Or.inl (by rw [h])
      · have hz : z = r.twin := by
          have h' := congrArg Card.twin h
          rw [tfc_card_twin_twin] at h'
          exact h'.symm
        exact Or.inr (by rw [hz])

/-- **The forced cancellation of a card-parent raise-pull excursion.**  Any
raise of a card `c` seated on a card parent `r`, followed by a pull of `c`
back to the tableau, is a pair-free orbit from its endpoint to its source
(for every pair `x`). -/
theorem cardParent_raise_pull_cancels {x c r : Card} {s s1 t : State} {b : Base}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (hpull : State.step s1 (Move.foundToTab c b) = some t) :
    (b = Sum.inr r ∨ b = Sum.inr r.twin) ∧ PairFreeOrbit x t s := by
  have hb := cardParent_pull_target_forced hwf hseat hpull
  exact ⟨hb, TwinForcedCancel.p_excursion_cancels hwf hseat hraise hpull hb⟩

/-! ## §3. The exact parent and twin rows -/

/-- **Parent arm: the excursion restores the source exactly.** -/
theorem sameSuit_excursion_parent_eq {s s1 t : State} {c r : Card}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (hpull : State.step s1 (Move.foundToTab c (Sum.inr r)) = some t) :
    t = s :=
  TwinCargoKernel.raise_pull_self_eq hwf hseat hraise hpull

/-- **Parent arm: the excursion is a pair-free loop**, for every pair `x`. -/
theorem sameSuit_excursion_parent_pairFreeOrbit {x : Card} {s s1 t : State}
    {c r : Card}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (hpull : State.step s1 (Move.foundToTab c (Sum.inr r)) = some t) :
    PairFreeOrbit x t s := by
  have ht : t = s := sameSuit_excursion_parent_eq hwf hseat hraise hpull
  rw [ht]
  exact pairFreeOrbit_refl x s

/-- **Twin arm: the raise-pull pair is exactly one slide of `c` onto the
parent's twin.** -/
theorem sameSuit_excursion_twin_slide {s s1 t : State} {c r : Card}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (hpull : State.step s1 (Move.foundToTab c (Sum.inr r.twin)) = some t) :
    State.step s (Move.tabToTab c (Sum.inr r.twin)) = some t :=
  TwinCargoKernel.raise_pull_twin_step_eq hwf hseat hraise hpull

/-- **Twin arm: the endpoint is a literal `slidAt` endpoint.** -/
theorem sameSuit_excursion_twin_endpoint {s s1 t : State} {c r : Card}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (hpull : State.step s1 (Move.foundToTab c (Sum.inr r.twin)) = some t) :
    ∃ a, s.pileHolding c = some a ∧
      t = TwinRaiseCommute.slidAt s c (Sum.inr r.twin) a := by
  have hslide := sameSuit_excursion_twin_slide hwf hseat hraise hpull
  obtain ⟨a, hhold, -, -, hshape⟩ := step_tabToTab_inv hslide
  exact ⟨a, hhold, hshape⟩

/-- **Twin arm: the excursion is a cargo letter.** -/
theorem sameSuit_excursion_twin_cargoLeg {s s1 t : State} {c r : Card}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (hpull : State.step s1 (Move.foundToTab c (Sum.inr r.twin)) = some t) :
    CargoLeg s t :=
  TwinCargoKernel.raise_pull_twin_cargoLeg hwf hseat hraise hpull

/-- **Twin arm: the excursion is a pair-free orbit** from its endpoint back
to its source, for every pair `x`. -/
theorem sameSuit_excursion_twin_pairFreeOrbit {x : Card} {s s1 t : State}
    {c r : Card}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (hpull : State.step s1 (Move.foundToTab c (Sum.inr r.twin)) = some t) :
    PairFreeOrbit x t s := by
  have hslide := sameSuit_excursion_twin_slide hwf hseat hraise hpull
  have hrev := TwinForcedCancel.reversibleAtW_slide_twin_of_seated hwf hseat hslide
  have hwalk : ShufflePlayW s [Move.tabToTab c (Sum.inr r.twin)] t :=
    Walk.cons hrev hslide (Walk.nil t)
  have hno : ∀ m ∈ [Move.tabToTab c (Sum.inr r.twin)], NotFoundPair x m := by
    intro m hm
    rw [List.mem_singleton] at hm
    subst hm
    exact ⟨by simp, by simp, fun b => by simp, fun b => by simp⟩
  exact TwinDetourArbitraryMid.pairFreeReversal_unseated hwf hwalk hno

/-! ## §4. Rank arithmetic for the attachment base -/

/-- The same-suit raised card is exactly the next rank above the foundation
top `y`. -/
theorem rank_succ_of_raise_sameSuit {s s1 : State} {c y : Card}
    (hwf : s.WF) (hft : s.foundTop y.suit = some y)
    (hcSuit : c.suit = y.suit)
    (hraise : State.step s (Move.tabToFound c) = some s1) :
    c.rank.toIdx = y.rank.toIdx + 1 := by
  have hnext : s.nextUp c = true := (step_tabToFound_inv hraise).1
  have hidx : c.rank.toIdx = (s.found c.suit).length := by
    unfold State.nextUp State.foundHeight at hnext
    exact of_decide_eq_true hnext
  have hchop := TwinPairFreeRev.found_chop_length_eq_rank hwf hft
  have hdecomp := lastOf_chop hft
  have hlen : (s.found c.suit).length = y.rank.toIdx + 1 := by
    rw [hcSuit, hdecomp]
    simp [hchop]
  omega

/-- **The attachment base `p` is not the twin of the raised card's parent.**
The raised card has rank one above `y`; its parent has rank one above that;
the attachment base `p` fits `y`, hence has rank exactly one above `y`.  The
parent's twin has the parent's rank, so it cannot be `p`. -/
theorem attachment_base_ne_parent_twin {s s1 : State} {y p c r : Card}
    (hwf : s.WF) (hft : s.foundTop y.suit = some y)
    (hfitY : canSitOn y p = true)
    (hcSuit : c.suit = y.suit)
    (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1) :
    p ≠ r.twin := by
  have hcIdx := rank_succ_of_raise_sameSuit hwf hft hcSuit hraise
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hfitC : canSitOn c r = true := (tfc_seat_parent hwf hhold hlast).1
  have hcr : c.rank.toIdx + 1 = r.rank.toIdx := ((canSitOn_eq c r).mp hfitC).1
  have hyp : y.rank.toIdx + 1 = p.rank.toIdx := ((canSitOn_eq y p).mp hfitY).1
  intro hpr
  have hrank : p.rank.toIdx = r.twin.rank.toIdx := by rw [hpr]
  have hrt : r.twin.rank.toIdx = r.rank.toIdx := rfl
  omega

/-! ## §5. The slide keeps the attachment base a pile top -/

/-- A slide of `c` to a target pile disjoint from `p` and from the source
pile of `c` leaves `p` a pile top. -/
theorem slidAt_pileOfTop_of_ne {s : State} {c z p : Card} {a kt kp : Anchor}
    (hwf : s.WF)
    (hhold : s.pileHolding c = some a)
    (hcp : s.canPlace c (Sum.inr z) = true)
    (htgt' : (s.setPile a (Pile.afterRunRemoved (s.piles a)
      (below c (s.piles a).faceUp))).pileOfTop z = some kt)
    (hkp : s.pileOfTop p = some kp)
    (hpa : kp ≠ a) (hpkt : kp ≠ kt) :
    (TwinRaiseCommute.slidAt s c (Sum.inr z) a).pileOfTop p = some kp := by
  have hstep : State.step s (Move.tabToTab c (Sum.inr z)) =
      some (TwinRaiseCommute.slidAt s c (Sum.inr z) a) :=
    TwinRaiseCommute.step_tabToTab_some hhold hcp
  have hwfS : (TwinRaiseCommute.slidAt s c (Sum.inr z) a).WF :=
    step_wf hwf hstep
  have hpiles : (TwinRaiseCommute.slidAt s c (Sum.inr z) a).piles kp =
      s.piles kp := by
    unfold TwinRaiseCommute.slidAt
    rw [putRun_piles_inr_ne
      (s.setPile a (Pile.afterRunRemoved (s.piles a)
        (below c (s.piles a).faceUp)))
      (fromCard c (s.piles a).faceUp) z kt htgt' (a' := kp) hpkt]
    exact setPile_piles_ne (st := s) (k := kp) (b := a)
      (Q := Pile.afterRunRemoved (s.piles a) (below c (s.piles a).faceUp)) hpa
  apply (pileOfTop_eq_some_iff hwfS).mpr
  show ((TwinRaiseCommute.slidAt s c (Sum.inr z) a).piles kp).top = some p
  rw [hpiles]
  exact (pileOfTop_eq_some_iff hwf).mp hkp

/-! ## §6. The twin arm preserves the attachment context -/

/-- **At an attachment context, the twin arm remains an attachment
context.**  The slide to the parent's twin changes the foundation nowhere,
keeps `y` unseated, and edits only piles other than the one topped by the
attachment base `p`. -/
theorem sameSuit_excursion_twin_ctx {s s1 t : State} {y p c r : Card}
    (hCtx : TwinPullLift.Ctx s y p)
    (hcSuit : c.suit = y.suit)
    (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (hpull : State.step s1 (Move.foundToTab c (Sum.inr r.twin)) = some t) :
    TwinPullLift.Ctx t y p := by
  obtain ⟨hwf, hseatY, htopY, ⟨kp, hkp⟩, hfitY⟩ := hCtx
  have hslide := sameSuit_excursion_twin_slide hwf hseat hraise hpull
  have hrev := TwinForcedCancel.reversibleAtW_slide_twin_of_seated hwf hseat hslide
  have hnoY : NotFoundPair y (Move.tabToTab c (Sum.inr r.twin)) :=
    ⟨by simp, by simp, fun b => by simp, fun b => by simp⟩
  have hseatY' : seatOf t y = none :=
    pairFree_step_seat_none hwf hslide hrev hnoY (Or.inl rfl) hseatY
  obtain ⟨a', hhold', hcp', -, hshape⟩ := step_tabToTab_inv hslide
  have hfound : t.found = s.found := by
    rw [hshape]
    exact TwinRaiseCommute.slidAt_found s c (Sum.inr r.twin) a'
  have htopY' : t.foundTop y.suit = some y := by
    unfold State.foundTop
    rw [hfound]
    exact htopY
  have hwfT : t.WF := step_wf hwf hslide
  obtain ⟨kt, htgt, hfitZ⟩ := canPlace_inr hcp'
  have hp_ne_rtwin : p ≠ r.twin :=
    attachment_base_ne_parent_twin hwf htopY hfitY hcSuit hseat hraise
  have hkp_ne_kt : kp ≠ kt := by
    intro hEq
    apply hp_ne_rtwin
    have htopP : (s.piles kp).top = some p := (pileOfTop_eq_some_iff hwf).mp hkp
    have htopT : (s.piles kt).top = some r.twin :=
      (pileOfTop_eq_some_iff hwf).mp htgt
    rw [← hEq] at htopT
    exact Option.some.inj (htopP.symm.trans htopT)
  obtain ⟨-, aC, hpoC, -⟩ := step_tabToFound_inv hraise
  have hholdC : s.pileHolding c = some aC :=
    (pileHolding_eq_some_iff hwf).mpr
      (Pile.mem_of_top (tfc_pileOfTop_top hpoC).2)
  have ha : aC = a' := pileHolding_inj hholdC hhold'
  have hp_ne_c : p ≠ c := by
    intro hpc
    have hcol := ((canSitOn_eq y p).mp hfitY).2
    rw [hpc, hcSuit] at hcol
    exact hcol rfl
  have hkp_ne_a : kp ≠ a' := by
    intro hEq
    have htopP : (s.piles kp).top = some p := (pileOfTop_eq_some_iff hwf).mp hkp
    have htopC : (s.piles aC).top = some c := (tfc_pileOfTop_top hpoC).2
    have hEqC : kp = aC := hEq.trans ha.symm
    rw [hEqC] at htopP
    exact hp_ne_c (Option.some.inj (htopP.symm.trans htopC))
  have hca_ne_rtwin : c ≠ r.twin := by
    intro h
    have hlt := ((canSitOn_eq c r.twin).mp hfitZ).1
    rw [h] at hlt
    omega
  have htopC' : (s.piles a').top = some c := by
    have h := (tfc_pileOfTop_top hpoC).2
    rwa [ha] at h
  have hka : a' ≠ kt := by
    intro hEq
    have htopT : (s.piles kt).top = some r.twin :=
      (pileOfTop_eq_some_iff hwf).mp htgt
    have h1 : (s.piles a').top = some r.twin := by
      rw [hEq]
      exact htopT
    exact hca_ne_rtwin (Option.some.inj (htopC'.symm.trans h1))
  obtain ⟨a0, hhold0, hbelow_ne0, hlast0⟩ := tfc_seatOf_of_inr hseat
  have ha0 : a0 = a' := pileHolding_inj hhold0 hhold'
  have hbelow_ne' : below c (s.piles a').faceUp ≠ [] := by
    rw [← ha0]
    exact hbelow_ne0
  have hlast' : lastOf (below c (s.piles a').faceUp) = some r := by
    rw [← ha0]
    exact hlast0
  have hQtop : (Pile.afterRunRemoved (s.piles a')
      (below c (s.piles a').faceUp)).top = some r := by
    show lastOf (Pile.afterRunRemoved (s.piles a')
      (below c (s.piles a').faceUp)).faceUp = some r
    rw [afterRunRemoved_faceUp_ne hbelow_ne']
    exact hlast'
  have hQ : (Pile.afterRunRemoved (s.piles a')
      (below c (s.piles a').faceUp)).top ≠ some r.twin := by
    intro hEq
    have hr : r = r.twin := Option.some.inj (hQtop.symm.trans hEq)
    exact card_twin_ne r hr.symm
  have htgt' : (s.setPile a' (Pile.afterRunRemoved (s.piles a')
      (below c (s.piles a').faceUp))).pileOfTop r.twin = some kt :=
    pileOfTop_setPile_ne hwf htgt hka hQ
  have htopP' : t.pileOfTop p = some kp := by
    rw [hshape]
    exact slidAt_pileOfTop_of_ne hwf hhold' hcp' htgt' hkp hkp_ne_a hkp_ne_kt
  exact ⟨hwfT, hseatY', htopY', ⟨kp, htopP'⟩, hfitY⟩

/-! ## §7. The same-suit row: cancellation and context -/

/-- **The same-suit excursion is pair-free.**  In both forced arms, the
endpoint is pair-free orbit back to the source, for every pair `x`. -/
theorem sameSuit_excursion_pairFreeOrbit {x : Card} {s s1 t : State}
    {c r : Card} {b : Base}
    (hwf : s.WF) (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (hpull : State.step s1 (Move.foundToTab c b) = some t)
    (hb : b = Sum.inr r ∨ b = Sum.inr r.twin) :
    PairFreeOrbit x t s :=
  TwinForcedCancel.p_excursion_cancels hwf hseat hraise hpull hb

/-- **The strongest forced-cancellation row of the same-suit foundation
excursion.**  It records simultaneously:

* the raise changes the foundation top to `c`, and every pull of `y` is
  blocked there;
* the pull target is forced to the original parent `r` or its twin;
* the excursion is pair-free orbit from its endpoint to its source;
* the parent arm restores the state exactly;
* the twin arm is literally one slide, a cargo letter, and preserves the
  attachment context. -/
theorem sameSuit_foundationRow_cancels {x : Card} {s s1 t : State}
    {y p c r : Card} {b : Base}
    (hCtx : TwinPullLift.Ctx s y p)
    (hcSuit : c.suit = y.suit) (hcy : c ≠ y)
    (hseat : seatOf s c = some (Sum.inr r))
    (hraise : State.step s (Move.tabToFound c) = some s1)
    (hpull : State.step s1 (Move.foundToTab c b) = some t) :
    s1.foundTop y.suit = some c ∧
      (∀ b' t', State.step s1 (Move.foundToTab y b') ≠ some t') ∧
        (b = Sum.inr r ∨ b = Sum.inr r.twin) ∧
          PairFreeOrbit x t s ∧
            (b = Sum.inr r → t = s) ∧
              (b = Sum.inr r.twin →
                State.step s (Move.tabToTab c (Sum.inr r.twin)) = some t ∧
                  CargoLeg s t ∧ TwinPullLift.Ctx t y p) := by
  have htopC := sameSuit_raise_foundTop hcSuit hraise
  have hblocked := sameSuit_raise_blocks_pull hcSuit hcy hraise
  have hb := cardParent_pull_target_forced hCtx.wf hseat hpull
  refine ⟨htopC, ?_, hb, sameSuit_excursion_pairFreeOrbit hCtx.wf hseat hraise hpull hb, ?_, ?_⟩
  · intro b' t' h
    rw [hblocked b'] at h
    cases h
  · intro hbr
    exact sameSuit_excursion_parent_eq hCtx.wf hseat hraise (by rwa [hbr] at hpull)
  · intro hbt
    have hpull' : State.step s1 (Move.foundToTab c (Sum.inr r.twin)) = some t := by
      rwa [hbt] at hpull
    exact ⟨sameSuit_excursion_twin_slide hCtx.wf hseat hraise hpull',
      sameSuit_excursion_twin_cargoLeg hCtx.wf hseat hraise hpull',
      sameSuit_excursion_twin_ctx hCtx hcSuit hseat hraise hpull'⟩

/-! ## §8. Audit -/

#print axioms twin_suit
#print axioms sameSuit_off_pair
#print axioms sameSuit_raise_notFoundPair
#print axioms sameSuit_pull_notFoundPair
#print axioms raise_found_self
#print axioms sameSuit_raise_foundTop
#print axioms sameSuit_raise_above
#print axioms foundToTab_none_of_foundTop_ne
#print axioms sameSuit_raise_blocks_pull
#print axioms foundTop_of_foundToTab_some
#print axioms sameSuit_raise_not_finalPull
#print axioms seated_inr_rank_ne_king
#print axioms cardParent_pull_target_forced
#print axioms cardParent_raise_pull_cancels
#print axioms sameSuit_excursion_parent_eq
#print axioms sameSuit_excursion_parent_pairFreeOrbit
#print axioms sameSuit_excursion_twin_slide
#print axioms sameSuit_excursion_twin_endpoint
#print axioms sameSuit_excursion_twin_cargoLeg
#print axioms sameSuit_excursion_twin_pairFreeOrbit
#print axioms rank_succ_of_raise_sameSuit
#print axioms attachment_base_ne_parent_twin
#print axioms slidAt_pileOfTop_of_ne
#print axioms sameSuit_excursion_twin_ctx
#print axioms sameSuit_excursion_pairFreeOrbit
#print axioms sameSuit_foundationRow_cancels

end TwinFoundationRow
