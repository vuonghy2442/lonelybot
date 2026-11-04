import Orig2.Fork.Split.ForkDrainClose
import Orig2.Fork.Class.ForkRaiseReorderProof
import Orig2.Fork.Class.ForkPosition
import Orig2.Fork.Class.ForkPairRung
import Orig2.Fork.Local.ForkCriticalPair
import Orig2.Substrate.PairClassSeed

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# Temp/Drain_transport_rows — the three `RaiseTransport` rows of the drain

`RaiseTransport x` (`Orig2/Fork/Split/ForkDrainInduction.lean:556`) has three
fields.  This card proves the two that are structural and isolates the third:

* **(A) `hcanrev`** — a licensed raise is reversible
  (`OneColourClosure.canRaise_reversibleAtW`), so the reversibility provider of
  `drain_raise_phase` is unconditional.
* **(C) `rank_preserved`** — already proved as `DrainClose.floor_raise`
  (the rank-floor transport across a licensed raise); this card re-exports it
  at the `RaiseTransport` field shape.
* **(B) `raisable_preserved`** — proved here.  The only card whose S-licence can
  *improve* across a bare raise is (i) the card directly beneath the raised one
  (which becomes the pile top, hence is vanilla-raisable) or (ii) the unique
  `rank + 1` card of the raised suit.  The latter is pinned by the twin pair:
  the two `CanRaiseS` twins sit on the two cards of the opposite colour family
  one rank above them, so the `c.rank + 1` card is either one of those two (and
  hence cannot be a top) or is already founded.  Hence no *new* blocked S-live
  third card is ever created.
* **(D) `raiseTransport_all` / `drain_phase_fork`** — the assembly.

House rules: no `sorry`, no `Classical`, no `noncomputable`.
-/

namespace OneColourClosure

/-! ## §0. Re-export of the `CanRaiseS` row (field 1) -/

/-- **Field 1: `CanRaiseS_preserved`.**  The lane's forward licence shift
(`specShift_sem_fwd`) at `d = x.twin`. -/
theorem drain_transport_canRaiseS_row {u u' : State} {x c : Card}
    (hwf : u.WF) (h : Drain.DrainInvariant u x)
    (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hstep : State.step u (Move.tabToFound c) = some u') :
    CanRaiseS u' x.twin := by
  have hstepS : RaiseStepS u u' c := ⟨u, Steps.refl u, hstep⟩
  have hd : x.twin ≠ c := fun hcon => hct hcon.symm
  have hdt : x.twin ≠ c.twin := by
    intro hcon
    have hxc : x = c := by
      simpa [card_twin_twin] using congrArg Card.twin hcon
    exact hcx hxc.symm
  exact specShift_sem_fwd hwf hstepS hd hdt h.2.1

/-! ## §1. Job (A): the reversibility provider -/

/-- **Job (A).**  A licensed raise of a card is reversible
(`canRaise_reversibleAtW`); the extra hypotheses are `drain_raise_phase`'s
provider signature, not mathematical input. -/
theorem canrev_drain_row {u : State} {x c : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x) (hra : Drain.DrainRaisable u x)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin) :
    reversibleAtW u (Move.tabToFound c) :=
  canRaise_reversibleAtW huwf hc

/-! ## §2. Job (C): the rank floor row -/

/-- **Job (C).**  The invariant's rank floor survives a licensed raise
(`DrainClose.floor_raise`).  The floor's own rank hypothesis `x.rank ≤ c.rank`
is the `DrainInvariant` floor applied to `CanRaiseS.now c hc`. -/
theorem rank_preserved_row {u u' : State} {x c : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x) (hra : Drain.DrainRaisable u x)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hstep : State.step u (Move.tabToFound c) = some u') :
    ∀ d, CanRaiseS u' d → x.rank.toIdx ≤ d.rank.toIdx := by
  have hrank : x.rank.toIdx ≤ c.rank.toIdx :=
    hinv.2.2.2 c (CanRaiseS.now c hc)
  exact DrainClose.floor_raise huwf hc hrank hstep hinv.2.2.2

/-! ## §2b. Forward monotonicity of the vanilla licence -/

/-- **A licensed raise cannot destroy another card's vanilla licence.**  The
raised pile's top is `c`; another card's top pile is a different pile, and its
suit is not `c.suit` (equal rank with `c` would name `c`). -/
theorem canRaise_tabToFound_fwd_of_ne {u u' : State} {c d : Card}
    (huwf : u.WF) (hstep : State.step u (Move.tabToFound c) = some u')
    (hdc : d ≠ c) (hd : CanRaise u d) :
    CanRaise u' d := by
  obtain ⟨hnext, a, hpa, hseat⟩ := hd
  have hu'wf : u'.WF := step_wf huwf hstep
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have hnextc : u.nextUp c = true := (step_tabToFound_inv hstep).1
  have hsu : d.suit ≠ c.suit := Drain.suit_ne_of_nextUp hnext hnextc hdc
  have hane : a ≠ a0 := by
    intro hae
    subst hae
    have h1 : (u.piles a).top = some d := (pileOfTop_top hpa).2
    have h2 : (u.piles a).top = some c := (pileOfTop_top hpa0).2
    rw [h1] at h2
    exact hdc (Option.some.inj h2)
  have hpile : u'.piles a = u.piles a := by
    rw [hpiles a, ite_eq_right hane]
  have hnext' : u'.nextUp d = true := by
    rw [nextUp_raise_ne hstep hsu]
    exact hnext
  have htop' : (u'.piles a).top = some d := by
    rw [hpile]
    exact (pileOfTop_top hpa).2
  exact ⟨hnext', a, (pileOfTop_eq_some_iff hu'wf).mpr htop', by rw [hpile]; exact hseat⟩

/-! ## §3. List and pile bookkeeping for the third-card row -/

/-- The last card of `P ++ u :: x :: S` is the last card of `x :: S`. -/
theorem lastOf_append_two : ∀ (P : List Card) (u x : Card) (S : List Card),
    lastOf (P ++ u :: x :: S) = lastOf (x :: S)
  | [], _, _, _ => rfl
  | [_], _, _, _ => rfl
  | a :: b :: P, u, x, S => lastOf_append_two (b :: P) u x S

/-- A card followed in the same list by another card is not the last one. -/
theorem lastOf_shape_ne {P S : List Card} {u x : Card}
    (hnd : (P ++ u :: x :: S).Nodup) :
    lastOf (P ++ u :: x :: S) ≠ some u := by
  intro hlast
  have hmem : u ∈ (x :: S) := by
    rw [lastOf_append_two P u x S] at hlast
    exact lastOf_mem hlast
  have hnd' : (u :: x :: S).Nodup := (List.nodup_append.mp hnd).2.1
  exact (List.nodup_cons.mp hnd').1 hmem

/-- **Predecessor uniqueness**: a card occurring once cannot be immediately
followed by two different cards. -/
theorem cons_eq_of_append_cons_eq :
    ∀ (P P' : List Card) (u x y : Card) (S S' : List Card),
      u ∉ P → u ∉ P' → P ++ u :: x :: S = P' ++ u :: y :: S' → x = y
  | [], P', u, x, y, S, S', _, h2, h => by
      cases P' with
      | nil =>
          injection h with _ hx
          exact (List.cons.inj hx).1
      | cons w P2 =>
          have huw : u = w := (List.cons.inj h).1
          exact absurd (by rw [← huw]; exact List.mem_cons_self ..) h2
  | a :: P1, P', u, x, y, S, S', h1, h2, h => by
      have hua : u ≠ a := fun hcon => h1 (by rw [hcon]; exact List.mem_cons_self ..)
      have h1' : u ∉ P1 := fun hm => h1 (List.mem_cons_of_mem a hm)
      cases P' with
      | nil =>
          have hau : a = u := (List.cons.inj h).1
          exact absurd hau.symm hua
      | cons w P2 =>
          have htail : P1 ++ u :: x :: S = P2 ++ u :: y :: S' := (List.cons.inj h).2
          have h2' : u ∉ P2 := fun hm => h2 (List.mem_cons_of_mem w hm)
          exact cons_eq_of_append_cons_eq P1 P2 u x y S S' h1' h2' htail

/-- **Not a pile top.**  A card with another card directly above it in a
`WF` pile is not any pile's top. -/
theorem pileOfTop_eq_none_of_shape {st : State} (hwf : st.WF) {P S : List Card}
    {u x : Card} {a : Anchor} (hshape : (st.piles a).faceUp = P ++ u :: x :: S) :
    st.pileOfTop u = none := by
  have hmem : u ∈ (st.piles a).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hnd : ((st.piles a).faceUp).Nodup := runOK_nodup (hwf.2.1 a)
  rw [hshape] at hnd
  have hlastne : lastOf (st.piles a).faceUp ≠ some u := by
    rw [hshape]
    exact lastOf_shape_ne hnd
  cases hp : st.pileOfTop u with
  | none => rfl
  | some b =>
      have hb : lastOf (st.piles b).faceUp = some u := (pileOfTop_top hp).2
      have hba : b = a := by
        by_cases hne : b = a
        · exact hne
        · exact absurd (lastOf_mem hb) ((mem_faceUp_unique hwf hmem b hne).1)
      exact (hlastne (by rw [← hba]; exact hb)).elim

/-- A card that is last in a `Nodup` list is its own `fromCard`. -/
theorem fromCard_of_last {l : List Card} {c : Card} (hnd : l.Nodup)
    (hlast : lastOf l = some c) :
    fromCard c l = [c] := by
  obtain ⟨bs, hbs⟩ := lastOf_eq_snoc hlast
  have hnot : c ∉ bs := by
    rw [hbs] at hnd
    exact fun hm => (List.nodup_append.mp hnd).2.2 c hm c (List.mem_singleton_self c) rfl
  rw [hbs]
  exact fromCard_append_singleton_of_not_mem hnot

/-- **S-live and top ⇒ vanilla-raisable.**  The flat seat clause and the
licence's seat clause agree when the card is the pile top. -/
theorem canRaise_of_canRaiseS_of_top {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (h : CanRaiseS st c) (hpa : st.pileOfTop c = some a) :
    CanRaise st c := by
  have htop : lastOf (st.piles a).faceUp = some c := (pileOfTop_top hpa).2
  have hmem : c ∈ (st.piles a).faceUp := lastOf_mem htop
  have hhold : st.pileHolding c = some a := (pileHolding_eq_some_iff hwf).mpr hmem
  have hnd : ((st.piles a).faceUp).Nodup := runOK_nodup (hwf.2.1 a)
  exact canRaise_of_canRaiseS_of_exposed hwf hhold (fromCard_of_last hnd htop) h

/-- **The two `S`-live twins sit on the same card.**  Two distinct cards of the
same list cannot have the same immediate predecessor. -/
theorem twin_under_card_ne {u : State} {x : Card} {U V : Card} {a b : Anchor}
    {P Q S T : List Card} (huwf : u.WF)
    (h1 : (u.piles a).faceUp = P ++ U :: x :: S)
    (h2 : (u.piles b).faceUp = Q ++ V :: x.twin :: T)
    (hUV : U = V) : False := by
  subst hUV
  have hmemU : U ∈ (u.piles a).faceUp := by
    rw [h1]; exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hmemUb : U ∈ (u.piles b).faceUp := by
    rw [h2]; exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hab : b = a := by
    by_cases hba : b = a
    · exact hba
    · exact absurd hmemUb ((mem_faceUp_unique huwf hmemU b hba).1)
  have h2a : (u.piles a).faceUp = Q ++ U :: x.twin :: T := by
    have h2' := h2
    rw [hab] at h2'
    exact h2'
  have hnd : ((u.piles a).faceUp).Nodup := runOK_nodup (huwf.2.1 a)
  have hnd1 : (P ++ U :: x :: S).Nodup := by rw [← h1]; exact hnd
  have hnd2 : (Q ++ U :: x.twin :: T).Nodup := by rw [← h2a]; exact hnd
  have hUP : U ∉ P := fun hm =>
    (List.nodup_append.mp hnd1).2.2 U hm U (List.mem_cons_self ..) rfl
  have hUQ : U ∉ Q := fun hm =>
    (List.nodup_append.mp hnd2).2.2 U hm U (List.mem_cons_self ..) rfl
  have heq : P ++ U :: x :: S = Q ++ U :: x.twin :: T := h1.symm.trans h2a
  exact (card_twin_ne_self x) (cons_eq_of_append_cons_eq P Q U x x.twin S T hUP hUQ heq).symm

/-- **The under-card of the pair.**  The two `S`-live twins sit on the two
distinct cards of the opposite colour family one rank above; in particular
those two cards are twins of one another and neither is a pile top. -/
theorem under_card_twins {u : State} {x : Card} (huwf : u.WF)
    (hxS : CanRaiseS u x) (htS : CanRaiseS u x.twin) (hk : x.rank ≠ Rank.king) :
    ∃ U : Card, U.rank.toIdx = x.rank.toIdx + 1 ∧ U.suit.color ≠ x.suit.color ∧
      u.pileOfTop U = none ∧ u.pileOfTop U.twin = none ∧
      (∃ a, U ∈ (u.piles a).faceUp) ∧ (∃ b, U.twin ∈ (u.piles b).faceUp) := by
  have hkt : x.twin.rank ≠ Rank.king := by rw [Card.twin_rank]; exact hk
  obtain ⟨a, U, P, S, hshape, hrank, hcol⟩ := live_under_card huwf hk hxS
  obtain ⟨b, V, Q, T, hshape2, hrank2, hcol2⟩ := live_under_card huwf hkt htS
  have hcolx : x.twin.suit.color = x.suit.color := by
    rw [Card.twin_suit]; exact Suit.color_twin x.suit
  have hVx : V.suit.color ≠ x.suit.color :=
    fun h => hcol2 (h.trans hcolx.symm)
  have hcolV : V.suit.color = U.suit.color :=
    SeedKit.color_pair hVx.symm hcol.symm
  have hrankV : V.rank.toIdx = U.rank.toIdx := by
    rw [hrank2, hrank, Card.twin_rank]
  have hV : V = U ∨ V = U.twin := SeedKit.rankColor_pair hrankV hcolV
  have hVne : V ≠ U := fun hVU => twin_under_card_ne huwf hshape hshape2 hVU.symm
  have hVt : V = U.twin := hV.resolve_left hVne
  have htopU : u.pileOfTop U = none := pileOfTop_eq_none_of_shape huwf hshape
  have hshapeV : (u.piles b).faceUp = Q ++ U.twin :: x.twin :: T := by
    rw [← hVt]; exact hshape2
  have htopV : u.pileOfTop U.twin = none := pileOfTop_eq_none_of_shape huwf hshapeV
  refine ⟨U, hrank, hcol, htopU, htopV, ⟨a, ?_⟩, ⟨b, ?_⟩⟩
  · rw [hshape]; exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  · rw [hshapeV]; exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))

/-! ## §4. The pair pin: the raised card sits at the pair's rank -/

/-- The raised card has the colour of the *other* family: if it had the pair's
colour its suit would be one of the two pair suits, hence its next-up rank
would be the pair rank, naming `x` or `x.twin`. -/
theorem color_ne_pair {u : State} {x c : Card} (huwf : u.WF)
    (hxS : CanRaiseS u x) (htS : CanRaiseS u x.twin)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin) :
    c.suit.color ≠ x.suit.color := by
  intro hcol
  have hnextc : u.nextUp c = true := hc.1
  have hnextx : u.nextUp x = true := ((canRaiseS_split huwf).mp hxS).1
  have hnextt : u.nextUp x.twin = true := ((canRaiseS_split huwf).mp htS).1
  have hcrank : c.rank.toIdx = u.foundHeight c.suit := by
    simpa [State.nextUp] using of_decide_eq_true hnextc
  rcases SeedKit.suit_family hcol with hsu | hsu
  · have hxrank : x.rank.toIdx = u.foundHeight x.suit := by
      simpa [State.nextUp] using of_decide_eq_true hnextx
    exact hcx (card_eq_of_suit_rank hsu (by rw [hcrank, hxrank, hsu]))
  · have htrank : x.twin.rank.toIdx = u.foundHeight x.twin.suit := by
      simpa [State.nextUp] using of_decide_eq_true hnextt
    have hsu' : c.suit = x.twin.suit := by rw [hsu, Card.twin_suit]
    exact hct (card_eq_of_suit_rank hsu' (by rw [hcrank, htrank, hsu']))

/-- **THE PAIR PIN.**  A licensed raise outside the twin pair can only sit at
the pair's rank.  The two `S`-live twins consume the two opposite-family cards
one rank above (so the `r+1` card of the raised suit is either one of those
two, and hence not a top, or is already founded), and the floor gives
`x.rank ≤ c.rank`. -/
theorem pair_rank_pin {u : State} {x c : Card} (huwf : u.WF)
    (hxS : CanRaiseS u x) (htS : CanRaiseS u x.twin) (hk : x.rank ≠ Rank.king)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hfloor : x.rank.toIdx ≤ c.rank.toIdx) :
    c.rank.toIdx = x.rank.toIdx := by
  have hnextc : u.nextUp c = true := hc.1
  have hcrank : c.rank.toIdx = rungAt u c.suit := by
    simpa [State.nextUp, State.foundHeight, rungAt] using of_decide_eq_true hnextc
  have hnecol : c.suit.color ≠ x.suit.color :=
    color_ne_pair huwf hxS htS hc hcx hct
  obtain ⟨U, hUrank, hUcol, htopU, htopUt, ⟨a, hUmem⟩, ⟨b, hUtmem⟩⟩ :=
    under_card_twins huwf hxS htS hk
  have hCU : c.suit.color = U.suit.color :=
    SeedKit.color_pair hnecol.symm hUcol.symm
  have hkidx : x.rank.toIdx ≠ 12 := by
    intro h12
    exact hk (Rank.toIdx_inj (by rw [h12]; rfl))
  have hle : c.rank.toIdx ≤ x.rank.toIdx + 1 := by
    by_cases hsmall : c.rank.toIdx ≤ x.rank.toIdx + 1
    · exact hsmall
    · exfalso
      have hge : x.rank.toIdx + 2 ≤ c.rank.toIdx := by omega
      let e : Card := ⟨c.suit, FoundKit.Rk (x.rank.toIdx + 1)⟩
      have he_rank : e.rank.toIdx = x.rank.toIdx + 1 :=
        FoundKit.Rk_toIdx _ (by have := Rank.toIdx_lt x.rank; omega)
      have he_col : e.suit.color = U.suit.color := hCU
      have heU : e = U ∨ e = U.twin :=
        SeedKit.rankColor_pair (by rw [he_rank, hUrank]) he_col
      have hfound : e ∈ u.found e.suit := by
        refine FoundKit.mem_found_of_rung huwf ?_
        have hlt : e.rank.toIdx < rungAt u e.suit := by
          rw [he_rank]
          show x.rank.toIdx + 1 < rungAt u c.suit
          rw [← hcrank]
          omega
        exact hlt
      have huniq := mem_found_unique huwf hfound
      rcases heU with heU | heU
      · exact (huniq.1 a).2 (by rw [heU]; exact hUmem)
      · exact (huniq.1 b).2 (by rw [heU]; exact hUtmem)
  have hne : c.rank.toIdx ≠ x.rank.toIdx + 1 := by
    intro hce
    obtain ⟨-, a0, hpa0, -⟩ := hc
    have hcu : c = U ∨ c = U.twin :=
      SeedKit.rankColor_pair (by rw [hce, hUrank]) hCU
    rcases hcu with hcu | hcu
    · rw [hcu] at hpa0
      rw [htopU] at hpa0
      exact absurd hpa0 (by simp)
    · rw [hcu] at hpa0
      rw [htopUt] at hpa0
      exact absurd hpa0 (by simp)
  omega

/-! ## §5. The `c.rank + 1` card is never newly `S`-live -/

/-- **Pile tops of the raised suit's colour survive the raise.**  A card that
is not a top before the raise and has the raised card's colour cannot become
one: the new top of the raised pile is the card (of the opposite colour)
directly beneath `c`. -/
theorem pileOfTop_tabToFound_eq_none_of_same_color {u u' : State} {c X : Card}
    (huwf : u.WF) (hcr : CanRaise u c) (hstep : State.step u (Move.tabToFound c) = some u')
    (hXc : X ≠ c) (hcol : X.suit.color = c.suit.color)
    (hu : u.pileOfTop X = none) :
    u'.pileOfTop X = none := by
  cases h' : u'.pileOfTop X with
  | none => rfl
  | some a =>
      exfalso
      obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
      have hlast : lastOf (u'.piles a).faceUp = some X := (pileOfTop_top h').2
      have hseat : chop (u.piles a0).faceUp ≠ [] ∨
          ((u.piles a0).hidden = [] ∧ c.rank = Rank.king) := by
        obtain ⟨a1, hpa1, hs⟩ := hcr.2
        have ha1 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
        rwa [ha1] at hs
      by_cases haa0 : a = a0
      · subst haa0
        have hfac : u'.piles a = Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp) := by
          rw [hpiles a, ite_eq_left rfl]
        have hXmem : X ∈ (u'.piles a).faceUp := lastOf_mem hlast
        rw [hfac] at hXmem
        have htopface : lastOf (u.piles a).faceUp = some c := (pileOfTop_top hpa0).2
        have hface : (u.piles a).faceUp = chop (u.piles a).faceUp ++ [c] :=
          lastOf_chop htopface
        by_cases hchop : chop (u.piles a).faceUp = []
        · have hhid : (u.piles a).hidden = [] := by
            rcases hseat with hne | ⟨hh, -⟩
            · exact absurd hchop hne
            · exact hh
          rw [hchop, afterRunRemoved_faceUp_bare hhid] at hXmem
          exact absurd hXmem List.not_mem_nil
        · rw [afterRunRemoved_faceUp_ne hchop] at hXmem
          have hlastchop : lastOf (chop (u.piles a).faceUp) = some X := by
            have hh := hlast
            rw [hfac, afterRunRemoved_faceUp_ne hchop] at hh
            exact hh
          obtain ⟨P, hP⟩ := lastOf_eq_snoc hlastchop
          have hshape : (u.piles a).faceUp = P ++ X :: c :: ([] : List Card) := by
            rw [hface, hP]
            simp
          have hok : runOK (P ++ X :: c :: ([] : List Card)) = true := by
            rw [← hshape]; exact huwf.2.1 a
          have hfit : canSitOn c X = true := SeedKit.runOK_adjacent_fit X c P [] hok
          exact ((canSitOn_eq c X).mp hfit).2 hcol.symm
      · have hpile : u'.piles a = u.piles a := by rw [hpiles a, ite_eq_right haa0]
        have hmem : X ∈ (u.piles a).faceUp := by rw [← hpile]; exact lastOf_mem hlast
        have htop : (u.piles a).top = some X := by
          show lastOf (u.piles a).faceUp = some X
          rw [← hpile]; exact hlast
        have hpos : u.pileOfTop X = some a := (pileOfTop_eq_some_iff huwf).mpr htop
        rw [hu] at hpos
        exact absurd hpos (by simp)

/-- **No `S`-live card of rank `c.rank + 1` is created outside the pair.**  At
the pair pin `c.rank = x.rank`, the unique `rank + 1` card of `c`'s suit is one
of the two pair under-cards (`under_card_twins`), and its twin is the other.
Neither is a top at the landing state, so a blocked `S`-live licence is
impossible. -/
theorem succ_card_not_live {u u' : State} {x c d : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x) (hra : Drain.DrainRaisable u x)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hstep : State.step u (Move.tabToFound c) = some u')
    (hdS : CanRaiseS u' d) (hdsuit : d.suit = c.suit)
    (hdrank : d.rank.toIdx = c.rank.toIdx + 1)
    (hdnot : ¬ CanRaise u' d) :
    False := by
  have hu'wf : u'.WF := step_wf huwf hstep
  have hxS : CanRaiseS u x := CanRaiseS.now x hinv.1
  have htS : CanRaiseS u x.twin := hinv.2.1
  have hfloor : x.rank.toIdx ≤ c.rank.toIdx :=
    hinv.2.2.2 c (CanRaiseS.now c hc)
  by_cases hk : x.rank = Rank.king
  · have h12 : c.rank.toIdx = 12 := by
      have hh := hfloor
      rw [hk] at hh
      have hking : Rank.king.toIdx = 12 := rfl
      rw [hking] at hh
      have hlt := Rank.toIdx_lt c.rank
      omega
    have h13 : d.rank.toIdx = 13 := by rw [hdrank, h12]
    have := Rank.toIdx_lt d.rank
    omega
  · have hpin : c.rank.toIdx = x.rank.toIdx :=
      pair_rank_pin huwf hxS htS hk hc hcx hct hfloor
    obtain ⟨U, hUrank, hUcol, htopU, htopUt, -, -⟩ :=
      under_card_twins huwf hxS htS hk
    have hCU : c.suit.color = U.suit.color :=
      SeedKit.color_pair (color_ne_pair huwf hxS htS hc hcx hct).symm hUcol.symm
    have hdrank' : d.rank.toIdx = U.rank.toIdx := by rw [hdrank, hpin, hUrank]
    have hdcol : d.suit.color = U.suit.color := by rw [hdsuit]; exact hCU
    have hdU : d = U ∨ d = U.twin := SeedKit.rankColor_pair hdrank' hdcol
    have htwintop : u'.pileOfTop d.twin ≠ none :=
      PairRungKit.pileOfTop_twin_of_block hu'wf hdS hdnot
    have hrankU : U.rank.toIdx = c.rank.toIdx + 1 := by rw [hUrank, ← hpin]
    have hUc : U ≠ c := by intro h; rw [h] at hrankU; omega
    have hUtc : U.twin ≠ c := by
      intro h
      have hr : U.rank.toIdx = c.rank.toIdx := by
        have := congrArg (fun z : Card => z.rank.toIdx) h
        simpa [Card.twin_rank] using this
      omega
    rcases hdU with hdU | hdU
    · have hdt : d.twin = U.twin := by rw [hdU]
      rw [hdt] at htwintop
      refine htwintop (pileOfTop_tabToFound_eq_none_of_same_color huwf hc hstep hUtc ?_ htopUt)
      rw [Card.twin_suit, Suit.color_twin]
      exact hCU.symm
    · have hdt : d.twin = U := by rw [hdU, card_twin_twin]
      rw [hdt] at htwintop
      exact htwintop (pileOfTop_tabToFound_eq_none_of_same_color huwf hc hstep hUc hCU.symm htopU)

/-! ## §6. Backward readiness for cards above the raised rank -/

/-- **A card of rank strictly above the raised card, not the next-up card of the
raised suit, keeps its tableau-readiness.**  If it is `S`-live and buried at
the landing state, its readiness already held before the raise: the raised
pile's new top has rank `c.rank + 1`, and the only way the twin-top clause can
turn on is `d.twin` becoming that new top — which would force `d` to be the
`rank + 1` card of the pair-colour family, hence not next-up. -/
theorem freeCardS_bwd_of_gt {u u' : State} {x c d : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hstep : State.step u (Move.tabToFound c) = some u')
    (hgt : c.rank.toIdx < d.rank.toIdx) (hsu : d.suit ≠ c.suit)
    (hdct : d ≠ c.twin) (hnext' : u'.nextUp d = true)
    (hfree' : freeCardS u' d = true) (htopnone : u'.pileOfTop d = none) :
    freeCardS u d = true := by
  have hu'wf : u'.WF := step_wf huwf hstep
  obtain ⟨p, run, hhold', hF', hseat', hthird'⟩ := freeCardS_unpack hfree'
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have hnecol : c.suit.color ≠ x.suit.color :=
    color_ne_pair huwf (CanRaiseS.now x hinv.1) hinv.2.1 hc hcx hct
  have hseat0 : chop (u.piles a0).faceUp ≠ [] ∨
      ((u.piles a0).hidden = [] ∧ c.rank = Rank.king) := by
    obtain ⟨a1, hpa1, hs⟩ := hc.2
    have ha1 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
    rwa [ha1] at hs
  -- the landing run is nonempty (else `d` would be a pile top)
  have hrunne : run ≠ [] := by
    intro hrun0
    have hF0 : fromCard d (u'.piles p).faceUp = [d] := by rw [hF', hrun0]
    obtain ⟨bs0, hbs0⟩ := fromCard_singleton_decomp hF0
    have htop : (u'.piles p).top = some d := by
      show lastOf (u'.piles p).faceUp = some d
      rw [hbs0]
      exact lastOf_snoc
    rw [(pileOfTop_eq_some_iff hu'wf).mpr htop] at htopnone
    exact absurd htopnone (by simp)
  have htwintop' : u'.pileOfTop d.twin ≠ none := hthird'.resolve_left hrunne
  obtain ⟨a2, ha2⟩ := option_some_of_ne_none htwintop'
  -- the twin's top pile is not the raised pile
  have ha2ne : a2 ≠ a0 := by
    intro h2a
    rw [h2a] at ha2
    have hlast2 : lastOf (u'.piles a0).faceUp = some d.twin := (pileOfTop_top ha2).2
    have hfac0 : u'.piles a0 =
        Pile.afterRunRemoved (u.piles a0) (chop (u.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    by_cases hchop : chop (u.piles a0).faceUp = []
    · have hhid : (u.piles a0).hidden = [] := by
        rcases hseat0 with hne | ⟨hh, -⟩
        · exact absurd hchop hne
        · exact hh
      rw [hfac0, hchop, afterRunRemoved_faceUp_bare hhid] at hlast2
      exact absurd hlast2 (by simp [lastOf])
    · have hlastchop : lastOf (chop (u.piles a0).faceUp) = some d.twin := by
        have hh := hlast2
        rw [hfac0, afterRunRemoved_faceUp_ne hchop] at hh
        exact hh
      have htopface : lastOf (u.piles a0).faceUp = some c := (pileOfTop_top hpa0).2
      have hface : (u.piles a0).faceUp = chop (u.piles a0).faceUp ++ [c] :=
        lastOf_chop htopface
      obtain ⟨P, hP⟩ := lastOf_eq_snoc hlastchop
      have hshape : (u.piles a0).faceUp = P ++ d.twin :: c :: ([] : List Card) := by
        rw [hface, hP]
        simp [List.append_assoc]
      have hok : runOK (P ++ d.twin :: c :: ([] : List Card)) = true := by
        rw [← hshape]; exact huwf.2.1 a0
      have hfit : canSitOn c d.twin = true := SeedKit.runOK_adjacent_fit d.twin c P [] hok
      have hcolcd : c.suit.color ≠ d.suit.color := by
        have h := ((canSitOn_eq c d.twin).mp hfit).2
        rwa [Card.twin_suit, Suit.color_twin] at h
      have hcoldx : d.suit.color = x.suit.color := SeedKit.color_pair hcolcd hnecol
      have hdx : d.suit = x.suit ∨ d.suit = x.twin.suit := SeedKit.suit_family hcoldx
      have hnextx : u.nextUp x = true := ((canRaiseS_split huwf).mp (CanRaiseS.now x hinv.1)).1
      have hnextt : u.nextUp x.twin = true := ((canRaiseS_split huwf).mp hinv.2.1).1
      have hhx : u.foundHeight x.suit = x.rank.toIdx := by
        simpa [State.nextUp] using (of_decide_eq_true hnextx).symm
      have hht : u.foundHeight x.twin.suit = x.rank.toIdx := by
        have h := (of_decide_eq_true hnextt).symm
        simpa [State.nextUp, Card.twin_rank] using h
      have hdh : u.foundHeight d.suit = x.rank.toIdx := by
        rcases hdx with hdx | hdx
        · rw [hdx]; exact hhx
        · rw [hdx]; exact hht
      have hfoundEq : u'.foundHeight d.suit = u.foundHeight d.suit := by
        unfold State.foundHeight
        rw [OneColourClosure.found_tabToFound hstep d.suit, ite_eq_right hsu]
      have hnextd : d.rank.toIdx = u'.foundHeight d.suit := by
        simpa [State.nextUp] using of_decide_eq_true hnext'
      have hfloor : x.rank.toIdx ≤ c.rank.toIdx :=
        hinv.2.2.2 c (CanRaiseS.now c hc)
      omega
  have htwintop_u : u.pileOfTop d.twin ≠ none := by
    have hpile_a2 : u'.piles a2 = u.piles a2 := by rw [hpiles a2, ite_eq_right ha2ne]
    have htop_a2 : (u.piles a2).top = some d.twin := by
      show lastOf (u.piles a2).faceUp = some d.twin
      rw [← hpile_a2]
      exact (pileOfTop_top ha2).2
    have hpos : u.pileOfTop d.twin = some a2 := (pileOfTop_eq_some_iff huwf).mpr htop_a2
    rw [hpos]
    exact Option.some_ne_none a2
  by_cases hp : p = a0
  · subst p
    have hchop : chop (u.piles a0).faceUp ≠ [] := by
      intro hch
      have hfac : u'.piles a0 =
          Pile.afterRunRemoved (u.piles a0) (chop (u.piles a0).faceUp) := by
        rw [hpiles a0, ite_eq_left rfl]
      have hmem' : d ∈ (u'.piles a0).faceUp := pileHolding_mem hhold'
      rw [hfac] at hmem'
      have hhid : (u.piles a0).hidden = [] := by
        rcases hseat0 with hne | ⟨hh, -⟩
        · exact absurd hch hne
        · exact hh
      rw [hch, afterRunRemoved_faceUp_bare hhid] at hmem'
      exact absurd hmem' List.not_mem_nil
    have hfac : u'.piles a0 =
        Pile.afterRunRemoved (u.piles a0) (chop (u.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    have hmem' : d ∈ (u'.piles a0).faceUp := pileHolding_mem hhold'
    rw [hfac, afterRunRemoved_faceUp_ne hchop] at hmem'
    have hmem : d ∈ (u.piles a0).faceUp := mem_chop_of_mem_chop hmem'
    have hhold_u : u.pileHolding d = some a0 := (pileHolding_eq_some_iff huwf).mpr hmem
    obtain ⟨run_u, hF_u⟩ := tfc_fromCard_cons_head ((u.piles a0).faceUp) hmem
    have htopface : lastOf (u.piles a0).faceUp = some c := (pileOfTop_top hpa0).2
    have hface : (u.piles a0).faceUp = chop (u.piles a0).faceUp ++ [c] :=
      lastOf_chop htopface
    have hbelow : below d ((u.piles a0).faceUp) = below d (chop (u.piles a0).faceUp) := by
      conv => lhs; rw [hface]
      exact tfc_below_mem_append_left (chop (u.piles a0).faceUp) [c] hmem'
    have hhiddeneq : (u'.piles a0).hidden = (u.piles a0).hidden := by
      rw [hfac]
      rcases afterRunRemoved_hidden (u.piles a0) (chop (u.piles a0).faceUp) with
        ⟨-, hh⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hh
      · exact absurd h1 hchop
      · exact absurd h1 hchop
    have hseat_u : below d ((u.piles a0).faceUp) ≠ [] ∨
        ((u.piles a0).hidden = [] ∧ d.rank = Rank.king) := by
      rcases hseat' with hb | ⟨hh, hk⟩
      · left
        rw [hbelow]
        rw [hfac, afterRunRemoved_faceUp_ne hchop] at hb
        exact hb
      · right
        refine ⟨?_, hk⟩
        rw [← hhiddeneq]
        exact hh
    exact freeCardS_of_data hhold_u hF_u hseat_u (Or.inr htwintop_u)
  · have hpile : u'.piles p = u.piles p := by rw [hpiles p, ite_eq_right hp]
    have hmem : d ∈ (u.piles p).faceUp := by rw [← hpile]; exact pileHolding_mem hhold'
    have hhold_u : u.pileHolding d = some p := (pileHolding_eq_some_iff huwf).mpr hmem
    obtain ⟨run_u, hF_u⟩ := tfc_fromCard_cons_head ((u.piles p).faceUp) hmem
    have hseat_u : below d ((u.piles p).faceUp) ≠ [] ∨
        ((u.piles p).hidden = [] ∧ d.rank = Rank.king) := by
      rcases hseat' with hb | ⟨hh, hk⟩
      · left
        rwa [hpile] at hb
      · right
        exact ⟨by rwa [hpile] at hh, hk⟩
    exact freeCardS_of_data hhold_u hF_u hseat_u (Or.inr htwintop_u)

/-! ## §7. Job (B): the carry-on condition survives the raise -/

/-- **Job (B).**  `DrainRaisable u' x`: every `S`-live card outside the pair is
vanilla-raisable at the landing state.  The only new `S`-live cards are the
card directly beneath the raised one (a top, hence raisable) and the unique
`c.rank + 1` card of the raised suit, which `succ_card_not_live` excludes. -/
theorem raisable_preserved_row {u u' : State} {x c : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x) (hra : Drain.DrainRaisable u x)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hstep : State.step u (Move.tabToFound c) = some u') :
    Drain.DrainRaisable u' x := by
  intro d hd'
  have hu'wf : u'.WF := step_wf huwf hstep
  by_cases hdx : d = x
  · exact Or.inl hdx
  by_cases hdt : d = x.twin
  · exact Or.inr (Or.inl hdt)
  rcases Nat.lt_trichotomy d.rank.toIdx c.rank.toIdx with hlt | heq | hgt
  · -- strictly lower: the licence is inert
    have hdS : CanRaiseS u d :=
      (canRaiseS_inert_tabToFound_of_low_rank huwf hstep hc hlt).mp hd'
    have hdc : d ≠ c := by intro h; rw [h] at hlt; omega
    have hcand : CanRaise u d := by
      rcases hra d hdS with h1 | h1 | h1
      · exact absurd h1 hdx
      · exact absurd h1 hdt
      · exact h1
    exact Or.inr (Or.inr (canRaise_tabToFound_fwd_of_ne huwf hstep hdc hcand))
  · -- equal rank
    by_cases hdc : d = c
    · -- the raised card itself is no longer live
      subst d
      exfalso
      have hn' : u'.nextUp c = true := ((canRaiseS_split hu'wf).mp hd').1
      have hfound : u'.found c.suit = u.found c.suit ++ [c] := by
        rw [OneColourClosure.found_tabToFound hstep c.suit]
        simp
      have hn'idx : c.rank.toIdx = (u'.found c.suit).length := by
        simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hn'
      have hnidx : c.rank.toIdx = (u.found c.suit).length := by
        simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hc.1
      rw [hfound, List.length_append, List.length_singleton] at hn'idx
      omega
    · by_cases hdct : d = c.twin
      · -- the raised card's twin is exposed (its twin is founded)
        subst d
        have hfoundc : c ∈ u'.found c.suit := by
          rw [OneColourClosure.found_tabToFound hstep c.suit]
          simp
        have htwinnone : u'.pileOfTop c.twin.twin = none := by
          rw [card_twin_twin]
          exact pileOfTop_eq_none_of_found hu'wf hfoundc
        have hfree' : freeCardS u' c.twin = true := ((canRaiseS_split hu'wf).mp hd').2
        obtain ⟨p, run, hp, hF, hseat, hthird⟩ := freeCardS_unpack hfree'
        have hexp : fromCard c.twin ((u'.piles p).faceUp) = [c.twin] :=
          fromCard_nil_of_freeCardS_of_twin_none hp hfree' htwinnone
        exact Or.inr (Or.inr (canRaise_of_canRaiseS_of_exposed hu'wf hp hexp hd'))
      · -- same rank, a different card: the licence is inert
        have hdrank : c.rank = d.rank := Rank.toIdx_inj heq.symm
        have hdc' : c ≠ d.twin := by
          intro h
          exact hdct (by rw [h, card_twin_twin])
        have hdS : CanRaiseS u d :=
          (canRaiseS_tabToFound_iff_of_rank_eq_notTwin huwf hstep hc hdrank
            (Ne.symm hdc) hdc').mp hd'
        have hcand : CanRaise u d := by
          rcases hra d hdS with h1 | h1 | h1
          · exact absurd h1 hdx
          · exact absurd h1 hdt
          · exact h1
        exact Or.inr (Or.inr (canRaise_tabToFound_fwd_of_ne huwf hstep hdc hcand))
  · -- strictly higher
    have hn' : u'.nextUp d = true := ((canRaiseS_split hu'wf).mp hd').1
    by_cases htop : u'.pileOfTop d = none
    · by_cases hsu : d.suit = c.suit
      · -- the `c.rank + 1` card of the raised suit: excluded
        have hdr : d.rank.toIdx = c.rank.toIdx + 1 := by
          have hfound : u'.found d.suit = u.found d.suit ++ [c] := by
            rw [OneColourClosure.found_tabToFound hstep d.suit, ite_eq_left hsu]
          have hn'idx : d.rank.toIdx = (u'.found d.suit).length := by
            simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hn'
          have hnidx : c.rank.toIdx = (u.found c.suit).length := by
            simpa [State.nextUp, State.foundHeight] using of_decide_eq_true hc.1
          have hnidx' : c.rank.toIdx = (u.found d.suit).length := by
            rw [hsu]
            exact hnidx
          rw [hfound, List.length_append, List.length_singleton] at hn'idx
          omega
        exfalso
        exact succ_card_not_live huwf hinv hra hc hcx hct hstep hd' hsu hdr
          (fun hcan => by
            obtain ⟨-, a, hpa, -⟩ := hcan
            rw [htop] at hpa
            exact absurd hpa (by simp))
      · -- another suit: transfer the readiness back
        have hdct' : d ≠ c.twin := by
          intro h
          rw [h, Card.twin_rank] at hgt
          omega
        have hfree' : freeCardS u' d = true := ((canRaiseS_split hu'wf).mp hd').2
        have hfreed : freeCardS u d = true :=
          freeCardS_bwd_of_gt huwf hinv hc hcx hct hstep hgt hsu hdct' hn' hfree' htop
        have hnextu : u.nextUp d = true := by
          rw [← nextUp_raise_ne hstep hsu]
          exact hn'
        have hdS : CanRaiseS u d := (canRaiseS_split huwf).mpr ⟨hnextu, hfreed⟩
        have hdc : d ≠ c := by intro h; rw [h] at hgt; omega
        have hcand : CanRaise u d := by
          rcases hra d hdS with h1 | h1 | h1
          · exact absurd h1 hdx
          · exact absurd h1 hdt
          · exact h1
        exact Or.inr (Or.inr (canRaise_tabToFound_fwd_of_ne huwf hstep hdc hcand))
    · -- a pile top: raisable now
      obtain ⟨a, ha⟩ := option_some_of_ne_none htop
      exact Or.inr (Or.inr (canRaise_of_canRaiseS_of_top hu'wf hd' ha))

/-! ## §8. Job (D): the transport bundle and the unconditional drain phase -/

/-- **The `RaiseTransport` bundle is unconditional.**  All three fields are
proved above (field 1 is the lane's forward licence shift, field 2 is the rank
floor transport, field 3 is `raisable_preserved_row`). -/
theorem raiseTransport_all (x : Card) : Drain.RaiseTransport x where
  CanRaiseS_preserved := by
    intro u u' c huwf hinv hra hc hcx hct hrev hstep
    exact drain_transport_canRaiseS_row huwf hinv hcx hct hstep
  rank_preserved := by
    intro u u' c huwf hinv hra hc hcx hct hrev hstep
    exact rank_preserved_row huwf hinv hra hc hcx hct hstep
  raisable_preserved := by
    intro u u' c huwf hinv hra hc hcx hct hrev hstep
    exact raisable_preserved_row huwf hinv hra hc hcx hct hstep

/-- **THE DRAIN PHASE, UNCONDITIONAL.**  From the twin asymmetry plus the
carry-on condition alone, a fork exists in the class: the reversibility
provider is `canrev_drain_row` and the transport bundle is
`raiseTransport_all`. -/
theorem drain_phase_fork {st : State} {x : Card}
    (hwf : st.WF) (h : Drain.DrainInvariant st x) (hra : Drain.DrainRaisable st x) :
    ∃ F, sameOrbitSetoid.r st F ∧ forkState F :=
  Drain.drain_raise_phase hwf h hra
    (fun u c huwf hinv hra' hc hcx hct =>
      canrev_drain_row (x := x) huwf hinv hra' hc hcx hct)
    (raiseTransport_all x)

end OneColourClosure

#print axioms OneColourClosure.drain_transport_canRaiseS_row
#print axioms OneColourClosure.canrev_drain_row
#print axioms OneColourClosure.rank_preserved_row
#print axioms OneColourClosure.canRaise_tabToFound_fwd_of_ne
#print axioms OneColourClosure.raisable_preserved_row
#print axioms OneColourClosure.raiseTransport_all
#print axioms OneColourClosure.drain_phase_fork
