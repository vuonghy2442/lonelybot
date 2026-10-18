import Orig2.FloatFiber

/-!
# Orig2.SeatMateStack — THE SEAT-MATE STACK CARD (the seat/floater axis)

Scrutiny's repaired target (`Orig2/ClaimsScrutiny.lean` §S5): a non-Floater
tableau card that changes seat along a reversible board play must involve a
founding move of itself or of a seat-mate.

This card proves the ladder's first rungs:

* the fit arithmetic (`canSitOn_parent_of_seat`, restated from the closed
  seam's `runOK_snoc_sit`);
* **`blocker_eq_twin`** — the card covering a twin target IS the moving
  card's twin (the arithmetic that withdraws witness W1);
* `card_eq_twin_of_rank_color` — same rank and colour means same card or twin.

House compliance: additive leaf (import surface: `Orig2.FloatFiber`, hence
the certified seam through Classification/Kit); zero sorry, zero
`Classical.choice`.
-/

/-! ## §1. Fit arithmetic -/

/-- Every prefix of a legal run is legal (private restatement; home
`Orig2/Classification.lean` §`runOK_append_right`, ported from
`Orig/Classify.lean:392`). -/
private theorem runOK_append_right : ∀ (A B : List Card),
    runOK (A ++ B) = true → runOK A = true := by
  intro A
  induction A with
  | nil => intro _ _; rfl
  | cons y t ih =>
      intro B h
      match t with
      | [] => rfl
      | w :: t' =>
          have h' : runOK (y :: w :: (t' ++ B)) = true := h
          rw [runOK, Bool.and_eq_true] at h' ⊢
          exact ⟨h'.1, ih B h'.2⟩

/-- Same rank and colour: same card or its twin. -/
theorem card_eq_twin_of_rank_color {x y : Card}
    (hr : x.rank = y.rank) (hcol : x.suit.color = y.suit.color) :
    x = y ∨ x = y.twin := by
  obtain ⟨sx, rx⟩ := x
  obtain ⟨sy, ry⟩ := y
  subst hr
  simp only [Card.twin]
  cases sx <;> cases sy <;>
    first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | (exfalso; revert hcol; intro h; cases h)

/-- A seated card fits on its parent (the run-legality seam row
`runOK_snoc_sit` read at the seat). -/
private theorem canSitOn_parent_of_seat {s : State} (hwf : s.WF)
    {c z : Card} (hse : seatOf s c = some (Sum.inr z)) :
    canSitOn c z = true := by
  obtain ⟨a, hhold, hbne, hlast⟩ := tfc_seatOf_of_inr hse
  obtain ⟨tr, htr⟩ := tfc_fromCard_cons_head (s.piles a).faceUp
    (pileHolding_mem hhold)
  have hface : (s.piles a).faceUp = (below c (s.piles a).faceUp ++ [c]) ++ tr := by
    calc (s.piles a).faceUp
        = below c (s.piles a).faceUp ++ fromCard c (s.piles a).faceUp :=
          (tfc_below_fromCard c (s.piles a).faceUp).symm
      _ = below c (s.piles a).faceUp ++ (c :: tr) := by rw [htr]
      _ = (below c (s.piles a).faceUp ++ [c]) ++ tr := by simp [List.append_assoc]
  have hrun : runOK (s.piles a).faceUp = true := hwf.2.1 a
  rw [hface] at hrun
  have hpre : runOK (below c (s.piles a).faceUp ++ [c]) = true :=
    runOK_append_right _ _ hrun
  obtain ⟨z', hz', hsit⟩ := runOK_snoc_sit (c := c) hbne hpre
  rw [hlast] at hz'
  cases hz'
  exact hsit

/-- No card is its own twin. -/
private theorem card_twin_ne (z : Card) : z.twin ≠ z := by
  obtain ⟨sz, rz⟩ := z
  cases sz <;> simp [Card.twin, Suit.twin]

/-- **`blocker_eq_twin`** — the card seated directly on `z.twin`, over a card
seated on `z`, is the seated card's twin.  (The fit arithmetic: same rank by
`canSitOn` twice, same colour by the two-colour dichotomy; distinct because
`z.twin ≠ z`.) -/
theorem blocker_eq_twin {s : State} (hwf : s.WF) {c z d : Card}
    (hc : seatOf s c = some (Sum.inr z))
    (hd : seatOf s d = some (Sum.inr z.twin)) :
    d = c.twin := by
  have hfit_c : canSitOn c z = true := canSitOn_parent_of_seat hwf hc
  have hfit_d : canSitOn d z.twin = true := canSitOn_parent_of_seat hwf hd
  obtain ⟨hrank_c, hcol_c⟩ := (canSitOn_eq c z).mp hfit_c
  obtain ⟨hrank_d, hcol_d⟩ := (canSitOn_eq d z.twin).mp hfit_d
  have hrank_tw : (z.twin).rank = z.rank := rfl
  have hrank : d.rank = c.rank := by
    have h : d.rank.toIdx + 1 = c.rank.toIdx + 1 := by
      rw [hrank_d, hrank_tw, hrank_c]
    have hidx : d.rank.toIdx = c.rank.toIdx := by omega
    exact Rank.toIdx_inj hidx
  have hcol_tw : (z.twin).suit.color = z.suit.color := by
    show z.suit.twin.color = z.suit.color
    exact Suit.color_twin z.suit
  have hcol : d.suit.color = c.suit.color := by
    have h1 : d.suit.color ≠ z.suit.color := by
      rw [← hcol_tw]; exact hcol_d
    have h2 : c.suit.color ≠ z.suit.color := hcol_c
    cases hd' : d.suit.color with
    | red =>
        cases hc' : c.suit.color with
        | red => rfl
        | black =>
            cases hz' : z.suit.color with
            | red => rw [hz'] at h1; exact absurd hd' h1
            | black => rw [hz'] at h2; exact absurd hc' h2
    | black =>
        cases hc' : c.suit.color with
        | red =>
            cases hz' : z.suit.color with
            | red => rw [hz'] at h2; exact absurd hc' h2
            | black => rw [hz'] at h1; exact absurd hd' h1
        | black => rfl
  rcases card_eq_twin_of_rank_color hrank hcol with h | h
  · exfalso
    rw [h] at hd
    rw [hc] at hd
    injection hd with hzz
    exact card_twin_ne z (Sum.inr.inj hzz).symm
  · exact h

/-- Two colours both different from a third are equal. -/
private theorem color_eq_of_ne {a b z : Color} (h1 : a ≠ z) (h2 : b ≠ z) : a = b := by
  cases a <;> cases b <;> cases z <;>
    first
      | rfl
      | (exfalso; revert h1; decide)
      | (exfalso; revert h2; decide)

/-- **`mover_floater`** — a reversible slide's mover is a licensed floater at
the source: the company cell (the target is pinned to the parent's twin by
the fit arithmetic) or the bare-king cell (a king onto a vacancy). -/
theorem mover_floater {u v : State} (hwf : u.WF) {c : Card} {b : Base}
    (hstep : State.step u (Move.tabToTab c b) = some v)
    (hrev : reversibleAtW u (Move.tabToTab c b)) :
    FloaterSpec u c := by
  obtain ⟨a, hhold, hcp, hcell⟩ :=
    tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwf c b).mpr hrev)
  rcases hcell with hbne | ⟨hb0, hhid, hkng⟩
  · obtain ⟨z, hlast⟩ := lastOf_exists hbne
    have hse : seatOf u c = some (Sum.inr z) :=
      tfc_seatOf_inr_intro hhold hlast
    obtain ⟨hsit, htopNone⟩ := tfc_seat_parent hwf hhold hlast
    refine Or.inl ⟨z, a, hse, hhold, ?_⟩
    cases b with
    | inl a' =>
        obtain ⟨hiso, hk⟩ := canPlace_inl hcp
        exact Or.inr ⟨hk, ⟨a', hiso⟩⟩
    | inr z' =>
        obtain ⟨k, hloc, hfit⟩ := canPlace_inr hcp
        have hz' : z' = z.twin := by
          obtain ⟨hrank_z', hcol_z'⟩ := (canSitOn_eq c z').mp hfit
          obtain ⟨hrank_z, hcol_z⟩ := (canSitOn_eq c z).mp hsit
          have hrank : z'.rank = z.rank := by
            have h : z'.rank.toIdx = z.rank.toIdx := by omega
            exact Rank.toIdx_inj h
          have hcol : z'.suit.color = z.suit.color :=
            color_eq_of_ne (z := c.suit.color) hcol_z'.symm hcol_z.symm
          rcases card_eq_twin_of_rank_color hrank hcol with h | h
          · exfalso
            rw [h] at hloc
            rw [htopNone] at hloc
            exact absurd hloc (by simp)
          · exact h
        exact Or.inl ⟨k, by rw [hz'] at hloc; exact hloc⟩
  · have hse : seatOf u c = some (Sum.inl a) :=
      tfc_seatOf_inl_intro hhold hb0
    cases b with
    | inl a' =>
        obtain ⟨hiso, -⟩ := canPlace_inl hcp
        exact Or.inr ⟨a, hse, hkng, hhid, ⟨a', hiso⟩⟩
    | inr z' =>
        obtain ⟨k, hloc, hfit⟩ := canPlace_inr hcp
        obtain ⟨hidx, -⟩ := (canSitOn_eq c z').mp hfit
        have h12 : c.rank.toIdx = 12 := by rw [hkng]; rfl
        have hlt := Rank.toIdx_lt z'.rank
        exfalso
        omega

/-! ## The audit battery -/

#print axioms card_eq_twin_of_rank_color
#print axioms mover_floater
#print axioms blocker_eq_twin