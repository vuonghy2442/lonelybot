import Orig2.Chart
import Orig2.FloatFiber
import Orig2.StepWF
import Orig2.Integrity
import Orig2.SeatMateFuel

/-!
# Orig2.SeatMateStack — THE SEAT-MATE STACK CARD (the seat/floater axis)

Scrutiny's repaired target (`Orig2/ClaimsScrutiny.lean` §S5): a non-Floater
tableau card that changes seat along a reversible board play must involve a
founding move of itself or of a seat-mate.

Landed rungs:

* the fit arithmetic (`canSitOn_parent_of_seat`, `color_eq_of_ne`,
  `card_eq_twin_of_rank_color`);
* **`blocker_eq_twin`** — the card covering a twin target IS the moving
  card's twin (the arithmetic that withdraws witness W1);
* `mover_floater` (private) — the forward direction of
  `floater_classification`;
* **`pull_seat_change`** — a pull changes only the pulled card's seat;
* the hidden ledger (`step_hidden_len_le`, `run_hidden_len_le`,
  `raise_hidden_nil_of_chop_nil`) and **`raise_seat_change_of_seated`** —
  a reversible stack leaves every other seated card's seat unchanged.

House compliance: additive leaf (import surface: `Orig2.FloatFiber` +
`Orig2.Chart`, hence the certified seam); zero sorry, zero
`Classical.choice`.
-/

/-! ## §1. Fit arithmetic -/

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

/-- Two colours both different from a third are equal. -/
private theorem color_eq_of_ne {a b z : Color} (h1 : a ≠ z) (h2 : b ≠ z) : a = b := by
  cases a <;> cases b <;> cases z <;>
    first
      | rfl
      | (exfalso; revert h1; decide)
      | (exfalso; revert h2; decide)

/-- A seated card fits on its parent (the seat leg of `tfc_seat_parent`). -/
private theorem canSitOn_parent_of_seat {s : State} (hwf : s.WF)
    {c z : Card} (hse : seatOf s c = some (Sum.inr z)) :
    canSitOn c z = true := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hse
  exact (tfc_seat_parent hwf hhold hlast).1

/-- **`blocker_eq_twin`** — the card seated directly on `z.twin`, over a card
seated on `z`, is the seated card's twin.  (Same rank by `canSitOn` twice,
same colour by the two-colour dichotomy; distinct because `z.twin ≠ z`.) -/
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
    exact color_eq_of_ne h1 h2
  rcases card_eq_twin_of_rank_color hrank hcol with h | h
  · exfalso
    rw [h] at hd
    rw [hc] at hd
    injection hd with hzz
    exact card_twin_ne z (Sum.inr.inj hzz).symm
  · exact h

/-- **`mover_floater`** — a reversible slide's mover is a licensed floater:
the forward direction of `floater_classification`, read at the fired letter. -/
private theorem mover_floater {u : State} (hwf : u.WF) {c : Card} {b : Base}
    (hrev : reversibleAtW u (Move.tabToTab c b)) :
    FloaterSpec u c :=
  (floater_classification u hwf c).mp ⟨b, hrev⟩

/-! ## §2. The pull's seat footprint -/

/-- Appending a fresh card does not disturb the prefix below an older one. -/
private theorem below_append_snoc_of_mem {x : Card} :
    ∀ {L : List Card}, x ∈ L → ∀ c : Card, below x (L ++ [c]) = below x L
  | [], hx, _ => by cases hx
  | y :: t, hx, c => by
      rw [List.cons_append, below_cons, below_cons]
      by_cases hyx : y = x
      · rw [ite_eq_left hyx, ite_eq_left hyx]
      · rw [ite_eq_right hyx, ite_eq_right hyx]
        have hx' : x ∈ t := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h (fun he => hyx he.symm)
          · exact h
        rw [below_append_snoc_of_mem hx' c]

/-- **`pull_seat_change`** — a pull changes the seat of exactly the pulled
card: the base pile gains the card at its top, so no existing card's parent
changes, and the foundation carries no seat. -/
theorem pull_seat_change {u v : State} {c : Card} {b : Base}
    (hstep : State.step u (Move.foundToTab c b) = some v) :
    ∀ x, x ≠ c → seatOf v x = seatOf u x := by
  intro x hx
  obtain ⟨c', htop, hc', hcp, hs⟩ := step_foundToTab_inv hstep
  subst c'
  rw [hs]
  have hmem : ∀ a, x ∈ (((u.setFound c.suit (chop (u.found c.suit))).putCard c b).piles a).faceUp
      ↔ x ∈ (u.piles a).faceUp := by
    intro a
    cases b with
    | inl a' =>
        rw [putCard_piles_inl]
        simp only []
        by_cases ha : a = a'
        · rw [ite_eq_left ha, ha]
          have hiso : (u.piles a').isEmpty = true := (canPlace_inl hcp).1
          rw [Pile.isEmpty_eq] at hiso
          rw [hiso.2]
          simp [hx]
        · rw [ite_eq_right ha]
          rfl
    | inr z =>
        obtain ⟨k, hloc, -⟩ := canPlace_inr hcp
        rw [putCard_piles_inr (u.setFound c.suit (chop (u.found c.suit))) c z k hloc]
        simp only []
        by_cases ha : a = k
        · rw [ite_eq_left ha, ha, List.mem_append]
          simp only [List.mem_singleton]
          constructor
          · rintro (h | h)
            · exact h
            · exact absurd h hx
          · intro h
            exact Or.inl h
        · rw [ite_eq_right ha]
          rfl
  have hpile : ((u.setFound c.suit (chop (u.found c.suit))).putCard c b).pileHolding x
      = u.pileHolding x := by
    unfold State.pileHolding
    apply firstWhere_congr
    intro a
    by_cases hxa : x ∈ (u.piles a).faceUp
    · rw [decide_eq_true ((hmem a).mpr hxa), decide_eq_true hxa]
    · have hxv : x ∉ (((u.setFound c.suit (chop (u.found c.suit))).putCard c b).piles a).faceUp :=
        fun hc => hxa ((hmem a).mp hc)
      rw [decide_eq_false hxv, decide_eq_false hxa]
  have hbelow : ∀ a, x ∈ (u.piles a).faceUp →
      below x (((u.setFound c.suit (chop (u.found c.suit))).putCard c b).piles a).faceUp
        = below x (u.piles a).faceUp := by
    intro a hxa
    cases b with
    | inl a' =>
        rw [putCard_piles_inl]
        simp only []
        by_cases ha : a = a'
        · exfalso
          have hiso : (u.piles a').isEmpty = true := (canPlace_inl hcp).1
          rw [← ha] at hiso
          rw [Pile.isEmpty_eq] at hiso
          rw [hiso.2] at hxa
          exact List.not_mem_nil hxa
        · rw [ite_eq_right ha]
          rfl
    | inr z =>
        obtain ⟨k, hloc, -⟩ := canPlace_inr hcp
        rw [putCard_piles_inr (u.setFound c.suit (chop (u.found c.suit))) c z k hloc]
        simp only []
        by_cases ha : a = k
        · rw [ite_eq_left ha, ← ha]
          exact below_append_snoc_of_mem hxa c
        · rw [ite_eq_right ha]
          rfl
  unfold seatOf
  rw [hpile]
  cases hph : u.pileHolding x with
  | none => rfl
  | some a0 =>
      simp only []
      rw [hbelow a0 (pileHolding_mem hph)]

/-! ## §3. The hidden ledger and the raise's footprint -/

/-- A removal with an empty remainder over an empty hidden deck leaves an
empty face-up run. -/
private theorem afterRunRemoved_faceUp_nil {p : Pile} {pre : List Card}
    (hpre : pre = []) (hhid : p.hidden = []) :
    (Pile.afterRunRemoved p pre).faceUp = [] := by
  subst hpre
  show (Pile.revealTop { p with faceUp := [] }).faceUp = []
  unfold Pile.revealTop
  dsimp only
  rw [hhid]

/-- A removal with an empty remainder strictly shrinks a nonempty hidden
deck. -/
private theorem afterRunRemoved_hidden_len_lt {p : Pile} {pre : List Card}
    (hpre : pre = []) (hhid : p.hidden ≠ []) :
    (Pile.afterRunRemoved p pre).hidden.length < p.hidden.length := by
  subst hpre
  show (Pile.revealTop { p with faceUp := [] }).hidden.length < p.hidden.length
  unfold Pile.revealTop
  dsimp only
  obtain ⟨h, t, hh⟩ := list_cons_of_ne_nil hhid
  rw [hh]
  simp

/-- The pile-update literal of a stack, read at an index. -/
private theorem raise_update_piles (u : State) (d : Card) (a : Anchor) (pre : List Card)
    (a' : Anchor) :
    ({ u.setFound d.suit (u.found d.suit ++ [d]) with
        piles := fun x => if x = a then Pile.afterRunRemoved (u.piles a) pre
          else u.piles x }).piles a'
      = (if a' = a then Pile.afterRunRemoved (u.piles a) pre else u.piles a') :=
  rfl

/-- A single card never grows a pile's hidden deck. -/
private theorem putCard_hidden_len_le (st : State) (c : Card) (b : Base) :
    ∀ a, ((st.putCard c b).piles a).hidden.length ≤ (st.piles a).hidden.length := by
  intro a
  cases b with
  | inl a' =>
      rw [putCard_piles_inl]
      dsimp only
      by_cases h : a = a'
      · rw [ite_eq_left h]; exact Nat.zero_le _
      · rw [ite_eq_right h]; exact Nat.le_refl _
  | inr z =>
      cases hz : st.pileOfTop z with
      | none =>
          show ((match st.pileOfTop z with
            | some k => st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
            | none => st).piles a).hidden.length ≤ (st.piles a).hidden.length
          rw [hz]
          dsimp only
          exact Nat.le_refl _
      | some k =>
          rw [putCard_piles_inr st c z k hz]
          dsimp only
          by_cases h : a = k
          · rw [ite_eq_left h, h]
            exact Nat.le_refl _
          · rw [ite_eq_right h]; exact Nat.le_refl _

/-- A run never grows a pile's hidden deck. -/
private theorem putRun_hidden_len_le (st : State) (run : List Card) (b : Base) :
    ∀ a, ((st.putRun run b).piles a).hidden.length ≤ (st.piles a).hidden.length := by
  intro a
  cases b with
  | inl a' =>
      rw [putRun_eq_inl]
      by_cases h : a = a'
      · rw [h, setPile_piles_self]; exact Nat.zero_le _
      · rw [setPile_piles_ne h]; exact Nat.le_refl _
  | inr z =>
      cases hz : st.pileOfTop z with
      | none =>
          show ((match st.pileOfTop z with
            | some k => st.setPile k { st.piles k with faceUp := (st.piles k).faceUp ++ run }
            | none => st).piles a).hidden.length ≤ (st.piles a).hidden.length
          rw [hz]
          dsimp only
          exact Nat.le_refl _
      | some k =>
          rw [putRun_inr_eq hz]
          dsimp only
          by_cases h : a = k
          · rw [h, setPile_piles_self]
            exact Nat.le_refl _
          · rw [setPile_piles_ne h]; exact Nat.le_refl _

/-- A pile write with a shorter hidden deck never grows any pile's hidden. -/
private theorem setPile_hidden_len_le (st : State) (a0 : Anchor) (Q : Pile)
    (hQ : Q.hidden.length ≤ (st.piles a0).hidden.length) :
    ∀ a, ((st.setPile a0 Q).piles a).hidden.length ≤ (st.piles a).hidden.length := by
  intro a
  by_cases h : a = a0
  · subst h
    rw [setPile_piles_self]
    exact hQ
  · rw [setPile_piles_ne h]
    exact Nat.le_refl _

/-- Every move's per-pile hidden length is non-increasing. -/
private theorem step_hidden_len_le {u v : State} {m : Move}
    (hstep : State.step u m = some v) :
    ∀ a, (v.piles a).hidden.length ≤ (u.piles a).hidden.length := by
  intro a
  cases m with
  | draw =>
      have hb := ((chart_draw hstep).2.2.1).1 a
      rw [hb]
      exact Nat.le_refl _
  | wasteToFound c =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      show (u.piles a).hidden.length ≤ (u.piles a).hidden.length
      exact Nat.le_refl _
  | wasteToTab c b =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToTab_inv hstep
      rw [hs]
      show ((u.putCard c b).piles a).hidden.length ≤ (u.piles a).hidden.length
      exact putCard_hidden_len_le u c b a
  | tabToFound c =>
      obtain ⟨-, a0, hpa, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      dsimp only
      by_cases h : a = a0
      · rw [h, ite_eq_left rfl]
        exact afterRunRemoved_hidden_le (u.piles a0) (chop (u.piles a0).faceUp)
      · rw [ite_eq_right h]
        exact Nat.le_refl _
  | foundToTab c b =>
      obtain ⟨-, -, -, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      exact putCard_hidden_len_le (u.setFound c.suit (chop (u.found c.suit))) c b a
  | tabToTab c b =>
      obtain ⟨a0, hhold, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      refine Nat.le_trans
        (putRun_hidden_len_le (u.setPile a0 (Pile.afterRunRemoved (u.piles a0)
          (below c (u.piles a0).faceUp))) (fromCard c (u.piles a0).faceUp) b a) ?_
      exact setPile_hidden_len_le u a0 _
        (afterRunRemoved_hidden_le (u.piles a0) (below c (u.piles a0).faceUp)) a

/-- Along an executed play the per-pile hidden lengths are non-increasing. -/
private theorem run_hidden_len_le : ∀ (ρ : List Move) {s W : State},
    s.run ρ = some W → ∀ a, (W.piles a).hidden.length ≤ (s.piles a).hidden.length
  | [], s, W, h => by
      simp only [State.run] at h
      have hsW : s = W := Option.some.inj h
      subst W
      intro a
      exact Nat.le_refl _
  | m :: ms, s, W, h => by
      simp only [State.run] at h
      split at h
      · rename_i s' hstep
        intro a
        exact Nat.le_trans (run_hidden_len_le ms h a) (step_hidden_len_le hstep a)
      · exact absurd h (by simp)

/-- A reversible stack never fires the reveal: a reveal strictly shrinks the
donor's hidden deck, and a return play could only keep or shrink it. -/
private theorem raise_hidden_nil_of_chop_nil {u v : State} {d : Card} {a : Anchor}
    (hstep : State.step u (Move.tabToFound d) = some v)
    (hrev : reversibleAtW u (Move.tabToFound d))
    (hpa : u.pileOfTop d = some a)
    (hchop : chop (u.piles a).faceUp = []) :
    (u.piles a).hidden = [] := by
  cases hh : (u.piles a).hidden with
  | nil => rfl
  | cons h t =>
    exfalso
    have hne : (u.piles a).hidden ≠ [] := by rw [hh]; exact List.cons_ne_nil _ _
    obtain ⟨-, a0, hpa0, hv⟩ := step_tabToFound_inv hstep
    have ha0 : a0 = a := Option.some.inj (hpa0.symm.trans hpa)
    rw [ha0] at hv
    have hstrict : (v.piles a).hidden.length < (u.piles a).hidden.length := by
      rw [hv, raise_update_piles]
      rw [ite_eq_left rfl]
      exact afterRunRemoved_hidden_len_lt hchop hne
    obtain ⟨s1, ρ, hs1, hrun⟩ := hrev
    have hs1v : s1 = v := Option.some.inj (hs1.symm.trans hstep)
    subst s1
    have hle : (u.piles a).hidden.length ≤ (v.piles a).hidden.length :=
      run_hidden_len_le ρ hrun a
    omega

/-- **`raise_seat_change_of_seated`** — a reversible stack leaves every OTHER
seated card's seat unchanged: the donor keeps its prefix (no reveal can fire),
and the raised card was the top. -/
theorem raise_seat_change_of_seated {u v : State} {d c : Card}
    (hstep : State.step u (Move.tabToFound d) = some v)
    (hrev : reversibleAtW u (Move.tabToFound d))
    (hseat : seatOf u c ≠ none) (hcd : c ≠ d) :
    seatOf v c = seatOf u c := by
  obtain ⟨-, a, hpa, hv⟩ := step_tabToFound_inv hstep
  rw [hv]
  obtain ⟨-, hlast⟩ := tfc_pileOfTop_top hpa
  have hface : (u.piles a).faceUp = chop (u.piles a).faceUp ++ [d] :=
    lastOf_chop hlast
  have hex : ∃ a0, u.pileHolding c = some a0 := by
    cases hph : u.pileHolding c with
    | none =>
        exfalso
        exact hseat (by unfold seatOf; rw [hph])
    | some a0 => exact ⟨a0, rfl⟩
  obtain ⟨a0, hhold⟩ := hex
  have hmemc : c ∈ (u.piles a0).faceUp := pileHolding_mem hhold
  have hmem : ∀ a', c ∈ (({ u.setFound d.suit (u.found d.suit ++ [d]) with
        piles := fun x => if x = a then Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
          else u.piles x }).piles a').faceUp
      ↔ c ∈ (u.piles a').faceUp := by
    intro a'
    rw [raise_update_piles]
    by_cases ha' : a' = a
    · rw [ite_eq_left ha', ha']
      by_cases hca : c ∈ (u.piles a).faceUp
      · have hcchop : c ∈ chop (u.piles a).faceUp := by
          have hca' := hca
          rw [hface, List.mem_append] at hca'
          rcases hca' with h | h
          · exact h
          · exact absurd (by simpa using h) hcd
        have hne : chop (u.piles a).faceUp ≠ [] := by
          intro hnil
          rw [hnil] at hcchop
          exact List.not_mem_nil hcchop
        rw [afterRunRemoved_faceUp_ne hne]
        constructor
        · intro h
          rw [hface, List.mem_append]
          exact Or.inl h
        · intro h
          rw [hface, List.mem_append] at h
          rcases h with h | h
          · exact h
          · exact absurd (by simpa using h) hcd
      · by_cases hchop : chop (u.piles a).faceUp = []
        · have hhid := raise_hidden_nil_of_chop_nil hstep hrev hpa hchop
          rw [hchop, afterRunRemoved_faceUp_nil rfl hhid]
          constructor
          · intro h
            exact False.elim (List.not_mem_nil h)
          · intro h
            exact False.elim (absurd h hca)
        · rw [afterRunRemoved_faceUp_ne hchop]
          constructor
          · intro h
            exact False.elim (hca (by rw [hface, List.mem_append]; exact Or.inl h))
          · intro h
            exact False.elim (absurd h hca)
    · rw [ite_eq_right ha']
  have hpile : ({ u.setFound d.suit (u.found d.suit ++ [d]) with
        piles := fun x => if x = a then Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
          else u.piles x }).pileHolding c = u.pileHolding c := by
    unfold State.pileHolding
    apply firstWhere_congr
    intro a'
    by_cases hc : c ∈ (u.piles a').faceUp
    · rw [decide_eq_true ((hmem a').mpr hc), decide_eq_true hc]
    · have hcv : c ∉ (({ u.setFound d.suit (u.found d.suit ++ [d]) with
          piles := fun x => if x = a then Pile.afterRunRemoved (u.piles a)
            (chop (u.piles a).faceUp) else u.piles x }).piles a').faceUp :=
        fun hcontra => hc ((hmem a').mp hcontra)
      rw [decide_eq_false hcv, decide_eq_false hc]
  have hbelow : ∀ a', c ∈ (u.piles a').faceUp →
      below c (({ u.setFound d.suit (u.found d.suit ++ [d]) with
        piles := fun x => if x = a then Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
          else u.piles x }).piles a').faceUp = below c (u.piles a').faceUp := by
    intro a' hc
    rw [raise_update_piles]
    by_cases ha' : a' = a
    · rw [ha'] at hc
      rw [ite_eq_left ha', ha']
      have hcchop : c ∈ chop (u.piles a).faceUp := by
        have hc' := hc
        rw [hface, List.mem_append] at hc'
        rcases hc' with h | h
        · exact h
        · exact absurd (by simpa using h) hcd
      have hne : chop (u.piles a).faceUp ≠ [] := by
        intro hnil
        rw [hnil] at hcchop
        exact List.not_mem_nil hcchop
      rw [afterRunRemoved_faceUp_ne hne]
      have hgoal : below c (u.piles a).faceUp = below c (chop (u.piles a).faceUp) := by
        conv =>
          lhs
          rw [hface]
        exact below_append_snoc_of_mem hcchop d
      exact hgoal.symm
    · rw [ite_eq_right ha']
  unfold seatOf
  rw [hpile]
  cases hph : u.pileHolding c with
  | none => rfl
  | some a2 =>
      simp only []
      rw [hbelow a2 (pileHolding_mem hph)]
/-! ## §4. The letters' seat footprints

The strong foundation arm (`nonFloater_change_found_needs_target_pull`) needs
to know that no letter except a raise of `c` takes a seated `c` off the
tableau, and that the single-card/run writers never lose an existing face-up
card.  These rows are the per-letter membership kit. -/

/-- The seat map misses exactly when the holding search misses. -/
private theorem seatOf_eq_none_iff_holding (st : State) (c : Card) :
    seatOf st c = none ↔ st.pileHolding c = none := by
  constructor
  · intro hse
    by_cases hh : st.pileHolding c = none
    · exact hh
    · obtain ⟨a, ha⟩ := option_some_of_ne_none hh
      rw [tfc_seatOf_pair ha] at hse
      cases hgl : List.getLast? (below c (st.piles a).faceUp) with
      | none =>
          rw [hgl] at hse
          dsimp only at hse
          exact absurd hse (by simp)
      | some z =>
          rw [hgl] at hse
          dsimp only at hse
          exact absurd hse (by simp)
  · intro hh
    exact tfc_seatOf_none hh

/-- A face-up card has a seat. -/
private theorem seatOf_ne_of_mem_faceUp {st : State} {c : Card} {a : Anchor}
    (h : c ∈ (st.piles a).faceUp) : seatOf st c ≠ none := by
  intro hse
  have hh : st.pileHolding c = none := (seatOf_eq_none_iff_holding st c).mp hse
  exact (tfc_not_mem_faceUp_of_holdNone hh a) h

/-- A seated card is face-up somewhere. -/
private theorem mem_faceUp_of_seatOf_ne {st : State} {c : Card}
    (h : seatOf st c ≠ none) : ∃ a, c ∈ (st.piles a).faceUp := by
  have hh : st.pileHolding c ≠ none := fun hh => h ((seatOf_eq_none_iff_holding st c).mpr hh)
  obtain ⟨a, ha⟩ := option_some_of_ne_none hh
  exact ⟨a, pileHolding_mem ha⟩

/-- **A reversible letter cannot take a seated card off the tableau except by
raising that card.**  Draws and `wasteToFound` leave the piles alone; a
reversible pull only moves its subject; a reversible slide only edits its
mover's seat (to a base); waste letters are never reversible. -/
private theorem step_seat_none_eq_tabToFound {u v : State} {m : Move} {c : Card}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hse : seatOf u c ≠ none) (hse' : seatOf v c = none) :
    m = Move.tabToFound c := by
  cases m with
  | draw =>
      exfalso
      rw [(chart_draw hstep).1 c] at hse'
      exact hse hse'
  | wasteToFound x =>
      exfalso
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToFound_inv hstep
      have hp : v.piles = u.piles := by rw [hs]; rfl
      rw [seatOf_congr_piles hp c] at hse'
      exact hse hse'
  | wasteToTab x b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u x b)
  | tabToFound x =>
      by_cases hxc : x = c
      · exact congrArg Move.tabToFound hxc
      · exfalso
        have hvv := raise_seat_change_of_seated hstep hrev hse (fun h => hxc h.symm)
        rw [hvv] at hse'
        exact hse hse'
  | foundToTab x b =>
      exfalso
      by_cases hxc : x = c
      · rw [hxc] at hstep
        obtain ⟨-, htop, -, hcp, hs⟩ := step_foundToTab_inv hstep
        rw [hs] at hse'
        have hmem : ∃ a', c ∈ (((u.setFound c.suit (chop (u.found c.suit))).putCard c b).piles a').faceUp := by
          cases b with
          | inl t =>
              refine ⟨t, ?_⟩
              rw [putCard_piles_inl]
              dsimp only
              rw [ite_eq_left rfl]
              exact List.mem_singleton.mpr rfl
          | inr z =>
              obtain ⟨k, hz, -⟩ := canPlace_inr hcp
              have hz' : (u.setFound c.suit (chop (u.found c.suit))).pileOfTop z = some k := by
                unfold State.pileOfTop State.topOf
                rw [setFound_piles]
                exact hz
              refine ⟨k, ?_⟩
              rw [putCard_piles_inr (u.setFound c.suit (chop (u.found c.suit))) c z k hz']
              dsimp only
              rw [ite_eq_left rfl]
              exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
        obtain ⟨a', ha'⟩ := hmem
        exact (seatOf_ne_of_mem_faceUp ha') hse'
      · exfalso
        have hvv := pull_seat_change hstep c (fun h => hxc h.symm)
        rw [hvv] at hse'
        exact hse hse'
  | tabToTab x b =>
      exfalso
      have h := tfc_seat_point_edit hwf hstep hrev c
      by_cases hxc : c = x
      · rw [ite_eq_left hxc] at h
        rw [h] at hse'
        nomatch hse'
      · rw [ite_eq_right hxc] at h
        rw [h] at hse'
        exact hse hse'

/-- **A card that starts on the tableau and ends off it was raised** along a
reversible play. -/
theorem tabToFound_of_seat_none
    {st w : State} (hwfst : st.WF) {c : Card}
    (htab : ∃ b, seatOf st c = some b)
    (hnone : seatOf w c = none)
    {play : List Move} (hplay : ShufflePlayW st play w) :
    Move.tabToFound c ∈ play := by
  have aux : ∀ {a b : State} {ρ : List Move}, ShufflePlayW a ρ b → a.WF →
      (∃ d, seatOf a c = some d) → seatOf b c = none → Move.tabToFound c ∈ ρ := by
    intro a b ρ h
    induction h with
    | nil s =>
        intro _ htab hnone
        obtain ⟨d, hd⟩ := htab
        rw [hd] at hnone
        nomatch hnone
    | @cons u v W m ρ hrev hstep hrest ih =>
        intro hwf htab hnone
        have hwfv : v.WF := step_wf hwf hstep
        by_cases hse : seatOf v c = none
        · have hseu : seatOf u c ≠ none := by
            obtain ⟨d, hd⟩ := htab
            rw [hd]; simp
          have hm := step_seat_none_eq_tabToFound hwf hstep hrev hseu hse
          rw [hm]
          exact List.mem_cons_self
        · obtain ⟨d, hd⟩ : ∃ d, seatOf v c = some d := by
            cases hv : seatOf v c with
            | none => exact absurd hv hse
            | some d => exact ⟨d, rfl⟩
          exact List.mem_cons_of_mem _ (ih hwfv ⟨d, hd⟩ hnone)
  exact aux hplay hwfst htab hnone

/-- A seated card's parent data: the fit and the parent is not a pile top. -/
private theorem seat_parent_data {s : State} (hwf : s.WF) {c z : Card}
    (hse : seatOf s c = some (Sum.inr z)) :
    canSitOn c z = true ∧ s.pileOfTop z = none := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hse
  exact tfc_seat_parent hwf hhold hlast

/-- The two cards a card can sit on are its parent and the parent's twin. -/
private theorem canSitOn_targets {c z w : Card}
    (hcz : canSitOn c z = true) (hcw : canSitOn c w = true) :
    w = z ∨ w = z.twin := by
  obtain ⟨hrz, hcolz⟩ := (canSitOn_eq c z).mp hcz
  obtain ⟨hrw, hcolw⟩ := (canSitOn_eq c w).mp hcw
  have hrank : w.rank = z.rank := by
    apply Rank.toIdx_inj
    omega
  have hcolor : w.suit.color = z.suit.color :=
    color_eq_of_ne (fun h => hcolw h.symm) (fun h => hcolz h.symm)
  exact card_eq_twin_of_rank_color hrank hcolor

/-- A card that fits on a parent is not a king. -/
private theorem canSitOn_not_king {c z : Card} (h : canSitOn c z = true) :
    c.rank ≠ Rank.king := by
  obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp h
  intro hk
  have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
  have hlt := Rank.toIdx_lt z.rank
  omega

/-- Foundation membership survives every letter except the pull of that very
card. -/
private theorem found_mem_step_of_not_pull {u v : State} {m : Move} {x : Card}
    (hstep : State.step u m = some v)
    (hmem : x ∈ u.found x.suit)
    (hnot : ∀ b : Base, m ≠ Move.foundToTab x b) :
    x ∈ v.found x.suit := by
  cases m with
  | draw =>
      rw [← (chart_draw hstep).2.1 x.suit]
      exact hmem
  | wasteToFound y =>
      obtain ⟨-, z, zs, hw, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      by_cases hys : y.suit = x.suit
      · rw [← hys]
        rw [← hys] at hmem
        rw [setFound_found_self]
        exact List.mem_append_left _ hmem
      · rw [setFound_found_ne (fun h => hys h.symm)]
        exact hmem
  | wasteToTab y b =>
      obtain ⟨-, z, zs, hw, hs⟩ := step_wasteToTab_inv hstep
      rw [hs]
      cases b with
      | inl t => rw [putCard_inl_found]; exact hmem
      | inr z => rw [putCard_inr_found]; exact hmem
  | tabToFound y =>
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      by_cases hys : y.suit = x.suit
      · rw [← hys]
        rw [← hys] at hmem
        rw [setFound_found_self]
        exact List.mem_append_left _ hmem
      · rw [setFound_found_ne (fun h => hys h.symm)]
        exact hmem
  | foundToTab y b =>
      obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      have hfound : ((u.setFound y.suit (chop (u.found y.suit))).putCard y b).found
          = (u.setFound y.suit (chop (u.found y.suit))).found := by
        cases b with
        | inl t => rw [putCard_inl_found]
        | inr z => rw [putCard_inr_found]
      rw [hfound]
      by_cases hys : y.suit = x.suit
      · rw [← hys]
        rw [← hys] at hmem
        have hlast : lastOf (u.found y.suit) = some y := by
          unfold State.foundTop at htop
          rw [hc'c] at htop
          exact htop
        have hyx : y ≠ x := by
          intro hyx
          exact hnot b (by rw [hyx])
        have hsnoc : u.found y.suit = chop (u.found y.suit) ++ [y] :=
          lastOf_chop hlast
        have hchop : x ∈ chop (u.found y.suit) := by
          rw [hsnoc, List.mem_append] at hmem
          rcases hmem with h | h
          · exact h
          · rw [List.mem_singleton] at h
            exact False.elim (hyx h.symm)
        rw [setFound_found_self]
        exact hchop
      · rw [setFound_found_ne (fun h => hys h.symm)]
        exact hmem
  | tabToTab y b =>
      obtain ⟨a, hhold, hcp, hface, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      rw [putRun_found, setPile_found]
      exact hmem

/-- A card in the foundation has no seat. -/
private theorem seatOf_none_of_found {s : State} (hwf : s.WF) {c : Card}
    (h : c ∈ s.found c.suit) : seatOf s c = none := by
  rw [seatOf_eq_none_iff_holding]
  by_cases hh : s.pileHolding c = none
  · exact hh
  · obtain ⟨a, ha⟩ := option_some_of_ne_none hh
    exact absurd (pileHolding_mem ha) ((mem_found_unique hwf h).1 a).2

/-- The pulled card lands on the named top card: its seat is that card. -/
private theorem pull_landing_inr {u v : State} {c w : Card}
    (hwf : u.WF) (hstep : State.step u (Move.foundToTab c (Sum.inr w)) = some v)
    (hcp : u.canPlace c (Sum.inr w) = true) :
    seatOf v c = some (Sum.inr w) := by
  obtain ⟨c', htop, hc'c, hcp', hs⟩ := step_foundToTab_inv hstep
  obtain ⟨k, hz, -⟩ := canPlace_inr hcp
  have hc_found : c ∈ u.found c.suit := by
    have hlast : lastOf (u.found c.suit) = some c := by
      unfold State.foundTop at htop
      rw [hc'c] at htop
      exact htop
    exact lastOf_mem hlast
  have hc_faces : c ∉ (u.piles k).faceUp := ((mem_found_unique hwf hc_found).1 k).2
  have hz' : (u.setFound c.suit (chop (u.found c.suit))).pileOfTop w = some k := by
    unfold State.pileOfTop State.topOf
    rw [setFound_piles]
    exact hz
  have hface : ((u.setFound c.suit (chop (u.found c.suit))).putCard c (Sum.inr w)).piles k
      = ⟨(u.piles k).hidden, (u.piles k).faceUp ++ [c]⟩ := by
    rw [putCard_piles_inr (u.setFound c.suit (chop (u.found c.suit))) c w k hz']
    dsimp only
    rw [ite_eq_left rfl]
    rw [setFound_piles]
  have hwf2 : ((u.setFound c.suit (chop (u.found c.suit))).putCard c (Sum.inr w)).WF := by
    rw [← hs]
    exact step_wf hwf hstep
  have hmem : c ∈ (((u.setFound c.suit (chop (u.found c.suit))).putCard c (Sum.inr w)).piles k).faceUp := by
    rw [hface]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hhold : ((u.setFound c.suit (chop (u.found c.suit))).putCard c (Sum.inr w)).pileHolding c = some k :=
    (pileHolding_eq_some_iff hwf2).mpr hmem
  have hbelow : below c (((u.setFound c.suit (chop (u.found c.suit))).putCard c (Sum.inr w)).piles k).faceUp
      = (u.piles k).faceUp := by
    rw [hface]
    exact below_snoc_not_mem hc_faces
  have hlastw : lastOf (below c (((u.setFound c.suit (chop (u.found c.suit))).putCard c (Sum.inr w)).piles k).faceUp)
      = some w := by
    rw [hbelow]
    exact (tfc_pileOfTop_top hz).2
  rw [hs]
  exact tfc_seatOf_inr_intro hhold hlastw

/-- No letter can place the seated card `c` on a card: its only fitting
parents are its own parent (covered) and the parent's twin (in the
foundation, hence not a top). -/
private theorem seated_no_canPlace {s : State} (_hwf : s.WF) {c z0 : Card}
    (hfit : canSitOn c z0 = true)
    (hz0top : s.pileOfTop z0 = none)
    (hztop : s.pileOfTop z0.twin = none) :
    ∀ b : Base, s.canPlace c b = false := by
  intro b
  cases hb : s.canPlace c b with
  | false => rfl
  | true =>
      exfalso
      cases b with
      | inl a => exact canSitOn_not_king hfit (canPlace_inl hb).2
      | inr w =>
          obtain ⟨k, hwtop, hcw⟩ := canPlace_inr hb
          rcases canSitOn_targets hfit hcw with hw | hw
          · rw [hw] at hwtop
            rw [hz0top] at hwtop
            nomatch hwtop
          · rw [hw] at hwtop
            rw [hztop] at hwtop
            nomatch hwtop

/-- The per-step invariant for the foundation pull arm.  Under no pull of
`z0.twin`, the tracked card's seat stays in `{none, some (inr z0)}`; when it
is `none` the card sits in the foundation. -/
private theorem hfound_step_invariant {u v : State} {m : Move} {c z0 : Card}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hzfound : z0.twin ∈ u.found z0.twin.suit)
    (hnotPull : ∀ b : Base, m ≠ Move.foundToTab z0.twin b)
    (hfit : canSitOn c z0 = true)
    (hseat : seatOf u c = none ∨ seatOf u c = some (Sum.inr z0))
    (hcfound : seatOf u c = none → c ∈ u.found c.suit) :
    (seatOf v c = none ∨ seatOf v c = some (Sum.inr z0)) ∧
      (seatOf v c = none → c ∈ v.found c.suit) ∧
      z0.twin ∈ v.found z0.twin.suit := by
  have hwfv : v.WF := step_wf hwf hstep
  have hzv : z0.twin ∈ v.found z0.twin.suit :=
    found_mem_step_of_not_pull hstep hzfound hnotPull
  have hztop : u.pileOfTop z0.twin = none := by
    cases h : u.pileOfTop z0.twin with
    | none => rfl
    | some k =>
        have hmem : z0.twin ∈ (u.piles k).faceUp := lastOf_mem (tfc_pileOfTop_top h).2
        exact absurd hmem ((mem_found_unique hwf hzfound).1 k).2
  cases m with
  | draw =>
      have hse := (chart_draw hstep).1
      refine ⟨?_, ?_, hzv⟩
      · rw [hse c]; exact hseat
      · intro hv
        have hu : seatOf u c = none := by rw [← hse c]; exact hv
        exact found_mem_step_of_not_pull hstep (hcfound hu) (fun b h => by nomatch h)
  | wasteToFound x =>
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToFound_inv hstep
      have hp : v.piles = u.piles := by rw [hs]; rfl
      have hse : ∀ c', seatOf v c' = seatOf u c' := seatOf_congr_piles hp
      refine ⟨?_, ?_, hzv⟩
      · rw [hse c]; exact hseat
      · intro hv
        have hu : seatOf u c = none := by rw [← hse c]; exact hv
        exact found_mem_step_of_not_pull hstep (hcfound hu) (fun b h => by nomatch h)
  | wasteToTab x b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u x b)
  | tabToFound x =>
      have hnotc : ∀ b : Base, Move.tabToFound x ≠ Move.foundToTab c b :=
        fun b h => by nomatch h
      have hcvNone : seatOf u c = none → c ∈ v.found c.suit :=
        fun h => found_mem_step_of_not_pull hstep (hcfound h) hnotc
      have hcvSelf : x = c → c ∈ v.found c.suit := by
        intro hxc
        rw [hxc] at hstep
        obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
        rw [hs]
        show c ∈ (u.setFound c.suit (u.found c.suit ++ [c])).found c.suit
        rw [setFound_found_self]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      refine ⟨?_, ?_, hzv⟩
      · rcases hseat with hnone | hsome
        · exact Or.inl (seatOf_none_of_found hwfv (hcvNone hnone))
        · by_cases hxc : x = c
          · exact Or.inl (seatOf_none_of_found hwfv (hcvSelf hxc))
          · refine Or.inr ?_
            have h := raise_seat_change_of_seated hstep hrev
              (by rw [hsome]; simp) (fun hcon => hxc hcon.symm)
            rw [h]
            exact hsome
      · intro hv
        rcases hseat with hnone | hsome
        · exact hcvNone hnone
        · by_cases hxc : x = c
          · exact hcvSelf hxc
          · exfalso
            have h := raise_seat_change_of_seated hstep hrev
              (by rw [hsome]; simp) (fun hcon => hxc hcon.symm)
            rw [h] at hv
            rw [hsome] at hv
            nomatch hv
  | foundToTab x b =>
      have hcvNone : x ≠ c → seatOf u c = none → c ∈ v.found c.suit := by
        intro hxc hnone
        exact found_mem_step_of_not_pull hstep (hcfound hnone)
          (fun b' h => by
            injection h with h1 _
            exact hxc h1)
      have hpullSeat : x = c → seatOf v c = some (Sum.inr z0) := by
        intro hxc
        rw [hxc] at hstep
        obtain ⟨-, htop, -, hcp, hs⟩ := step_foundToTab_inv hstep
        cases b with
        | inl a =>
            exfalso
            exact canSitOn_not_king hfit (canPlace_inl hcp).2
        | inr w =>
            obtain ⟨k, hwtop, hcw⟩ := canPlace_inr hcp
            rcases canSitOn_targets hfit hcw with hw | hw
            · have hland := pull_landing_inr hwf hstep hcp
              rw [hland, hw]
            · exfalso
              have : u.pileOfTop z0.twin = some k := by
                rw [← hw]
                exact hwtop
              rw [hztop] at this
              nomatch this
      refine ⟨?_, ?_, hzv⟩
      · rcases hseat with hnone | hsome
        · by_cases hxc : x = c
          · exact Or.inr (hpullSeat hxc)
          · exact Or.inl (seatOf_none_of_found hwfv (hcvNone hxc hnone))
        · by_cases hxc : x = c
          · exfalso
            rw [hxc] at hstep
            obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
            have hlast : lastOf (u.found c.suit) = some c := by
              unfold State.foundTop at htop
              rw [hc'c] at htop
              exact htop
            have hcfin : c ∈ u.found c.suit := lastOf_mem hlast
            have hcface : ∃ a, c ∈ (u.piles a).faceUp := mem_faceUp_of_seatOf_ne (by rw [hsome]; simp)
            obtain ⟨a, ha⟩ := hcface
            exact ((mem_found_unique hwf hcfin).1 a).2 ha
          · refine Or.inr ?_
            have h := pull_seat_change hstep c (fun hcon => hxc hcon.symm)
            rw [h]
            exact hsome
      · intro hv
        rcases hseat with hnone | hsome
        · by_cases hxc : x = c
          · have hs := hpullSeat hxc
            rw [hs] at hv
            nomatch hv
          · exact hcvNone hxc hnone
        · exfalso
          by_cases hxc : x = c
          · rw [hxc] at hstep
            obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
            have hlast : lastOf (u.found c.suit) = some c := by
              unfold State.foundTop at htop
              rw [hc'c] at htop
              exact htop
            have hcfin : c ∈ u.found c.suit := lastOf_mem hlast
            have hcface : ∃ a, c ∈ (u.piles a).faceUp := mem_faceUp_of_seatOf_ne (by rw [hsome]; simp)
            obtain ⟨a, ha⟩ := hcface
            exact ((mem_found_unique hwf hcfin).1 a).2 ha
          · have h := pull_seat_change hstep c (fun hcon => hxc hcon.symm)
            rw [h] at hv
            rw [hsome] at hv
            nomatch hv
  | tabToTab x b =>
      have hfoundv : ∀ c', (v.found c') = (u.found c') := by
        obtain ⟨a, hhold, hcp, hface, hs⟩ := step_tabToTab_inv hstep
        intro c'
        rw [hs, putRun_found, setPile_found]
      have hcvNone : seatOf u c = none → c ∈ v.found c.suit := by
        intro hnone
        rw [hfoundv]
        exact hcfound hnone
      refine ⟨?_, ?_, hzv⟩
      · rcases hseat with hnone | hsome
        · exact Or.inl (seatOf_none_of_found hwfv (hcvNone hnone))
        · have hz0top : u.pileOfTop z0 = none := (seat_parent_data hwf hsome).2
          have hcpy : u.canPlace c b = false :=
            seated_no_canPlace hwf hfit hz0top hztop b
          by_cases hxc : x = c
          · exfalso
            rw [hxc] at hstep
            obtain ⟨a, hhold, hcp, hface, hs⟩ := step_tabToTab_inv hstep
            rw [hcpy] at hcp
            nomatch hcp
          · refine Or.inr ?_
            have h := tfc_seat_point_edit hwf hstep hrev c
            rw [ite_eq_right (fun hcon => hxc hcon.symm)] at h
            rw [h]
            exact hsome
      · intro hv
        rcases hseat with hnone | hsome
        · exact hcvNone hnone
        · exfalso
          have hz0top : u.pileOfTop z0 = none := (seat_parent_data hwf hsome).2
          have hcpy : u.canPlace c b = false :=
            seated_no_canPlace hwf hfit hz0top hztop b
          by_cases hxc : x = c
          · rw [hxc] at hstep
            obtain ⟨a, hhold, hcp, hface, hs⟩ := step_tabToTab_inv hstep
            rw [hcpy] at hcp
            nomatch hcp
          · have h := tfc_seat_point_edit hwf hstep hrev c
            rw [ite_eq_right (fun hcon => hxc hcon.symm)] at h
            rw [h] at hv
            rw [hsome] at hv
            nomatch hv

/-- A finite search for a pull of `x` in a play (constructive witness). -/
private def hasPull (x : Card) : List Move → Bool
  | [] => false
  | m :: ρ =>
      (match m with
       | Move.foundToTab x' _ => decide (x' = x)
       | _ => false) || hasPull x ρ

private theorem hasPull_cons_of_ne {x : Card} {m : Move} {ρ : List Move}
    (hm : ∀ b : Base, m ≠ Move.foundToTab x b) :
    hasPull x (m :: ρ) = hasPull x ρ := by
  cases m with
  | foundToTab x' b =>
      by_cases h : x' = x
      · exact absurd (by rw [h]) (hm b)
      · have hdec : decide (x' = x) = false := decide_false_of_not h
        simp [hasPull, hdec]
  | _ => rfl

private theorem hasPull_iff (x : Card) : ∀ (play : List Move),
    hasPull x play = true ↔ ∃ b : Base, Move.foundToTab x b ∈ play
  | [] => by simp [hasPull]
  | m :: ρ => by
      cases m with
      | foundToTab x' b =>
          simp only [hasPull, Bool.or_eq_true, decide_eq_true_eq]
          constructor
          · rintro (h | h)
            · subst h
              exact ⟨b, List.mem_cons_self⟩
            · obtain ⟨b', hb'⟩ := (hasPull_iff x ρ).mp h
              exact ⟨b', List.mem_cons_of_mem _ hb'⟩
          · rintro ⟨b', hb'⟩
            rcases List.mem_cons.mp hb' with h | h
            · injection h with h1 _
              left
              exact h1.symm
            · exact Or.inr ((hasPull_iff x ρ).mpr ⟨b', h⟩)
      | draw =>
          rw [hasPull_cons_of_ne (x := x) (m := Move.draw) (ρ := ρ) (fun b h => by nomatch h),
            hasPull_iff x ρ]
          constructor
          · rintro ⟨b, hb⟩; exact ⟨b, List.mem_cons_of_mem _ hb⟩
          · rintro ⟨b, hb⟩
            rcases List.mem_cons.mp hb with h | h
            · nomatch h
            · exact ⟨b, h⟩
      | wasteToFound y =>
          rw [hasPull_cons_of_ne (x := x) (m := Move.wasteToFound y) (ρ := ρ) (fun b h => by nomatch h),
            hasPull_iff x ρ]
          constructor
          · rintro ⟨b, hb⟩; exact ⟨b, List.mem_cons_of_mem _ hb⟩
          · rintro ⟨b, hb⟩
            rcases List.mem_cons.mp hb with h | h
            · nomatch h
            · exact ⟨b, h⟩
      | wasteToTab y c =>
          rw [hasPull_cons_of_ne (x := x) (m := Move.wasteToTab y c) (ρ := ρ) (fun b h => by nomatch h),
            hasPull_iff x ρ]
          constructor
          · rintro ⟨b, hb⟩; exact ⟨b, List.mem_cons_of_mem _ hb⟩
          · rintro ⟨b, hb⟩
            rcases List.mem_cons.mp hb with h | h
            · nomatch h
            · exact ⟨b, h⟩
      | tabToFound y =>
          rw [hasPull_cons_of_ne (x := x) (m := Move.tabToFound y) (ρ := ρ) (fun b h => by nomatch h),
            hasPull_iff x ρ]
          constructor
          · rintro ⟨b, hb⟩; exact ⟨b, List.mem_cons_of_mem _ hb⟩
          · rintro ⟨b, hb⟩
            rcases List.mem_cons.mp hb with h | h
            · nomatch h
            · exact ⟨b, h⟩
      | tabToTab y c =>
          rw [hasPull_cons_of_ne (x := x) (m := Move.tabToTab y c) (ρ := ρ) (fun b h => by nomatch h),
            hasPull_iff x ρ]
          constructor
          · rintro ⟨b, hb⟩; exact ⟨b, List.mem_cons_of_mem _ hb⟩
          · rintro ⟨b, hb⟩
            rcases List.mem_cons.mp hb with h | h
            · nomatch h
            · exact ⟨b, h⟩

/-- **The strong foundation arm.**  If the origin parent's twin is in the
foundation and `c` ends on the tableau, then the play pulls that twin: the
pull is forced, no seat-mate raise is needed. -/
theorem nonFloater_change_found_needs_target_pull
    {st w : State} (hwfst : st.WF) (_hw : w.WF) {c : Card}
    (_htab : ∃ b, seatOf st c = some b)
    (_hnf : ¬ FloaterSpec st c)
    (hchg : seatOf w c ≠ seatOf st c)
    (hfound : ∃ z : Card,
      seatOf st c = some (Sum.inr z) ∧ z.twin ∈ st.found z.twin.suit)
    (hends : ∃ b, seatOf w c = some b) :
    ∀ play : List Move, ShufflePlayW st play w →
      ∃ z : Card, ∃ b : Base,
        seatOf st c = some (Sum.inr z) ∧ Move.foundToTab z.twin b ∈ play := by
  rintro play hplay
  obtain ⟨z0, hse0, hzfound0⟩ := hfound
  by_cases hpull : hasPull z0.twin play = true
  · obtain ⟨b, hb⟩ := (hasPull_iff z0.twin play).mp hpull
    exact ⟨z0, b, hse0, hb⟩
  · exfalso
    have hnoPullB : ∀ b : Base, Move.foundToTab z0.twin b ∉ play := by
      intro b hmem
      exact hpull ((hasPull_iff z0.twin play).mpr ⟨b, hmem⟩)
    have hfit : canSitOn c z0 = true := canSitOn_parent_of_seat hwfst hse0
    have aux : ∀ {a b : State} {ρ : List Move}, ShufflePlayW a ρ b → a.WF →
        (∀ b' : Base, Move.foundToTab z0.twin b' ∉ ρ) →
        (seatOf a c = none ∨ seatOf a c = some (Sum.inr z0)) →
        (seatOf a c = none → c ∈ a.found c.suit) →
        z0.twin ∈ a.found z0.twin.suit →
        (seatOf b c = none ∨ seatOf b c = some (Sum.inr z0)) := by
      intro a b ρ h
      induction h with
      | nil s =>
          intro _ hno hS _ _
          exact hS
      | @cons u v W m ρ hrev hstep hrest ih =>
          intro hwf hno hS hF hZ
          have hnotPull : ∀ b : Base, m ≠ Move.foundToTab z0.twin b := by
            intro b hm
            exact hno b (by rw [hm]; exact List.mem_cons_self)
          have hno' : ∀ b : Base, Move.foundToTab z0.twin b ∉ ρ := by
            intro b hmem
            exact hno b (List.mem_cons_of_mem _ hmem)
          obtain ⟨hS', hF', hZ'⟩ :=
            hfound_step_invariant hwf hstep hrev hZ hnotPull hfit hS hF
          exact ih (step_wf hwf hstep) hno' hS' hF' hZ'
    have hS := aux hplay hwfst hnoPullB (Or.inr hse0)
      (fun h => by rw [hse0] at h; nomatch h) hzfound0
    rcases hS with hnone | hsome
    · obtain ⟨b, hb⟩ := hends
      rw [hnone] at hb
      nomatch hb
    · exact hchg (hsome.trans hse0.symm)

/-- A live target makes the seated card a floater-spec. -/
private theorem floaterSpec_of_top {s : State} {c z0 : Card} {a k : Anchor}
    (hse : seatOf s c = some (Sum.inr z0))
    (hhold : s.pileHolding c = some a)
    (htop : s.pileOfTop z0.twin = some k) :
    FloaterSpec s c :=
  Or.inl ⟨z0, a, hse, hhold, Or.inl ⟨k, htop⟩⟩

/-- For a non-king card seated on `z0`, floater-spec is exactly a live
`z0.twin` target. -/
private theorem top_of_floaterSpec {s : State} {c z0 : Card}
    (hse : seatOf s c = some (Sum.inr z0))
    (hnk : c.rank ≠ Rank.king) (hf : FloaterSpec s c) :
    ∃ k : Anchor, s.pileOfTop z0.twin = some k := by
  rcases hf with ⟨z, a, hsez, hhold, htop | ⟨hk, -⟩⟩ | ⟨a, hseinl, hk, -⟩
  · have hz : z = z0 := by
      rw [hsez] at hse
      injection hse with h1
      exact Sum.inr.inj h1
    rw [hz] at htop
    exact htop
  · exact absurd hk hnk
  · exact absurd hk hnk

/-- Before the first gain, the target twin cannot enter the foundation: a
raise of it would already be the gain, a waste-found is irreversible, and the
other foundation edits cannot add it. -/
private theorem not_found_step {u v : State} {m : Move} {c z0 : Card}
    (_hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hse : seatOf u c = some (Sum.inr z0))
    (hnf : ¬ FloaterSpec u c)
    (hnot : z0.twin ∉ u.found z0.twin.suit) :
    z0.twin ∉ v.found z0.twin.suit := by
  intro hmem
  obtain ⟨a, hhold, -, -⟩ := tfc_seatOf_of_inr hse
  cases m with
  | draw =>
      exact hnot (by rwa [(chart_draw hstep).2.1 z0.twin.suit])
  | wasteToFound x =>
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToFound_inv hstep
      rw [hs] at hmem
      by_cases hx : x = z0.twin
      · subst hx
        exact absurd hrev (wasteToFound_not_reversibleAtW u z0.twin)
      · have hmem' : z0.twin ∈ u.found z0.twin.suit := by
          by_cases hsu : x.suit = z0.twin.suit
          · rw [← hsu] at hmem ⊢
            rw [setFound_found_self, List.mem_append] at hmem
            rcases hmem with h | h
            · exact h
            · rw [List.mem_singleton] at h
              exact absurd h.symm hx
          · rw [setFound_found_ne (fun h => hsu h.symm)] at hmem
            exact hmem
        exact hnot hmem'
  | wasteToTab x b =>
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToTab_inv hstep
      rw [hs] at hmem
      cases b with
      | inl t =>
          rw [putCard_inl_found] at hmem
          exact hnot hmem
      | inr z =>
          rw [putCard_inr_found] at hmem
          exact hnot hmem
  | tabToFound x =>
      obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
      rw [hs] at hmem
      by_cases hx : x = z0.twin
      · subst hx
        have htop : u.pileOfTop z0.twin = some a := hpa
        exact hnf (floaterSpec_of_top hse hhold htop)
      · have hmem' : z0.twin ∈ u.found z0.twin.suit := by
          by_cases hsu : x.suit = z0.twin.suit
          · rw [← hsu] at hmem ⊢
            rw [setFound_found_self, List.mem_append] at hmem
            rcases hmem with h | h
            · exact h
            · rw [List.mem_singleton] at h
              exact absurd h.symm hx
          · rw [setFound_found_ne (fun h => hsu h.symm)] at hmem
            exact hmem
        exact hnot hmem'
  | foundToTab x b =>
      obtain ⟨-, htop, hcx, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs] at hmem
      have hfoundEq : ((u.setFound x.suit (chop (u.found x.suit))).putCard x b).found
          = (u.setFound x.suit (chop (u.found x.suit))).found := by
        cases b with
        | inl t => rw [putCard_inl_found]
        | inr z => rw [putCard_inr_found]
      rw [hfoundEq] at hmem
      by_cases hsu : x.suit = z0.twin.suit
      · rw [← hsu] at hmem
        rw [setFound_found_self] at hmem
        exact hnot (by rw [← hsu]; exact chop_mem hmem)
      · rw [setFound_found_ne (fun h => hsu h.symm)] at hmem
        exact hnot hmem
  | tabToTab x b =>
      obtain ⟨a, hhold', hcp, hface, hs⟩ := step_tabToTab_inv hstep
      rw [hs] at hmem
      rw [putRun_found, setPile_found] at hmem
      exact hnot hmem

/-- Under `¬FloaterSpec` and no seat-mate raise, a seated card's seat cannot
move to another tableau seat: the only mover is a slide of the card itself,
which would already be a floater-spec. -/
private theorem stack_seat_change {u v : State} {m : Move} {c z0 : Card}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hse : seatOf u c = some (Sum.inr z0))
    (hnf : ¬ FloaterSpec u c)
    (hnoStack : ∀ x : Card, SeatMate c x → m ≠ Move.tabToFound x)
    {b : Base} (hse' : seatOf v c = some b) (hne : b ≠ Sum.inr z0) :
    False := by
  have eq_of_seat : seatOf u c = some b → b = Sum.inr z0 := by
    intro hs
    have h1 : (some (Sum.inr z0) : Option Base) = some b := hse.symm.trans hs
    injection h1 with h2
    exact h2.symm
  cases m with
  | draw =>
      have h := (chart_draw hstep).1 c
      rw [h] at hse'
      exact hne (eq_of_seat hse')
  | wasteToFound x =>
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToFound_inv hstep
      have hp : v.piles = u.piles := by rw [hs]; rfl
      have h := seatOf_congr_piles hp c
      rw [h] at hse'
      exact hne (eq_of_seat hse')
  | wasteToTab x b' =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u x b')
  | tabToFound x =>
      by_cases hxc : x = c
      · exfalso
        rw [hxc] at hstep
        obtain ⟨-, a, hpa, hs⟩ := step_tabToFound_inv hstep
        have hwfv : v.WF := step_wf hwf hstep
        have hcfin : c ∈ v.found c.suit := by
          rw [hs]
          show c ∈ (u.setFound c.suit (u.found c.suit ++ [c])).found c.suit
          rw [setFound_found_self]
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        rw [seatOf_none_of_found hwfv hcfin] at hse'
        nomatch hse'
      · have h := raise_seat_change_of_seated hstep hrev
          (by rw [hse]; simp) (fun hcon => hxc hcon.symm)
        rw [h] at hse'
        exact hne (eq_of_seat hse')
  | foundToTab x b' =>
      by_cases hxc : x = c
      · exfalso
        rw [hxc] at hstep
        obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
        have hlast : lastOf (u.found c.suit) = some c := by
          unfold State.foundTop at htop
          rw [hc'c] at htop
          exact htop
        have hcfin : c ∈ u.found c.suit := lastOf_mem hlast
        have hcface : ∃ a, c ∈ (u.piles a).faceUp := mem_faceUp_of_seatOf_ne (by rw [hse]; simp)
        obtain ⟨a, ha⟩ := hcface
        exact ((mem_found_unique hwf hcfin).1 a).2 ha
      · have h := pull_seat_change hstep c (fun hcon => hxc hcon.symm)
        rw [h] at hse'
        exact hne (eq_of_seat hse')
  | tabToTab x b' =>
      by_cases hxc : x = c
      · exfalso
        rw [hxc] at hstep
        rw [hxc] at hrev
        have hF : Floater u c := ⟨b', hrev⟩
        exact hnf ((floater_classification u hwf c).mp hF)
      · have h := tfc_seat_point_edit hwf hstep hrev c
        rw [ite_eq_right (fun hcon => hxc hcon.symm)] at h
        rw [h] at hse'
        exact hne (eq_of_seat hse')

/-- A raise of the card itself is always a seat-mate stack. -/
private theorem stack_of_tabToFound_self {c : Card} {play : List Move}
    (h : Move.tabToFound c ∈ play) :
    ∃ x : Card, SeatMate c x ∧ Move.tabToFound x ∈ play := by
  by_cases hk : c.rank = Rank.king
  · exact ⟨c, Or.inl ⟨hk, hk⟩, h⟩
  · exact ⟨c, Or.inr ⟨hk, Or.inl rfl⟩, h⟩

private theorem fg_canSitOn_parent_of_seat {s : State} (hwf : s.WF)
    {c z : Card} (hse : seatOf s c = some (Sum.inr z)) :
    canSitOn c z = true := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hse
  exact (tfc_seat_parent hwf hhold hlast).1

/-- A seated card's parent tops no pile (same restatement, second
conjunct). -/
private theorem fg_parent_not_top {s : State} (hwf : s.WF)
    {c z : Card} (hse : seatOf s c = some (Sum.inr z)) :
    s.pileOfTop z = none := by
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hse
  exact (tfc_seat_parent hwf hhold hlast).2

/-- The twin relabeling is invisible to the fit (restatement of
`Orig/Twin.lean:74`, not seam-available). -/
private theorem fg_canSitOn_twin_left (c b : Card) :
    canSitOn c.twin b = canSitOn c b := by
  rcases c with ⟨s, r⟩
  rcases b with ⟨s', r'⟩
  cases s <;> cases s' <;> rfl

/-- A live `z0.twin` top makes a seated card a floater-spec
(restatement of `Orig2/SeatMateStack.lean`'s private
`floaterSpec_of_top`). -/
private theorem fg_floaterSpec_of_top {s : State} {c z0 : Card} {a k : Anchor}
    (hse : seatOf s c = some (Sum.inr z0))
    (hhold : s.pileHolding c = some a)
    (htop : s.pileOfTop z0.twin = some k) :
    FloaterSpec s c :=
  Or.inl ⟨z0, a, hse, hhold, Or.inl ⟨k, htop⟩⟩

/-- For a non-king card seated on `z0`, floater-spec is exactly a live
`z0.twin` target (restatement of `Orig2/SeatMateStack.lean`'s private
`top_of_floaterSpec`). -/
private theorem fg_top_of_floaterSpec {s : State} {c z0 : Card}
    (hse : seatOf s c = some (Sum.inr z0))
    (hnk : c.rank ≠ Rank.king) (hf : FloaterSpec s c) :
    ∃ k : Anchor, s.pileOfTop z0.twin = some k := by
  rcases hf with ⟨z, a, hsez, hhold, htop | ⟨hk, -⟩⟩ | ⟨a, hseinl, hk, -⟩
  · have hz : z = z0 := by
      rw [hsez] at hse
      injection hse with h1
      exact Sum.inr.inj h1
    rw [hz] at htop
    exact htop
  · exact absurd hk hnk
  · exact absurd hk hnk

/-- A reversible raise never fires the reveal: the `tabToFoundR` cell
at an empty chop forces the hidden deck empty.  (Restatement of the
conclusion of `Orig2/SeatMateStack.lean`'s private
`raise_hidden_nil_of_chop_nil`, re-proved from the public oracle
bridge.) -/
private theorem fg_hidden_nil_of_chop_nil {u : State} {x : Card} {a : Anchor}
    (hwf : u.WF) (hrev : reversibleAtW u (Move.tabToFound x))
    (hn : u.nextUp x = true) (hpa : u.pileOfTop x = some a)
    (hchop : chop (u.piles a).faceUp = []) :
    (u.piles a).hidden = [] := by
  have hR : tabToFoundR u x = true :=
    (tabToFoundR_iff_reversibleAtW hwf x).mpr hrev
  cases hhid : (u.piles a).hidden with
  | nil => rfl
  | cons h t =>
      simp only [tabToFoundR, hn, hpa, hchop, hhid] at hR
      exact Bool.noConfusion hR

/-- The last of a moving run is the last of its pile's face-up list. -/
private theorem fg_lastOf_fromCard {x : Card} {l : List Card}
    (hfr : fromCard x l ≠ []) :
    lastOf (fromCard x l) = lastOf l := by
  have h1 : lastOf (below x l ++ fromCard x l) = lastOf (fromCard x l) :=
    tfc_lastOf_append_ne _ hfr
  rw [tfc_below_fromCard x l] at h1
  exact h1.symm

/-! ## §2. The first-gain step -/

theorem floaterSpec_gain_step {u v : State} {m : Move} {c z0 : Card}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hse : seatOf u c = some (Sum.inr z0))
    (hse' : seatOf v c = some (Sum.inr z0))
    (hnk : c.rank ≠ Rank.king)
    (hnf : ¬ FloaterSpec u c) (hf : FloaterSpec v c) :
    m = Move.tabToFound c.twin ∨
      (∃ b : Base, m = Move.foundToTab z0.twin b) := by
  obtain ⟨ahold, hhold, -, hlastc⟩ := tfc_seatOf_of_inr hse
  -- no `z0.twin` top at the origin
  have hnotop : u.pileOfTop z0.twin = none := by
    cases h : u.pileOfTop z0.twin with
    | none => rfl
    | some k => exact absurd (fg_floaterSpec_of_top hse hhold h) hnf
  -- a `z0.twin` top at the successor
  obtain ⟨kv, htopv⟩ := fg_top_of_floaterSpec hse' hnk hf
  have htopk : lastOf (v.piles kv).faceUp = some z0.twin :=
    (tfc_pileOfTop_top htopv).2
  -- the old-top contradiction kit
  have oldTop : ∀ j, v.piles j = u.piles j →
      lastOf (v.piles j).faceUp = some z0.twin → False := by
    intro j hpj hvj
    have hu : lastOf (u.piles j).faceUp = some z0.twin := by
      rw [← hpj]
      exact hvj
    have hsome : u.pileOfTop z0.twin = some j :=
      (pileOfTop_eq_some_iff hwf).mpr hu
    rw [hnotop] at hsome
    nomatch hsome
  cases m with
  | draw =>
      exfalso
      have hp : v.piles = u.piles := stepDraw_piles hstep
      exact oldTop kv (by rw [hp]) htopk
  | wasteToFound x =>
      exfalso
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToFound_inv hstep
      have hp : v.piles = u.piles := by rw [hs]; rfl
      exact oldTop kv (by rw [hp]) htopk
  | wasteToTab x b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u x b)
  | tabToFound x =>
      -- the witness top is the donor pile's new top
      obtain ⟨hnxt, a, hpa, hs⟩ := step_tabToFound_inv hstep
      have hkva : kv = a := by
        by_cases hk : kv = a
        · exact hk
        · exfalso
          have hpk : v.piles kv = u.piles kv := by
            rw [hs]
            dsimp only
            rw [ite_eq_right hk]
          exact oldTop kv hpk htopk
      subst kv
      have hpa' : v.piles a =
          Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp) := by
        rw [hs]
        dsimp only
        rw [ite_eq_left rfl]
      have hlastQ : lastOf
          (Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)).faceUp
          = some z0.twin := by
        rw [← hpa']
        exact htopk
      -- reversibility excludes the reveal
      have hchopNe : chop (u.piles a).faceUp ≠ [] := by
        intro hchop
        have hhid : (u.piles a).hidden = [] :=
          fg_hidden_nil_of_chop_nil hwf hrev hnxt hpa hchop
        have hface : (Pile.afterRunRemoved (u.piles a)
            (chop (u.piles a).faceUp)).faceUp = [] :=
          afterRunRemoved_faceUp_nil hchop hhid
        rw [hface] at hlastQ
        nomatch hlastQ
      have hlastPre : lastOf (chop (u.piles a).faceUp) = some z0.twin := by
        have h := hlastQ
        rw [afterRunRemoved_faceUp_ne hchopNe] at h
        exact h
      -- the raised card sat directly on `z0.twin`
      have hlastx : lastOf (u.piles a).faceUp = some x :=
        (tfc_pileOfTop_top hpa).2
      have hface : (u.piles a).faceUp = chop (u.piles a).faceUp ++ [x] :=
        lastOf_chop hlastx
      have hnd : (u.piles a).faceUp.Nodup := runOK_nodup (hwf.2.1 a)
      have hnotmem : x ∉ chop (u.piles a).faceUp := by
        rw [hface] at hnd
        exact List.snoc_nodup_notMem _ _ hnd
      have hbelow : below x (u.piles a).faceUp = chop (u.piles a).faceUp := by
        have h := below_snoc_not_mem (x := x)
          (L := chop (u.piles a).faceUp) hnotmem
        rwa [← hface] at h
      have hholdx : u.pileHolding x = some a :=
        (pileHolding_eq_some_iff hwf).mpr (lastOf_mem hlastx)
      have hxse : seatOf u x = some (Sum.inr z0.twin) :=
        tfc_seatOf_inr_intro hholdx (by rw [hbelow]; exact hlastPre)
      have hx : x = c.twin := blocker_eq_twin hwf hse hxse
      exact Or.inl (by rw [hx])
  | foundToTab x b =>
      -- every new top is the pulled card itself
      obtain ⟨x', htopx, hx'x, hcp, hs⟩ := step_foundToTab_inv hstep
      subst x'
      cases b with
      | inl t =>
          have hvt : v.piles t = (⟨[], [x]⟩ : Pile) := by
            rw [hs]
            show (if t = t then (⟨[], [x]⟩ : Pile)
              else (u.setFound x.suit (chop (u.found x.suit))).piles t) = ⟨[], [x]⟩
            rw [ite_eq_left rfl]
          have hpk : ∀ j, j ≠ t → v.piles j = u.piles j := by
            intro j hj
            rw [hs]
            show (if j = t then (⟨[], [x]⟩ : Pile)
              else (u.setFound x.suit (chop (u.found x.suit))).piles j) = u.piles j
            rw [ite_eq_right hj]
            rfl
          by_cases hkt : kv = t
          · subst kv
            have hlastx : lastOf (v.piles t).faceUp = some x := by
              rw [hvt]
              rfl
            have hxz : x = z0.twin := by
              rw [hlastx] at htopk
              exact Option.some.inj htopk
            exact Or.inr ⟨Sum.inl t, by rw [hxz]⟩
          · exact False.elim (oldTop kv (hpk kv hkt) htopk)
      | inr z =>
          cases hz : (u.setFound x.suit (chop (u.found x.suit))).pileOfTop z with
          | none =>
              have hv : v = u.setFound x.suit (chop (u.found x.suit)) := by
                rw [hs]
                show (u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inr z)
                  = u.setFound x.suit (chop (u.found x.suit))
                rw [State.putCard, hz]
              have hpku : v.piles kv = u.piles kv := by
                rw [hv]
                rfl
              exact False.elim (oldTop kv hpku htopk)
          | some t =>
              have hvt : v.piles t =
                  { (u.setFound x.suit (chop (u.found x.suit))).piles t with
                    faceUp := ((u.setFound x.suit (chop (u.found x.suit))).piles t).faceUp
                      ++ [x] } := by
                rw [hs]
                show ((u.setFound x.suit (chop (u.found x.suit))).putCard x
                  (Sum.inr z)).piles t = _
                rw [State.putCard, hz]
                exact setPile_piles_self
              have hpk : ∀ j, j ≠ t → v.piles j
                  = (u.setFound x.suit (chop (u.found x.suit))).piles j := by
                intro j hj
                rw [hs]
                show ((u.setFound x.suit (chop (u.found x.suit))).putCard x
                  (Sum.inr z)).piles j = _
                rw [State.putCard, hz]
                exact setPile_piles_ne hj
              by_cases hkt : kv = t
              · subst kv
                rw [hvt] at htopk
                rw [lastOf_snoc] at htopk
                have hxz : x = z0.twin := Option.some.inj htopk
                exact Or.inr ⟨Sum.inr z, by rw [hxz]⟩
              · have hpku : v.piles kv = u.piles kv := by
                  rw [hpk kv hkt]
                  rfl
                exact False.elim (oldTop kv hpku htopk)
  | tabToTab x b =>
      exfalso
      obtain ⟨a, hhold, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
      have hmem : x ∈ (u.piles a).faceUp := pileHolding_mem hhold
      have hR : tabToTabR u x b = true :=
        (tabToTabR_iff_reversibleAtW hwf x b).mpr hrev
      obtain ⟨aR, hholdR, hcpR, hcellR⟩ := tfc_tabToTabR_inv hR
      have haR : aR = a := Option.some.inj (hholdR.symm.trans hhold)
      subst aR
      -- a new top equal to the moving run's top repeats an old top
      have runAbsurd :
          lastOf (fromCard x (u.piles a).faceUp) = some z0.twin → False := by
        intro hl
        have hu : u.pileOfTop z0.twin = some a :=
          (pileOfTop_eq_some_iff hwf).mpr (by
            show lastOf (u.piles a).faceUp = some z0.twin
            rw [← fg_lastOf_fromCard hfr]
            exact hl)
        rw [hnotop] at hu
        nomatch hu
      -- a new source top equal to `z0.twin` puts the mover on it
      have sourceAbsurd :
          lastOf (Pile.afterRunRemoved (u.piles a)
            (below x (u.piles a).faceUp)).faceUp = some z0.twin → False := by
        intro hlastQ
        cases hpre : below x (u.piles a).faceUp with
        | nil =>
            rw [hpre] at hlastQ
            rcases hcellR with hne | ⟨-, hhid, -⟩
            · exact absurd hpre hne
            · rw [Pile.afterRunRemoved_bare hhid] at hlastQ
              nomatch hlastQ
        | cons w ws =>
            rw [hpre] at hlastQ
            have hlastPre : lastOf (below x (u.piles a).faceUp) = some z0.twin := by
              have h := hlastQ
              rw [afterRunRemoved_faceUp_ne (p := u.piles a)
                (pre := w :: ws) (by simp)] at h
              rw [hpre]
              exact h
            have hxse : seatOf u x = some (Sum.inr z0.twin) :=
              tfc_seatOf_inr_intro hhold hlastPre
            have hx : x = c.twin := blocker_eq_twin hwf hse hxse
            have hfitc : canSitOn c z0 = true := fg_canSitOn_parent_of_seat hwf hse
            have hz0none : u.pileOfTop z0 = none := fg_parent_not_top hwf hse
            rw [hx] at hcp
            cases b with
            | inl t =>
                obtain ⟨-, hking⟩ := canPlace_inl hcp
                exact hnk (by
                  have hrank : (c.twin).rank = c.rank := rfl
                  rw [hrank] at hking
                  exact hking)
            | inr w =>
                obtain ⟨k, hlocw, hfitw⟩ := canPlace_inr hcp
                have hfitcw : canSitOn c w = true := by
                  rw [← fg_canSitOn_twin_left c w]
                  exact hfitw
                rcases tfc_fitting_parent hfitcw hfitc with hw | hw
                · rw [hw] at hlocw
                  rw [hz0none] at hlocw
                  nomatch hlocw
                · rw [hw] at hlocw
                  rw [hnotop] at hlocw
                  nomatch hlocw
      have sourceTop : ∀ (hva : v.piles a = Pile.afterRunRemoved (u.piles a)
            (below x (u.piles a).faceUp)),
          lastOf (v.piles a).faceUp = some z0.twin → False := by
        intro hva hv
        apply sourceAbsurd
        rw [← hva]
        exact hv
      cases b with
      | inl t =>
          have hv_t : v.piles t = (⟨[], fromCard x (u.piles a).faceUp⟩ : Pile) := by
            rw [hs]
            show (((u.setPile a (Pile.afterRunRemoved (u.piles a)
              (below x (u.piles a).faceUp))).putRun
              (fromCard x (u.piles a).faceUp) (Sum.inl t)).piles t) = _
            rw [putRun_eq_inl, setPile_piles_self]
          have hv_j : ∀ j, j ≠ t → v.piles j =
              (u.setPile a (Pile.afterRunRemoved (u.piles a)
                (below x (u.piles a).faceUp))).piles j := by
            intro j hj
            rw [hs]
            show (((u.setPile a (Pile.afterRunRemoved (u.piles a)
              (below x (u.piles a).faceUp))).putRun
              (fromCard x (u.piles a).faceUp) (Sum.inl t)).piles j) = _
            rw [putRun_eq_inl, setPile_piles_ne hj]
          by_cases hka : kv = a
          · subst kv
            by_cases hta : a = t
            · subst t
              apply runAbsurd
              rw [hv_t] at htopk
              exact htopk
            · have hva : v.piles a = Pile.afterRunRemoved (u.piles a)
                  (below x (u.piles a).faceUp) := by
                rw [hv_j a hta, setPile_piles_self]
              exact sourceTop hva htopk
          · by_cases hkt : kv = t
            · subst kv
              apply runAbsurd
              rw [hv_t] at htopk
              exact htopk
            · have hpku : v.piles kv = u.piles kv := by
                rw [hv_j kv hkt, setPile_piles_ne hka]
              exact False.elim (oldTop kv hpku htopk)
      | inr z =>
          cases hz : (u.setPile a (Pile.afterRunRemoved (u.piles a)
              (below x (u.piles a).faceUp))).pileOfTop z with
          | none =>
              have hv : v = u.setPile a (Pile.afterRunRemoved (u.piles a)
                  (below x (u.piles a).faceUp)) := by
                rw [hs]
                show ((u.setPile a (Pile.afterRunRemoved (u.piles a)
                  (below x (u.piles a).faceUp))).putRun
                  (fromCard x (u.piles a).faceUp) (Sum.inr z)) =
                  u.setPile a (Pile.afterRunRemoved (u.piles a)
                    (below x (u.piles a).faceUp))
                rw [State.putRun, hz]
              by_cases hka : kv = a
              · subst kv
                have hva : v.piles a = Pile.afterRunRemoved (u.piles a)
                    (below x (u.piles a).faceUp) := by
                  rw [hv, setPile_piles_self]
                exact sourceTop hva htopk
              · have hpku : v.piles kv = u.piles kv := by
                  rw [hv, setPile_piles_ne hka]
                exact False.elim (oldTop kv hpku htopk)
          | some t =>
              have hv_t : v.piles t =
                  { (u.setPile a (Pile.afterRunRemoved (u.piles a)
                      (below x (u.piles a).faceUp))).piles t with
                    faceUp := ((u.setPile a (Pile.afterRunRemoved (u.piles a)
                      (below x (u.piles a).faceUp))).piles t).faceUp
                        ++ fromCard x (u.piles a).faceUp } := by
                rw [hs]
                show ((u.setPile a (Pile.afterRunRemoved (u.piles a)
                  (below x (u.piles a).faceUp))).putRun
                  (fromCard x (u.piles a).faceUp) (Sum.inr z)).piles t = _
                rw [putRun_inr_eq hz]
                rw [setPile_piles_self]
              have hv_j : ∀ j, j ≠ t → v.piles j =
                  (u.setPile a (Pile.afterRunRemoved (u.piles a)
                    (below x (u.piles a).faceUp))).piles j := by
                intro j hj
                rw [hs]
                show ((u.setPile a (Pile.afterRunRemoved (u.piles a)
                  (below x (u.piles a).faceUp))).putRun
                  (fromCard x (u.piles a).faceUp) (Sum.inr z)).piles j = _
                rw [putRun_inr_eq hz]
                rw [setPile_piles_ne hj]
              by_cases hka : kv = a
              · subst kv
                by_cases hta : a = t
                · subst t
                  apply runAbsurd
                  rw [hv_t] at htopk
                  rw [setPile_piles_self, tfc_lastOf_append_ne _ hfr] at htopk
                  exact htopk
                · have hva : v.piles a = Pile.afterRunRemoved (u.piles a)
                      (below x (u.piles a).faceUp) := by
                    rw [hv_j a hta, setPile_piles_self]
                  exact sourceTop hva htopk
              · by_cases hkt : kv = t
                · subst kv
                  apply runAbsurd
                  rw [hv_t] at htopk
                  rw [tfc_lastOf_append_ne _ hfr] at htopk
                  exact htopk
                · have hpku : v.piles kv = u.piles kv := by
                    rw [hv_j kv hkt, setPile_piles_ne hka]
                  exact False.elim (oldTop kv hpku htopk)

/-! ## Audit battery -/


/-- The per-step stack invariant: before the first gain, either the seated
card stays on its parent with `¬FloaterSpec` and the target still outside the
foundation, or a seat-mate raise has already occurred. -/
private theorem stack_step {u v : State} {m : Move} {c z0 : Card}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hse : seatOf u c = some (Sum.inr z0))
    (hnf : ¬ FloaterSpec u c)
    (hznot : z0.twin ∉ u.found z0.twin.suit)
    (hnoStack : ∀ x : Card, SeatMate c x → m ≠ Move.tabToFound x) :
    (seatOf v c = some (Sum.inr z0) ∧ ¬ FloaterSpec v c ∧
        z0.twin ∉ v.found z0.twin.suit) ∨
      (∃ x : Card, SeatMate c x ∧ m = Move.tabToFound x) := by
  have hnk : c.rank ≠ Rank.king :=
    canSitOn_not_king (canSitOn_parent_of_seat hwf hse)
  have hfit : canSitOn c z0 = true := canSitOn_parent_of_seat hwf hse
  have hseat : seatOf v c = some (Sum.inr z0) ∨
      (∃ x : Card, SeatMate c x ∧ m = Move.tabToFound x) := by
    by_cases hnone : seatOf v c = none
    · have hm : m = Move.tabToFound c :=
        step_seat_none_eq_tabToFound hwf hstep hrev (by rw [hse]; simp) hnone
      exact Or.inr ⟨c, Or.inr ⟨hnk, Or.inl rfl⟩, hm⟩
    · obtain ⟨b, hb⟩ : ∃ b, seatOf v c = some b := by
        cases hv : seatOf v c with
        | none => exact absurd hv hnone
        | some b => exact ⟨b, rfl⟩
      by_cases hb0 : b = Sum.inr z0
      · exact Or.inl (by rw [hb0] at hb; exact hb)
      · exact False.elim (stack_seat_change hwf hstep hrev hse hnf hnoStack hb hb0)
  rcases hseat with hsame | hstack
  · cases htop : v.pileOfTop z0.twin with
    | none =>
        have hnoGain : ¬ FloaterSpec v c := by
          intro hf
          obtain ⟨k, hk⟩ := top_of_floaterSpec hsame hnk hf
          rw [htop] at hk
          nomatch hk
        exact Or.inl ⟨hsame, hnoGain, not_found_step hwf hstep hrev hse hnf hznot⟩
    | some k =>
        obtain ⟨a', hhold', -, -⟩ := tfc_seatOf_of_inr hsame
        have hgain : FloaterSpec v c := floaterSpec_of_top hsame hhold' htop
        rcases floaterSpec_gain_step hwf hstep hrev hse hsame hnk hnf hgain with
          hraise | ⟨b, hpull⟩
        · exact Or.inr ⟨c.twin, Or.inr ⟨hnk, Or.inr rfl⟩, hraise⟩
        · exfalso
          rw [hpull] at hstep
          obtain ⟨z', htop', hz'c, hcp, hs⟩ := step_foundToTab_inv hstep
          have hlast : lastOf (u.found z0.twin.suit) = some z0.twin := by
            unfold State.foundTop at htop'
            rw [hz'c] at htop'
            exact htop'
          exact hznot (lastOf_mem hlast)
  · exact Or.inr hstack

/-- The boolean form of `SeatMate`. -/
private def seatMateB (c x : Card) : Bool :=
  (decide (c.rank = Rank.king) && decide (x.rank = Rank.king)) ||
    (!decide (c.rank = Rank.king) && (decide (x = c) || decide (x = c.twin)))

private theorem seatMateB_eq (c x : Card) : seatMateB c x = true ↔ SeatMate c x := by
  unfold seatMateB SeatMate
  by_cases hk : c.rank = Rank.king <;> simp [hk]

/-- A finite search for a seat-mate raise in a play (constructive witness). -/
private def stackHead (c : Card) (m : Move) : Bool :=
  match m with
  | Move.tabToFound x => seatMateB c x
  | _ => false

private theorem stackHead_tabToFound (c x : Card) :
    stackHead c (Move.tabToFound x) = true ↔ SeatMate c x := by
  simp [stackHead, seatMateB_eq]

private def hasStack (c : Card) : List Move → Bool
  | [] => false
  | m :: ρ => stackHead c m || hasStack c ρ

private theorem hasStack_cons_of_not {c : Card} {m : Move} {ρ : List Move}
    (hm : ∀ x : Card, m ≠ Move.tabToFound x) :
    hasStack c (m :: ρ) = hasStack c ρ := by
  cases m with
  | tabToFound x => exact absurd rfl (hm x)
  | _ => rfl

private theorem hasStack_iff (c : Card) : ∀ (play : List Move),
    hasStack c play = true ↔ ∃ x : Card, SeatMate c x ∧ Move.tabToFound x ∈ play
  | [] => by simp [hasStack]
  | m :: ρ => by
      cases m with
      | tabToFound x =>
          simp only [hasStack, Bool.or_eq_true, stackHead_tabToFound]
          constructor
          · rintro (hs | hs)
            · exact ⟨x, hs, List.mem_cons_self⟩
            · obtain ⟨y, hsy, hy⟩ := (hasStack_iff c ρ).mp hs
              exact ⟨y, hsy, List.mem_cons_of_mem _ hy⟩
          · rintro ⟨y, hsy, hy⟩
            rcases List.mem_cons.mp hy with h | h
            · injection h with h1
              left
              rw [← h1]
              exact hsy
            · exact Or.inr ((hasStack_iff c ρ).mpr ⟨y, hsy, h⟩)
      | draw =>
          rw [hasStack_cons_of_not (c := c) (m := Move.draw) (ρ := ρ) (fun x h => by nomatch h),
            hasStack_iff c ρ]
          constructor
          · rintro ⟨y, hsy, hy⟩; exact ⟨y, hsy, List.mem_cons_of_mem _ hy⟩
          · rintro ⟨y, hsy, hy⟩
            rcases List.mem_cons.mp hy with h | h
            · nomatch h
            · exact ⟨y, hsy, h⟩
      | wasteToFound y =>
          rw [hasStack_cons_of_not (c := c) (m := Move.wasteToFound y) (ρ := ρ) (fun x h => by nomatch h),
            hasStack_iff c ρ]
          constructor
          · rintro ⟨z, hsz, hz⟩; exact ⟨z, hsz, List.mem_cons_of_mem _ hz⟩
          · rintro ⟨z, hsz, hz⟩
            rcases List.mem_cons.mp hz with h | h
            · nomatch h
            · exact ⟨z, hsz, h⟩
      | wasteToTab y b =>
          rw [hasStack_cons_of_not (c := c) (m := Move.wasteToTab y b) (ρ := ρ) (fun x h => by nomatch h),
            hasStack_iff c ρ]
          constructor
          · rintro ⟨z, hsz, hz⟩; exact ⟨z, hsz, List.mem_cons_of_mem _ hz⟩
          · rintro ⟨z, hsz, hz⟩
            rcases List.mem_cons.mp hz with h | h
            · nomatch h
            · exact ⟨z, hsz, h⟩
      | foundToTab y b =>
          rw [hasStack_cons_of_not (c := c) (m := Move.foundToTab y b) (ρ := ρ) (fun x h => by nomatch h),
            hasStack_iff c ρ]
          constructor
          · rintro ⟨z, hsz, hz⟩; exact ⟨z, hsz, List.mem_cons_of_mem _ hz⟩
          · rintro ⟨z, hsz, hz⟩
            rcases List.mem_cons.mp hz with h | h
            · nomatch h
            · exact ⟨z, hsz, h⟩
      | tabToTab y b =>
          rw [hasStack_cons_of_not (c := c) (m := Move.tabToTab y b) (ρ := ρ) (fun x h => by nomatch h),
            hasStack_iff c ρ]
          constructor
          · rintro ⟨z, hsz, hz⟩; exact ⟨z, hsz, List.mem_cons_of_mem _ hz⟩
          · rintro ⟨z, hsz, hz⟩
            rcases List.mem_cons.mp hz with h | h
            · nomatch h
            · exact ⟨z, hsz, h⟩

/-- A non-king card at the bottom of a pile cannot move to another seat:
its slide is unlicensed, and every other letter either preserves its seat or
raises it (a stack). -/
private theorem bottom_seat_step {u v : State} {m : Move} {c : Card} {a0 : Anchor}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hse : seatOf u c = some (Sum.inl a0))
    (hnk : c.rank ≠ Rank.king)
    (hnoStack : ∀ x : Card, SeatMate c x → m ≠ Move.tabToFound x) :
    seatOf v c = some (Sum.inl a0) ∨
      (∃ x : Card, SeatMate c x ∧ m = Move.tabToFound x) := by
  cases m with
  | draw =>
      exact Or.inl (by rw [(chart_draw hstep).1 c]; exact hse)
  | wasteToFound x =>
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToFound_inv hstep
      have hp : v.piles = u.piles := by rw [hs]; rfl
      exact Or.inl (by rw [seatOf_congr_piles hp c]; exact hse)
  | wasteToTab x b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u x b)
  | tabToFound x =>
      by_cases hxc : x = c
      · exact Or.inr ⟨c, Or.inr ⟨hnk, Or.inl rfl⟩, by rw [hxc]⟩
      · exact Or.inl (by
          rw [raise_seat_change_of_seated hstep hrev (by rw [hse]; simp) (fun hcon => hxc hcon.symm)]
          exact hse)
  | foundToTab x b =>
      by_cases hxc : x = c
      · exfalso
        rw [hxc] at hstep
        obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
        have hlast : lastOf (u.found c.suit) = some c := by
          unfold State.foundTop at htop
          rw [hc'c] at htop
          exact htop
        have hcfin : c ∈ u.found c.suit := lastOf_mem hlast
        have hcface : ∃ a, c ∈ (u.piles a).faceUp := mem_faceUp_of_seatOf_ne (by rw [hse]; simp)
        obtain ⟨a, ha⟩ := hcface
        exact ((mem_found_unique hwf hcfin).1 a).2 ha
      · exact Or.inl (by
          rw [pull_seat_change hstep c (fun hcon => hxc hcon.symm)]
          exact hse)
  | tabToTab x b =>
      by_cases hxc : x = c
      · exfalso
        rw [hxc] at hstep
        rw [hxc] at hrev
        have hR : tabToTabR u c b = true :=
          (tabToTabR_iff_reversibleAtW hwf c b).mpr hrev
        obtain ⟨a, hhold, hcp, hcell⟩ := tfc_tabToTabR_inv hR
        obtain ⟨hhold0, hbelow0⟩ := tfc_seatOf_of_inl hse
        have ha : a = a0 := by
          rw [hhold0] at hhold
          injection hhold with h
          exact h.symm
        rw [ha] at hcell
        rcases hcell with hne | ⟨hbelow, hhid, hk⟩
        · exact absurd hbelow0 hne
        · exact hnk hk
      · have h := tfc_seat_point_edit hwf hstep hrev c
        rw [ite_eq_right (fun hcon => hxc hcon.symm)] at h
        exact Or.inl (by rw [h]; exact hse)

/-- The interior (inr-seat) stack arm: under no stack, the card never leaves
its parent and never gains a floater-spec, contradicting the seat change. -/
private theorem stack_arm_inr {st w : State} (hwfst : st.WF) {c z0 : Card}
    (hse : seatOf st c = some (Sum.inr z0))
    (hnf : ¬ FloaterSpec st c)
    (hznot : z0.twin ∉ st.found z0.twin.suit)
    (hchg : seatOf w c ≠ seatOf st c)
    {play : List Move} (hplay : ShufflePlayW st play w)
    (hnoStack : ∀ x : Card, SeatMate c x → Move.tabToFound x ∉ play) :
    False := by
  have aux : ∀ {a b : State} {ρ : List Move}, ShufflePlayW a ρ b → a.WF →
      (∀ x : Card, SeatMate c x → Move.tabToFound x ∉ ρ) →
      seatOf a c = some (Sum.inr z0) → ¬ FloaterSpec a c →
      z0.twin ∉ a.found z0.twin.suit →
      seatOf b c = some (Sum.inr z0) ∧ ¬ FloaterSpec b c ∧
        z0.twin ∉ b.found z0.twin.suit := by
    intro a b ρ h
    induction h with
    | nil s =>
        intro _ _ hs hf hz
        exact ⟨hs, hf, hz⟩
    | @cons u v W m ρ hrev hstep hrest ih =>
        intro hwf hno hs hf hz
        have hnoHead : ∀ x : Card, SeatMate c x → m ≠ Move.tabToFound x := by
          intro x hsx hm
          exact hno x hsx (by rw [hm]; exact List.mem_cons_self)
        have hnoTail : ∀ x : Card, SeatMate c x → Move.tabToFound x ∉ ρ := by
          intro x hsx hmem
          exact hno x hsx (List.mem_cons_of_mem _ hmem)
        rcases stack_step hwf hstep hrev hs hf hz hnoHead with hinv | ⟨x, hsx, hm⟩
        · exact ih (step_wf hwf hstep) hnoTail hinv.1 hinv.2.1 hinv.2.2
        · exact absurd hm (hnoHead x hsx)
  have hinv := aux hplay hwfst hnoStack hse hnf hznot
  exact hchg (hinv.1.trans hse.symm)

/-- The bottom (inl-seat) stack arm: a non-king at the bottom cannot move
under no stack. -/
private theorem stack_arm_inl {st w : State} (hwfst : st.WF) {c : Card} {a0 : Anchor}
    (hnk : c.rank ≠ Rank.king)
    (hse : seatOf st c = some (Sum.inl a0))
    (hchg : seatOf w c ≠ seatOf st c)
    {play : List Move} (hplay : ShufflePlayW st play w)
    (hnoStack : ∀ x : Card, SeatMate c x → Move.tabToFound x ∉ play) :
    False := by
  have aux : ∀ {a b : State} {ρ : List Move}, ShufflePlayW a ρ b → a.WF →
      (∀ x : Card, SeatMate c x → Move.tabToFound x ∉ ρ) →
      seatOf a c = some (Sum.inl a0) → seatOf b c = some (Sum.inl a0) := by
    intro a b ρ h
    induction h with
    | nil s =>
        intro _ _ hs
        exact hs
    | @cons u v W m ρ hrev hstep hrest ih =>
        intro hwf hno hs
        have hnoHead : ∀ x : Card, SeatMate c x → m ≠ Move.tabToFound x := by
          intro x hsx hm
          exact hno x hsx (by rw [hm]; exact List.mem_cons_self)
        have hnoTail : ∀ x : Card, SeatMate c x → Move.tabToFound x ∉ ρ := by
          intro x hsx hmem
          exact hno x hsx (List.mem_cons_of_mem _ hmem)
        rcases bottom_seat_step hwf hstep hrev hs hnk hnoHead with hs' | ⟨x, hsx, hm⟩
        · exact ih (step_wf hwf hstep) hnoTail hs'
        · exact absurd hm (hnoHead x hsx)
  exact hchg ((aux hplay hwfst hnoStack hse).trans hse.symm)

/-- **The non-king stack arm.**  If the origin parent's twin is not in the
foundation (so no foundation pull can explain the gain), a seat-mate of `c`
is raised. -/
theorem nonFloater_nonKing_change_seatmate_of_not_found
    {st w : State} (hwfst : st.WF) (_hw : w.WF) {c : Card}
    (hnk : c.rank ≠ Rank.king)
    (htab : ∃ b, seatOf st c = some b)
    (hnf : ¬ FloaterSpec st c)
    (hchg : seatOf w c ≠ seatOf st c)
    (hnotfound : ∀ z : Card,
      seatOf st c = some (Sum.inr z) → z.twin ∉ st.found z.twin.suit) :
    ∀ play : List Move, ShufflePlayW st play w →
      ∃ x : Card, SeatMate c x ∧ Move.tabToFound x ∈ play := by
  intro play hplay
  by_cases hs : hasStack c play = true
  · exact (hasStack_iff c play).mp hs
  · exfalso
    have hnoStack : ∀ x : Card, SeatMate c x → Move.tabToFound x ∉ play := by
      intro x hsx hmem
      exact hs ((hasStack_iff c play).mpr ⟨x, hsx, hmem⟩)
    obtain ⟨b, hb⟩ := htab
    cases b with
    | inl a0 => exact stack_arm_inl hwfst hnk hb hchg hplay hnoStack
    | inr z0 => exact stack_arm_inr hwfst hb hnf (hnotfound z0 hb) hchg hplay hnoStack

/-- **The `ends off-tableau` stack arm**: if `c` starts seated and ends off
the tableau, it was raised, so a seat-mate (itself) is stacked. -/
theorem nonFloater_change_stack_of_ends_none
    {st w : State} (hwfst : st.WF) {c : Card}
    (htab : ∃ b, seatOf st c = some b)
    (hnone : seatOf w c = none)
    {play : List Move} (hplay : ShufflePlayW st play w) :
    ∃ x : Card, SeatMate c x ∧ Move.tabToFound x ∈ play :=
  stack_of_tabToFound_self (tabToFound_of_seat_none hwfst htab hnone hplay)

/-- **The non-king `¬hfound` stack arm** in the negation shape used by the
binary split. -/
theorem nonFloater_nonKing_change_stack_of_not_found
    {st w : State} (hwfst : st.WF) (hw : w.WF) {c : Card}
    (hnk : c.rank ≠ Rank.king)
    (htab : ∃ b, seatOf st c = some b)
    (hnf : ¬ FloaterSpec st c)
    (hchg : seatOf w c ≠ seatOf st c)
    (hnotfound : ¬ ∃ z : Card,
      seatOf st c = some (Sum.inr z) ∧ z.twin ∈ st.found z.twin.suit) :
    ∀ play : List Move, ShufflePlayW st play w →
      ∃ x : Card, SeatMate c x ∧ Move.tabToFound x ∈ play := by
  intro play hplay
  exact nonFloater_nonKing_change_seatmate_of_not_found hwfst hw hnk htab hnf hchg
    (fun z hz hmem => hnotfound ⟨z, hz, hmem⟩) play hplay

private theorem ka_canSitOn_not_king {c z : Card} (h : canSitOn c z = true) :
    c.rank ≠ Rank.king := by
  obtain ⟨hidx, -⟩ := (canSitOn_eq c z).mp h
  intro hk
  have h12 : c.rank.toIdx = 12 := by rw [hk]; rfl
  have hlt := Rank.toIdx_lt z.rank
  omega

/-- A king's tableau seat is always a pile-bottom seat (`inl`); an `inr`
seat would let the king sit on a card. -/
private theorem ka_king_seat_inl {s : State} (hwf : s.WF) {c : Card}
    (hking : c.rank = Rank.king) {b : Base} (hse : seatOf s c = some b) :
    ∃ a : Anchor, b = Sum.inl a := by
  cases b with
  | inl a => exact ⟨a, rfl⟩
  | inr z =>
      exfalso
      obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hse
      exact ka_canSitOn_not_king ((tfc_seat_parent hwf hhold hlast).1) hking

/-- A non-Floater bare king forces every pile nonempty. -/
private theorem ka_no_empty_of_nf {s : State} {c : Card} {a0 : Anchor}
    (hking : c.rank = Rank.king)
    (hse : seatOf s c = some (Sum.inl a0))
    (hnf : ¬ FloaterSpec s c)
    (hhid : (s.piles a0).hidden = []) :
    ∀ a : Anchor, (s.piles a).isEmpty = false := by
  intro a
  cases ha : (s.piles a).isEmpty with
  | false => rfl
  | true =>
      exact absurd (Or.inr ⟨a0, hse, hking, hhid, a, ha⟩) hnf

/-! ## §2. The hidden ledger of a reversible step -/

/-- A reversible raise never reveals: every hidden deck is unchanged. -/
private theorem ka_tabToFound_hidden_eq {u v : State} {x : Card}
    (hwf : u.WF) (hstep : State.step u (Move.tabToFound x) = some v)
    (hrev : reversibleAtW u (Move.tabToFound x)) :
    ∀ a : Anchor, (v.piles a).hidden = (u.piles a).hidden := by
  intro a
  obtain ⟨hnxt, a', hpa, hs⟩ := step_tabToFound_inv hstep
  rw [hs]
  dsimp only
  by_cases ha : a = a'
  · rw [ite_eq_left ha, ha]
    rcases afterRunRemoved_hidden (u.piles a') (chop (u.piles a').faceUp) with
      ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨hchop, hhidne, -⟩
    · exact h
    · exact h
    · exfalso
      have hR : tabToFoundR u x = true :=
        (tabToFoundR_iff_reversibleAtW hwf x).mpr hrev
      cases hh : (u.piles a').hidden with
      | nil => exact absurd hh hhidne
      | cons g gs =>
          simp only [tabToFoundR, hnxt, hpa, hchop, hh] at hR
          exact Bool.noConfusion hR
  · rw [ite_eq_right ha]

/-- Every reversible step keeps every hidden deck. -/
private theorem ka_hidden_eq_of_rev_step {u v : State} {m : Move}
    (hwf : u.WF) (hstep : State.step u m = some v) (hrev : reversibleAtW u m) :
    ∀ a : Anchor, (v.piles a).hidden = (u.piles a).hidden := by
  intro a
  cases m with
  | draw =>
      rw [stepDraw_piles hstep]
  | wasteToFound x =>
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      rfl
  | wasteToTab x b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u x b)
  | tabToFound x =>
      exact ka_tabToFound_hidden_eq hwf hstep hrev a
  | foundToTab x b =>
      obtain ⟨c', htop, hcx, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      exact putCard_hidden_eq (st := u.setFound x.suit (chop (u.found x.suit)))
        (c := x) (b := b) hcp a
  | tabToTab x b =>
      exact ((tfa_slide_conserves hwf hstep hrev).1.1 a).symm

/-! ## §3. No empty pile appears without a king raise -/

/-- With no empty pile to start with and no king raise fired, a
reversible step creates no empty pile: a bare raise or a bare slide
would have to move a king (the raise excluded, the slide's empty-seat
landing or the bare-king hand needing an empty target at the origin). -/
private theorem ka_no_empty_step {u v : State} {m : Move}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hne : ∀ a : Anchor, (u.piles a).isEmpty = false)
    (hnoKing : ∀ x : Card, x.rank = Rank.king → m ≠ Move.tabToFound x) :
    ∀ a : Anchor, (v.piles a).isEmpty = false := by
  intro a
  by_cases hva : (v.piles a).isEmpty = true
  · exfalso
    rcases KingFuel.empty_gain_step_is_raise_or_slide hstep hne ⟨a, hva⟩ with
      ⟨x, a', hm, hpa, hemp⟩ | ⟨x, b, hm⟩
    · -- an emptying raise is a king raise
      have hstep' : State.step u (Move.tabToFound x) = some v := by
        rw [← hm]; exact hstep
      have hrev' : reversibleAtW u (Move.tabToFound x) := by
        rw [← hm]; exact hrev
      exact (hnoKing x (KingFuel.emptying_raise_is_king hstep' hrev' hpa hemp)) hm
    · -- an emptying slide is a bare king slide, which needs an empty target
      have hstep' : State.step u (Move.tabToTab x b) = some v := by
        rw [← hm]; exact hstep
      have hrev' : reversibleAtW u (Move.tabToTab x b) := by
        rw [← hm]; exact hrev
      obtain ⟨a0, hhold, hcp, hcell⟩ :=
        tfc_tabToTabR_inv ((tabToTabR_iff_reversibleAtW hwf x b).mpr hrev')
      cases b with
      | inl t =>
          obtain ⟨hempty, -⟩ := canPlace_inl hcp
          rw [hne t] at hempty
          exact Bool.noConfusion hempty
      | inr z =>
          obtain ⟨k, hloc, hsit⟩ := canPlace_inr hcp
          rcases hcell with hbelow | ⟨hbelow, hhid, hking⟩
          · -- the source keeps a nonempty face-up prefix; all other piles
            -- are unchanged or appended to, hence no pile empties
            obtain ⟨a1, hhold1, hcp1, hfr, hs⟩ := step_tabToTab_inv hstep'
            have ha1 : a1 = a0 := Option.some.inj (hhold1.symm.trans hhold)
            subst a1
            have hQface :
                (Pile.afterRunRemoved (u.piles a0)
                  (below x (u.piles a0).faceUp)).faceUp
                  = below x (u.piles a0).faceUp :=
              afterRunRemoved_faceUp_ne hbelow
            have hsourceNonempty :
                ∀ {a' : Anchor}, a' = a0 →
                  ((u.setPile a0 (Pile.afterRunRemoved (u.piles a0)
                    (below x (u.piles a0).faceUp))).piles a').isEmpty = false := by
              intro a' ha'
              subst a'
              rw [setPile_piles_self]
              obtain ⟨y, hy⟩ : ∃ y, y ∈ below x (u.piles a0).faceUp := by
                cases hb : below x (u.piles a0).faceUp with
                | nil => exact absurd hb hbelow
                | cons y ys => exact ⟨y, by simp⟩
              exact Pile.isEmpty_eq_false_of_mem
                (p := Pile.afterRunRemoved (u.piles a0)
                  (below x (u.piles a0).faceUp))
                (by rw [hQface]; exact hy)
            have hfalse : (v.piles a).isEmpty = false := by
              rw [hs]
              cases hz : (u.setPile a0 (Pile.afterRunRemoved (u.piles a0)
                  (below x (u.piles a0).faceUp))).pileOfTop z with
              | none =>
                  rw [putRun_inr_none_piles hz a]
                  by_cases ha0 : a = a0
                  · exact hsourceNonempty ha0
                  · rw [setPile_piles_ne ha0]
                    exact hne a
              | some t =>
                  by_cases hat : a = t
                  · rw [hat]
                    rw [putRun_piles_inr_self (u.setPile a0 (Pile.afterRunRemoved
                      (u.piles a0) (below x (u.piles a0).faceUp)))
                      (fromCard x (u.piles a0).faceUp) z t hz]
                    cases hc : fromCard x (u.piles a0).faceUp with
                    | nil => exact absurd hc hfr
                    | cons r rs =>
                        exact Pile.isEmpty_eq_false_of_mem (c := r) (by simp)
                  · rw [putRun_piles_inr_ne (u.setPile a0 (Pile.afterRunRemoved
                      (u.piles a0) (below x (u.piles a0).faceUp)))
                      (fromCard x (u.piles a0).faceUp) z t hz hat]
                    by_cases ha0 : a = a0
                    · exact hsourceNonempty ha0
                    · rw [setPile_piles_ne ha0]
                      exact hne a
            rw [hfalse] at hva
            exact Bool.noConfusion hva
          · exact ka_canSitOn_not_king hsit hking
  · cases ha : (v.piles a).isEmpty with
    | false => rfl
    | true => exact absurd ha hva

/-! ## §4. The seat is constant while no king is raised -/

/-- One reversible step with no king raise keeps a bare king's seat. -/
private theorem ka_seat_step {u v : State} {m : Move} {c : Card} {a0 : Anchor}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hking : c.rank = Rank.king)
    (hse : seatOf u c = some (Sum.inl a0))
    (hcase : (u.piles a0).hidden ≠ [] ∨ (∀ j : Anchor, (u.piles j).isEmpty = false))
    (hno : ∀ x : Card, x.rank = Rank.king → m ≠ Move.tabToFound x) :
    seatOf v c = some (Sum.inl a0) := by
  cases m with
  | draw =>
      rw [(chart_draw hstep).1 c]
      exact hse
  | wasteToFound x =>
      obtain ⟨-, y, ys, hw, hs⟩ := step_wasteToFound_inv hstep
      have hp : v.piles = u.piles := by rw [hs]; rfl
      rw [seatOf_congr_piles hp c]
      exact hse
  | wasteToTab x b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u x b)
  | tabToFound x =>
      by_cases hxc : x = c
      · exfalso
        exact (hno x (by rw [hxc]; exact hking)) (by rw [hxc])
      · rw [raise_seat_change_of_seated hstep hrev (by rw [hse]; simp)
          (fun hcon => hxc hcon.symm)]
        exact hse
  | foundToTab x b =>
      obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
      by_cases hxc : x = c
      · exfalso
        have hlast : lastOf (u.found c.suit) = some c := by
          unfold State.foundTop at htop
          rw [hxc] at htop
          rw [hc'c, hxc] at htop
          exact htop
        have hfin : c ∈ u.found c.suit := lastOf_mem hlast
        obtain ⟨hhold, hbl⟩ := tfc_seatOf_of_inl hse
        exact ((mem_found_unique hwf hfin).1 a0).2 (pileHolding_mem hhold)
      · rw [pull_seat_change hstep c (fun hcon => hxc hcon.symm)]
        exact hse
  | tabToTab x b =>
      by_cases hxc : x = c
      · exfalso
        subst x
        have hR : tabToTabR u c b = true :=
          (tabToTabR_iff_reversibleAtW hwf c b).mpr hrev
        obtain ⟨a, hhold, hcp, hcell⟩ := tfc_tabToTabR_inv hR
        obtain ⟨hhold0, hbl0⟩ := tfc_seatOf_of_inl hse
        have ha : a = a0 := Option.some.inj (hhold.symm.trans hhold0)
        rw [ha] at hcell
        rcases hcell with hbelow | ⟨-, hhid, -⟩
        · exact hbelow hbl0
        · rcases hcase with hhidne | hnonempty
          · exact hhidne hhid
          · cases b with
            | inl t =>
                obtain ⟨hempty, -⟩ := canPlace_inl hcp
                rw [hnonempty t] at hempty
                exact Bool.noConfusion hempty
            | inr z =>
                obtain ⟨k, -, hfit⟩ := canPlace_inr hcp
                exact ka_canSitOn_not_king hfit hking
      · rw [tfc_seat_point_edit hwf hstep hrev c]
        rw [ite_eq_right (fun hcon => hxc hcon.symm)]
        exact hse

/-- Along a play with no king raise, a bare king's seat never changes,
provided either its hidden deck is nonempty or every pile is nonempty. -/
private theorem ka_seat_const_aux {u w : State} {play : List Move} {c : Card}
    {a0 : Anchor}
    (hplay : ShufflePlayW u play w) (hwf : u.WF)
    (hno : ∀ x : Card, x.rank = Rank.king → Move.tabToFound x ∉ play)
    (hking : c.rank = Rank.king)
    (hse : seatOf u c = some (Sum.inl a0))
    (hcase : (u.piles a0).hidden ≠ [] ∨
      (∀ j : Anchor, (u.piles j).isEmpty = false)) :
    seatOf w c = seatOf u c := by
  induction hplay with
  | nil => rfl
  | @cons a b W m ρ hrev hstep hrest ih =>
      have hnoStep : ∀ x : Card, x.rank = Rank.king → m ≠ Move.tabToFound x := by
        intro x hxk hm
        exact hno x hxk (by rw [hm]; exact List.mem_cons_self)
      have hnoRest : ∀ x : Card, x.rank = Rank.king → Move.tabToFound x ∉ ρ := by
        intro x hxk hmem
        exact hno x hxk (List.mem_cons_of_mem _ hmem)
      have hwfb : b.WF := step_wf hwf hstep
      have hseb : seatOf b c = some (Sum.inl a0) :=
        ka_seat_step hwf hstep hrev hking hse hcase hnoStep
      have hcaseb : (b.piles a0).hidden ≠ [] ∨
          (∀ j : Anchor, (b.piles j).isEmpty = false) := by
        rcases hcase with hhid | hne
        · exact Or.inl (by
            rw [ka_hidden_eq_of_rev_step hwf hstep hrev a0]
            exact hhid)
        · exact Or.inr (ka_no_empty_step hwf hstep hrev hne hnoStep)
      have hres := ih hwfb hnoRest hseb hcaseb
      rw [hres, hseb, hse]

/-! ## §5. A constructive search for a king raise -/

private def ka_isKingRaise : Move → Bool
  | Move.tabToFound x => decide (x.rank = Rank.king)
  | _ => false

private def ka_hasKingRaise : List Move → Bool
  | [] => false
  | m :: ρ => ka_isKingRaise m || ka_hasKingRaise ρ

private theorem ka_hasKingRaise_cons_of_not {m : Move} {ρ : List Move}
    (hm : ∀ x : Card, m ≠ Move.tabToFound x) :
    ka_hasKingRaise (m :: ρ) = ka_hasKingRaise ρ := by
  cases m with
  | tabToFound x => exact absurd rfl (hm x)
  | _ => rfl

private theorem ka_hasKingRaise_iff (play : List Move) :
    ka_hasKingRaise play = true ↔
      ∃ x : Card, x.rank = Rank.king ∧ Move.tabToFound x ∈ play := by
  induction play with
  | nil => simp [ka_hasKingRaise]
  | cons m ρ ih =>
      cases m with
      | tabToFound x =>
          simp only [ka_hasKingRaise, ka_isKingRaise, Bool.or_eq_true,
            decide_eq_true_eq]
          constructor
          · rintro (hx | hrest)
            · exact ⟨x, hx, List.mem_cons_self⟩
            · obtain ⟨y, hyk, hy⟩ := ih.mp hrest
              exact ⟨y, hyk, List.mem_cons_of_mem _ hy⟩
          · rintro ⟨y, hyk, hy⟩
            rcases List.mem_cons.mp hy with h | h
            · left
              injection h with h1
              rw [← h1]
              exact hyk
            · right
              exact ih.mpr ⟨y, hyk, h⟩
      | draw =>
          rw [ka_hasKingRaise_cons_of_not (m := Move.draw) (ρ := ρ)
            (fun x h => by nomatch h), ih]
          constructor
          · rintro ⟨y, hyk, hy⟩; exact ⟨y, hyk, List.mem_cons_of_mem _ hy⟩
          · rintro ⟨y, hyk, hy⟩
            rcases List.mem_cons.mp hy with h | h
            · nomatch h
            · exact ⟨y, hyk, h⟩
      | wasteToFound y =>
          rw [ka_hasKingRaise_cons_of_not (m := Move.wasteToFound y) (ρ := ρ)
            (fun x h => by nomatch h), ih]
          constructor
          · rintro ⟨y', hyk, hy⟩; exact ⟨y', hyk, List.mem_cons_of_mem _ hy⟩
          · rintro ⟨y', hyk, hy⟩
            rcases List.mem_cons.mp hy with h | h
            · nomatch h
            · exact ⟨y', hyk, h⟩
      | wasteToTab y b =>
          rw [ka_hasKingRaise_cons_of_not (m := Move.wasteToTab y b) (ρ := ρ)
            (fun x h => by nomatch h), ih]
          constructor
          · rintro ⟨y', hyk, hy⟩; exact ⟨y', hyk, List.mem_cons_of_mem _ hy⟩
          · rintro ⟨y', hyk, hy⟩
            rcases List.mem_cons.mp hy with h | h
            · nomatch h
            · exact ⟨y', hyk, h⟩
      | foundToTab y b =>
          rw [ka_hasKingRaise_cons_of_not (m := Move.foundToTab y b) (ρ := ρ)
            (fun x h => by nomatch h), ih]
          constructor
          · rintro ⟨y', hyk, hy⟩; exact ⟨y', hyk, List.mem_cons_of_mem _ hy⟩
          · rintro ⟨y', hyk, hy⟩
            rcases List.mem_cons.mp hy with h | h
            · nomatch h
            · exact ⟨y', hyk, h⟩
      | tabToTab y b =>
          rw [ka_hasKingRaise_cons_of_not (m := Move.tabToTab y b) (ρ := ρ)
            (fun x h => by nomatch h), ih]
          constructor
          · rintro ⟨y', hyk, hy⟩; exact ⟨y', hyk, List.mem_cons_of_mem _ hy⟩
          · rintro ⟨y', hyk, hy⟩
            rcases List.mem_cons.mp hy with h | h
            · nomatch h
            · exact ⟨y', hyk, h⟩

/-! ## §6. The king arm -/

theorem nonFloater_king_change_needs_king_stack
    {st w : State} (hwfst : st.WF) (hw : w.WF) {c : Card}
    (hking : c.rank = Rank.king)
    (htab : ∃ b, seatOf st c = some b)
    (hnf : ¬ FloaterSpec st c)
    (hchg : seatOf w c ≠ seatOf st c) :
    ∀ play : List Move, ShufflePlayW st play w →
      ∃ x : Card, x.rank = Rank.king ∧ Move.tabToFound x ∈ play := by
  have _ : w.WF := hw
  intro play hplay
  by_cases hsearch : ka_hasKingRaise play = true
  · exact (ka_hasKingRaise_iff play).mp hsearch
  · exfalso
    obtain ⟨b, hseb⟩ := htab
    obtain ⟨a0, hb⟩ := ka_king_seat_inl hwfst hking hseb
    subst hb
    have hno : ∀ x : Card, x.rank = Rank.king → Move.tabToFound x ∉ play := by
      intro x hxk hmem
      exact hsearch ((ka_hasKingRaise_iff play).mpr ⟨x, hxk, hmem⟩)
    have hcase : (st.piles a0).hidden ≠ [] ∨
        (∀ j : Anchor, (st.piles j).isEmpty = false) := by
      by_cases hhid : (st.piles a0).hidden = []
      · exact Or.inr (ka_no_empty_of_nf hking hseb hnf hhid)
      · exact Or.inl hhid
    exact hchg (ka_seat_const_aux hplay hwfst hno hking hseb hcase)

theorem nonFloater_change_split
    {st w : State} (hwfst : st.WF) (hw : w.WF) {c : Card}
    (htab : ∃ b, seatOf st c = some b)
    (hnf : ¬ FloaterSpec st c)
    (hchg : seatOf w c ≠ seatOf st c) :
    ∀ play : List Move, ShufflePlayW st play w →
      (PullConfiguration st w c → HasTargetPull st c play)
      ∧ (¬ PullConfiguration st w c → HasSeatMateStack c play) := by
  intro play hplay
  constructor
  · intro hconf
    exact nonFloater_change_found_needs_target_pull hwfst hw htab hnf hchg
      hconf.1 hconf.2 play hplay
  · intro hnot
    by_cases hk : c.rank = Rank.king
    · obtain ⟨x, hxk, hx⟩ :=
        nonFloater_king_change_needs_king_stack hwfst hw hk htab hnf hchg play hplay
      exact ⟨x, Or.inl ⟨hk, hxk⟩, hx⟩
    · cases hwseat : seatOf w c with
      | none =>
          exact nonFloater_change_stack_of_ends_none hwfst htab hwseat hplay
      | some b =>
          have hnotfound : ¬ ∃ z : Card,
              seatOf st c = some (Sum.inr z) ∧ z.twin ∈ st.found z.twin.suit := by
            intro hf
            exact hnot ⟨hf, ⟨b, hwseat⟩⟩
          exact nonFloater_nonKing_change_stack_of_not_found hwfst hw hk htab hnf hchg
            hnotfound play hplay

/-- **The main disjunctive target**: a seat-mate raise or the origin parent's
twin pull. -/
theorem nonFloater_change_needs_seatmate_stack
    {st w : State} (hwfst : st.WF) (hw : w.WF) {c : Card}
    (htab : ∃ b, seatOf st c = some b)
    (hnf : ¬ FloaterSpec st c)
    (hchg : seatOf w c ≠ seatOf st c) :
    ∀ play : List Move, ShufflePlayW st play w →
      HasSeatMateStack c play ∨ HasTargetPull st c play := by
  intro play hplay
  have hsplit := nonFloater_change_split hwfst hw htab hnf hchg play hplay
  cases hseat_st : seatOf st c with
  | none =>
      obtain ⟨b, hb⟩ := htab
      rw [hseat_st] at hb
      nomatch hb
  | some bst =>
      cases bst with
      | inl a =>
          exact Or.inl (hsplit.2 (by
            rintro ⟨⟨z, hz, -⟩, -⟩
            rw [hseat_st] at hz
            nomatch hz))
      | inr z0 =>
          by_cases hmem : z0.twin ∈ st.found z0.twin.suit
          · cases hseat_w : seatOf w c with
            | none =>
                exact Or.inl (hsplit.2 (by
                  rintro ⟨-, ⟨b, hb⟩⟩
                  rw [hseat_w] at hb
                  nomatch hb))
            | some bw =>
                have hres := hsplit.1 ⟨⟨z0, hseat_st, hmem⟩, ⟨bw, hseat_w⟩⟩
                exact Or.inr (by simpa only [HasTargetPull, hseat_st] using hres)
          · exact Or.inl (hsplit.2 (by
              rintro ⟨⟨z, hz, hzm⟩, -⟩
              rw [hseat_st] at hz
              injection hz with h1
              have hz0 : z = z0 := (Sum.inr.inj h1).symm
              rw [hz0] at hzm
              exact hmem hzm))

/-- A `setPile` at a different anchor, whose new pile does not top the
searched card, leaves the top search alone. -/
theorem pileOfTop_setPile_ne {st : State} (hwf : st.WF)
    {b k : Anchor} {z : Card} {Q : Pile}
    (h : st.pileOfTop z = some k) (hb : b ≠ k) (hQ : Q.top ≠ some z) :
    (st.setPile b Q).pileOfTop z = some k := by
  have htopk : st.topOf k = some z :=
    of_decide_eq_true (firstWhere_sound (p := fun a => decide (st.topOf a = some z)) h)
  show firstWhere (fun a => decide ((st.setPile b Q).topOf a = some z)) Anchor.all = some k
  apply firstWhere_find (Anchor.mem_all k)
  · simp only [decide_eq_true_eq]
    rw [setPile_topOf_ne (st := st) (k := k) (b := b) (Q := Q)
      (fun hkb => hb hkb.symm)]
    exact htopk
  · intro y _ hyk
    simp only [decide_eq_false_iff_not]
    by_cases hyb : y = b
    · subst hyb
      simpa only [State.topOf, setPile_piles_self] using hQ
    · rw [setPile_topOf_ne (st := st) (k := y) (b := b) (Q := Q) hyb]
      intro htop
      exact (mem_faceUp_unique hwf (lastOf_mem htopk) y hyk).1 (lastOf_mem htop)

/-- A reversible raise whose chop is nonempty flips no hidden card: every
card that had no seat still has none. -/
theorem raise_none_of_chop_ne {u v : State} {d y : Card} {a : Anchor}
    (hstep : State.step u (Move.tabToFound d) = some v)
    (hpa : u.pileOfTop d = some a)
    (hchop : chop (u.piles a).faceUp ≠ [])
    (hseat : seatOf u y = none) : seatOf v y = none := by
  obtain ⟨-, a', hpa', hv⟩ := step_tabToFound_inv hstep
  have hae : a' = a := pileOfTop_inj hpa' hpa
  rw [hae] at hv
  have hnone : u.pileHolding y = none := holdNone_of_seatNone hseat
  have hnotmem : ∀ a', y ∉ (u.piles a').faceUp :=
    fun a' => tfc_not_mem_faceUp_of_holdNone hnone a'
  have hmem : ∀ a', y ∈ (({ u.setFound d.suit (u.found d.suit ++ [d]) with
      piles := fun x => if x = a then Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
        else u.piles x }).piles a').faceUp ↔ y ∈ (u.piles a').faceUp := by
    intro a'
    show y ∈ (if a' = a then Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
      else u.piles a').faceUp ↔ y ∈ (u.piles a').faceUp
    by_cases ha' : a' = a
    · rw [ite_eq_left ha', ha', afterRunRemoved_faceUp_ne hchop]
      constructor
      · intro hm
        exact absurd (chop_mem hm) (hnotmem a)
      · intro hm
        exact absurd hm (hnotmem a)
    · rw [ite_eq_right ha']
  rw [hv]
  apply tfc_seatOf_none
  apply tfc_pileHolding_none
  intro a' hm
  exact hnotmem a' ((hmem a').mp hm)

/-! ## The audit battery -/

#print axioms card_eq_twin_of_rank_color
#print axioms blocker_eq_twin
#print axioms pull_seat_change
#print axioms raise_seat_change_of_seated
#print axioms tabToFound_of_seat_none
#print axioms nonFloater_change_found_needs_target_pull
#print axioms nonFloater_nonKing_change_seatmate_of_not_found
#print axioms nonFloater_change_stack_of_ends_none
#print axioms nonFloater_nonKing_change_stack_of_not_found
#print axioms nonFloater_king_change_needs_king_stack
#print axioms nonFloater_change_split
#print axioms nonFloater_change_needs_seatmate_stack
#print axioms pileOfTop_setPile_ne
#print axioms raise_none_of_chop_ne
