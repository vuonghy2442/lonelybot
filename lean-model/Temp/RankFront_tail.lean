import Temp.RankFront_close

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# RankFront_tail — the tail-existence theorem

This file attacks the last residual of the `raiseS` rank-front lane,
`TailExists` (`Temp/RankFront_close.lean:403`).

## The route

The parent's plan compares the endpoint of `[c] · R` with the interior state of
the original play at which `x` is raised.  Those two states are *not* a
same-multiset play pair, so `(S)` cannot compare them; step 1 has a hole there.

This file uses the **flat characterization** of the licence
(`CanRaiseS st c ↔` a local pile shape, `Orig2/Substrate/CargoRaise.lean:706`),
which removes all cargo-slide bookkeeping from licence questions:

* `CanRaiseS st c = nextUp c ∧` (`c` is face-up in pile `a` as `bs ++ c :: run`,
  and (`bs ≠ []` or bare king), and (`run = []` or `c.twin` tops a pile)).
* raising a card of the *same rank* transfers a licence explicitly (§1), with
  the twin case one-directional (backward unconditional, forward requiring the
  tracked card to be exposed);
* a same-rank adjacent transposition in a *play* then follows in both cases
  (§2, `tie_swap`); the twin case uses `twin_raise_square` at the vanilla
  witness of the first card's step — the existence of the play forces the
  second card to be exposed there, so the square applies;
* a strictly-lower-rank card is passed with `canRaiseS_inert_of_canRaiseStep`
  (§3, `asc_swap`), and the two swaps move `c` to the front of an ascending
  play (§4);
* the remaining tie-order mismatch is handled by `tieFree`: any two ascending
  plays of the same multiset are interchangeable (§5).

House rules: no `sorry`, no `Classical`, no `noncomputable`.
-/

namespace OneColourClosure

/-! ## §0. Small list facts -/

/-- `chop` of a snoc is the prefix. -/
theorem chop_append_singleton : ∀ (l : List Card) (c : Card),
    chop (l ++ [c]) = l
  | [], _ => rfl
  | [x], c => by simp [chop]
  | x :: y :: t, c => by
      show x :: chop ((y :: t) ++ [c]) = x :: (y :: t)
      rw [chop_append_singleton (y :: t) c]

/-- `below` of a snoc is the prefix, provided the card is absent from it. -/
theorem below_append_singleton_of_not_mem : ∀ {l : List Card} {c : Card},
    c ∉ l → below c (l ++ [c]) = l
  | [], _, _ => by simp [below]
  | x :: t, c, h => by
      have hx : x ≠ c := fun hcon => h (by rw [hcon]; exact List.mem_cons_self ..)
      have ht : c ∉ t := fun hmem => h (List.mem_cons_of_mem _ hmem)
      show (if x = c then [] else x :: below c (t ++ [c])) = x :: t
      rw [ite_eq_right hx, below_append_singleton_of_not_mem ht]

/-- If `c` is absent from a prefix, appending `c` makes it the `fromCard`. -/
theorem fromCard_append_singleton_of_not_mem : ∀ {l : List Card} {c : Card},
    c ∉ l → fromCard c (l ++ [c]) = [c]
  | [], _, _ => by simp [fromCard]
  | x :: t, c, h => by
      have hx : x ≠ c := fun hcon => h (by rw [hcon]; exact List.mem_cons_self ..)
      have ht : c ∉ t := fun hmem => h (List.mem_cons_of_mem _ hmem)
      show (if x = c then x :: (t ++ [c]) else fromCard c (t ++ [c])) = [c]
      rw [ite_eq_right hx, fromCard_append_singleton_of_not_mem ht]

/-- If `fromCard c l` is the singleton, then `l` is a prefix followed by `c`. -/
theorem fromCard_singleton_decomp : ∀ {l : List Card} {c : Card},
    fromCard c l = [c] → ∃ bs, l = bs ++ [c]
  | [], _, h => by simp [fromCard] at h
  | x :: t, c, h => by
      by_cases hx : x = c
      · refine ⟨[], ?_⟩
        have hc : c :: t = [c] := by simpa [fromCard, hx] using h
        rwa [hx]
      · have h' : fromCard c t = [c] := by
          rw [show fromCard c (x :: t) = fromCard c t from by simp [fromCard, hx]] at h
          exact h
        obtain ⟨bs, hbs⟩ := fromCard_singleton_decomp h'
        exact ⟨x :: bs, by rw [hbs]; rfl⟩

/-- The twin of a card is not the card. -/
theorem card_twin_ne_self (c : Card) : c.twin ≠ c := by
  intro h
  have hs : c.suit.twin = c.suit := congrArg Card.suit h
  exact Suit.twin_ne c.suit hs

/-- `a = c.twin` gives a different suit. -/
theorem suit_ne_of_twin {a c : Card} (h : a = c.twin) : c.suit ≠ a.suit := by
  rw [h]
  exact (Suit.twin_ne c.suit).symm

/-! ## §1. Same-rank licence transfer -/

/-- A card of the same rank as the pile top cannot occur in that pile. -/
theorem not_mem_pileOfTop_of_rank_eq {z : State} (hz : z.WF) {e d : Card}
    {a : Anchor} (hpa : z.pileOfTop e = some a) (hr : d.rank = e.rank) (hde : d ≠ e) :
    d ∉ (z.piles a).faceUp := by
  intro hmem
  have hlast : lastOf (z.piles a).faceUp = some e := (pileOfTop_top hpa).2
  have hlt := rank_lt_of_mem_of_lastOf (hz.2.1 a) hlast hmem hde
  rw [hr] at hlt
  omega

/-- The twin of a card of the pile top's rank cannot occur in that pile either. -/
theorem not_mem_pileOfTop_twin_of_rank_eq {z : State} (hz : z.WF) {e d : Card}
    {a : Anchor} (hpa : z.pileOfTop e = some a) (hr : d.rank = e.rank)
    (hdt : d.twin ≠ e) :
    d.twin ∉ (z.piles a).faceUp := by
  intro hmem
  have hlast : lastOf (z.piles a).faceUp = some e := (pileOfTop_top hpa).2
  have hlt := rank_lt_of_mem_of_lastOf (hz.2.1 a) hlast hmem hdt
  have hrank : d.twin.rank.toIdx = e.rank.toIdx := by
    rw [Card.twin_rank, hr]
  rw [hrank] at hlt
  omega

/-! ### §1.1 Unpacking / repacking `freeCardS` -/

/-- The flat data of `freeCardS`. -/
theorem freeCardS_unpack {st : State} {c : Card} (hfree : freeCardS st c = true) :
    ∃ p run, st.pileHolding c = some p ∧
      fromCard c ((st.piles p).faceUp) = c :: run ∧
      (below c ((st.piles p).faceUp) ≠ [] ∨
        ((st.piles p).hidden = [] ∧ c.rank = Rank.king)) ∧
      (run = [] ∨ st.pileOfTop c.twin ≠ none) := by
  unfold freeCardS at hfree
  split at hfree
  · exact absurd hfree (by simp)
  · rename_i p hhold
    split at hfree
    · exact absurd hfree (by simp)
    · rename_i head run hF0
      obtain ⟨run', hF'⟩ := tfc_fromCard_cons_head (l := (st.piles p).faceUp)
        (pileHolding_mem hhold)
      rw [hF'] at hF0
      injection hF0 with hhead hrun
      subst hhead
      subst hrun
      rw [Bool.and_eq_true] at hfree
      obtain ⟨hseat, hthird⟩ := hfree
      refine ⟨p, run', hhold, hF', ?_, ?_⟩
      · rw [Bool.or_eq_true] at hseat
        rcases hseat with h | h
        · exact Or.inl (of_decide_eq_true h)
        · rw [Bool.and_eq_true] at h
          exact Or.inr ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩
      · rw [Bool.or_eq_true] at hthird
        rcases hthird with h | h
        · exact Or.inl (of_decide_eq_true h)
        · exact Or.inr (Option.isSome_iff_ne_none.mp h)

/-- Repacking the flat data into `freeCardS`. -/
theorem freeCardS_of_data {st : State} {c : Card} {p : Anchor} {run : List Card}
    (hhold : st.pileHolding c = some p)
    (hF : fromCard c ((st.piles p).faceUp) = c :: run)
    (hseat : below c ((st.piles p).faceUp) ≠ [] ∨
      ((st.piles p).hidden = [] ∧ c.rank = Rank.king))
    (hthird : run = [] ∨ st.pileOfTop c.twin ≠ none) :
    freeCardS st c = true := by
  simp only [freeCardS, hhold, hF]
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [Bool.or_eq_true]
    rcases hseat with h | ⟨h1, h2⟩
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (by rw [Bool.and_eq_true]; exact ⟨decide_eq_true h1, decide_eq_true h2⟩)
  · rw [Bool.or_eq_true]
    rcases hthird with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (Option.isSome_iff_ne_none.mpr h)

/-- **Same-rank, non-twin: the tableau-readiness is unchanged by a licensed raise.**
The raised card's pile neither holds `c` nor `c.twin` (same rank, distinct card),
and a licensed raise never reveals, so every read of `freeCardS c` is fixed. -/
theorem freeCardS_tabToFound_eq_of_rank_eq_notTwin {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (hr : a.rank = c.rank) (hac : a ≠ c) (hat : a ≠ c.twin) :
    freeCardS z' c = freeCardS z c := by
  obtain ⟨-, a1, hpa1, hseat⟩ := hcr
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have ha10 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
  rw [ha10] at hseat
  have hwz' : z'.WF := step_wf hz hstep
  have hc0 : c ∉ (z.piles a0).faceUp :=
    not_mem_pileOfTop_of_rank_eq hz hpa0 hr.symm (Ne.symm hac)
  have hct0 : c.twin ∉ (z.piles a0).faceUp :=
    not_mem_pileOfTop_twin_of_rank_eq hz hpa0 hr.symm (Ne.symm hat)
  have hc0' : c ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_ne hne]
      intro h; exact hc0 (mem_chop_of_mem_chop h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, Pile.afterRunRemoved_bare hhid]; simp
      · rw [afterRunRemoved_ne hch]
        intro h; exact hc0 (mem_chop_of_mem_chop h)
  have hct0' : c.twin ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_ne hne]
      intro h; exact hct0 (mem_chop_of_mem_chop h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, Pile.afterRunRemoved_bare hhid]; simp
      · rw [afterRunRemoved_ne hch]
        intro h; exact hct0 (mem_chop_of_mem_chop h)
  have hagree : ∀ a', a' ≠ a0 → z'.piles a' = z.piles a' := by
    intro a' ha'
    rw [hpiles a', ite_eq_right ha']
  have hph : z'.pileHolding c = z.pileHolding c :=
    pileHolding_eq_of_agree hwz' hagree hc0 hc0'
  have hpt : z'.pileOfTop c.twin = z.pileOfTop c.twin :=
    pileOfTop_eq_of_agree hagree hct0 hct0'
  unfold freeCardS
  rw [hph]
  cases hhh : z.pileHolding c with
  | none => rfl
  | some a' =>
      have ha0 : a' ≠ a0 := by
        intro h; subst h; exact hc0 (pileHolding_mem hhh)
      simp only [hagree a' ha0, hpt]

/-- **Same-rank, non-twin: the licence transfers both ways.** -/
theorem canRaiseS_tabToFound_iff_of_rank_eq_notTwin {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (hr : a.rank = c.rank) (hac : a ≠ c) (hat : a ≠ c.twin) :
    CanRaiseS z' c ↔ CanRaiseS z c := by
  have hwz' : z'.WF := step_wf hz hstep
  have hsu : c.suit ≠ a.suit := by
    intro h
    exact hac (card_eq_of_suit_rank (c := c) (c' := a) h.symm (by rw [hr]))
  have hnext : z'.nextUp c = z.nextUp c := nextUp_raise_ne hstep hsu
  have hfree := freeCardS_tabToFound_eq_of_rank_eq_notTwin hz hstep hcr hr hac hat
  rw [canRaiseS_split hwz', canRaiseS_split hz, hnext, hfree]

/-! ### §1.2 The twin case -/

/-- **The exposed read**: if `freeCardS st c` holds and `c.twin` is not a pile top,
then `c` is exposed (nothing sits above it in its pile). -/
theorem fromCard_nil_of_freeCardS_of_twin_none {st : State} {c : Card} {p : Anchor}
    (hhold : st.pileHolding c = some p) (hfree : freeCardS st c = true)
    (htwin : st.pileOfTop c.twin = none) :
    fromCard c ((st.piles p).faceUp) = [c] := by
  obtain ⟨p', run, hhold', hF, hseat, hthird⟩ := freeCardS_unpack hfree
  have hp : p' = p := by rw [hhold] at hhold'; exact (Option.some.inj hhold').symm
  subst hp
  rcases hthird with h | h
  · rw [h] at hF
    exact hF
  · rw [htwin] at h
    exact absurd h (by simp)

/-- **A licensed raise of a twin, backwards.**  Readiness survives un-raising
`c.twin`: after the twin is founded, `c` is forced to be exposed, and the
un-raised state satisfies the same flat data (the hatch disjunct is vacuous). -/
theorem freeCardS_tabToFound_bwd_of_twin {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (ht : a = c.twin) :
    freeCardS z' c = true → freeCardS z c = true := by
  intro hfree'
  obtain ⟨-, a1, hpa1, hseat⟩ := hcr
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have ha10 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
  rw [ha10] at hseat
  have hwz' : z'.WF := step_wf hz hstep
  have hc0 : c ∉ (z.piles a0).faceUp := by
    apply not_mem_pileOfTop_of_rank_eq hz hpa0
    · rw [ht, Card.twin_rank]
    · intro h; exact (card_twin_ne_self c).symm (h.trans ht)
  have hc0' : c ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_ne hne]
      intro h; exact hc0 (mem_chop_of_mem_chop h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, Pile.afterRunRemoved_bare hhid]; simp
      · rw [afterRunRemoved_ne hch]
        intro h; exact hc0 (mem_chop_of_mem_chop h)
  have hagree : ∀ a', a' ≠ a0 → z'.piles a' = z.piles a' := by
    intro a' ha'
    rw [hpiles a', ite_eq_right ha']
  have hph : z'.pileHolding c = z.pileHolding c :=
    pileHolding_eq_of_agree hwz' hagree hc0 hc0'
  have hfound : a ∈ z'.found a.suit := by
    rw [found_tabToFound hstep a.suit, ite_eq_left rfl]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have htwinnone : z'.pileOfTop c.twin = none := by
    rw [← ht]
    exact pileOfTop_eq_none_of_found hwz' hfound
  obtain ⟨p', run, hhold', hF', hseat', hthird'⟩ := freeCardS_unpack hfree'
  have hholdz : z.pileHolding c = some p' := by rw [← hph]; exact hhold'
  have hexp' : fromCard c ((z'.piles p').faceUp) = [c] :=
    fromCard_nil_of_freeCardS_of_twin_none hhold' hfree' htwinnone
  have hpne : p' ≠ a0 := by
    intro h; subst h; exact hc0 (pileHolding_mem hholdz)
  have hpile : z.piles p' = z'.piles p' := (hagree p' hpne).symm
  have hexp : fromCard c ((z.piles p').faceUp) = [c] := by rw [hpile]; exact hexp'
  have hseat_z : below c ((z.piles p').faceUp) ≠ [] ∨
      ((z.piles p').hidden = [] ∧ c.rank = Rank.king) := by
    rcases hseat' with h | h
    · exact Or.inl (by rwa [hpile])
    · exact Or.inr ⟨by rw [hpile]; exact h.1, h.2⟩
  exact freeCardS_of_data hholdz hexp hseat_z (Or.inl rfl)

/-- **Same-rank twin, backward: the licence transfers back across the twin's raise.** -/
theorem canRaiseS_tabToFound_bwd_of_twin {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (ht : a = c.twin) :
    CanRaiseS z' c → CanRaiseS z c := by
  intro hc
  have hwz' : z'.WF := step_wf hz hstep
  have hnext : z'.nextUp c = z.nextUp c := nextUp_raise_ne hstep (suit_ne_of_twin ht)
  have hsplit := (canRaiseS_split hwz').mp hc
  rw [canRaiseS_split hz]
  exact ⟨by rw [← hnext]; exact hsplit.1,
    freeCardS_tabToFound_bwd_of_twin hz hstep hcr ht hsplit.2⟩

/-- **A licensed raise of a twin, forwards, when the tracked card is exposed.**
Nothing sits above `c`, so the hatch clause is vacuous on both sides. -/
theorem freeCardS_tabToFound_fwd_of_twin {z z' : State} {a c : Card} {p : Anchor}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (ht : a = c.twin)
    (hhold : z.pileHolding c = some p)
    (hexp : fromCard c ((z.piles p).faceUp) = [c]) :
    freeCardS z c = true → freeCardS z' c = true := by
  intro hfree
  obtain ⟨-, a1, hpa1, hseat⟩ := hcr
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have ha10 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
  rw [ha10] at hseat
  have hwz' : z'.WF := step_wf hz hstep
  have hc0 : c ∉ (z.piles a0).faceUp := by
    apply not_mem_pileOfTop_of_rank_eq hz hpa0
    · rw [ht, Card.twin_rank]
    · intro h; exact (card_twin_ne_self c).symm (h.trans ht)
  have hc0' : c ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_ne hne]
      intro h; exact hc0 (mem_chop_of_mem_chop h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, Pile.afterRunRemoved_bare hhid]; simp
      · rw [afterRunRemoved_ne hch]
        intro h; exact hc0 (mem_chop_of_mem_chop h)
  have hagree : ∀ a', a' ≠ a0 → z'.piles a' = z.piles a' := by
    intro a' ha'
    rw [hpiles a', ite_eq_right ha']
  have hph : z'.pileHolding c = z.pileHolding c :=
    pileHolding_eq_of_agree hwz' hagree hc0 hc0'
  obtain ⟨p', run, hhold', hF, hseat', hthird⟩ := freeCardS_unpack hfree
  have hp : p' = p := by rw [hhold] at hhold'; exact (Option.some.inj hhold').symm
  rw [hp] at hhold' hF hseat'
  have hpne : p ≠ a0 := by
    intro h; subst h; exact hc0 (pileHolding_mem hhold)
  have hpile : z'.piles p = z.piles p := hagree p hpne
  have hhold'' : z'.pileHolding c = some p := by rw [hph]; exact hhold'
  have hF' : fromCard c ((z'.piles p).faceUp) = c :: run := by rw [hpile]; exact hF
  have hrun : run = [] := by
    rw [hexp] at hF
    injection hF with _ h
    exact h.symm
  have hseat'' : below c ((z'.piles p).faceUp) ≠ [] ∨
      ((z'.piles p).hidden = [] ∧ c.rank = Rank.king) := by
    rcases hseat' with h | h
    · exact Or.inl (by rwa [hpile])
    · exact Or.inr ⟨by rw [hpile]; exact h.1, h.2⟩
  exact freeCardS_of_data hhold'' hF' hseat'' (Or.inl hrun)

/-! ### §1.3 Cargo invariance and the step-level forms -/

/-- Cargo slides preserve the licence (same orbit, same rungs). -/
theorem canRaiseS_cargoPath_iff {z z' : State} (hz : z.WF) (hpath : CargoPath z z')
    {c : Card} : CanRaiseS z' c ↔ CanRaiseS z c := by
  have hz' : z'.WF := cargoPath_wf hz hpath
  constructor
  · intro h
    exact (canRaiseS_orbit_rung hz' (sameOrbitSetoid.iseqv.symm (sameOrbit_of_cargoPath hpath))
      (fun σ => (rungAt_cargoPath hpath σ).symm)).mp h
  · intro h
    exact (canRaiseS_orbit_rung hz (sameOrbit_of_cargoPath hpath)
      (rungAt_cargoPath hpath)).mp h

/-- **Same-rank, non-twin licensed step: the licence transfers both ways.** -/
theorem canRaiseS_rankEq_notTwin_step_iff {z z₀ z' : State} {a c : Card}
    (hz : z.WF) (hpath : CargoPath z z₀) (hcr : CanRaise z₀ a)
    (hstep : State.step z₀ (Move.tabToFound a) = some z')
    (hr : a.rank = c.rank) (hac : a ≠ c) (hat : a ≠ c.twin) :
    CanRaiseS z' c ↔ CanRaiseS z c := by
  have hz₀ : z₀.WF := cargoPath_wf hz hpath
  exact (canRaiseS_tabToFound_iff_of_rank_eq_notTwin hz₀ hstep hcr hr hac hat).trans
    (canRaiseS_cargoPath_iff hz hpath)

/-- **Same-rank twin licensed step, backward: the licence transfers back.** -/
theorem canRaiseS_rankEq_twin_step_bwd {z z₀ z' : State} {a c : Card}
    (hz : z.WF) (hpath : CargoPath z z₀) (hcr : CanRaise z₀ a)
    (hstep : State.step z₀ (Move.tabToFound a) = some z')
    (ht : a = c.twin) :
    CanRaiseS z' c → CanRaiseS z c := by
  have hz₀ : z₀.WF := cargoPath_wf hz hpath
  intro hc
  have h1 : CanRaiseS z₀ c :=
    canRaiseS_tabToFound_bwd_of_twin hz₀ hstep hcr ht hc
  exact (canRaiseS_cargoPath_iff hz hpath).mp h1

/-! ### §1.4 From the flat data to a vanilla raise -/

/-- **Exposed + S-licensed ⇒ vanilla-licensed.**  If nothing sits above `c` in its
pile, the flat licence is literally the vanilla licence. -/
theorem canRaise_of_canRaiseS_of_exposed {st : State} {c : Card} {p : Anchor}
    (hwf : st.WF) (hhold : st.pileHolding c = some p)
    (hexp : fromCard c ((st.piles p).faceUp) = [c])
    (hc : CanRaiseS st c) : CanRaise st c := by
  have hsplit := (canRaiseS_split hwf).mp hc
  have hnext := hsplit.1
  obtain ⟨-, hfree⟩ := hsplit
  obtain ⟨p', run, hhold', hF', hseat', hthird⟩ := freeCardS_unpack hfree
  have hp : p' = p := by rw [hhold] at hhold'; exact (Option.some.inj hhold').symm
  rw [hp] at hF' hseat'
  have hrun : run = [] := by
    rw [hexp] at hF'
    injection hF' with _ h
    exact h.symm
  subst hrun
  -- decompose the face-up list
  obtain ⟨bs, hbs⟩ := fromCard_singleton_decomp hexp
  have hnotmem : c ∉ bs := by
    intro hmem
    have hnodup : ((st.piles p).faceUp).Nodup := runOK_nodup (hwf.2.1 p)
    rw [hbs] at hnodup
    exact (List.nodup_append.mp hnodup).2.2 c hmem c (List.mem_singleton_self c) rfl
  have hchop : chop ((st.piles p).faceUp) = bs := by rw [hbs]; exact chop_append_singleton bs c
  have hbelow : below c ((st.piles p).faceUp) = bs := by
    rw [hbs]; exact below_append_singleton_of_not_mem hnotmem
  have htop : (st.piles p).top = some c := by
    show lastOf ((st.piles p).faceUp) = some c
    rw [hbs]; exact lastOf_snoc
  refine ⟨hnext, p, ?_, ?_⟩
  · exact (pileOfTop_eq_some_iff hwf).mpr htop
  · rw [hbelow] at hseat'
    rw [hchop]
    exact hseat'

/-! ### §1.5 Pile geometry of a twin raise -/

/-- The pile facts around a licensed raise of `c.twin`: `c` is in another pile,
that pile is unchanged, and `c` is off the raised pile. -/
theorem twinStep_piles {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (ht : a = c.twin) :
    ∃ a0, z.pileOfTop a = some a0 ∧
      c ∉ (z.piles a0).faceUp ∧ c ∉ (z'.piles a0).faceUp ∧
      (∀ a', a' ≠ a0 → z'.piles a' = z.piles a') ∧
      z'.pileHolding c = z.pileHolding c := by
  obtain ⟨-, a1, hpa1, hseat⟩ := hcr
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have ha10 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
  rw [ha10] at hseat
  have hwz' : z'.WF := step_wf hz hstep
  have hc0 : c ∉ (z.piles a0).faceUp := by
    apply not_mem_pileOfTop_of_rank_eq hz hpa0
    · rw [ht, Card.twin_rank]
    · intro h; exact (card_twin_ne_self c).symm (h.trans ht)
  have hc0' : c ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_ne hne]
      intro h; exact hc0 (mem_chop_of_mem_chop h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, Pile.afterRunRemoved_bare hhid]; simp
      · rw [afterRunRemoved_ne hch]
        intro h; exact hc0 (mem_chop_of_mem_chop h)
  have hagree : ∀ a', a' ≠ a0 → z'.piles a' = z.piles a' := by
    intro a' ha'
    rw [hpiles a', ite_eq_right ha']
  exact ⟨a0, hpa0, hc0, hc0', hagree,
    pileHolding_eq_of_agree hwz' hagree hc0 hc0'⟩

/-- **Exposure transfers backwards across a twin raise.**  If `c` is licensed
after `c.twin` is founded, then at the start `c` was already exposed (same pile,
nothing above it). -/
theorem exposed_bwd_of_twin_step {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound a) = some z')
    (hcr : CanRaise z a) (ht : a = c.twin) (hc : CanRaiseS z' c) :
    ∃ p, z.pileHolding c = some p ∧ fromCard c ((z.piles p).faceUp) = [c] := by
  have hwz' : z'.WF := step_wf hz hstep
  obtain ⟨-, hfree⟩ := (canRaiseS_split hwz').mp hc
  obtain ⟨p, run, hhold', hF, hseat', hthird⟩ := freeCardS_unpack hfree
  have hfound : a ∈ z'.found a.suit := by
    rw [found_tabToFound hstep a.suit, ite_eq_left rfl]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have htwinnone : z'.pileOfTop c.twin = none := by
    rw [← ht]
    exact pileOfTop_eq_none_of_found hwz' hfound
  have hexp' : fromCard c ((z'.piles p).faceUp) = [c] :=
    fromCard_nil_of_freeCardS_of_twin_none hhold' hfree htwinnone
  obtain ⟨a0, -, hc0, -, hagree, hph⟩ := twinStep_piles hz hstep hcr ht
  have hhold : z.pileHolding c = some p := by rw [← hph]; exact hhold'
  have hpne : p ≠ a0 := by
    intro h; subst h; exact hc0 (pileHolding_mem hhold)
  exact ⟨p, hhold, by rw [← hagree p hpne]; exact hexp'⟩

/-! ### §1.6 Vanilla persistence across a same-rank raise -/

/-- A vanilla licence of `a` survives a vanilla raise of a *different card of the
same rank*: the two cards are in different piles and the raised pile's removal
does not touch `a`'s. -/
theorem canRaise_of_raise_sameRank {z z' : State} {a c : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound c) = some z')
    (hr : a.rank = c.rank) (hac : a ≠ c) (ha : CanRaise z a) :
    CanRaise z' a := by
  have hwz' : z'.WF := step_wf hz hstep
  obtain ⟨hnext, pa, hpa, hseat⟩ := ha
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have hsu : a.suit ≠ c.suit := by
    intro h
    exact hac (card_eq_of_suit_rank (c := c) (c' := a) h (by rw [hr]))
  have hnext' : z'.nextUp a = true := by
    rw [nextUp_raise_ne hstep hsu]
    exact hnext
  have hae : a ∉ (z.piles a0).faceUp :=
    not_mem_pileOfTop_of_rank_eq hz hpa0 hr hac
  have hpane : pa ≠ a0 := by
    intro h
    subst h
    exact hae (Pile.mem_of_top (pileOfTop_top hpa).2)
  have hpile : z'.piles pa = z.piles pa := by
    rw [hpiles pa, ite_eq_right hpane]
  refine ⟨hnext', pa, ?_, ?_⟩
  · have htop : (z'.piles pa).top = some a := by
      rw [hpile]
      exact (pileOfTop_top hpa).2
    exact (pileOfTop_eq_some_iff hwz').mpr htop
  · rw [hpile]
    exact hseat

/-! ## §2. Equal-rank adjacent transposition in a play -/

/-- **Ascending** (non-decreasing by rank). -/
def Asc (P : List Card) : Prop :=
  P.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx)

theorem asc_nil : Asc [] := List.Pairwise.nil

theorem asc_tail {a : Card} {l : List Card} (h : Asc (a :: l)) : Asc l :=
  (List.pairwise_cons.mp h).2

/-- In an ascending list the head is below every member. -/
theorem asc_head_le_all : ∀ {l : List Card} {a : Card}, Asc (a :: l) →
    ∀ x ∈ a :: l, a.rank.toIdx ≤ x.rank.toIdx
  | [], a, h, x, hx => by
      rw [List.mem_singleton] at hx
      subst hx
      omega
  | b :: t, a, h, x, hx => by
      have hab : a.rank.toIdx ≤ b.rank.toIdx :=
        (List.pairwise_cons.mp h).1 b (List.mem_cons_self ..)
      have ht : Asc (b :: t) := (List.pairwise_cons.mp h).2
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · have := asc_head_le_all ht x hx'
        omega

/-- In an ascending list, a member of a prefix is below the element that follows
the prefix. -/
theorem asc_le_of_mem_append : ∀ {X Y : List Card} {b : Card}, Asc (X ++ b :: Y) →
    ∀ x ∈ X, x.rank.toIdx ≤ b.rank.toIdx
  | [], Y, b, h, x, hx => absurd hx List.not_mem_nil
  | x :: X', Y, b, h, y, hy => by
      have hxb : x.rank.toIdx ≤ b.rank.toIdx :=
        (List.pairwise_cons.mp h).1 b (by simp)
      have htail : Asc (X' ++ b :: Y) := (List.pairwise_cons.mp h).2
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hxb
      · exact asc_le_of_mem_append htail y hy'

/-- **Tie swap.**  Two adjacent raises of the *same rank* in a licensed play can
be performed in the other order (with the rest of the play replayed).

The non-twin case is the flat licence transfer of §1.3.  In the twin case we
un-raise the twin to expose `c` at the vanilla witness `z₀` of the first step;
there both raises are vanilla, so `twin_raise_square` commutes them exactly. -/
theorem tie_swap {u z : State} {a c : Card} {T : List Card}
    (hu : u.WF) (h : RaiseSSeqL u (playWord (a :: c :: T)) z)
    (hr : a.rank = c.rank) (hac : a ≠ c) :
    ∃ z', RaiseSSeqL u (playWord (c :: a :: T)) z' := by
  obtain ⟨u_ac, h_old, hT⟩ := RaiseSSeqL.split_chron (A := [a, c]) (R := T) h
  obtain ⟨u_a, h_a, h_c⟩ := RaiseSSeqL.split_chron (A := [a]) (R := [c]) h_old
  have hc_ua : CanRaiseS u_a c := canRaiseS_of_raiseSSeqL_head h_c
  have ha_u : CanRaiseS u a := canRaiseS_of_raiseSSeqL_head h_a
  obtain ⟨w0, z₀, hnil, hpath, hcr, hstep⟩ := RaiseSSeqL.step_s h_a
  cases hnil
  have hz₀ : z₀.WF := cargoPath_wf hu hpath
  have hperm : ([a, c] : List Card).Perm [c, a] := by
    simpa using (List.Perm.swap c a ([] : List Card))
  by_cases hat : a = c.twin
  · -- the twin case
    have hc_z₀ : CanRaiseS z₀ c :=
      canRaiseS_tabToFound_bwd_of_twin hz₀ hstep hcr hat hc_ua
    obtain ⟨p, hhold, hexp⟩ := exposed_bwd_of_twin_step hz₀ hstep hcr hat hc_ua
    have hcvan : CanRaise z₀ c :=
      canRaise_of_canRaiseS_of_exposed hz₀ hhold hexp hc_z₀
    obtain ⟨v, hstep_c⟩ := step_tabToFound_of_canRaise hcvan
    have hsu : c.suit ≠ a.suit := suit_ne_of_twin hat
    obtain ⟨w', hstep_v_a, -⟩ := twin_raise_square hz₀ hsu hstep_c hstep
    have ha_v : CanRaise v a := canRaise_of_raise_sameRank hz₀ hstep_c hr hac hcr
    have hNew : RaiseSSeqL u (playWord [c, a]) w' := by
      have h1 : RaiseSSeqL u (playWord [c]) v :=
        RaiseSSeqL.cons (RaiseSSeqL.nil u) hpath hcvan hstep_c
      have h2 : RaiseSSeqL v (playWord [a]) w' :=
        RaiseSSeqL.cons (RaiseSSeqL.nil v) (Steps.refl v) ha_v hstep_v_a
      simpa [playWord] using RaiseSSeqL.append h1 h2
    obtain ⟨z', hz'⟩ := RaiseSSeqL.tail_transport hu h_old hNew hperm hT
    exact ⟨z', by simpa [playWord] using RaiseSSeqL.append hNew hz'⟩
  · -- the non-twin case
    have hc_u : CanRaiseS u c :=
      (canRaiseS_rankEq_notTwin_step_iff hu hpath hcr hstep hr hac hat).mp hc_ua
    obtain ⟨u_c, h_c'⟩ := raiseSSeqL_step_of_canRaiseS hc_u
    obtain ⟨w1, z1, hnil2, hpath2, hcr2, hstep2⟩ := RaiseSSeqL.step_s h_c'
    cases hnil2
    have hat2 : c ≠ a.twin := by
      intro hcon
      exact hat (by rw [hcon, card_twin_twin])
    have hc2 : CanRaiseS u_c a :=
      (canRaiseS_rankEq_notTwin_step_iff hu hpath2 hcr2 hstep2 hr.symm
        (Ne.symm hac) hat2).mpr ha_u
    obtain ⟨u_ca, h_a'⟩ := raiseSSeqL_step_of_canRaiseS hc2
    have hNew : RaiseSSeqL u (playWord [c, a]) u_ca := by
      simpa [playWord] using RaiseSSeqL.append h_c' h_a'
    obtain ⟨z', hz'⟩ := RaiseSSeqL.tail_transport hu h_old hNew hperm hT
    exact ⟨z', by simpa [playWord] using RaiseSSeqL.append hNew hz'⟩

/-! ## §3. Passing a strictly lower-rank card -/

/-- **Ascending swap.**  A licensed play beginning `y, c` with `y` strictly
lower-ranked can be rearranged to begin `c, y`, provided `c` is licensed at the
start: `y`'s licence survives `c`'s raise by inertness. -/
theorem asc_swap {u z : State} {y c : Card} {T : List Card}
    (hu : u.WF) (h : RaiseSSeqL u (playWord (y :: c :: T)) z)
    (hr : y.rank.toIdx < c.rank.toIdx) (hc : CanRaiseS u c) :
    ∃ z', RaiseSSeqL u (playWord (c :: y :: T)) z' := by
  obtain ⟨u_yc, h_old, hT⟩ := RaiseSSeqL.split_chron (A := [y, c]) (R := T) h
  obtain ⟨u_y, h_y, h_c⟩ := RaiseSSeqL.split_chron (A := [y]) (R := [c]) h_old
  have hy_u : CanRaiseS u y := canRaiseS_of_raiseSSeqL_head h_y
  obtain ⟨u_c, h_c'⟩ := raiseSSeqL_step_of_canRaiseS hc
  obtain ⟨w1, z1, hnil2, hpath2, hcr2, hstep2⟩ := RaiseSSeqL.step_s h_c'
  cases hnil2
  have hy_uc : CanRaiseS u_c y :=
    (canRaiseS_inert_of_canRaiseStep hu hpath2 hcr2 hstep2 hr).mpr hy_u
  obtain ⟨u_cy, h_y'⟩ := raiseSSeqL_step_of_canRaiseS hy_uc
  have hNew : RaiseSSeqL u (playWord [c, y]) u_cy := by
    simpa [playWord] using RaiseSSeqL.append h_c' h_y'
  have hperm : ([y, c] : List Card).Perm [c, y] := by
    simpa using (List.Perm.swap c y ([] : List Card))
  obtain ⟨z', hz'⟩ := RaiseSSeqL.tail_transport hu h_old hNew hperm hT
  exact ⟨z', by simpa [playWord] using RaiseSSeqL.append hNew hz'⟩

/-! ## §4. Moving the front card through a prefix -/

/-- Move `c` to the front of a same-rank block `B` that precedes it. -/
theorem bubble_tie (B : List Card) :
    ∀ {u z : State} {c : Card} {T : List Card},
      u.WF → c ∉ B → (∀ b ∈ B, b.rank = c.rank) →
      RaiseSSeqL u (playWord (B ++ c :: T)) z →
      ∃ z', RaiseSSeqL u (playWord (c :: B ++ T)) z' := by
  induction B with
  | nil =>
      intro u z c T hu _ _ h
      exact ⟨z, by simpa using h⟩
  | cons b B ih =>
      intro u z c T hu hcB hB h
      have hcb : b ≠ c := by
        intro hcon; exact hcB (by rw [hcon]; exact List.mem_cons_self ..)
      have hcB' : c ∉ B := fun hmem => hcB (List.mem_cons_of_mem _ hmem)
      have hb : b.rank = c.rank := hB b (List.mem_cons_self ..)
      have hB' : ∀ b' ∈ B, b'.rank = c.rank :=
        fun b' hb' => hB b' (List.mem_cons_of_mem _ hb')
      obtain ⟨u_b, h_b, hrest⟩ :=
        RaiseSSeqL.split_chron (A := [b]) (R := B ++ c :: T) (by simpa using h)
      obtain ⟨z₁, hz₁⟩ := ih (u := u_b) (z := z) (c := c) (T := T)
        (RaiseSSeqL.wf h_b hu) hcB' hB' hrest
      have hplay : RaiseSSeqL u (playWord (b :: c :: (B ++ T))) z₁ := by
        have h1 := RaiseSSeqL.append h_b hz₁
        simpa [playWord, List.append_assoc] using h1
      obtain ⟨z', hz'⟩ := tie_swap hu hplay hb hcb
      exact ⟨z', by simpa [playWord, List.append_assoc] using hz'⟩

/-- **Bubble the front card.**  In an ascending play whose prefix `A` has ranks
at most `c.rank`, the card `c` can be raised first (and the rest replayed). -/
theorem bubble_front (A : List Card) :
    ∀ {u z : State} {c : Card} {T : List Card},
      u.WF → Asc A → c ∉ A → (∀ a ∈ A, a.rank.toIdx ≤ c.rank.toIdx) → CanRaiseS u c →
      RaiseSSeqL u (playWord (A ++ c :: T)) z →
      ∃ z', RaiseSSeqL u (playWord (c :: A ++ T)) z' := by
  induction A with
  | nil =>
      intro u z c T hu _ _ _ _ h
      exact ⟨z, by simpa using h⟩
  | cons a A ih =>
      intro u z c T hu hAsc hcA hA hc h
      have hal : a.rank.toIdx ≤ c.rank.toIdx := hA a (List.mem_cons_self ..)
      by_cases hlt : a.rank.toIdx < c.rank.toIdx
      · obtain ⟨u_a, h_a, hrest⟩ :=
          RaiseSSeqL.split_chron (A := [a]) (R := A ++ c :: T) (by simpa using h)
        have hAsc' : Asc A := asc_tail hAsc
        have hcA' : c ∉ A := fun hmem => hcA (List.mem_cons_of_mem _ hmem)
        have hA' : ∀ a' ∈ A, a'.rank.toIdx ≤ c.rank.toIdx :=
          fun a' ha' => hA a' (List.mem_cons_of_mem _ ha')
        obtain ⟨w0, z₀, hnil, hpath, hcr, hstep⟩ := RaiseSSeqL.step_s h_a
        cases hnil
        have hc_a : CanRaiseS u_a c :=
          canRaiseS_step_of_rank_ne hu ⟨z₀, hpath, hstep⟩
            (fun hcon => by rw [hcon] at hlt; omega) hc
        obtain ⟨z₁, hz₁⟩ := ih (u := u_a) (z := z) (c := c) (T := T)
          (RaiseSSeqL.wf h_a hu) hAsc' hcA' hA' hc_a hrest
        have hplay : RaiseSSeqL u (playWord (a :: c :: (A ++ T))) z₁ := by
          have h1 := RaiseSSeqL.append h_a hz₁
          simpa [playWord, List.append_assoc] using h1
        obtain ⟨z', hz'⟩ := asc_swap hu hplay hlt hc
        exact ⟨z', by simpa [playWord, List.append_assoc] using hz'⟩
      · -- the whole prefix is the equal-rank block
        have hae : a.rank = c.rank :=
          Rank.toIdx_inj (by omega)
        have hAll : ∀ b ∈ a :: A, b.rank = c.rank := by
          intro b hb
          have h1 : a.rank.toIdx ≤ b.rank.toIdx := asc_head_le_all hAsc b hb
          have h2 : b.rank.toIdx ≤ c.rank.toIdx := hA b hb
          have h3 : a.rank.toIdx = c.rank.toIdx := by rw [hae]
          exact Rank.toIdx_inj (by omega)
        exact bubble_tie (a :: A) hu hcA hAll h

/-! ## §5. Ascending-list kit -/

/-- A prefix of an ascending list is ascending. -/
theorem asc_append_left {l m : List Card} (h : Asc (l ++ m)) : Asc l := by
  induction l with
  | nil => exact asc_nil
  | cons x t ih =>
      rw [List.cons_append] at h
      obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
      refine List.pairwise_cons.mpr ⟨?_, ih ht⟩
      intro z hz
      exact hx z (List.mem_append_left m hz)

/-- Erasing a card from an ascending list leaves it ascending. -/
theorem asc_erase : ∀ {l : List Card} {x : Card}, Asc l → Asc (l.erase x)
  | [], x, h => List.Pairwise.nil
  | a :: t, x, h => by
      by_cases ha : a = x
      · subst ha
        rw [List.erase_cons_head]
        exact asc_tail h
      · rw [List.erase_cons_tail (by simp [ha])]
        obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
        refine List.pairwise_cons.mpr ⟨?_, asc_erase ht⟩
        intro z hz
        exact hx z (List.mem_of_mem_erase hz)

/-- Removing an element from the middle of an ascending list keeps it ascending. -/
theorem asc_erase_append {X Y : List Card} {b : Card} (h : Asc (X ++ b :: Y)) :
    Asc (X ++ Y) := by
  induction X with
  | nil => exact asc_tail h
  | cons x X' ih =>
      rw [List.cons_append] at h
      obtain ⟨hx, htail⟩ := List.pairwise_cons.mp h
      refine List.pairwise_cons.mpr ⟨?_, ih htail⟩
      intro z hz
      rcases List.mem_append.mp hz with h1 | h2
      · exact hx z (List.mem_append_left _ h1)
      · exact hx z (List.mem_append_right _ (List.mem_cons_of_mem _ h2))

/-! ## §6. The rank sort -/

theorem mem_insRank : ∀ (a : Card) (L : List Card) (z : Card),
    z ∈ insRank a L ↔ z = a ∨ z ∈ L
  | a, [], z => by simp [insRank]
  | a, b :: t, z => by
      have hins : insRank a (b :: t) =
          if a.rank.toIdx ≤ b.rank.toIdx then a :: b :: t else b :: insRank a t := rfl
      rw [hins]
      by_cases h : a.rank.toIdx ≤ b.rank.toIdx
      · rw [ite_eq_left h]
        simp
      · rw [ite_eq_right h]
        simp only [List.mem_cons, mem_insRank a t z]
        constructor
        · rintro (rfl | rfl | hz)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hz)
        · rintro (rfl | rfl | hz)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hz)

theorem insRank_perm (a : Card) : ∀ (L : List Card), (insRank a L).Perm (a :: L)
  | [] => by simp [insRank]
  | b :: t => by
      have hins : insRank a (b :: t) =
          if a.rank.toIdx ≤ b.rank.toIdx then a :: b :: t else b :: insRank a t := rfl
      rw [hins]
      by_cases h : a.rank.toIdx ≤ b.rank.toIdx
      · rw [ite_eq_left h]
      · rw [ite_eq_right h]
        exact ((insRank_perm a t).cons b).trans (List.Perm.swap b a t).symm

theorem insRank_asc {a : Card} : ∀ {L : List Card}, Asc L → Asc (insRank a L)
  | [], _ => by
      show Asc [a]
      exact List.pairwise_cons.mpr ⟨by simp, List.Pairwise.nil⟩
  | b :: t, h => by
      obtain ⟨hb, ht⟩ := List.pairwise_cons.mp h
      have hins : insRank a (b :: t) =
          if a.rank.toIdx ≤ b.rank.toIdx then a :: b :: t else b :: insRank a t := rfl
      rw [hins]
      by_cases hab : a.rank.toIdx ≤ b.rank.toIdx
      · rw [ite_eq_left hab]
        refine List.pairwise_cons.mpr ⟨?_, h⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact hab
        · exact Nat.le_trans hab (hb z hz')
      · rw [ite_eq_right hab]
        have hba : b.rank.toIdx ≤ a.rank.toIdx := by omega
        refine List.pairwise_cons.mpr ⟨?_, insRank_asc ht⟩
        intro z hz
        rcases (mem_insRank a t z).mp hz with rfl | hz'
        · exact hba
        · exact hb z hz'

theorem sortRank_perm : ∀ (P : List Card), (sortRank P).Perm P
  | [] => List.Perm.nil
  | a :: t => (insRank_perm a (sortRank t)).trans ((sortRank_perm t).cons a)

theorem sortRank_asc : ∀ (P : List Card), Asc (sortRank P)
  | [] => List.Pairwise.nil
  | a :: t => insRank_asc (sortRank_asc t)

/-- A list is a permutation of its reversal. -/
theorem reverse_perm : ∀ (l : List Card), l.reverse.Perm l
  | [] => List.Perm.nil
  | a :: t => by
      rw [List.reverse_cons]
      refine ((reverse_perm t).append_right [a]).trans ?_
      induction t with
      | nil => exact List.Perm.refl _
      | cons y t ih =>
          have h1 : (y :: t ++ [a]).Perm (y :: (t ++ [a])) := List.Perm.refl _
          exact h1.trans ((ih.cons y).trans (List.Perm.swap y a t).symm)

/-! ## §7. Any two ascending orders of a multiset are interchangeable -/

/-- Erasing the same card from two permutations gives permutations
(constructive replacement for the core `List.Perm.erase`, which is
`Classical.choice`-tainted). -/
theorem perm_erase {l₁ l₂ : List Card} {x : Card} (h : l₁.Perm l₂) :
    (l₁.erase x).Perm (l₂.erase x) := by
  induction h with
  | nil => exact List.Perm.nil
  | cons a h ih =>
      by_cases hax : (a == x) = true
      · have hae : a = x := beq_iff_eq.mp hax
        subst hae
        rw [List.erase_cons_head, List.erase_cons_head]
        exact h
      · rw [List.erase_cons_tail hax, List.erase_cons_tail hax]
        exact ih.cons a
  | swap a b l =>
      by_cases hb : b = x
      · rw [hb]
        by_cases ha : a = x
        · have e1 : (x :: a :: l).erase x = a :: l := List.erase_cons_head x (a :: l)
          have e2 : (a :: x :: l).erase x = a :: l := by
            rw [ha]
            exact List.erase_cons_head x (x :: l)
          rw [e1, e2]
        · have hne : ¬((a == x) = true) := by simp [beq_iff_eq, ha]
          have e1 : (x :: a :: l).erase x = a :: l := List.erase_cons_head x (a :: l)
          have e2 : (a :: x :: l).erase x = a :: l := by
            rw [List.erase_cons_tail hne, List.erase_cons_head]
          rw [e1, e2]
      · have hneb : ¬((b == x) = true) := by simp [beq_iff_eq, hb]
        by_cases ha : a = x
        · rw [ha]
          have e1 : (b :: x :: l).erase x = b :: l := by
            rw [List.erase_cons_tail hneb, List.erase_cons_head]
          have e2 : (x :: b :: l).erase x = b :: l := List.erase_cons_head x (b :: l)
          rw [e1, e2]
        · have hnea : ¬((a == x) = true) := by simp [beq_iff_eq, ha]
          have e1 : (b :: a :: l).erase x = b :: a :: l.erase x := by
            rw [List.erase_cons_tail hneb, List.erase_cons_tail hnea]
          have e2 : (a :: b :: l).erase x = a :: b :: l.erase x := by
            rw [List.erase_cons_tail hnea, List.erase_cons_tail hneb]
          rw [e1, e2]
          exact List.Perm.swap a b (l.erase x)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem tieFree_aux (n : Nat) : ∀ (A : List Card), A.length ≤ n →
    ∀ {u z : State} {B : List Card}, u.WF → Asc A → Asc B → A.Perm B →
      RaiseSSeqL u (playWord A) z → ∃ z', RaiseSSeqL u (playWord B) z' := by
  induction n with
  | zero =>
      intro A hlen u z B hu hA hB hperm hplay
      cases A with
      | nil =>
          cases B with
          | nil => exact ⟨z, by simpa using hplay⟩
          | cons b B' => exact absurd hperm (by simp)
      | cons a A' => simp at hlen
  | succ n ih =>
      intro A hlen u z B hu hA hB hperm hplay
      cases A with
      | nil =>
          cases B with
          | nil => exact ⟨z, by simpa using hplay⟩
          | cons b B' => exact absurd hperm (by simp)
      | cons a A' =>
          cases B with
          | nil => exact absurd hperm (by simp)
          | cons b B' =>
              have hbA : b ∈ a :: A' := hperm.mem_iff.mpr (List.mem_cons_self ..)
              obtain ⟨X, Y, hXY, hbX⟩ := exists_append_cons_of_mem hbA
              have hAscX : Asc (X ++ b :: Y) := by rw [← hXY]; exact hA
              have hb_le_a : b.rank.toIdx ≤ a.rank.toIdx :=
                asc_head_le_all hB a (hperm.mem_iff.mp (List.mem_cons_self ..))
              have hXr : ∀ x ∈ X, x.rank = b.rank := by
                intro x hx
                have h1 : x.rank.toIdx ≤ b.rank.toIdx := asc_le_of_mem_append hAscX x hx
                have h2 : a.rank.toIdx ≤ x.rank.toIdx :=
                  asc_head_le_all hA x (by rw [hXY]; exact List.mem_append_left _ hx)
                exact Rank.toIdx_inj (by omega)
              have hplayX : RaiseSSeqL u (playWord (X ++ b :: Y)) z := by
                rw [← hXY]; exact hplay
              obtain ⟨z₁, hz₁⟩ := bubble_tie X hu hbX hXr hplayX
              obtain ⟨u_b, h_b, hrest⟩ :=
                RaiseSSeqL.split_chron (A := [b]) (R := X ++ Y) (by simpa using hz₁)
              have hAscXY : Asc (X ++ Y) := asc_erase_append hAscX
              have hpermXY : B'.Perm (X ++ Y) := by
                have hp' : (b :: B').Perm (X ++ b :: Y) := by rw [← hXY]; exact hperm.symm
                have h1 : ((b :: B').erase b).Perm ((X ++ b :: Y).erase b) := perm_erase (x := b) hp'
                rwa [List.erase_cons_head, erase_append_cons_of_not_mem hbX] at h1
              have hlenXY : (X ++ Y).length ≤ n := by
                have h1 : (X ++ b :: Y).length = (a :: A').length := by rw [← hXY]
                have hlen' : A'.length ≤ n := by
                  simp only [List.length_cons] at hlen
                  omega
                simp only [List.length_append, List.length_cons] at h1 ⊢
                omega
              obtain ⟨z₂, hz₂⟩ := ih (X ++ Y) hlenXY (u := u_b) (z := z₁) (B := B')
                (RaiseSSeqL.wf h_b hu) hAscXY (asc_tail hB) hpermXY.symm hrest
              refine ⟨z₂, ?_⟩
              have hfin := RaiseSSeqL.append h_b hz₂
              simpa [playWord] using hfin

/-- **Tie freedom.**  Any two ascending orders of the same multiset are
interchangeable as licensed plays. -/
theorem tieFree {u z : State} {A B : List Card}
    (hu : u.WF) (hA : Asc A) (hB : Asc B) (hperm : A.Perm B)
    (hplay : RaiseSSeqL u (playWord A) z) :
    ∃ z', RaiseSSeqL u (playWord B) z' :=
  tieFree_aux A.length A (Nat.le_refl _) hu hA hB hperm hplay

/-! ## §8. Tail existence -/

/-- **`TailExists`** — the last residual of the rank-front lane. -/
theorem tail_exists : TailExists := by
  intro s z ws c hs hc hplay hmem
  have hplay' : RaiseSSeqL s (playWord ws.reverse) z := by simpa [playWord] using hplay
  obtain ⟨z₁, hz₁⟩ := sortable (P := ws.reverse) hs hplay'
  have hc_mem : c ∈ sortRank ws.reverse :=
    (sortRank_perm ws.reverse).mem_iff.mpr (by simpa using hmem)
  obtain ⟨A, B, hAB, hcA⟩ := exists_append_cons_of_mem hc_mem
  have hAsc : Asc (sortRank ws.reverse) := sortRank_asc _
  have hAscA : Asc A := by rw [hAB] at hAsc; exact asc_append_left hAsc
  have hAle : ∀ a ∈ A, a.rank.toIdx ≤ c.rank.toIdx := by
    rw [hAB] at hAsc
    exact fun a ha => asc_le_of_mem_append hAsc a ha
  have hplayA : RaiseSSeqL s (playWord (A ++ c :: B)) z₁ := by rw [← hAB]; exact hz₁
  obtain ⟨z₂, hz₂⟩ := bubble_front A hs hAscA hcA hAle hc hplayA
  obtain ⟨s₁, h_c, hrest⟩ :=
    RaiseSSeqL.split_chron (A := [c]) (R := A ++ B)
      (by simpa [playWord, List.append_assoc] using hz₂)
  refine ⟨s₁, h_c, ?_⟩
  have hs₁ : s₁.WF := RaiseSSeqL.wf h_c hs
  have hAscAB : Asc (A ++ B) := by
    have h1 : A ++ B = (sortRank ws.reverse).erase c := by
      rw [hAB, erase_append_cons_of_not_mem hcA]
    rw [h1]
    exact asc_erase hAsc
  have hpermAB : (A ++ B).Perm (sortRank (ws.erase c)) := by
    have h1 : A ++ B = (sortRank ws.reverse).erase c := by
      rw [hAB, erase_append_cons_of_not_mem hcA]
    rw [h1]
    have e1 : ((sortRank ws.reverse).erase c).Perm ((ws.reverse).erase c) :=
      perm_erase (sortRank_perm ws.reverse)
    have e2 : ((ws.reverse).erase c).Perm (ws.erase c) := perm_erase (reverse_perm ws)
    have e3 : (ws.erase c).Perm ((ws.erase c).reverse) := (reverse_perm (ws.erase c)).symm
    have e4 : ((ws.erase c).reverse).Perm (sortRank (ws.erase c)) :=
      (reverse_perm (ws.erase c)).trans (sortRank_perm (ws.erase c)).symm
    exact e1.trans (e2.trans (e3.trans e4))
  obtain ⟨z₃, hz₃⟩ := tieFree hs₁ hAscAB (sortRank_asc (ws.erase c)) hpermAB hrest
  exact ⟨z₃, hz₃⟩

/-- **The rank-front theorem** (licensed grade), from `TailExists`. -/
theorem raiseS_rankfront_L {s z : State} {c : Card} {ws : List Card}
    (hs : s.WF) (hc : CanRaiseS s c) (hplay : RaiseSSeqL s ws z) (hmem : c ∈ ws) :
    ∃ z', RaiseSSeqL s (rankFront c ws) z' :=
  raiseS_rankfront_L_of_tail tail_exists hs hc hplay hmem

end OneColourClosure

#print axioms OneColourClosure.fromCard_singleton_decomp
#print axioms OneColourClosure.freeCardS_unpack
#print axioms OneColourClosure.canRaiseS_tabToFound_iff_of_rank_eq_notTwin
#print axioms OneColourClosure.canRaiseS_tabToFound_bwd_of_twin
#print axioms OneColourClosure.canRaiseS_rankEq_notTwin_step_iff
#print axioms OneColourClosure.canRaiseS_rankEq_twin_step_bwd
#print axioms OneColourClosure.canRaise_of_canRaiseS_of_exposed
#print axioms OneColourClosure.exposed_bwd_of_twin_step
#print axioms OneColourClosure.canRaise_of_raise_sameRank
#print axioms OneColourClosure.tie_swap
#print axioms OneColourClosure.asc_swap
#print axioms OneColourClosure.bubble_tie
#print axioms OneColourClosure.bubble_front
#print axioms OneColourClosure.asc_erase
#print axioms OneColourClosure.asc_erase_append
#print axioms OneColourClosure.insRank_perm
#print axioms OneColourClosure.insRank_asc
#print axioms OneColourClosure.sortRank_perm
#print axioms OneColourClosure.sortRank_asc
#print axioms OneColourClosure.reverse_perm
#print axioms OneColourClosure.tieFree
#print axioms OneColourClosure.tail_exists
#print axioms OneColourClosure.raiseS_rankfront_L
#print axioms OneColourClosure.chop_append_singleton
#print axioms OneColourClosure.below_append_singleton_of_not_mem
#print axioms OneColourClosure.fromCard_append_singleton_of_not_mem
#print axioms OneColourClosure.card_twin_ne_self
#print axioms OneColourClosure.suit_ne_of_twin
#print axioms OneColourClosure.not_mem_pileOfTop_of_rank_eq
#print axioms OneColourClosure.not_mem_pileOfTop_twin_of_rank_eq
#print axioms OneColourClosure.freeCardS_of_data
#print axioms OneColourClosure.freeCardS_tabToFound_eq_of_rank_eq_notTwin
#print axioms OneColourClosure.fromCard_nil_of_freeCardS_of_twin_none
#print axioms OneColourClosure.freeCardS_tabToFound_bwd_of_twin
#print axioms OneColourClosure.freeCardS_tabToFound_fwd_of_twin
#print axioms OneColourClosure.canRaiseS_cargoPath_iff
#print axioms OneColourClosure.twinStep_piles
#print axioms OneColourClosure.asc_nil
#print axioms OneColourClosure.asc_tail
#print axioms OneColourClosure.asc_head_le_all
#print axioms OneColourClosure.asc_le_of_mem_append
#print axioms OneColourClosure.asc_append_left
#print axioms OneColourClosure.mem_insRank
#print axioms OneColourClosure.perm_erase
#print axioms OneColourClosure.tieFree_aux

#check OneColourClosure.tail_exists
#check OneColourClosure.raiseS_rankfront_L

