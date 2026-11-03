import Temp.RankFront_proof

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Rank-front — the final attempt

This file formalises the *rows* of the parent's argument and states the exact
residual.  It does **not** close `raiseS_rankfront`; what it does close is
recorded below and at the battery.

## Convention

`RaiseSSeq`'s head is the **last** raise.  A *play* `P = [σ₁, …, σₙ]` (σ₁ raised
first) is the word `P.reverse`; `Real s P = ∃ z, RaiseSSeq s P.reverse z`.
`rankFront c ws = (sortRank (ws.erase c)).reverse ++ [c]` is the word whose play
is `c :: sortRank (ws.erase c)` (`Temp/RankFront_proof.lean`).

## Plumbing (route (a))

`RaiseSSeq` steps are `State.step` only (`nextUp` + `pileOfTop`), so a play's
step need not be `CanRaise`; the witness is kernel-checked in
`Temp/RankFront_proof.lean` (`t4a_fires` + `t4a_not_canRaise`: a *commit* raise
that flips a hidden card).  I therefore state the theorem for **licensed** plays
(all cards `CanRaiseS` at the start); no bridge from bare steps to `CanRaise`
exists, so route (b) is impossible, not merely inconvenient.

## Rows

* **R1** (discharged, `Temp/RankFront_proof.lean`):
  `canRaiseS_step_of_rank_ne` / `canRaiseS_persist_of_rank_ne` — a raise of
  strictly different rank preserves `c`'s licence (both `specShift_sem_fwd`
  side conditions are automatic since twins share rank).
* **R2** (discharged here): `above_rank_lt` — a card above another in a face-up
  run has strictly lower rank (`runOK` descends going up).  With
  `cover_rank_lt` this is the "ascending clears covers first" primitive.
* **R3** (partly discharged here):
  * `seat_possibilities` — a card seated on `t` can only ever sit on `t` or
    `t.twin` (`cover_seats` re-arranged);
  * `no_canPlace_of_seated` — while the cover `x` sits on `t` and `t.twin` is
    founded, `x` has **no legal placement** anywhere (its two seats are
    `t` = not a top, and `t.twin` = founded);
  * `twin_covered_persists` — hence in the whole cargo class of `w`, `t` is
    **never a pile top**; and `step_none_of_twin_covered`: `t` can never be
    raised there.
  The remaining half of R3 ("therefore a play that raises `t` must also raise
  `x`") is the play-level induction, stated as `CoverMustBeRaised` below and
  **not** proved.
-/

namespace OneColourClosure

/-! ## §1. R2 — a card above another has strictly lower rank -/

/-- **The R2 primitive.**  In a legal face-up run, a card that appears *after*
`y` (i.e. above `y`) has strictly lower rank than `y`. -/
theorem above_rank_lt {l : List Card} (h : runOK l = true) :
    ∀ (B : List Card) (A : List Card) (y x : Card),
      l = A ++ y :: B → x ∈ B → x.rank.toIdx < y.rank.toIdx := by
  intro B
  induction B with
  | nil => intro A y x _ hx; exact absurd hx List.not_mem_nil
  | cons z B' ih =>
      intro A y x hl hx
      have hzy : canSitOn z y = true :=
        SeedKit.runOK_adjacent_fit y z A B' (by rw [← hl]; exact h)
      have hzlt : z.rank.toIdx < y.rank.toIdx := cover_rank_lt hzy
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hzlt
      · have hl' : l = (A ++ [y]) ++ z :: B' := by rw [hl]; simp [List.append_assoc]
        have := ih (A ++ [y]) z x hl' hx'
        omega

/-- The same fact read on a pile: a face-up card above another in the same pile
has strictly lower rank. -/
theorem above_rank_lt_of_pile {st : State} (hwf : st.WF) {a : Anchor} {y x : Card}
    {A B : List Card} (hl : (st.piles a).faceUp = A ++ y :: B) (hx : x ∈ B) :
    x.rank.toIdx < y.rank.toIdx :=
  above_rank_lt (hwf.2.1 a) B A y x hl hx

/-! ## §2. R3 — the cover of a twin can never be slid away -/

/-- **The seats of a card that sits on `t`**: only `t` and `t.twin`. -/
theorem seat_possibilities {x t y : Card} (hxt : canSitOn x t = true)
    (hy : canSitOn x y = true) : y = t ∨ y = t.twin := by
  have hc : canSitOn x t.twin.twin = true := by rw [card_twin_twin]; exact hxt
  have h := cover_seats (c := t.twin) (x := x) (y := y) hc hy
  rw [card_twin_twin] at h
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **`x` cannot be placed anywhere** while it sits on `t` and `t.twin` is
founded: its only two seats are `t` (not a pile top — `x` is on it) and
`t.twin` (founded, hence not a pile top). -/
theorem no_canPlace_of_seated {w : State} (hwf : w.WF) {x t : Card}
    (hseat : seatOf w x = some (Sum.inr t))
    (hfound : t.twin ∈ w.found t.twin.suit) :
    ∀ b : Base, w.canPlace x b = false := by
  intro b
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hfit : canSitOn x t = true := (tfc_seat_parent hwf hhold hlast).1
  have hxking : x.rank ≠ Rank.king := tfc_seatOf_inr_rank_ne_king hwf hseat
  cases b with
  | inl a' => simp [State.canPlace, hxking]
  | inr y =>
      cases hpt : w.pileOfTop y with
      | none => simp [State.canPlace, hpt]
      | some k =>
          have hnots : canSitOn x y = false := by
            by_cases hxy : canSitOn x y = true
            · rcases seat_possibilities hfit hxy with h | h
              · rw [h] at hpt
                exact absurd hpt (by rw [no_top_of_seat hwf hseat]; simp)
              · rw [h] at hpt
                exact absurd hpt (by rw [pileOfTop_eq_none_of_found hwf hfound]; simp)
            · cases hcan : canSitOn x y with
              | false => rfl
              | true => exact absurd hcan hxy
          simp only [State.canPlace, hpt]
          exact hnots

/-- **R3, transportation**: across a whole cargo path, the cover `x` stays on
`t`, so `t` is never a pile top. -/
theorem twin_covered_persists {w v : State} (hwf : w.WF) {x t : Card}
    (hseat : seatOf w x = some (Sum.inr t))
    (hfound : t.twin ∈ w.found t.twin.suit)
    (hpath : CargoPath w v) : v.pileOfTop t = none := by
  have hwv : v.WF := cargoPath_wf hwf hpath
  have hxking : x.rank ≠ Rank.king := tfc_seatOf_inr_rank_ne_king hwf hseat
  have hparv : Parented v x :=
    parented_of_cargoPath hwf hpath hxking ⟨t, hseat⟩
  obtain ⟨z, hz⟩ := hparv
  obtain ⟨a, hhold, -, hlast⟩ := tfc_seatOf_of_inr hseat
  have hfit : canSitOn x t = true := (tfc_seat_parent hwf hhold hlast).1
  obtain ⟨a', hhold', -, hlast'⟩ := tfc_seatOf_of_inr hz
  have hfitz : canSitOn x z = true := (tfc_seat_parent hwv hhold' hlast').1
  have hfund : t.twin ∈ v.found t.twin.suit := by
    rw [found_cargoPath hpath]; exact hfound
  rcases seat_possibilities hfit hfitz with h | h
  · rw [h] at hz
    exact no_top_of_seat hwv hz
  · exfalso
    rw [h] at hlast'
    have hmem : t.twin ∈ (v.piles a').faceUp := mem_below _ (lastOf_mem hlast')
    exact ((mem_found_unique hwv hfund).1 a').2 hmem

/-- **R3, final form for one state**: if the cover `x` of `t` is present and
`t.twin` is founded, then `t` cannot be raised from any cargo mate — the cover
can only be removed by *raising* it. -/
theorem step_none_of_twin_covered {w v : State} (hwf : w.WF) {x t : Card}
    (hseat : seatOf w x = some (Sum.inr t))
    (hfound : t.twin ∈ w.found t.twin.suit)
    (hpath : CargoPath w v) :
    State.step v (Move.tabToFound t) = none := by
  have htop : v.pileOfTop t = none := twin_covered_persists hwf hseat hfound hpath
  rw [step_tabToFound_eq]
  by_cases hnext : v.nextUp t = true
  · rw [if_pos hnext, htop]
  · rw [if_neg hnext]

/-! ## §3. The exact residual of R3 -/

/-- **The residual of R3** (play level, *not* proved): if `x` sits on `t` and
`t.twin` is founded, then every valid play that raises `t` also raises `x`.
(`twin_covered_persists` + `step_none_of_twin_covered` are the state-level half;
turning them into this play statement needs the induction over the play whose
invariant is "`x` is still seated on `t`, or `x` has already been raised".) -/
def CoverMustBeRaised : Prop :=
  ∀ {s z : State} {ws : List Card} {x t : Card},
    RaiseSSeq s ws z → s.WF →
    seatOf s x = some (Sum.inr t) →
    t.twin ∈ s.found t.twin.suit →
    t ∈ ws → x ∈ ws

/-! ## §4. The claim and what is closed

`RankFrontClaim` (from `Temp/RankFront_proof.lean`) is the target.  Closed
fragments, restated here for the record:
* `raiseS_rankfront_of_licensed` — the word form, if **every** card of the
  target play is licensed at `s` and the ranks are pairwise distinct (this is
  R1 applied exhaustively; it also covers the fully-independent states);
* `swap_last_two` — the adjacent rank-swap of the last two steps;
* the two-card case below (both cards licensed). -/

/-- The two-card rank-front: if `a` is the lower-ranked card, `[a, b]` works once
both are licensed (the only sort-relevant case of length 2). -/
theorem real_rankfront_two {s : State} {a b : Card} (hs : s.WF)
    (ha : CanRaiseS s a) (hb : CanRaiseS s b) (hr : a.rank.toIdx < b.rank.toIdx) :
    ∃ z', RaiseSSeq s [b, a] z' := by
  obtain ⟨u₂, z₀, hp, hst⟩ := raiseStepS_of_canRaiseS ha
  have hu₂ : u₂.WF := raiseStepS_wf hs ⟨z₀, hp, hst⟩
  have hb₂ : CanRaiseS u₂ b :=
    canRaiseS_step_of_rank_ne hs ⟨z₀, hp, hst⟩ (fun h => by rw [h] at hr; omega) hb
  obtain ⟨u₃, z₁, hp₁, hst₁⟩ := raiseStepS_of_canRaiseS hb₂
  exact ⟨u₃, RaiseSSeq.cons (RaiseSSeq.cons (RaiseSSeq.nil s) hp hst) hp₁ hst₁⟩

/-- Sanity check: the empty word is the empty play. -/
theorem real_nil (s : State) : Real s [] := ⟨s, RaiseSSeq.nil s⟩

/-- A single licensed card is a valid singleton play, and `rankFront c [c]` is
exactly the word `[c]`. -/
theorem raiseS_rankfront_single {s : State} {c : Card} (hc : CanRaiseS s c) :
    ∃ z', RaiseSSeq s (rankFront c [c]) z' := by
  have hw : rankFront c [c] = [c] := by
    unfold rankFront
    rw [List.erase_cons_head]
    rfl
  obtain ⟨z, hz⟩ := raiseStepS_of_canRaiseS hc
  obtain ⟨z₀, hp, hst⟩ := hz
  exact ⟨z, by rw [hw]; exact RaiseSSeq.cons (RaiseSSeq.nil s) hp hst⟩

end OneColourClosure

#print axioms OneColourClosure.above_rank_lt
#print axioms OneColourClosure.above_rank_lt_of_pile
#print axioms OneColourClosure.seat_possibilities
#print axioms OneColourClosure.no_canPlace_of_seated
#print axioms OneColourClosure.twin_covered_persists
#print axioms OneColourClosure.step_none_of_twin_covered
#print axioms OneColourClosure.real_rankfront_two
#print axioms OneColourClosure.raiseS_rankfront_single
#print axioms OneColourClosure.real_nil
#print axioms OneColourClosure.raiseS_rankfront_of_licensed
#print axioms OneColourClosure.swap_last_two
