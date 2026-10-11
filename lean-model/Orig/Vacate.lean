import Orig.PileSwap
import Orig.Irreversible

/-!
# Orig — the vacate rule (wave 24, cards B and C; the shape skeleton)

The engine rule under proof, in the user's words: *if a tab-to-tab
move leaves an empty slot, we shouldn't do it — if there's already
an empty slot* (unless it's stacking to foundation, which the
statement's shape exempts by design: only `tabToTab` heads are on
trial).

The Klondike-model analogue is macro-game `420f99f` (Dominance
SS5.4b); its residue `vacate_secondMove_residue` is the case map.
Its two obstructions — the slate permutation and the orphaned hole
— are artifacts of the macro model's deal/board split and do not
exist here: `Pile = {hidden, faceUp}` lives at the anchor, so the
pile transposition preserves `WF` outright (`wf_swapPiles_iff`),
and the anchor landing guard reads `Pile.isEmpty` — both lists —
so kings land only on truly empty piles.

## This file carries the shape; the case map is worked in the
## wave notes and lands with the rows

This chapter this wave lands the *shape* and its computational
meaning; the prunability row (card B) and the aggregate (card C)
walk the residue's case map, whose Orig-side derivation —
re-derived from scratch in this wave's notes and re-verified
against the fit rules — is:

* the corner — `m₂` consumes the just-emptied pile `a` with a king
  landing (`foundToTab K (inl a)`, `wasteToTab K (inl a)`, or
  `tabToTab c₂ (inl a)` with `c₂`'s run rooted at a king): reroute
  `[m; king-to-a]` to `[king-to-h; m]` (h the pre-existing empty
  pile, legal from the start — `isEmpty` holds from the first
  move).  The two post-states are `swapPiles a h`-conjugate up to
  the king's source-splitting, a one-liner off
  `WinFrom_swapPiles_iff` + `run_swapPiles`: no slate, no
  reveal-token divergence (the flip composes inside `step`).
* the exchange ledger — `m₂` commutes past `m`, per kind:
  `draw` (fieldwise-disjoint: the draw writes `stock`/`waste`, the
  vacate writes `piles`; exact square);
  `wasteToFound` (writes `found`+`waste` against `piles`: exact
  square);
  `wasteToTab` (empty-seat targets: pre-existing holes exact; the
  seat `t_R` rides — the waste card lands on the run's top either
  side of the vacate, append-associative exact square; the seat
  `z` dies — `z` is buried under the landed run, `canPlace` false);
  `tabToFound` (the run-top seats: `fromCard`-`chop` composes, the
  single-card run merges into the lone `tabToFound c`);
  `foundToTab` (card-seats as `wasteToTab`; the empty seats by the
  corner or exact squares);
  `tabToTab` (the root reroot merges to a different-token single
  move; sub-run jettisons commute by the chop/below kit with the
  suffix appended-before-the-target; interior kings cannot exist —
  runs descend from non-king roots and kings never sit above;
  the old-`P_T` sources ride through by located-`putRun`
  associativity; self-seats die — `canPlace_inr_target_off_run`
  and the rank discipline kill them at WF).
* drop-at-end — never needed for card B: every living route
  re-inserts `m` second.

`vacateShape` (card C) lifts the `hvac` spelling.
-/

/-! ## The vacate shape -/

/-- The move `tabToTab c b` is a *vacate at `c`* when `c` is not a
king and `c`'s whole pile rides: `c` sits face up in pile `a`, the
pile has nothing hidden, and `c` is the pile's first face-up card.
Such a move — when legal — empties pile `a` (the `below`/`hidden`
shape below is exactly the tabToTab arm's vacate condition, and
`vacate_emptiesPile` is its computational meaning).  The shape is
base-blind, as card C's statement narrows only the head. -/
def vacateShape (st : State) (c : Card) : Prop :=
  c.rank ≠ Rank.king ∧ ∃ a, st.pileHolding c = some a ∧
    (st.piles a).hidden = [] ∧ below c (st.piles a).faceUp = []

/-! ## The computational meaning of the shape -/

/-- The emptied source pile, as a literal: no hidden cards and an
empty `below`-split leave the bare empty pile after the ride (the
removal's `revealTop` branch is dead).  Farm-local twin of
`afterRunRemoved_empty_eq'` / `afterRunRemoved_bare_empty`,
private in Irreversible/Classify/EdgeLabel — this chapter is the
natural public home; dedup at their harvest. -/
private theorem afterRunRemoved_of_vacate {p : Pile} (hhid : p.hidden = []) :
    Pile.afterRunRemoved p ([] : List Card) = ⟨[], ([] : List Card)⟩ := by
  rcases p with ⟨hlist, flist⟩
  cases hlist with
  | nil => rfl
  | cons x xs => exact absurd hhid (by simp)

/-- The computational meaning of the vacate shape: a fired vacate
`tabToTab` leaves its source pile genuinely empty (`Pile.isEmpty`,
both lists — the engine's `free_slot` slot).  The landing never
touches the source: the `inl` arm demands a king (the shape's moving
head is a non-king), while an `inr` landing cannot locate the source
pile, because at the intermediate state it is already the bare empty
pile — the removal happens before the placement in the step arm, so
no descent/WF argument is needed; the row is state-universal. -/
theorem vacate_emptiesPile {st : State} {c : Card} {b : Base} {s₁ : State}
    (hvac : vacateShape st c)
    (hstep : State.step st (Move.tabToTab c b) = some s₁) :
    ∃ a, st.pileHolding c = some a ∧ (s₁.piles a).isEmpty = true := by
  obtain ⟨hnk, a, hhold, hhid, hbel⟩ := hvac
  obtain ⟨a₀, hhold₀, hcp, -, hs₁⟩ := step_tabToTab_inv hstep
  have hae : a = a₀ := Option.some.inj (hhold.symm.trans hhold₀)
  subst hae
  rw [hbel, afterRunRemoved_of_vacate hhid] at hs₁
  refine ⟨a, hhold, ?_⟩
  have hSp : (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles a =
      ⟨[], ([] : List Card)⟩ := setPile_piles_self
  cases b with
  | inl k =>
      rw [canPlace_inl_unfold] at hcp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcp
      exact absurd hcp.2 hnk
  | inr z =>
      cases hpo : (st.setPile a ⟨[], ([] : List Card)⟩ : State).pileOfTop z with
      | none =>
          rw [hs₁]
          show (((st.setPile a ⟨[], ([] : List Card)⟩ : State).putRun
              (fromCard c (st.piles a).faceUp) (Sum.inr z)).piles a).isEmpty = true
          simp only [State.putRun, hpo]
          rw [hSp]
          rfl
      | some k =>
          have hka : k ≠ a := by
            intro hcon
            obtain ⟨hfe, -⟩ := pileOfTop_top (hpo.trans (congrArg some hcon))
            rw [hSp] at hfe
            simp at hfe
          rw [hs₁, putRun_piles_inr_ne _ _ _ _ hpo (Ne.symm hka), hSp]
          rfl

#print axioms vacate_emptiesPile

/-- A vacate `tabToTab` writes no foundation (the `[m]`-alone arm of
the Card-B shell: a one-move vacate play can only reach a win the
root already had). -/
theorem vacate_keepsFound {st : State} {c : Card} {b : Base} {s₁ : State}
    (hstep : State.step st (Move.tabToTab c b) = some s₁) :
    s₁.found = st.found := by
  obtain ⟨_a₀, _hhold₀, _hcp, hfr, hs₁⟩ := step_tabToTab_inv hstep
  rw [hs₁, putRun_found, setPile_found]

#print axioms vacate_keepsFound

/-! ## The corner, leg one — the conjugated landing -/

/-- An empty pile is the bare pair of lists. -/
private theorem isEmpty_spec {p : Pile} (h : p.isEmpty = true) :
    p.hidden = [] ∧ p.faceUp = [] := by
  rcases p with ⟨hl, fl⟩
  match hl, fl with
  | [], [] => exact ⟨rfl, rfl⟩
  | x :: xs, ys => rw [Pile.isEmpty] at h; exact absurd h (by simp)

/-- The holding search is determined by its pointwise membership
profile — the single-pile-write companion of State's full-piles
`pileHolding_congr` (State.lean:610; the profile form covers the
states the exchange squares write at one anchor). -/
private theorem pileHolding_congr_mem {S T : State} {c : Card}
    (h : ∀ x : Anchor, decide (c ∈ (S.piles x).faceUp)
      = decide (c ∈ (T.piles x).faceUp)) :
    S.pileHolding c = T.pileHolding c :=
  firstWhere_congr h

/-- The top search is determined by its pointwise profile — the
single-pile-write companion of the top-search rows. -/
private theorem pileOfTop_congr_profile {S T : State} {z : Card}
    (h : ∀ x : Anchor, decide (S.topOf x = some z)
      = decide (T.topOf x = some z)) :
    S.pileOfTop z = T.pileOfTop z :=
  firstWhere_congr h

/-- The transposition of two empty piles is the identity state — the
two bare records exchange and everything else is untouched. -/
theorem swapPiles_id_of_bothEmpty (st : State) (i j : Anchor)
    (hi : (st.piles i).isEmpty = true) (hj : (st.piles j).isEmpty = true) :
    st.swapPiles i j = st := by
  obtain ⟨hhi, hfi⟩ := isEmpty_spec hi
  obtain ⟨hhj, hfj⟩ := isEmpty_spec hj
  refine State.ext rfl (funext fun x => ?_) rfl rfl rfl
  rw [State.swapPiles_piles]
  by_cases hxi : x = i
  · rw [hxi, Anchor.swap_self_left]
    exact Pile.ext (hhj.trans hhi.symm) (hfj.trans hfi.symm)
  · by_cases hxj : x = j
    · rw [hxj, Anchor.swap_self_right]
      exact Pile.ext (hhi.trans hhj.symm) (hfi.trans hfj.symm)
    · rw [Anchor.swap_eq_self _ _ hxi hxj]

/-- **The corner's conjugation leg** (king flavor generic): after a
fired vacate, both the just-emptied pile and the pre-existing hole
are bare, so the transposition fixes `s₁` and the co-action mirrors
the king landing at `a` into a landing at `h`, landing on the
transposed composite.  The three king flavors instantiate with their
one-line mirror rows (`Move.swapM`'s arms and
`Base.swapBase_inl` / `Anchor.swap_self_left`). -/
theorem vacate_corner_conj_after {st : State} {c : Card} {b : Base}
    {a h : Anchor} {s₁ U : State} {mK mK' : Move}
    (hwf : st.WF) (hnk : c.rank ≠ Rank.king)
    (hhold : st.pileHolding c = some a) (hhid : (st.piles a).hidden = [])
    (hbel : below c (st.piles a).faceUp = [])
    (hfree : (st.piles h).isEmpty = true)
    (hm : st.step (.tabToTab c b) = some s₁)
    (hmirror : Move.swapM a h mK = mK')
    (hm₂ : s₁.step mK = some U) :
    ∃ U', s₁.step mK' = some U' ∧ U' = U.swapPiles a h := by
  -- the vacate shape, assembled
  have hshape : vacateShape st c := ⟨hnk, a, hhold, hhid, hbel⟩
  obtain ⟨a₁, hhold₁, hempty₁⟩ := vacate_emptiesPile hshape hm
  have hae : a = a₁ := Option.some.inj (hhold.symm.trans hhold₁)
  subst hae
  -- h differs from a: pile a holds c face up, h is empty
  have hha : h ≠ a := by
    intro hcon
    rw [hcon] at hfree
    exact absurd (pileHolding_mem hhold) (by
      rw [(isEmpty_spec hfree).2]; simp)
  -- the vacate's write set never touches h
  obtain ⟨a₀, hh₀, hcp, -, hs₁W⟩ := step_tabToTab_inv hm
  have haa : a = a₀ := Option.some.inj (hhold.symm.trans hh₀)
  subst haa
  rw [hbel, afterRunRemoved_of_vacate hhid] at hs₁W
  have hSp : (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles h = st.piles h :=
    setPile_piles_ne hha
  cases b with
  | inl k =>
      rw [canPlace_inl_unfold] at hcp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcp
      exact absurd hcp.2 hnk
  | inr z =>
      have hs₁hE : (s₁.piles h).isEmpty = true := by
        cases hpo : (st.setPile a ⟨[], ([] : List Card)⟩ : State).pileOfTop z with
        | none =>
            have hs₁h : s₁.piles h = st.piles h := by
              rw [hs₁W]
              simp only [State.putRun, hpo]
              exact hSp
            rw [hs₁h]
            exact hfree
        | some k =>
            have hkh : k ≠ h := by
              intro hcon
              obtain ⟨hfe, -⟩ := pileOfTop_top (hpo.trans (congrArg some hcon))
              rw [hSp] at hfe
              rw [(isEmpty_spec hfree).2] at hfe
              exact hfe rfl
            have hs₁h : s₁.piles h = st.piles h := by
              rw [hs₁W, putRun_piles_inr_ne _ _ _ _ hpo (Ne.symm hkh), hSp]
            rw [hs₁h]
            exact hfree
      -- both piles bare at `s₁`: the transposition fixes it
      have htid : s₁.swapPiles a h = s₁ :=
        swapPiles_id_of_bothEmpty s₁ _ _ hempty₁ hs₁hE
      have hwf₁ : s₁.WF := step_wf hwf hm
      have hconj := State.step_swapPiles (st := s₁) (i := a) (j := h) hwf₁ mK
      rw [htid, hmirror, hm₂, Option.map_some] at hconj
      exact ⟨_, hconj, rfl⟩
#print axioms vacate_corner_conj_after

/-! ## The corner, leg two — the exchange square -/

/-- **The vacate's write set never touches an empty `h`**: the `inl`
landing is king-only (dead for a non-king mover), and the located
`inr` target's pile is never the bare hole, so the hole still reads
empty at the post-vacate state. -/
theorem vacate_keepsHole {st : State} {c : Card} {b : Base} {a h : Anchor} {s₁ : State}
    (hnk : c.rank ≠ Rank.king) (hcp : st.canPlace c b = true)
    (hfree : (st.piles h).isEmpty = true) (hha : h ≠ a)
    (hs₁W : s₁ = (st.setPile a ⟨[], ([] : List Card)⟩ : State).putRun
      (fromCard c (st.piles a).faceUp) b) :
    (s₁.piles h).isEmpty = true := by
  have hSp : (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles h = st.piles h :=
    setPile_piles_ne hha
  cases b with
  | inl k =>
      rw [canPlace_inl_unfold] at hcp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcp
      exact absurd hcp.2 hnk
  | inr z =>
      have hs₁h : s₁.piles h = st.piles h := by
        cases hpo : (st.setPile a ⟨[], ([] : List Card)⟩ : State).pileOfTop z with
        | none =>
            rw [hs₁W]
            simp only [State.putRun, hpo]
            exact hSp
        | some k =>
            have hkh : k ≠ h := by
              intro hcon
              obtain ⟨hfe, -⟩ := pileOfTop_top (hpo.trans (congrArg some hcon))
              rw [hSp] at hfe
              rw [(isEmpty_spec hfree).2] at hfe
              exact hfe rfl
            rw [hs₁W, putRun_piles_inr_ne _ _ _ _ hpo (Ne.symm hkh), hSp]
      rw [hs₁h]
      exact hfree

#print axioms vacate_keepsHole

/-! ### Leg two (the exchange square) — the next card

    `vacate_xchg_foundToTab_hole`: the king worry-back onto the
    pre-existing hole commutes with the disjoint vacate —
    `st₁'.step m` and `s₁.step (foundToTab K (Sum.inl h))` share one
    common successor.  Construction: the king landing expands by
    `step_foundToTab_eq` + `putCard`-inl (`= setPile h ⟨[], [K]⟩`);
    the vacate at `st₁'` locates the same `z`-pile (`k ≠ a` by       `canPlace_inr_target_pile_ne`, `k ≠ h` / `z ≠ K` by the bare hole / `mem_found_unique`);  the two composites are then compared fieldwise — `found` via   `vacate_keepsFound` + the common `setFound`, `piles` per anchor
    (`setPile`/`putRun_piles_inr_self`/`_ne` reads, `Pile.ext` at
    the three written anchors, the congr twins above for the shared
    searches), the other five fields `rfl`-equal.  With leg one
    (`vacate_corner_conj_after`) this hands the shell the
    head-avoiding order `[king-to-h; m]` at the transposed composite. -/

/-! ## Card B row (statement landed with the next wave's rows;
## see the case map above and the wave-24 FARM block) -/
