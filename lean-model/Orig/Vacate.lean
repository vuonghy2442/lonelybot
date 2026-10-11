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

/-! ## Card B row (statement landed with the next wave's rows;
## see the case map above and the wave-24 FARM block) -/
