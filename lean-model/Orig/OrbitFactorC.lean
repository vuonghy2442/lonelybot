import Orig.OrbitFactor

/-!
# Orig — the orbit factorization completion

THE RESIDUE COMPLETION of `Orig/OrbitFactor.lean`: the two named
residues of the orbit-factorization card, proved as this chapter's
own standalone rows.

* §1 `shuffle_drawsLast` — the witness-grade draw-last regrouping
  (the erstwhile `shuffle_split_drawsLastW` residue, rebuilt here
  under its own fresh name): every witness journey factors as a
  draw-free board segment to a mid-state, then an all-draw tail
  segment landing the original end, BOTH segments still carrying
  their per-leg `reversibleAtW` witnesses.
* §2 `sameOrbit_factor_fwd` — the `→` direction of the
  factorization (the erstwhile `sameOrbit_factor` sorry): two
  `WF` same-orbit mates decompose as the board component
  (`NoDrawPlayW`) onto the phase component (`SWRotW`).
* §3 `sameOrbit_factor_full` — the full biconditional, the
  canonical import for all downstream consumers: `←` is the bank's
  own four-witness glue (copied so the row carries no `sorryAx`
  lineage through the parent's residue), `→` is §2.

## The route (§1)

The parent card's docstring left the pull direction open: after a
draw↔board swap the re-sited leg needs a fresh `reversibleAtW`
witness, and pushing or pulling the LEG's RETURN PLAY through the
draw lands at a preimage of the return target, underdetermined
without the draw cycle's injectivity — the push grade was solved
in the edge-label chapter, the pull grade was left as the residue.

This completion takes a different road: NO return play is ever
transported.  The re-witness of each pulled board leg goes through
the WF-gated oracle bridge of `Orig/Classify.lean`
(`reversible_iff_of` / `reversibleAtW_of_reversible`): the leg's
original site `s₁` (WF along the journey by `Orig.Reach.step_wf`)
and the pulled site `x` (the journey's own real frame, WF by the
theorem's gate) share the whole board — a fired draw keeps
`piles`/`found` (`stepDraw_piles`/`stepDraw_found`) — and the
oracle's shape Bool `irreversibleOf` reads only the board fields
for the three table movers (the private-shape congruence copies
below), so the false cell at `s₁` re-instantiates at `x`, where
the bridge mints the witness outright.  The shape disjunction the
residue's route named as "the one open work item" never has to be
re-derived by hand: the bridge already contains it.

The bubbling itself is one core lemma, `pull_one` (the pull-side
twin of the edge-label chapter's push, witness grade): a witnessed
journey at the drawn landing `x --draw--> s₁ --play--> y` re-runs
wholesale at `x`, still witnessed leg by leg, landing `y'` one
draw before `y`, WITH the re-sited front draw's witness at `y'`
delivered as part of the induction's own bookkeeping (the base
case IS the front draw's own witness; the draw case consumes the
leg's own witness as the next front; the board case crosses the
public §1 square `board_draw_commute`, re-witnesses the board leg
through the bridge as above, and re-witnesses the front draw at
the crossed site by the public zone census `draw_revW_congr` over
the board-leg zone-keep).  The draw-last split then follows by the
same induction shape as the run-grade `run_split_drawsLast` of
the parent card, with the final `D`-leg's witness arriving
straight from `pull_one`.

## The route (§2)

The four-piece layout of the parent's docstring, executed: both
witness journeys split draws-last by §1; `NoDrawPlayW u zF`'s
backward journey is the board part of re-splitting the composite
`zF --D--> v --b--> zB --d--> u` draws-last, landing `u` again by
the accounting (boards keep the zone verbatim, draws keep the
board verbatim — `State.ext` closes the landing); `SWRotW zF v`'s
backward round is `d` transplanted to `v`'s frame by the proved
`draw_play_transplant` (`v` shares `zB`'s zone by the board
journey's zone-keep), landing exactly `zF` again by the same
field-keeps.

## Axiom discipline

Every row audits `[propext, Quot.sound]` — zero `Classical.choice`,
zero `sorryAx`; the `#print axioms` block at the file's end is
part of the build.  The private copies below follow the farm's
isolation convention (dedup at merge).
-/

/-! ## §1 support: the oracle's shape Bool is board-determined

The three table-move cells of `Orig.Classify`'s private shape Bool
(`tabToFoundIrr`, `foundToTabIrr`, `tabToTabIrr`) are re-stated
here verbatim, so their getter-congruence can be proved without
naming the parent's private constants; the `rfl` welds below join
each copy to the public `irreversibleOf` assembly definitionally.
Farm-isolation copies; dedup at merge. -/

/-- Farm copy of the classification's private `.tabToFound` shape. -/
private def tabToFoundIrrC (st : State) (c : Card) : Bool :=
  match st.nextUp c with
  | false => true
  | true =>
      match st.pileOfTop c with
      | none => true
      | some a =>
          match chop (st.piles a).faceUp with
          | [] =>
              match (st.piles a).hidden with
              | [] => decide (c.rank ≠ Rank.king)
              | _ :: _ => true
          | _ :: _ => false

/-- Farm copy of the classification's private `.foundToTab` shape. -/
private def foundToTabIrrC (st : State) (c : Card) (b : Base) : Bool :=
  match st.foundTop c.suit with
  | none => true
  | some c' => if c' = c then !(st.canPlace c b) else true

/-- Farm copy of the classification's private `.tabToTab` shape. -/
private def tabToTabIrrC (st : State) (c : Card) (b : Base) : Bool :=
  match st.pileHolding c with
  | none => true
  | some a =>
      match st.canPlace c b with
      | false => true
      | true =>
          match below c (st.piles a).faceUp with
          | [] =>
              match (st.piles a).hidden with
              | [] => decide (c.rank ≠ Rank.king)
              | _ :: _ => true
          | _ :: _ => false

/-- The `.tabToFound` cell of the oracle reads the board only. -/
private theorem tabToFoundIrrC_congr {u u' : State} {c : Card}
    (hp : u.piles = u'.piles) (hf : u.found = u'.found) :
    tabToFoundIrrC u c = tabToFoundIrrC u' c := by
  unfold tabToFoundIrrC
  rw [nextUp_congr c hf, pileOfTop_congr c hp, hp]

/-- The `.foundToTab` cell of the oracle reads the board only. -/
private theorem foundToTabIrrC_congr {u u' : State} {c : Card} {b : Base}
    (hp : u.piles = u'.piles) (hf : u.found = u'.found) :
    foundToTabIrrC u c b = foundToTabIrrC u' c b := by
  unfold foundToTabIrrC
  rw [foundTop_congr c.suit hf, canPlace_congr c b hp]

/-- The `.tabToTab` cell of the oracle reads the board only. -/
private theorem tabToTabIrrC_congr {u u' : State} {c : Card} {b : Base}
    (hp : u.piles = u'.piles) (_hf : u.found = u'.found) :
    tabToTabIrrC u c b = tabToTabIrrC u' c b := by
  unfold tabToTabIrrC
  rw [pileHolding_congr (st := u') (s' := u) hp, canPlace_congr c b hp, hp]

/-- `irreversibleOf` at a non-draw move reads the board only (the
`rfl` welds ride the public assembly; the waste cells are
constant `true`). -/
private theorem irreversibleOf_board_congr {u u' : State} {m : Move}
    (hnd : m ≠ Move.draw) (hp : u.piles = u'.piles) (hf : u.found = u'.found) :
    irreversibleOf u m = irreversibleOf u' m := by
  cases m with
  | draw => exact absurd rfl hnd
  | wasteToFound _ => rfl
  | wasteToTab _ _ => rfl
  | tabToFound c =>
      rw [show irreversibleOf u (Move.tabToFound c) = tabToFoundIrrC u c from rfl,
        show irreversibleOf u' (Move.tabToFound c) = tabToFoundIrrC u' c from rfl,
        tabToFoundIrrC_congr hp hf]
  | foundToTab c b =>
      rw [show irreversibleOf u (Move.foundToTab c b) = foundToTabIrrC u c b from rfl,
        show irreversibleOf u' (Move.foundToTab c b) = foundToTabIrrC u' c b from rfl,
        foundToTabIrrC_congr hp hf]
  | tabToTab c b =>
      rw [show irreversibleOf u (Move.tabToTab c b) = tabToTabIrrC u c b from rfl,
        show irreversibleOf u' (Move.tabToTab c b) = tabToTabIrrC u' c b from rfl,
        tabToTabIrrC_congr hp hf]

/-- **The pulled-leg re-witness**: a witnessed reversible board
leg at the drawn landing `s₁` re-witnesses at the drawing origin
`x` — the two frames share the whole board (a fired draw keeps
`piles`/`found`), the oracle's shape Bool is board-read
(`irreversibleOf_board_congr`), so the leg's false cell transfers,
and the WF-gated bridge mints the witness at `x` outright.  No
return play is ever transported; the preimage gap does not
arise. -/
theorem reversibleAtW_stepDraw_frame {x s₁ : State} {m : Move}
    (hd : x.stepDraw = some s₁) (hwfs₁ : s₁.WF) (hwfx : x.WF)
    (hw : reversibleAtW s₁ m) (hnd : m ≠ Move.draw) :
    reversibleAtW x m := by
  have hp : x.piles = s₁.piles := (stepDraw_piles hd).symm
  have hf : x.found = s₁.found := (stepDraw_found hd).symm
  have hcell : irreversibleOf s₁ m = false :=
    (reversible_iff_of hwfs₁ m).mp (reversibleAt_of_W hw)
  have hcellx : irreversibleOf x m = false := by
    rw [irreversibleOf_board_congr hnd hp hf, hcell]
  exact reversibleAtW_of_reversible hwfx
    ((reversible_iff_of hwfx m).mpr hcellx)

/-! ## §1 support: per-fire and journey-grade field keeps

Farm copies of `Orig/OrbitFactor.lean`'s private
`leg_keep_zone`/`zone_keep_journey` landed beside the originals
(the board-fire zone rows re-ride the public inversions and field
lemmas); dedup at merge. -/

/-- A witnessed reversible non-draw leg keeps the draw zone
verbatim — per move kind, the fired record re-read (farm copy of
`Orig/OrbitFactor.lean`'s private `leg_keep_zone`; dedup at
merge). -/
private theorem leg_zone_keep {x y : State} {m : Move}
    (hw : reversibleAtW x m) (hstep : State.step x m = some y)
    (hnd : m ≠ Move.draw) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  cases m with
  | draw => exact absurd rfl hnd
  | wasteToFound c => exact absurd hw (journey_never_wasteToFound hstep)
  | wasteToTab c b => exact absurd hw (journey_never_wasteToTab hstep)
  | tabToFound c =>
      obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
      rw [hs]
      exact ⟨rfl, rfl, rfl⟩
  | foundToTab c b =>
      obtain ⟨c₀, ht, hce, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      exact ⟨by rw [putCard_stock, setFound_stock],
        by rw [putCard_waste, setFound_waste],
        by rw [putCard_drawStep, setFound_drawStep]⟩
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      exact ⟨by rw [putRun_stock, setPile_stock],
        by rw [putRun_waste, setPile_waste],
        by rw [putRun_drawStep, setPile_drawStep]⟩

/-- Witness journeys preserve WF (`step_wf` per leg; farm copy of
`Orig/EdgeLabel.lean`'s private row; dedup at merge). -/
private theorem shuffleW_wf_end : ∀ {st z : State} {l : List Move},
    ShufflePlayW st l z → st.WF → z.WF := by
  intro st z l h
  induction h with
  | nil s => intro hwfs; exact hwfs
  | cons hw hstep hrest ih =>
      intro hwfst
      exact ih (step_wf hwfst hstep)

/-- A draw-free witness journey keeps the whole draw zone
verbatim (farm copy of `Orig/OrbitFactor.lean`'s private
`zone_keep_journey`; dedup at merge). -/
private theorem shuffleW_zone_keep : ∀ {x : State} {play : List Move} {y : State},
    ShufflePlayW x play y → (∀ m ∈ play, m ≠ Move.draw) →
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  intro x play y h
  induction h with
  | nil s => intro _; exact ⟨rfl, rfl, rfl⟩
  | @cons st₀ m mid rest st' hw hstep hrest ih =>
      intro hnd
      obtain ⟨h1, h2, h3⟩ := leg_zone_keep hw hstep (hnd m (by simp))
      obtain ⟨h4, h5, h6⟩ :=
        ih (fun m' hm' => hnd m' (List.mem_cons_of_mem _ hm'))
      exact ⟨h4.trans h1, h5.trans h2, h6.trans h3⟩

/-- A draws-only witness journey keeps the whole board verbatim. -/
private theorem shuffleW_board_keep : ∀ {x : State} {play : List Move} {y : State},
    ShufflePlayW x play y → (∀ m ∈ play, m = Move.draw) →
    y.piles = x.piles ∧ y.found = x.found := by
  intro x play y h
  induction h with
  | nil s => intro _; exact ⟨rfl, rfl⟩
  | @cons st₀ m mid rest st' hw hstep hrest ih =>
      intro hdr
      have hmd : m = Move.draw := hdr m (by simp)
      subst hmd
      have hstep' : st₀.stepDraw = some mid := hstep
      obtain ⟨h1, h2⟩ :=
        ih (fun m' hm' => hdr m' (List.mem_cons_of_mem _ hm'))
      exact ⟨h1.trans (stepDraw_piles hstep'), h2.trans (stepDraw_found hstep')⟩

/-- Cons-inversion for witness journeys (the play's index match
dismisses the `nil` case). -/
private theorem shuffleW_cons_inv {st : State} {m : Move} {rest : List Move}
    {st' : State} (h : ShufflePlayW st (m :: rest) st') :
    ∃ mid, reversibleAtW st m ∧ State.step st m = some mid ∧
      ShufflePlayW mid rest st' := by
  cases h with
  | @cons _ _ mid _ _ hw hfire hrest => exact ⟨mid, hw, hfire, hrest⟩

/-- **The pull core** (the pull-side twin of the edge-label
chapter's witness push): a witnessed journey at the drawn landing
`x --draw--> s₁ --play--> y` re-runs wholesale at the drawing
origin `x`, still witness-shuffled leg by leg, landing `y'` one
draw before `y` — and the re-sited front draw carries its own
`reversibleAtW` witness at `y'`, delivered by the induction's
bookkeeping: the base case hands back the front draw's very own
witness, a draw leg hands the recursion its own leg-witness as
the next front, and a board leg crosses the public §1 square
(`board_draw_commute`), re-witnesses itself at `x` through the
oracle bridge (`reversibleAtW_stepDraw_frame`), and re-witnesses
the front draw at the crossed site through the zone census
(`draw_revW_congr` over `leg_zone_keep`). -/
private theorem pull_one : ∀ (play : List Move) (x s₁ y : State),
    x.stepDraw = some s₁ → reversibleAtW x Move.draw → x.WF → s₁.WF →
    ShufflePlayW s₁ play y →
    ∃ y', ShufflePlayW x play y' ∧ y'.stepDraw = some y ∧
      y'.WF ∧ reversibleAtW y' Move.draw := by
  intro play
  induction play with
  | nil =>
      intro x s₁ y hd hwfd hwfx hwfs₁ hJ
      cases hJ
      exact ⟨x, ShufflePlayW.nil x, hd, hwfx, hwfd⟩
  | cons m rest ih =>
      intro x s₁ y hd hwfd hwfx hwfs₁ hJ
      obtain ⟨mid, hw, hfire, hrest⟩ := shuffleW_cons_inv hJ
      cases m with
      | draw =>
          have hd' : s₁.stepDraw = some mid := hfire
          have hwfmid : mid.WF := step_wf hwfs₁ hfire
          obtain ⟨y', jlift, hstepD, hwfy, hrevy⟩ :=
            ih s₁ mid y hd' hw hwfs₁ hwfmid hrest
          exact ⟨y', ShufflePlayW.cons hwfd hd jlift, hstepD, hwfy, hrevy⟩
      | wasteToFound c => exact absurd hw (journey_never_wasteToFound hfire)
      | wasteToTab c b => exact absurd hw (journey_never_wasteToTab hfire)
      | tabToFound c =>
          have hrevx : reversibleAtW x (Move.tabToFound c) :=
            reversibleAtW_stepDraw_frame hd hwfs₁ hwfx hw (by simp)
          obtain ⟨t, hfireX, htD⟩ := board_draw_commute hd hfire hw
          obtain ⟨hz1, hz2, hz3⟩ := leg_zone_keep hrevx hfireX (by simp)
          have hrevt : reversibleAtW t Move.draw :=
            draw_revW_congr (hwfx.drawStep_pos) hz1.symm hz2.symm hz3.symm hwfd
          have hwft : t.WF := step_wf hwfx hfireX
          have hwfmid : mid.WF := step_wf hwfs₁ hfire
          obtain ⟨y', jlift, hstepD, hwfy, hrevy⟩ :=
            ih t mid y htD hrevt hwft hwfmid hrest
          exact ⟨y', ShufflePlayW.cons hrevx hfireX jlift, hstepD, hwfy, hrevy⟩
      | foundToTab c b =>
          have hrevx : reversibleAtW x (Move.foundToTab c b) :=
            reversibleAtW_stepDraw_frame hd hwfs₁ hwfx hw (by simp)
          obtain ⟨t, hfireX, htD⟩ := board_draw_commute hd hfire hw
          obtain ⟨hz1, hz2, hz3⟩ := leg_zone_keep hrevx hfireX (by simp)
          have hrevt : reversibleAtW t Move.draw :=
            draw_revW_congr (hwfx.drawStep_pos) hz1.symm hz2.symm hz3.symm hwfd
          have hwft : t.WF := step_wf hwfx hfireX
          have hwfmid : mid.WF := step_wf hwfs₁ hfire
          obtain ⟨y', jlift, hstepD, hwfy, hrevy⟩ :=
            ih t mid y htD hrevt hwft hwfmid hrest
          exact ⟨y', ShufflePlayW.cons hrevx hfireX jlift, hstepD, hwfy, hrevy⟩
      | tabToTab c b =>
          have hrevx : reversibleAtW x (Move.tabToTab c b) :=
            reversibleAtW_stepDraw_frame hd hwfs₁ hwfx hw (by simp)
          obtain ⟨t, hfireX, htD⟩ := board_draw_commute hd hfire hw
          obtain ⟨hz1, hz2, hz3⟩ := leg_zone_keep hrevx hfireX (by simp)
          have hrevt : reversibleAtW t Move.draw :=
            draw_revW_congr (hwfx.drawStep_pos) hz1.symm hz2.symm hz3.symm hwfd
          have hwft : t.WF := step_wf hwfx hfireX
          have hwfmid : mid.WF := step_wf hwfs₁ hfire
          obtain ⟨y', jlift, hstepD, hwfy, hrevy⟩ :=
            ih t mid y htD hrevt hwft hwfmid hrest
          exact ⟨y', ShufflePlayW.cons hrevx hfireX jlift, hstepD, hwfy, hrevy⟩

/-- **§1: the witness-grade draw-last bubbling** (the residue, at
last): every witness journey factors as a draw-free board segment
to a mid-state, then an all-draw tail segment landing the
original end — both segments still witness shuffles, every leg of
both still carrying its own `reversibleAtW` round trip.

At a head draw, the pull core (`pull_one`) benches the head draw
behind the entire rest journey and hands back the re-sited
journey plus the final leg's own witness; the induction then
appends the head draw at the tail's end.  At a head board move,
nothing moves.  The waste movers never ride (`journey_never`
census).  The `x.WF` gate pays every bridge call along the way
(`step_wf` carries it forward), replacing the residue route's
open shape-disjunction work outright. -/
theorem shuffle_drawsLast : ∀ (play : List Move) (x y : State),
    ShufflePlayW x play y → x.WF →
    ∃ B D z, (∀ m ∈ B, m ≠ Move.draw) ∧ (∀ m ∈ D, m = Move.draw) ∧
      ShufflePlayW x B z ∧ ShufflePlayW z D y := by
  intro play
  induction play with
  | nil =>
      intro x y h _
      cases h
      exact ⟨[], [], x, by simp, by simp, ShufflePlayW.nil x, ShufflePlayW.nil x⟩
  | cons m rest ih =>
      intro x y h hwf
      obtain ⟨mid, hw, hfire, hrest⟩ := shuffleW_cons_inv h
      have hwfmid : mid.WF := step_wf hwf hfire
      cases m with
      | draw =>
          obtain ⟨y', jlift, hstepD, _, hrevy⟩ :=
            pull_one rest x mid y (show x.stepDraw = some mid from hfire) hw hwf hwfmid hrest
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ := ih x y' jlift hwf
          refine ⟨B, D ++ [Move.draw], z, hBnd, ?_, hBz, ?_⟩
          · intro m' hm'
            rcases List.mem_append.mp hm' with h1 | h2
            · exact hDdr m' h1
            · exact List.mem_singleton.mp h2
          · exact ShufflePlayW_append hDz
              (ShufflePlayW.cons hrevy hstepD (ShufflePlayW.nil y))
      | tabToFound c =>
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ := ih mid y hrest hwfmid
          refine ⟨Move.tabToFound c :: B, D, z, ?_, hDdr, ?_, hDz⟩
          · intro m' hm'
            cases List.mem_cons.mp hm' with
            | inl heq => intro hcon; rw [heq] at hcon; exact nomatch hcon
            | inr htl => exact hBnd m' htl
          · exact ShufflePlayW.cons hw hfire hBz
      | foundToTab c b =>
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ := ih mid y hrest hwfmid
          refine ⟨Move.foundToTab c b :: B, D, z, ?_, hDdr, ?_, hDz⟩
          · intro m' hm'
            cases List.mem_cons.mp hm' with
            | inl heq => intro hcon; rw [heq] at hcon; exact nomatch hcon
            | inr htl => exact hBnd m' htl
          · exact ShufflePlayW.cons hw hfire hBz
      | tabToTab c b =>
          obtain ⟨B, D, z, hBnd, hDdr, hBz, hDz⟩ := ih mid y hrest hwfmid
          refine ⟨Move.tabToTab c b :: B, D, z, ?_, hDdr, ?_, hDz⟩
          · intro m' hm'
            cases List.mem_cons.mp hm' with
            | inl heq => intro hcon; rw [heq] at hcon; exact nomatch hcon
            | inr htl => exact hBnd m' htl
          · exact ShufflePlayW.cons hw hfire hBz
      | wasteToFound c => exact absurd hw (journey_never_wasteToFound hfire)
      | wasteToTab c b => exact absurd hw (journey_never_wasteToTab hfire)

/-- **§2: the forward factorization.**  Two `WF` same-orbit mates
decompose as the board component onto the phase component — the
four-piece layout of the parent card's docstring, executed:

* both witnessing journeys split draws-last by §1:
  `u --B--> zF --D--> v` and `v --b--> zB --d--> u`;
* `NoDrawPlayW u zF`'s backward journey is the board part of
  re-splitting the composite `zF --D--> v --b--> zB --d--> u`
  draws-last at `zF` (WF carried there by the journey keep), the
  re-split's own landing `z₂` closing to `u` by the accounting:
  its board is `u`'s through the all-draw tail, its zone is `u`'s
  through the draw-free board parts — `State.ext`;
* `SWRotW zF v`'s backward round is `d` transplanted to `v`'s
  frame (`draw_play_transplant`; `v` shares `zB`'s zone by the
  board journey's zone-keep), the transplanted landing closing
  to `zF` the same way: `v`'s board through the two draws-only
  journeys, `u`'s zone through the `B`-journey plus the
  transplant's own landing facts. -/
theorem sameOrbit_factor_fwd {u v : State} (hwf₁ : u.WF) (hwf₂ : v.WF)
    (h : sameOrbitSetoid.r u v) :
    ∃ z, NoDrawPlayW u z ∧ SWRotW z v := by
  have h' : RevEqW v u := h
  obtain ⟨σ, hσW, τ, hτW⟩ := h'
  obtain ⟨B, D, zF, hBnd, hDdr, hBz, hDz⟩ := shuffle_drawsLast τ u v hτW hwf₁
  obtain ⟨b, d, zB, hbnd, hddr, hbz, hdz⟩ := shuffle_drawsLast σ v u hσW hwf₂
  obtain ⟨kF1, kF2, kF3⟩ := shuffleW_zone_keep hBz hBnd
  obtain ⟨kB1, kB2, kB3⟩ := shuffleW_zone_keep hbz hbnd
  have hzFwf := shuffleW_wf_end hBz hwf₁
  have hzBwf := shuffleW_wf_end hbz hwf₂
  have hcomp : ShufflePlayW zF (D ++ b ++ d) u :=
    ShufflePlayW_append (ShufflePlayW_append hDz hbz) hdz
  obtain ⟨B₂, D₂, z₂, hB₂nd, hD₂dr, hB₂z, hD₂z⟩ :=
    shuffle_drawsLast (D ++ b ++ d) zF u hcomp hzFwf
  obtain ⟨k₂1, k₂2, k₂3⟩ := shuffleW_zone_keep hB₂z hB₂nd
  obtain ⟨kD1, kD2⟩ := shuffleW_board_keep hD₂z hD₂dr
  have hz₂u : z₂ = u :=
    State.ext kD2.symm kD1.symm (k₂1.trans kF1) (k₂2.trans kF2) (k₂3.trans kF3)
  rw [hz₂u] at hB₂z
  have hposzB : 0 < zB.drawStep := hzBwf.drawStep_pos
  obtain ⟨y', jμ, hyz1, hyz2, hyz3⟩ :=
    draw_play_transplant hdz hddr hposzB kB1 kB2 kB3
  obtain ⟨ky1, ky2⟩ := shuffleW_board_keep jμ hddr
  obtain ⟨kv1, kv2⟩ := shuffleW_board_keep hDz hDdr
  have hyeq : y' = zF :=
    State.ext (ky2.trans kv2) (ky1.trans kv1)
      (hyz1.trans kF1.symm) (hyz2.trans kF2.symm) (hyz3.trans kF3.symm)
  rw [hyeq] at jμ
  exact ⟨zF, ⟨B, hBz, hBnd, B₂, hB₂z, hB₂nd⟩, D, d, ⟨hDz, hDdr⟩, ⟨jμ, hddr⟩⟩

/-- **§3: the full biconditional** — the canonical import for all
downstream consumers (the mod-phase spectrum row, the pairClass
assembly, the bracket wiring).  `→` is §2; `←` is the bank's own
four-witness glue (the parent card's proved direction, copied here
so the row carries no `sorryAx` lineage through the parent's
residue): a `z` factored by both components supplies the
`v→u` journey as the rotation round followed by the board back,
and the `u→v` journey as the board front followed by the rotation
round. -/
theorem sameOrbit_factor_full {u v : State} (hwf₁ : u.WF) (hwf₂ : v.WF) :
    sameOrbitSetoid.r u v ↔ ∃ z, NoDrawPlayW u z ∧ SWRotW z v := by
  constructor
  · exact sameOrbit_factor_fwd hwf₁ hwf₂
  · rintro ⟨z, ⟨P₁, hP₁, hP₁nd, P₂, hP₂, hP₂nd⟩, σ, τ, ⟨hσW, -⟩, ⟨hτW, -⟩⟩
    exact ⟨τ ++ P₂, ShufflePlayW_append hτW hP₂, P₁ ++ σ, ShufflePlayW_append hP₁ hσW⟩

#print axioms reversibleAtW_stepDraw_frame
#print axioms shuffleW_cons_inv
#print axioms leg_zone_keep
#print axioms shuffleW_wf_end
#print axioms shuffleW_zone_keep
#print axioms shuffleW_board_keep
#print axioms pull_one
#print axioms shuffle_drawsLast
#print axioms sameOrbit_factor_fwd
#print axioms sameOrbit_factor_full
