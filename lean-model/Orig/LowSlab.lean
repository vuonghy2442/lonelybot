import Orig.PairName
import Orig.BracketDecomp
import Orig.SlabEquiv
import Orig.Reach
import Orig.Classify
import Orig.HostCensus
import Orig.ForkStateSB

/-!
# Orig.LowSlab — THE LOW-SLAB SUFFICIENCY (the fork's exploration budget)

The fork's NEIGHBORHOOD is visible entirely from its LOW SLAB: every
COMMITMENT out of a fork's macro class — every `irreversibleAt` move,
the program's own commit grain (the selector `win_iff_macro`'s
decomposition commits by) — is matched by a LOW DUPLICATE: a
commitment from a class member whose covered twin has not been
founded, into the same target class.  The exploration consequence: a
solver or counter program walking the macro lattice from a fork never
has to inhabit twin-consumed states to see which classes are
reachable — the slab members enumerate the full adjacency.

THE TWIN-SIDE REFINEMENT (owner decision, 2026-10-12): the low slab of
a fork (witness `x`, fork point `x.rank.toIdx`) is the TWIN SIDE
ALONE — `rungAt w x.twin.suit ≤ x.rank.toIdx` — replacing the
earlier both-suits draft.  Within a fork's macro class the
just-landed one-founding row (`Orig/PairConfine.lean`'s door complex)
bars both pair members being founded, so the twin side carries the
whole content and x-lift members are absorbed into the slab; at the WF
grade the slab read is an ARRANGEMENT fact — the covered twin still
EXISTS in the tableau (`Orig/SlabEquiv.lean`'s
`twin_slab_tableau`, proved zero-sorry in this campaign).  The
statement of the main row below is kept BYTE-IDENTICAL (the slab
conjunct still reads `familyBelowFrontier u₀ x`; the refinement
travels through the def alone — consumers keep compiling).

* §1 `familyBelowFrontier` — the twin-side slab (the def, restated).
* §2 `fork_self_low` (proved, zero-sorry) — the fork state sits on
  its own slab: the covered twin's S-live sibling forces its suit's
  rung EXACTLY to the fork index (`canRaiseS_rung` on `x.twin`).
* §3 The commit-grade support rows (all proved, zero-sorry, carried
  verbatim): `p_run_append`, `commit_exits_class`,
  `commit_blocks_class_return`.
* §4 THE RESIDUE TREE (post probe-triage, census swap, commutation
  swap AND the 2026-10-13 finale pass): the sufficiency, routed.
  **THE EMPTY ARM** `fork_lowbridge_empty` (proved): a committing
  member already on the slab closes by itself.  **THE CLASS-LINK
  GLUE** `fork_lowbridge_commitGlue` (proved): the duplicate's commit
  grade is free from the class links alone.  THE PROVED CENSUS ROWS:
  `lowslab_draw_reversible_phase` (the deduped Phase wrapper for the
  ≤-deal draw fragment), `lowslab_pull_wf_undo` (PROMOTED at the
  probe-triage pass) with its corollary
  `lowslab_pull_never_commit_wf` (the pull arm is VOID at WF,
  theorem-grade).  LANDED AT THE FINALE (two long-pending residues
  closed, both zero-sorry at `[propext, Quot.sound]`):
  `lowslab_draw_emptyReversible` — the empty-stock draw at a
  POSITIVE step size is UNDOABLE across the whole regime: the ≤-deal
  half is the Phase wrapper's, the long-waste half is the
  recycled-arrangement block induction (`zone_loop_terminal` +
  `zone_loop_return`: the invariant `x.waste.reverse ++ x.stock = S`
  carries verbatim leg by leg, the intermediate stock length is the
  measure, the clipped terminal deal restores the arrangement
  exactly) — and `fork_lowbridge_draw` — the draw-kind replay,
  fully paid by the sibling's cleaned commutation kit
  (`chain_assembly` + `interleave_leg_conjugation`, the two public
  WF-free scaffold rows, plus this file's cycle-pin kit and the
  `EdgeKit` firing pair): the FORK ITSELF is the duplicate for
  every fired committed draw at any class member, the landing
  classes weld for free, and the old (A)/(B) case split, the
  dashed-witness transport and the wild-grade (B) gap are all
  retired.  The waste rows are now PROVED ROUTERS (the waste-shrink
  pass) over two shared named subsets: `lowslab_waste_reseat` [H —
  the cursor rail + the hot bracket at ONE slab member] and
  `lowslab_waste_targetclass` [H — the dashed-witness transport
  welding the two landings]; the waste kind's guard-refusal
  transport itself is LANDED in-file at the finale
  (`waste_head_refusal`: the shifted cursor refuses both waste
  letters outright; `witness_zone_flat`: a board-only witness
  journey carries the two-zone cells verbatim — the cursor
  coincidence's draw-free leg, and the refusal its one-way bound).
  THE NAMED RESIDUES (SIX, finale
  grades): `lowslab_top_census` [H: the seat transport banked
  upstream (`Orig/HostCensus.lean`'s ledger family); the survivors
  are the card-level bootstrap and the slab-side landing],
  `fork_lowbridge_raise` [H: transport + commit-modes banked
  (`census_tabToFound_witness`, `bare_lift_irreversibleAt`); the
  bracket's transfer mechanics landed in-file
  (`lowslab_bracket_transfer`), the σ-letter net census survives per
  the seats-vs-rungs adjudication],
  `fork_lowbridge_reveal` [H: cargo transport + commit-modes banked
  (`census_tabToTab_inr_witness`, `bare_burn_irreversibleAt`); the
  card-level re-scheduling survives], `lowslab_waste_reseat` [H: the
  shifted-cursor refusal on record as the boundary datum, the
  cursor-orbit re-scheduling onto a slab member] and
  `lowslab_waste_targetclass` [H: the per-leg dashed-witness weld],
  and `fork_lowbridge_pull` [H, WILD-REMAINDER ONLY: the WF arm
  retired into the corollary; the row survives for the WF-free
  statement's wild members].  Each residue carries a complete priced
  route with the probe evidence folded in
  (`Orig/LowSlabProbe.lean`), and NOTHING consumes the sibling's own
  residue `witness_leg_mint_confined`.  The private dispatcher
  `fork_lowbridge_elevated` (proved, zero-sorry) routes the six
  constructor arms through the assemble row.  The main head
  concludes by the empty/elevated dichotomy — its proof is a short
  routing skeleton and nothing else.

  SESSION-2 LANDINGS (2026-10-13, the take-over pass): the
  provable content still missing from the six routes' plumbing was
  extracted and LANDED (zero-sorry, §4.2.0 and the waste kit): the
  class-weld and journey-membership rows, the per-leg rung deltas,
  the rung-walk engine and — its first headline —
  `lowslab_elevation_crossing` (every elevated member is crossed
  INTO by a reversible raise of the covered twin itself, at a
  fork-exact boundary member, over an on-slab prefix); for the waste
  pair, `lowslab_pair_netcensus` (the guards at two members net the
  commit suit's letters to zero along any witnessing journey — the
  re-threading's remaining work is purely the nesting) and
  `lowslab_waste_guard_fires` (the guard fires its letter
  unconditionally; `lowslab_waste_targetclass` thereby SHRUNK to
  the bare class-mateship).  Two statement-level findings are
  recorded in the rows' docstrings per the never-force discipline:
  `lowslab_top_census` was REFUTABLE as stated (wild singleton
  class — repaired by restoring the `ForkWitness` parcel its
  docstring always meant), and the WASTE rail carries a live
  REFUTATION CANDIDATE (the raised-twin-suit commit card above the
  fork point — the refuter-first Q(B) shape — priced against
  `lowslab_waste_reseat` and the waste routers, probe certification
  pending); the six residues remain, each now reduced to its exact
  honest open content.

  SESSION-3 VERDICT (2026-10-13, the third succession — all six
  attempted, none forced): every residue's assembly was re-attempted
  against the banked arsenal; none licenses a full closure at the
  WF-free grade, and per the never-force discipline ALL SIX CARRY at
  their named grades, statements byte-frozen, fates recorded in their
  docstrings.  The load-bearing walls, now precisely named: every
  WF-free mirror kit runs into the wild COPY CORNERS the banked undos'
  premises fence (doubled seat searches, miscounted rungs), the
  upstream doors (`forkState_one_founding`, the canonical-assignment
  route, the census dichotomies) are WF-GATED while the byte-frozen
  main statement admits wild forks, and the class links would need
  the DASHED-WITNESS TRANSPORT (the Dyck re-threading) no banked
  WF-free row builds; the waste pair keeps its live D5-refutation
  candidate (probe certification the pending gate) and
  `fork_lowbridge_pull` hosts as the final honest wild-remainder
  carry.  LANDED THIS PASS, all zero-sorry (§4.1.5):
  `lowslab_fork_pair_rungs` (the fork's pair rungs, named once),
  `lowslab_class_hiddenPinned` + `lowslab_top_census_hidden` (the
  class hidden-pin — the seat census's hidden conjunct now CLOSED for
  free at every class member, that residue's first on-record shrink),
  and `lowslab_raise_commit_shape_wf` (the WF-grade commit face of a
  raise: the raised card is a lone top, the census's two commit
  species exactly).  The battery is refreshed; the sorry count stays
  exactly the six, and `fork_neighbor_lowbridge`'s profile stays
  `[propext, sorryAx, Quot.sound]` with no new inflow.

  SESSION-4 VERDICT (2026-10-13, the fourth succession — the waste
  reseat gate DISCHARGED): the session-3 pending gate — probe
  certification of the waste reseat's live D5-refutation candidate —
  is now CERTIFIED IN-FILE at decide grade: the fork board `wr_st`
  of §4.2.a.R (waste heading `5♦`, one past the fork point) satisfies
  every premise of `lowslab_waste_reseat` while its conclusion is
  unreachable (the founding guard demands the ♦ rung exactly 4 at a
  slab member the slab conjunct pins at-or-below 3), so THE ROW AS
  STATED IS FALSE and hosts at [H, REFUTED]; the certified negation
  is the zero-sorry public row `lowslab_waste_reseat_refuted`.  The
  remaining five residues carry unchanged at their recorded grades
  (statements byte-frozen); the routers and the main row's
  statements are untouched by the board (its founding letter is
  reversible there — the giveback re-fires onto the vacated twin
  seat — so the extra commit-grade premises fail at the exhibit).
  All six sorries stay exactly where the statements freeze them.

GRADE NOTE (the design decision, kept): the theorem is stated at the
PROGRAM'S OWN commit grain — `irreversibleAt`, the full no-return
notion of `Orig/Fate.lean` (plays of any grain) — not at the softer
setoid-exit grade `¬ sameOrbitSetoid.r`; the bridge row of §3 shows
the semantic grade implies the setoid exit, so the statement carries
the stronger hypothesis while remaining comparable with the class
algebra.  No WF hypothesis anywhere: the census consumption rows are
stated WF-free, with the WF-grade readings confined to the routes
(where the probe boards' regime licenses them).

House compliance: additive leaf (`Orig.PairName`,
`Orig.BracketDecomp`, `Orig.SlabEquiv` below both, plus at the
probe-triage pass the early `Orig.Reach` — for the banked WF-descent
row `step_wf` — and `Orig.Classify` — for the banked pulled-rank
discipline `wf_found_chop_toIdx`, and at the census swap pass
`Orig.HostCensus` — the sibling's proved seating ledger, itself an
additive leaf below `Orig.BracketDecomp`, so no cycle); and at the
session-4 pass `Orig.ForkStateSB` — the decidable fork-parcel door
(`forkWitnessRowSB` + its iff bridge) consumed by the reseat
refutation board alone, itself below the ALREADY
transitively-present `Orig.PairName → Orig.ForkWeaker` chain, so
again no cycle and no inflow anywhere else; every fresh
head is audited in the battery; every named residue carries a
complete route; no `Classical.choice`; the main statement is
byte-frozen. -/

/-! ## §1. The slab -/

/-- **THE LOW SLAB** — the twin-side refinement: the fork's slab is
the covered twin's pair position — the twin suit's rung sits at or
below the witness's rank index (the covered twin is not founded).
The earlier draft read both family suits; the owner's refinement
keeps the twin side alone: the just-landed one-founding row bars
both pair members being founded within one fork class, so the twin
side carries the content and the x-lift members are absorbed into
the slab, making the sufficiency independent of whether x-lifts are
realizable.  At the WF grade the read is an arrangement fact: the
twin still exists in the tableau (`Orig/SlabEquiv.twin_slab_tableau`).
The NAME is kept (byte-st stability of the main conjunct); only the
def's body refined. -/
def familyBelowFrontier (w : State) (x : Card) : Prop :=
  rungAt w x.twin.suit ≤ x.rank.toIdx

/-! ## §2. The fork sits on its own slab -/

/-- **THE SELF-SLAB ROW** — a fork state is a member of its own low
slab: the covered twin is the S-live sibling of the witness pair
(`ForkWitness`'s iff saturates `x.twin` too), so its suit's rung reads
EXACTLY the fork index (`canRaiseS_rung`), at or below itself.  The
row halved at the twin-side refinement — the x-side read is no longer
part of the slab. -/
theorem fork_self_low {st : State} {x : Card} (hx : ForkWitness st x) :
    familyBelowFrontier st x := by
  unfold familyBelowFrontier
  have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
  rw [Card.twin_rank] at h2
  exact Nat.le_of_eq h2

/-! ## §3. The commit-grade support rows -/

/-- The run-append compose: two successful runs concatenate into one
(the forward-facing companion of `Orig/Play.lean`'s split reader
`run_append_split`; needed here to join the class witness plays into
a single return play). -/
private theorem p_run_append : ∀ (a : State) (A B : List Move) (z w : State),
    a.run A = some z → z.run B = some w → a.run (A ++ B) = some w := by
  intro a A
  induction A generalizing a with
  | nil =>
      intro B z w h1 h2
      have hz : some a = some z := h1
      injection hz with hc
      subst hc
      exact h2
  | cons m rest ih =>
      intro B z w h1 h2
      obtain ⟨a₁, hs, hr⟩ := State.run_cons h1
      have h3 := ih a₁ B z w hr h2
      rw [List.cons_append]
      show (match State.step a m with
        | some st' => st'.run (rest ++ B)
        | none => none) = some w
      rw [hs]
      exact h3

/-- **THE COMMIT-CROSSING BRIDGE** — a semantic commitment exits the
setoid class: the successor of an `irreversibleAt` move is never
class-connected back, since a class connection carries a FORWARD
witness play (`sameOrbit_forward` through the setoid's symmetry)
and therefore, in particular, a legal return play — which the
no-future-read of `irreversibleAt` rules out in full generality
(plays of any grain, committed or not). -/
theorem commit_exits_class {u v : State} {m : Move}
    (hstep : State.step u m = some v)
    (hiv : irreversibleAt u m) :
    ¬ sameOrbitSetoid.r u v := by
  intro hcon
  have hrvu : sameOrbitSetoid.r v u := sameOrbitSetoid.iseqv.symm hcon
  obtain ⟨ρ, hρ⟩ := sameOrbit_forward hrvu
  exact hiv v ρ hstep (ShufflePlayW_run hρ)

/-- **THE SLAB DUPLICATE's IRREVERSIBILITY IS FREE** — whenever the
duplicate target lands in the same class as the original commitment's
successor, and the duplicate's origin rides the original's class,
any return play from the duplicate's successor composes — through
the two class witness plays — into a return play from the original
successor, against the original's `irreversibleAt`.  The row lets the
§4 residue conclude its duplicate's commit-grade without re-arguing
it: the routing only has to produce the class links. -/
theorem commit_blocks_class_return {u v u₀ v₀ : State} {m : Move}
    (hstep : State.step u m = some v)
    (hiv : irreversibleAt u m)
    (hlink : sameOrbitSetoid.r u₀ u)
    (hmatch : sameOrbitSetoid.r v₀ v)
    (hback : ∃ play, State.run v₀ play = some u₀) :
    False := by
  obtain ⟨πback, hrb⟩ := hback
  -- the class joins: v ⇝ v₀ (the match, read backward) and u₀ ⇝ u
  obtain ⟨πv, hv⟩ := sameOrbit_forward (st := v) (w := v₀)
    (sameOrbitSetoid.iseqv.symm hmatch)
  obtain ⟨πu, hu⟩ := sameOrbit_forward (st := u₀) (w := u) hlink
  -- compose the forbidden return: v ⇝ v₀ ⇝ u₀ ⇝ u
  have hmid : v₀.run (πback ++ πu) = some u :=
    p_run_append v₀ πback πu u₀ u hrb (ShufflePlayW_run hu)
  have h1 : v.run (πv ++ (πback ++ πu)) = some u :=
    p_run_append v πv (πback ++ πu) v₀ u (ShufflePlayW_run hv) hmid
  exact hiv v (πv ++ (πback ++ πu)) hstep h1

/-! ## §4. The residue tree: the sufficiency, routed -/

/-! ### §4.0. The two proved arms -/

/-- **THE EMPTY ARM** — the case where the committing member already
sits on the slab closes by itself: the duplicate IS the original
(`u₀ := u`, `m₀ := m`, `v₀ := v`); every conjunct is a hypothesis or
the setoid's own reflexivity (the class membership and the slab
membership are given; the step and the commit grade are given; the
target-class match reads `r v v` by the setoid instance's
reflexivity).  The arm carries no `ForkWitness` premise — the fork
plays no role here (honesty of the package, the `pullEscape`
lesson). -/
theorem fork_lowbridge_empty {st u v : State} {x : Card}
    (hmem : sameOrbitSetoid.r st u)
    (hslab : familyBelowFrontier u x)
    {m : Move} (hstep : State.step u m = some v)
    (hiv : irreversibleAt u m) :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      irreversibleAt u₀ m₀ ∧
      sameOrbitSetoid.r v₀ v :=
  ⟨u, m, v, hmem, hslab, hstep, hiv, sameOrbitSetoid.iseqv.1 v⟩

/-- **THE CLASS-LINK GLUE** — the duplicate's commit grade is free:
once a candidate slab member `u₀` (class-anchored at the fork) carries
a step into the target class of the original commitment's successor,
any return play from ITS successor composes — through the class
witness plays — into a forbidden return against the original's
`irreversibleAt` (`commit_blocks_class_return`'s read; the u₀-side
link to the original member derives from the two st-anchors by the
setoid's own transitivity over the symmetric reads).  This is the
mission's mechanical class-link glue: per-kind replay rows produce
membership + slab + step + match, and this row concludes the
`irreversibleAt u₀ m₀` conjunct for nothing. -/
theorem fork_lowbridge_commitGlue {st u v u₀ v₀ : State} {m m₀ : Move}
    (hmem : sameOrbitSetoid.r st u)
    (hclass₀ : sameOrbitSetoid.r st u₀)
    (hstep : State.step u m = some v)
    (hiv : irreversibleAt u m)
    (hstep₀ : State.step u₀ m₀ = some v₀)
    (hmatch : sameOrbitSetoid.r v₀ v) :
    irreversibleAt u₀ m₀ := by
  intro z play hstepz hrz
  have hzs : v₀ = z := Option.some.inj (hstep₀.symm.trans hstepz)
  subst hzs
  have hlink : sameOrbitSetoid.r u₀ u :=
    sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm hclass₀) hmem
  exact commit_blocks_class_return hstep hiv hlink hmatch ⟨play, hrz⟩

/-- **THE ROUTE HELPER** — packaging: a produced candidate (class
anchor + slab + step + target-class match, the four-line package
every per-kind replay row returns) assembles into the main
statement's five conjuncts, the commit grade arriving by the glue
row's free read. -/
private theorem fork_lowbridge_assemble {st : State} {x : Card} {u v : State} {m : Move}
    (hmem : sameOrbitSetoid.r st u)
    (hstep : State.step u m = some v)
    (hiv : irreversibleAt u m)
    (hpre : ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      sameOrbitSetoid.r v₀ v) :
    ∃ (u₁ : State) (m₁ : Move) (v₁ : State),
      sameOrbitSetoid.r st u₁ ∧
      familyBelowFrontier u₁ x ∧
      State.step u₁ m₁ = some v₁ ∧
      irreversibleAt u₁ m₁ ∧
      sameOrbitSetoid.r v₁ v := by
  obtain ⟨u₀, m₀, v₀, hc, hsl, hst, hm⟩ := hpre
  exact ⟨u₀, m₀, v₀, hc, hsl, hst,
    fork_lowbridge_commitGlue hmem hc hstep hiv hst hm, hm⟩

/-! ### §4.1. The census consumption rows (named, for the sibling swap) -/

/-- **THE PHASE-DRAW WRAPPER** `lowslab_draw_reversible_phase` (proved,
deduped) — the empty-stock draw whose whole waste fits one deal is a
state-wise no-op: the recycle reverses the waste into the stock and
the deal pays it straight back, so the empty play returns.  The
content is `Orig/Phase.lean`'s banked `draw_reversible_selfRecycleW`,
cited and instantiated here (the probe-triage dedup pass: this
fragment of the old `lowslab_draw_emptyReversible` residue is now
upstream's, not ours). -/
theorem lowslab_draw_reversible_phase {u : State}
    (hempty : u.stock = [])
    (hw : u.waste ≠ [])
    (hsize : u.waste.length ≤ u.drawStep) :
    reversibleAtW u Move.draw :=
  draw_reversible_selfRecycleW hempty hw hsize

/-- **THE ZONE-LOOP TERMINAL** (support for `zone_loop_return`) — at
an exhausted stock the loop invariant closes the state: the
reassembled waste is the arrangement's own reverse, every other
field rode verbatim, so the loop's returned state IS its origin (the
empty play returns). -/
private theorem zone_loop_terminal {x u : State} {S : List Card}
    (hds : x.drawStep = u.drawStep)
    (hstock : u.stock = ([] : List Card))
    (hw : u.waste = S.reverse)
    (hinv : x.waste.reverse ++ x.stock = S)
    (hp : x.piles = u.piles) (hf : x.found = u.found)
    (hnil : x.stock = ([] : List Card)) :
    ∃ play, x.run play = some u := by
  have hrev : x.waste.reverse = S := by
    rw [hnil, List.append_nil] at hinv
    exact hinv
  have hxu : x = u :=
    State.ext hf hp (hnil.trans hstock.symm)
      (by rw [← List.reverse_reverse x.waste, hrev, hw]) hds
  exact ⟨[], by rw [hxu]; rfl⟩

/-- **THE LONG-WASTE ZONE LOOP** (the recycled-arrangement block
induction — `lowslab_draw_emptyReversible`'s landing engine) — from
any state `x` whose two-zone cells read as one recycled arrangement of
`S` (the invariant `x.waste.reverse ++ x.stock = S`), a concatenated
play of draws returns `x` to the origin `u` (whose arrangement is the
reverse: `u.stock = []`, `u.waste = S.reverse`).

THE RECEIPT (each step banked or definitionally mechanical):

1. THE FIRE: while the stock is nonempty every draw fires
   (`plain_draw_shape`: the deal at a nonempty stock reads the stock
   alone) and peels ONE DEAL of its heads into the waste, reversed,
   onto the old waste — `dealUpTo` is the take/drop split
   (`dealUpTo_eq_take_drop`, `Orig/Play.lean`).
2. THE INVARIANT: the peeled block re-appends as the arrangement's
   next prefix chunk — `(peeled ++ x.waste).reverse ++ x.stock.drop k
   = x.waste.reverse ++ (x.stock.take k ++ x.stock.drop k) = S`
   (`List.reverse_append`, `List.reverse_reverse`, `List.append_assoc`
   and `List.take_append_drop`) — so the invariant rides verbatim
   through every leg, and with it the piles, the founds and the deal
   size (`stepDraw_piles`, `stepDraw_found`, `draw_drawStep`).
3. THE MEASURE: the intermediate stock length strictly drops by the
   positive deal size each leg (`List.length_drop`), so the fuel
   induction terminates; the terminal stock-empty case is
   `zone_loop_terminal` — the clipped take saturates and the state
   coalesces to the origin field-for-field. -/
private theorem zone_loop_return : ∀ (fuel : Nat) (x u : State) (S : List Card),
    0 < u.drawStep →
    x.drawStep = u.drawStep →
    u.stock = ([] : List Card) →
    u.waste = S.reverse →
    x.waste.reverse ++ x.stock = S →
    x.piles = u.piles →
    x.found = u.found →
    x.stock.length ≤ fuel →
    ∃ play, x.run play = some u := by
  intro fuel
  induction fuel with
  | zero =>
      intro x u S _hpos hds hstock hw hinv hp hf hlen
      exact zone_loop_terminal hds hstock hw hinv hp hf
        (by
          cases hsX : x.stock with
          | nil => rfl
          | cons d ds => rw [hsX, List.length_cons] at hlen; omega)
  | succ f ih =>
      intro x u S hpos hds hstock hw hinv hp hf hlen
      cases hstx : x.stock with
      | nil => exact zone_loop_terminal hds hstock hw hinv hp hf hstx
      | cons c cs =>
          have hx1 : 1 ≤ x.stock.length := by
            rw [hstx, List.length_cons]; omega
          have hkey : ∃ y, State.step x Move.draw = some y ∧
              y.stock = x.stock.drop x.drawStep ∧
              y.waste = (x.stock.take x.drawStep).reverse ++ x.waste := by
            refine ⟨{ x with stock := x.stock.drop x.drawStep, waste := (x.stock.take x.drawStep).reverse ++ x.waste },
              plain_draw_shape (by rw [hstx]; simp), rfl, rfl⟩
          obtain ⟨y, hfire, hys, hyw⟩ := hkey
          have hsDy : State.stepDraw x = some y := hfire
          have hinv' : y.waste.reverse ++ y.stock = S := by
            rw [hyw, hys, List.reverse_append, List.reverse_reverse,
              List.append_assoc, List.take_append_drop x.drawStep x.stock, hinv]
          have hlen' : y.stock.length ≤ f := by
            rw [hys, List.length_drop]; omega
          obtain ⟨play, hrun⟩ :=
            ih y u S hpos ((EdgeKit.stepDraw_drawStep hsDy).trans hds) hstock hw hinv'
              ((stepDraw_piles hsDy).trans hp) ((stepDraw_found hsDy).trans hf) hlen'
          exact ⟨Move.draw :: play,
            p_run_append x [Move.draw] play y u (run_one hfire) hrun⟩

/-- **THE CURSOR LOOP ROW** `lowslab_draw_emptyReversible` — LANDED at
the finale (2026-10-13, the long-pending [M] residue closed) — an
empty-stock draw at a POSITIVE step size is UNDOABLE, so a COMMITTED
draw can never fire at an empty stock in the committed regime: the
waste never fits in the recyclable dead zone (the fired draw refuses
outright when the waste is empty).

THE RECEIPT (the old route's three steps, all banked or landed):

1. DICHOTOMY AT THE DRAW: `hstep` at an empty stock forces the waste
   nonempty — the both-empty draw refuses to fire (the recycle is the
   identity and the deal at an empty stock is `none`
   (`recycle_allEmpty` + `dealStock_nil`), contradiction with the
   fired `hstep`) — and `base_draw_shape` (`Orig/Phase.lean`) reads
   the leg as one recycle then one clipped deal: the waste reverses
   into the stock and one deal peels back off it.
2. THE ≤-DEAL FRAGMENT — BANKED: the Phase wrapper
   `lowslab_draw_reversible_phase` above (the whole waste fits one
   deal: the draw restores the arrangement in place, `s₁ = u`, the
   empty play returns).
3. THE LONG-WASTE CURSOR LOOP — LANDED HERE as `zone_loop_return`:
   the block induction on the recycled arrangement (the invariant
   `x.waste.reverse ++ x.stock = S` carried verbatim leg by leg, the
   measure the intermediate stock length strictly dropping by the
   positive deal size, the terminal clipped deal saturating the take
   and restoring the pre-draw arrangement exactly), with the
   inductive draw count as the witness play from `s₁` back to `u`.
   Draws write only the two zone cells, so piles, founds and the deal
   size ride verbatim — the returned state IS the origin
   (`zone_loop_terminal`'s field-for-field close).

PROBE NOTE (`Orig/LowSlabProbe.lean`, decide-grade): the loop form is
instantiated on-board at the cursor boards — the two-leg zone loop at
`wb0`/`wbW` (`wb0_draw`/`wbW_draw`: the clipped second deal restores
the arrangement exactly, both legs `reversibleAtW` with each other as
mirrors) is this row's witness play of length one; the contrapositive
side stays on record at the lb-boards (`lb0_drawCommit` /
`lb1_drawCommit` — draws at NONEMPTY stock are pristine-grade
commitments there).  The row's consumer `fork_lowbridge_draw` needs
none of this (the cycle pin suffices for the class replay); this row
is the fired/no-op dichotomy's own [M] piece, now closed. -/
private theorem lowslab_draw_emptyReversible {u s₁ : State}
    (hds : 0 < u.drawStep)
    (hempty : u.stock = [])
    (hstep : State.step u Move.draw = some s₁) :
    reversibleAtW u Move.draw := by
  -- step 1: the both-empty refusal pins the waste nonempty
  by_cases hw : u.waste = []
  · have hsD : State.stepDraw u = some s₁ := hstep
    rw [show State.stepDraw u = State.dealStock (State.recycle u) from rfl,
      show State.recycle u = u from recycle_allEmpty u hempty hw,
      dealStock_nil u hempty] at hsD
    exact absurd hsD (by simp)
  -- step 2: the ≤-deal fragment is the banked Phase wrapper
  by_cases hsize : u.waste.length ≤ u.drawStep
  · exact lowslab_draw_reversible_phase hempty hw hsize
  -- step 3: the long-waste cursor loop — the base draw's landing is
  -- the recycled arrangement one deal in; the loop returns it to u
  have hsD : State.stepDraw u = some s₁ := hstep
  rw [base_draw_shape hempty hw] at hsD
  injection hsD with hR
  -- the base-draw landing: the recycled arrangement, one deal in
  have hsD2 : s₁.drawStep = u.drawStep := by rw [← hR]
  have hsP : s₁.piles = u.piles := by rw [← hR]
  have hsF : s₁.found = u.found := by rw [← hR]
  have hsInv : s₁.waste.reverse ++ s₁.stock = u.waste.reverse := by
    rw [← hR]
    show ((u.waste.reverse.take u.drawStep).reverse ++ ([] : List Card)).reverse
        ++ u.waste.reverse.drop u.drawStep = u.waste.reverse
    rw [List.reverse_append, List.reverse_nil, List.reverse_reverse,
      List.nil_append, List.take_append_drop]
  obtain ⟨play, hrun⟩ :=
    zone_loop_return s₁.stock.length s₁ u u.waste.reverse hds hsD2 hempty
      (show u.waste = u.waste.reverse.reverse from (List.reverse_reverse u.waste).symm)
      hsInv hsP hsF (Nat.le_refl _)
  exact ⟨s₁, play, hstep, hrun⟩

/-! ### §4.1.5. The session-3 pins (the third succession)

Small banked supports, all zero-sorry, landing per the isolating
discipline the pieces the six routes' docstrings were re-deriving per
call; nothing here moves a residue's grade (the six carry, fates
recorded in their docstrings) — the rows are landed for the sequel
passes, and two of the four (the class hidden-pin pair) SHRINK a named
residue's honest open content on record. -/

/-- **THE FORK'S PAIR RUNGS** (WF-free) — both family suits' rungs at
the fork itself read the fork point EXACTLY: the two S-live pair
cards' `canRaiseS_rung` reads, the twin's through `Card.twin_rank`.
The pair of reads the routes' elevated-census steps re-derive per
call, named once; the fork's own self-slab row (`fork_self_low`) is
the ≤-read of the second conjunct. -/
private theorem lowslab_fork_pair_rungs {st : State} {x : Card}
    (hx : ForkWitness st x) :
    rungAt st x.suit = x.rank.toIdx ∧
      rungAt st x.twin.suit = x.rank.toIdx := by
  refine ⟨canRaiseS_rung ((hx.1 x).mp (Or.inl rfl)), ?_⟩
  have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
  rwa [Card.twin_rank] at h2

/-- **THE CLASS HIDDEN-PIN** (WF-free) — class-mates share the fork's
per-pile hidden decks: the pin is banked (`shuffle_hiddenPinned`)
along any witness shuffle, and the setoid's rev-closure hands a
forward witness journey out of the membership itself
(`sameOrbit_forward`).  This is the reveal row's HIDDEN PIN step as a
named read, and the seat census's hidden conjunct's whole content. -/
private theorem lowslab_class_hiddenPinned {st u : State}
    (hmem : sameOrbitSetoid.r st u) :
    ∀ a, (u.piles a).hidden = (st.piles a).hidden := by
  obtain ⟨τ, hτ⟩ := sameOrbit_forward hmem
  exact shuffle_hiddenPinned hτ

/-- **THE SEAT CENSUS'S HIDDEN CONJUNCT, CLOSED** (WF-free) — at any
class member the demanded anchor's hidden deck equals the fork's, so
any two members' decks agree: `lowslab_top_census`'s hidden conjunct
is FREE at EVERY class member and the residue's open content shrinks
to exactly its two named survivors — the card-level presentation of
`c` and the slab-side landing. -/
private theorem lowslab_top_census_hidden {st u d : State} {k : Anchor}
    (hmem : sameOrbitSetoid.r st u)
    (hclass : sameOrbitSetoid.r st d) :
    (d.piles k).hidden = (u.piles k).hidden := by
  rw [lowslab_class_hiddenPinned hmem k]
  exact lowslab_class_hiddenPinned hclass k

/-- **THE WF-GRADE COMMIT FACE OF A RAISE** — at a WF commit site an
IRREVERSIBLE `tabToFound` has exactly the census's two commit
species: the raised card is a LONE face-up top (`faceUp = [c]`), over
a HIDDEN deck it strips (the reveal species) or over a completely
BARE seat at a NON-KING (the §2 census's own graded species).  Every
other firing shape is reversible at the site — the under-seat arm
through the banked one-move undo (`tabToFound_undo_under`, its search
premise exact at WF through `pileOfTop_eq_some_iff`, its fit premise
through the WF run discipline), the bare king through
`tabToFound_undo_bare` — and a reversible firing contradicts `hiv`.
The row pins the commit card's exact arrangement face for the raise
row's seat re-fire and the waste rail's hot bracket.  The WF premise
is honest: at a wild site the same undos' premises name real corners
(doubled seat searches, misfit stacks — the fences
`foundToTab_undo`'s docstring records), so the WF-free statement
grades stay exactly where they were and the row is landed for the
sequels (not consumed by a residue here). -/
private theorem lowslab_raise_commit_shape_wf {u v : State} {c : Card}
    (hwfu : u.WF)
    (hstep : State.step u (Move.tabToFound c) = some v)
    (hiv : irreversibleAt u (Move.tabToFound c)) :
    ∃ a, u.pileOfTop c = some a ∧ (u.piles a).faceUp = [c] ∧
      ((u.piles a).hidden ≠ [] ∨
        ((u.piles a).hidden = [] ∧ c.rank ≠ Rank.king)) := by
  obtain ⟨-, k, hpa, hs⟩ := step_tabToFound_inv hstep
  obtain ⟨-, hlast⟩ := pileOfTop_top hpa
  have hsnoc : (u.piles k).faceUp =
      chop (u.piles k).faceUp ++ [c] := lastOf_chop hlast
  by_cases hchop : chop (u.piles k).faceUp = []
  · -- the lone-top read, then the two species
    have hface : (u.piles k).faceUp = [c] := by
      rw [hsnoc, hchop, List.nil_append]
    refine ⟨k, hpa, hface, ?_⟩
    rcases Decidable.em ((u.piles k).hidden = []) with hhid | hhid
    · refine Or.inr ⟨hhid, ?_⟩
      rcases Decidable.em (c.rank = Rank.king) with hk | hk
      · exact absurd (tabToFound_undo_bare hstep hpa hchop hhid hk)
          (not_reversibleAtW_of_irreversibleAt hiv)
      · exact hk
    · exact Or.inl hhid
  · -- the under-seat shape is reversible at WF: the one-move undo returns
    exfalso
    have hrok : runOK (chop (u.piles k).faceUp ++ [c]) = true := by
      rw [← hsnoc]
      exact hwfu.2.1 k
    obtain ⟨z, hz, hsit⟩ := runOK_snoc_sit hchop hrok
    have hwfv : v.WF := step_wf hwfu hstep
    have hvpa : (v.piles k).faceUp = chop (u.piles k).faceUp := by
      have hpilk : v.piles k =
          Pile.afterRunRemoved (u.piles k) (chop (u.piles k).faceUp) := by
        rw [hs]
        show (if k = k then
            Pile.afterRunRemoved (u.piles k) (chop (u.piles k).faceUp)
          else u.piles k) = _
        rw [ite_eq_left rfl]
      rw [hpilk, afterRunRemoved_ne hchop]
    have hvtopa : (v.piles k).top = some z := by
      rw [show (v.piles k).top = lastOf ((v.piles k).faceUp) from rfl, hvpa]
      exact hz
    have hsearch : v.pileOfTop z = some k :=
      (pileOfTop_eq_some_iff hwfv).2 hvtopa
    exact absurd (tabToFound_undo_under hstep hpa hz hsit hsearch)
      (not_reversibleAtW_of_irreversibleAt hiv)

/-- **THE SEAT CENSUS** `lowslab_top_census` [H, SHRUNK at the census
swap pass] — the elevation mechanism's arrangement face, the
takeback-checklist executability the raise-like and reveal replays
consume: a face-up card at or below the fork point that TOPS a pile at
an elevated member is re-presentable — topping a pile, over the same
hidden deck — at some member of the slab in the same class.

ROUTE (post-census-swap; the arrangement transport is now BANKED
upstream in `Orig/HostCensus.lean`, and what survives is the
card-level bootstrap plus the slab-side landing):

1. THE HIDDEN PIN (unchanged, banked): `shuffle_hiddenPinned` — every
   class member's per-pile hidden deck equals the fork's.
2. THE SEAT TRANSPORT — BANKED, CONSUMED (the sibling's proved rows,
   none riding its residue): the per-cell HOST CENSUS ledger
   (`seatLedger_pair`, `play_census_ledger`) telescopes any play
   exactly (`census(end) + burns = census(start) + mints`), the
   leg-letters discipline (`witness_leg_letters`) bars the waste
   letters, the cargo legs are census-NEUTRAL cell-for-cell
   (`census_tabToTab_inr_witness`, `census_tabToTab_inl`), the ride
   raises mint only the exposed below-card's cell while burning the
   raised card's (`census_tabToFound_witness`), the pulls transfer
   host-to-pulled cell (`census_foundToTab_inr`, `census_step_draw`
   for the draws), and over the class's own round trip the budgets
   CANCEL with no capacity issued beyond the arrangement profile —
   THE OWNER'S BET (`excursion_issues_noNewSeat` +
   `roundtrip_census_repay`).  This is the old "exhumable set is
   arrangement-pinned" swap point (A): LANDED.  DISCIPLINE: none of
   the consumed rows rides the sibling's named residue
   `witness_leg_mint_confined` (per-leg mint confinement) — the
   ledger rows and `excursion_issues_noNewSeat` are residue-free
   per the sibling's own audit.
3. THE SURVIVING CONTENT [the row's honest remainder, both parts
   still open]:
   (a) CARD-LEVEL BOOTSTRAP — the census counts CELLS, not cards:
   from "`c`'s cell is carried (or repaid) along the class's
   journeys" to "`c` ITSELF tops a pile at the said member" —
   includes naming WHICH member's journey the transport rides and
   the wild-corner card-identity discipline.
   (b) THE SLAB-SIDE LANDING — descending to a member whose TWIN
   side is back under the frontier (the rung ledger
   `witness_rung_census` + `fork_self_low` as before): the census
   is deliberately blind to rungs, so the slab selection stays
   this tree's own.
4. THE HIDDEN CONJUNCT: free once the target member is chosen (the
   pin of step 1, instantiated on the same journey).

PROBE NOTE (Orig/LowSlabProbe.lean, decide-grade): the transaction
rules got their decided witness chains on the `lb0`-economy and no
stress-counterexample was found; the hidden-pin face is theorem-grade
(`shuffle_hiddenPinned`, instantiated at the boards).

HOSTCENSUS POST-SWAP: swap point (A) is CONSUMED (step 2); swap point
(B) (the takeback host's re-presentation) is PARTIALLY banked — the
under-raise's exposed host is now census-accounted
(`census_tabToFound_witness`: opposite family, raised index + 1,
unfounded) — so (B) reduces to the same card-level bootstrap of (a).
POST-COMMUTATION-SWAP: ASSESSED — no further license: the congruence
rows transport `boardEq` pairs (the draw's blindness), while this
row's card-level bootstrap crosses ρ-images.  Consumers:
`fork_lowbridge_raise` step 4 and
`fork_lowbridge_reveal` step 3.

FINALE ASSESSMENT (2026-10-13, priced shrink — the canonical-form
alternative priced and declined this pass): the TWIN-BLIND datum is
on record (§12(a) of `Orig/LowSlabProbe.lean`, `r2_censusBlind`:
two boards whose (red, 3) cell censuses are IDENTICAL — ONE top
either way — while the TWIN holding the cell differs), so the
card-level bootstrap is irreducible to cell data: the route must
ride the one-founding door (`Orig/PairConfine.lean`: both pair
members cannot be founded within one fork class — the twin-side
refinement's own rationale) for the twin separation, then name the
member whose journey carries the cell — which is the canonical-form
route's own shape (the class contains its `canon` form,
`canon_in_class` in `Orig/Canonical.lean`; the canonicalizer keeps
the zone cells — `canon_stock`/`canon_waste`/`canon_drawStep`; the
realization of the seat assignment is the last priced step before
the slab-side descent), PRICED [H] against the confluence program
and not pursued this pass.  The survivors are unchanged and named:
(a) the card-level bootstrap, (b) the slab-side landing (the rung
ledger `witness_rung_census` + `fork_self_low`); the waste seat
rail's landing-base consult rides the same bootstrap.

SESSION-2 REPAIR (2026-10-13, the take-over pass): the row AS
ORIGINALLY STATED — no `ForkWitness` parcel, WF-free, rank-free —
was REFUTABLE by hand at a wild singleton class: take `st = u` with
`found heart = [K♥]`, the lone ace CA topping p1, an empty zone,
`x = A♦` and `c = CA` — all four premises hold (`helev` reads the
heart rung `1 > 0`; `hlow`/`htop` read the ace) while `st`'s only
legal moves are the committed `tabToFound CA` and `foundToTab K♥`
(neither has a return play), so the class is the singleton `{st}`:
every member is elevated, NO slab member exists, and the conclusion
  dies.  The fork parcel — this docstring's own "fork point" reading,
  and the shape the raise/reveal consumers carry anyway — is restored
  as a premise (`ForkWitness st x` first); the statement is now the
  intended one, and the survivors (a)/(b) above remain its honest open
  content.

  SESSION-3 PIN (2026-10-13, the third succession): the HIDDEN
  conjunct of the conclusion is now CLOSED at term grade and for FREE
  at EVERY class member — the banked `lowslab_class_hiddenPinned`
  (`shuffle_hiddenPinned` instanced at the membership's own forward
  witness journey) reads every class member's per-pile hidden deck as
  the fork's, and `lowslab_top_census_hidden` welds the demanded
  anchor's deck to `u`'s at any candidate `d`.  The row's open
  content shrinks to exactly the two named survivors: (a) the
  card-level presentation of `c` itself at one slab-side class member
  (`lastOf (d.piles k).faceUp = some c` — the §12(a) twin-blindness
  keeps this from all cell data), and (b) the slab-side landing; the
  canonical-assignment route stays priced [H] as the finale assessed,
  and the row CARRIES at [H], statement byte-frozen. -/
private theorem lowslab_top_census {st u : State} {x : Card} {c : Card}
    (hx : ForkWitness st x)
    (hmem : sameOrbitSetoid.r st u)
    (helev : ¬ familyBelowFrontier u x)
    (hlow : c.rank.toIdx ≤ x.rank.toIdx)
    (htop : ∃ a, lastOf (u.piles a).faceUp = some c) :
    ∃ (d : State) (k : Anchor),
      sameOrbitSetoid.r st d ∧
      familyBelowFrontier d x ∧
      lastOf (d.piles k).faceUp = some c ∧
      (d.piles k).hidden = (u.piles k).hidden := by
  sorry

/-- **THE WF-GRADE PULL UNDO** `lowslab_pull_wf_undo` [PROMOTED at the
probe-triage pass: former [M] residue, now a PROVED row] — at a WF
state the foundation giveback always carries a one-move mirror: the
undo row's three local premises are all WF-derivable.

ROUTE (complete; every step banked — the probe's twin-takeback and
king-giveback rows are the worked examples, kernel-verified):

1. THE RANK DISCIPLINE (`hnext`): the popped card's own index is the
   chopped foundation's length — the banked WF arithmetic
   `wf_found_chop_toIdx` (`Orig/Classify.lean`), read off the step's
   own `foundTop` guard (`step_foundToTab_inv`).
2. THE SEARCH PIN (`hsearch`): the successor is WF (`step_wf`,
   `Orig/Reach.lean`), and the top search is exact at WF
   (`pileOfTop_eq_some_iff`, `Orig/Integrity.lean`): it answers
   exactly the seat the placement wrote:
   * `b = inl a`: `canPlace_inl` guards the empty seat and
     `putCard_piles_inl` writes the singleton pile the search then
     finds;
   * `b = inr z`: `canPlace_inr` locates the base pile and
     `putCard_piles_inr` appends to it — the new top, found again.
3. THE SEAT (`hseat`): the very same seat, read directly off the
   placement guard of step 2.
4. `foundToTab_undo` (`Orig/Irreversible.lean`) assembles the
   one-move mirror — reversible full-stop at every WF member. -/
theorem lowslab_pull_wf_undo {u s₁ : State} {c : Card} {b : Base}
    (hwfu : u.WF)
    (hstep : State.step u (Move.foundToTab c b) = some s₁) :
    reversibleAtW u (Move.foundToTab c b) := by
  obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
  -- step 1: the rank discipline, off the step's own foundTop read
  have hnext : (chop (u.found c.suit)).length = c.rank.toIdx :=
    wf_found_chop_toIdx hwfu (by rw [htop, hc'c])
  -- the successor is WF, so the top search is exact there
  have hwf₁ : s₁.WF := step_wf hwfu hstep
  cases b with
  | inl a =>
      -- the empty-seat write, read through the successor's record
      have hspleq : s₁.piles =
          (fun a' => if a' = a then ⟨[], [c]⟩
            else (u.setFound c.suit (chop (u.found c.suit))).piles a') := by
        rw [hs]
        exact putCard_piles_inl _ c a
      have htopa : (s₁.piles a).top = some c := by
        rw [hspleq]
        cases a <;> rfl
      exact foundToTab_undo hstep hnext
        ((pileOfTop_eq_some_iff hwf₁).2 htopa) (Or.inl rfl)
  | inr z =>
      obtain ⟨k₀, hpo, -⟩ := canPlace_inr hcp
      -- the located base pile, read through the setFound record
      -- (its pile fields are carried verbatim, so the search is the same)
      have hhold : (u.setFound c.suit (chop (u.found c.suit))).pileOfTop z
          = some k₀ := hpo
      have hspleq : s₁.piles =
          (fun a' => if a' = k₀ then
              { (u.setFound c.suit (chop (u.found c.suit))).piles k₀ with
                faceUp := ((u.setFound c.suit (chop (u.found c.suit))).piles k₀).faceUp ++ [c] }
            else (u.setFound c.suit (chop (u.found c.suit))).piles a') := by
        rw [hs]
        exact putCard_piles_inr _ c z k₀ hhold
      have htopk : (s₁.piles k₀).top = some c := by
        rw [hspleq]
        cases k₀ <;> exact lastOf_snoc
      exact foundToTab_undo hstep hnext
        ((pileOfTop_eq_some_iff hwf₁).2 htopk) (Or.inr ⟨z, rfl, hpo⟩)

/-- **THE PULL NEVER-COMMITS COROLLARY** `lowslab_pull_never_commit_wf`
(proved at the probe-triage pass) — at a WF member of any class, a
foundation giveback is NEVER a commitment: the promoted undo row's
witness play contradicts the no-future-read outright.  This row
retires the WF arm of the pull-kind residue: the vacuity the probe
circumstantially searched for (twin takeback, king giveback) is now
theorem-grade. -/
theorem lowslab_pull_never_commit_wf {u s₁ : State} {c : Card} {b : Base}
    (hwfu : u.WF)
    (hstep : State.step u (Move.foundToTab c b) = some s₁) :
    ¬ irreversibleAt u (Move.foundToTab c b) := by
  intro hiv
  obtain ⟨s₁', play, hstep', hrun⟩ := lowslab_pull_wf_undo hwfu hstep
  exact absurd hrun (hiv s₁' play hstep')

/-! ### §4.2. The per-kind replay rows -/

/-- **THE BRACKET TRANSFER** (the rung bracket's mechanics, isolated
at the finale per the ladder): a witness journey whose `σ`-letter
raises and pulls NET TO ZERO carries the `σ`-rung VERBATIM from
source to landing — the one mechanical leg of the raise row's
bracket (`rungAt d c.suit = rungAt u c.suit`) and of the waste
rail's hot bracket, both thereby reduced to their honest open bit:
the `σ`-letter NET CENSUS itself (no banked row nets `raisesOf`
against `pullsOf` for the commit suit — the benign probe boards
read zero there; a higher pair-suit commit is the live
counterexample family).  The transfer is one read of the rung
ledger (`witness_rung_census`, `Orig/BracketDecomp.lean`:
`rungAt w σ + pullsOf ρ σ = rungAt st σ + raisesOf ρ σ`). -/
private theorem lowslab_bracket_transfer {st u : State} {c : Card} {ρ : List Move}
    (hρ : ShufflePlayW st ρ u)
    (hnet : raisesOf ρ c.suit = pullsOf ρ c.suit) :
    rungAt st c.suit = rungAt u c.suit := by
  have h := witness_rung_census hρ c.suit
  omega

/-- **THE SLIDE's BOARD RE-FIRE** (the reveal row's mechanical leg,
isolated at the finale per the ladder): the reveal slide `tabToTab
c b` IS A BOARD MOVE — every guard consults piles only
(`pileHolding`, `canPlace`/`pileOfTop`, the run data), no foundation
and no zone cell — so at any member BOARD-EQUAL to the commit site
(`boardEq`: equal piles and equal founds) the SAME slide re-fires
and lands BOARD-EQUAL to the commit's landing.  The row is the
specialization of the sibling's `step_congr_board` at the third
`boardMove` arm; the reveal row's open content is thereby sharpened
to its honest bit: producing the BOARD-EQUAL slab member that
presents the run head (or its counterpart-slide variant) — the
card-level re-scheduling through the defusing inventory — plus the
same-fit guard assembly. -/
private theorem lowslab_slide_board_refire {u d u' : State} {c : Card} {b : Base}
    (hstep : State.step u (Move.tabToTab c b) = some u')
    (hboard : boardEq u d) :
    ∃ d', State.step d (Move.tabToTab c b) = some d' ∧ boardEq u' d' :=
  step_congr_board hboard (Or.inr (Or.inr ⟨c, b, rfl⟩)) hstep

/-! ### §4.2.0. The journey mechanism rows (the take-over pass, proved)

The per-kind routes' steps 1-2 (THE ELEVATED READ and THE CLASS
ANCHOR) priced a piece of mechanics every one of them re-derived per
call: that a witness journey's members are class-mates of its
origin (per-leg class weld, the round-trip engine pattern), and that
a fork-hovering journey out to an elevated member must CROSS the
fork threshold on a RAISE leg alone — the covered twin raising
ITSELF, at a boundary member whose twin rung reads the fork point
EXACTLY, over a prefix that never leaves the slab.  Both rows land
here, zero-sorry, over the public banked rows alone (`witness_rung_census`
consumed at the wrapper's callers; `rungAt` arithmetic by the step
inversions).  The private copies follow the house dedup discipline
(the `Orig/HostCensus.lean` originals are themselves private). -/

/-- The round-trip engine (private per-file copy of the loop-closure
row: a play from `x` landing at `w`, spliced with any play back
from `w` to `x`, is a witness shuffle `x ⇝ w`). -/
private theorem lowslab_shuffleW_of_round : ∀ (σ : List Move) (x w : State),
    x.run σ = some w → ∀ ρ : List Move, w.run ρ = some x →
      ShufflePlayW x σ w := by
  intro σ
  induction σ with
  | nil =>
      intro x w hσ ρ hρ
      have hxw : some x = some w := hσ
      injection hxw with hx
      rw [hx]
      exact .nil w
  | cons p rest ih =>
      intro x w hσ ρ hρ
      obtain ⟨y, hp, hrest⟩ := State.run_cons hσ
      refine .cons ⟨y, rest ++ ρ, hp, run_split rest y w ρ x hrest hρ⟩ hp ?_
      exact ih y w hrest (ρ ++ [p]) (run_split ρ w x [p] y hρ (run_one hp))

/-- The class weld of a reversible leg (private per-file copy): a
witness-reversible leg stays inside the macro class. -/
private theorem lowslab_class_leg {st s₁ : State} {m : Move}
    (hrev : reversibleAtW st m) (hstep : State.step st m = some s₁) :
    sameOrbitSetoid.r st s₁ := by
  obtain ⟨s₁', play, hstep', hrun⟩ := hrev
  have hs : s₁' = s₁ := Option.some.inj (hstep'.symm.trans hstep)
  rw [hs] at hrun
  show RevEqW s₁ st
  exact ⟨play, lowslab_shuffleW_of_round play s₁ st hrun [m] (run_one hstep),
    [m], .cons ⟨s₁, play, hstep, hrun⟩ hstep (.nil s₁)⟩

/-- Every member a witness journey reaches is a class-mate of the
journey's origin — the mechanical half of every route's CLASS ANCHOR
step. -/
private theorem lowslab_journey_class {st z : State} {ρ : List Move}
    (hρ : ShufflePlayW st ρ z) : sameOrbitSetoid.r st z := by
  induction hρ with
  | nil s => exact sameOrbitSetoid.iseqv.1 s
  | @cons s m s₁ rest w hrev hstep hrest ih =>
      exact sameOrbitSetoid.iseqv.trans (lowslab_class_leg hrev hstep) ih

/-- **THE PER-LEG RUNG DELTAS** (private kit) — the step-guard
arithmetic any rung-walk over witness journeys consumes: draws and
slides write no foundation row; a raise lifts exactly its own suit's
rung by one; a pull lowers exactly its own suit's rung by one (the
popped row's snoc shape, `lastOf_chop`). -/
private theorem lowslab_rung_delta_draw {s s' : State}
    (hstep : State.step s Move.draw = some s') (σ : Suit) :
    rungAt s' σ = rungAt s σ := by
  have hf : s'.found = s.found := stepDraw_found hstep
  show (s'.found σ).length = (s.found σ).length
  rw [hf]

private theorem lowslab_rung_delta_tabToTab {s s' : State} {c : Card} {b : Base}
    (hstep : State.step s (Move.tabToTab c b) = some s') (σ : Suit) :
    rungAt s' σ = rungAt s σ := by
  obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv hstep
  show (s'.found σ).length = (s.found σ).length
  have h1 : s'.found σ =
      (s.setPile a (Pile.afterRunRemoved (s.piles a)
        (below c (s.piles a).faceUp))).found σ := by
    rw [hs, putRun_found]
  rw [h1, congrFun (setPile_found s a _) σ]

private theorem lowslab_rung_delta_tabToFound {s s' : State} {c : Card}
    (hstep : State.step s (Move.tabToFound c) = some s') :
    rungAt s' c.suit = rungAt s c.suit + 1 ∧
      ∀ σ, σ ≠ c.suit → rungAt s' σ = rungAt s σ := by
  obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
  obtain ⟨hself, hothers, -⟩ := tabToFound_found_trio (a := a) hs
  refine ⟨?_, ?_⟩
  · show (s'.found c.suit).length = (s.found c.suit).length + 1
    rw [hself, List.length_append]
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  · intro σ hσ
    show (s'.found σ).length = (s.found σ).length
    rw [hothers σ hσ]

private theorem lowslab_rung_delta_foundToTab {s s' : State} {c : Card} {b : Base}
    (hstep : State.step s (Move.foundToTab c b) = some s') :
    rungAt s' c.suit + 1 = rungAt s c.suit ∧
      ∀ σ, σ ≠ c.suit → rungAt s' σ = rungAt s σ := by
  obtain ⟨c', htop, hc'c, -, hs⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  have hf : s'.found c.suit = chop (s.found c.suit) := by
    rw [hs, putCard_found, setFound_found_self]
  have hsnoc : s.found c.suit = chop (s.found c.suit) ++ [c] :=
    lastOf_chop htop
  have hlen : (s.found c.suit).length
      = (chop (s.found c.suit)).length + 1 := by
    have h := congrArg List.length hsnoc
    rw [List.length_append] at h
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  refine ⟨?_, ?_⟩
  · show (s'.found c.suit).length + 1 = (s.found c.suit).length
    rw [hf]
    omega
  · intro σ hσ
    show (s'.found σ).length = (s.found σ).length
    have h1 : s'.found σ = (s.setFound c.suit (chop (s.found c.suit))).found σ := by
      rw [hs, putCard_found]
    rw [h1]
    exact congrArg List.length (setFound_found_ne hσ)

/-- **THE RUNG-WALK CROSSING ENGINE** (private) — a witness journey
whose ends read one suit's rung as `≤ k` and `> k` must cross the
threshold `k` on a RAISE leg alone: the leg is `tabToFound e` of the
threshold suit with `e.rank.toIdx` AT the threshold (the raise fires
`nextUp`), at a member whose suit-rung is EXACTLY `k`, and every
prefix landing reads at-or-below `k`.  Pure walk arithmetic over the
per-leg deltas — no census, no WF, no class analysis. -/
private theorem lowslab_rung_walk {τ : Suit} {k : Nat} :
    ∀ {s z : State} {ρ : List Move},
      ShufflePlayW s ρ z →
      rungAt s τ ≤ k → k < rungAt z τ →
      ∃ (e : Card) (w w₁ : State) (π rest : List Move),
        ρ = π ++ Move.tabToFound e :: rest ∧
        ShufflePlayW s π w ∧
        rungAt w τ = k ∧
        e.suit = τ ∧
        e.rank.toIdx = k ∧
        State.step w (Move.tabToFound e) = some w₁ ∧
        reversibleAtW w (Move.tabToFound e) ∧
        ShufflePlayW w₁ rest z ∧
        (∀ (pre post : List Move), π = pre ++ post →
          ∀ y, s.run pre = some y → rungAt y τ ≤ k) := by
  intro s z ρ h
  induction h with
  | nil s₀ =>
      intro hs hk
      exact absurd hk (by omega)
  | @cons s₀ m s₁ rest z₀ hrev hstep hrest ih =>
      intro hs hk
      obtain hmd | ⟨c, hc⟩ | ⟨c, bb, hc⟩ | ⟨c, bb, hc⟩ :=
        witness_leg_letters hstep hrev
      · -- draw: the rung rides verbatim; the walk continues
        subst hmd
        obtain ⟨e, w, w₁, π, rest', hd, hπ, hline, hes, her, hcr, hrv, htl,
          hpre⟩ :=
          ih (by
              have hcarry := lowslab_rung_delta_draw hstep τ
              omega) hk
        refine ⟨e, w, w₁, Move.draw :: π, rest', ?_, ?_, hline, hes, her, hcr,
          hrv, htl, ?_⟩
        · rw [hd, List.cons_append]
        · exact ShufflePlayW.cons hrev hstep hπ
        · intro pre post hpp y hrun
          cases pre with
          | nil =>
              rw [List.nil_append] at hpp
              subst post
              have hy : y = s₀ := by
                have h2 : (some s₀ : Option State) = some y := hrun
                injection h2 with hcon
                exact hcon.symm
              rw [hy]
              exact hs
          | cons p t =>
              rw [List.cons_append] at hpp
              injection hpp with hp htl2
              subst hp
              obtain ⟨smid, hsd, hrt⟩ := State.run_cons hrun
              have hsm : smid = s₁ := Option.some.inj (hsd.symm.trans hstep)
              rw [hsm] at hrt
              exact hpre t post htl2 y hrt
      · -- raise: the only letter that can cross
        subst hc
        obtain ⟨hΔ, hoΔ⟩ := lowslab_rung_delta_tabToFound hstep
        by_cases hup : rungAt s₁ τ ≤ k
        · -- no crossing yet; carry the walk
          obtain ⟨e, w, w₁, π, rest', hd, hπ, hline, hes, her, hcr, hrv, htl,
            hpre⟩ :=
            ih hup hk
          refine ⟨e, w, w₁, Move.tabToFound c :: π, rest', ?_, ?_, hline, hes,
            her, hcr, hrv, htl, ?_⟩
          · rw [hd, List.cons_append]
          · exact ShufflePlayW.cons hrev hstep hπ
          · intro pre post hpp y hrun
            cases pre with
            | nil =>
                rw [List.nil_append] at hpp
                subst post
                have hy : y = s₀ := by
                  have h2 : (some s₀ : Option State) = some y := hrun
                  injection h2 with hcon
                  exact hcon.symm
                rw [hy]
                exact hs
            | cons p t =>
                rw [List.cons_append] at hpp
                injection hpp with hp htl2
                subst hp
                obtain ⟨smid, hsd, hrt⟩ := State.run_cons hrun
                have hsm : smid = s₁ :=
                  Option.some.inj (hsd.symm.trans hstep)
                rw [hsm] at hrt
                exact hpre t post htl2 y hrt
        · -- the crossing is here: suit forced, rank pinned by the guard
          by_cases hcs : c.suit = τ
          · rw [hcs] at hΔ hoΔ
            obtain ⟨hn, -, -, -⟩ := step_tabToFound_inv hstep
            have hrung : rungAt s₀ τ = k := by omega
            have herk : c.rank.toIdx = k := by
              have hnext : c.rank.toIdx = rungAt s₀ c.suit := of_decide_eq_true hn
              rw [hcs, hrung] at hnext
              exact hnext
            refine ⟨c, s₀, s₁, [], rest, rfl, ShufflePlayW.nil s₀, hrung, hcs,
              herk, hstep, hrev, hrest, ?_⟩
            intro pre post hpp y hrun
            cases pre with
            | nil =>
                rw [List.nil_append] at hpp
                subst post
                have hy : y = s₀ := by
                  have h2 : (some s₀ : Option State) = some y := hrun
                  injection h2 with hcon
                  exact hcon.symm
                rw [hy]
                exact hs
            | cons p t => exact absurd hpp (by simp)
          · exfalso
            have hcar : rungAt s₁ τ = rungAt s₀ τ := hoΔ τ (fun hcon => hcs hcon.symm)
            omega
      · -- pull: the rung only falls; the walk continues
        subst hc
        obtain ⟨hΔ, hoΔ⟩ := lowslab_rung_delta_foundToTab hstep
        have hs₁ : rungAt s₁ τ ≤ k := by
          by_cases hcs : τ = c.suit
          · rw [← hcs] at hΔ
            omega
          · have hcar : rungAt s₁ τ = rungAt s₀ τ :=
              hoΔ τ (fun hcon => hcs hcon)
            omega
        obtain ⟨e, w, w₁, π, rest', hd, hπ, hline, hes, her, hcr, hrv, htl,
          hpre⟩ :=
          ih hs₁ hk
        refine ⟨e, w, w₁, Move.foundToTab c bb :: π, rest', ?_, ?_, hline, hes,
          her, hcr, hrv, htl, ?_⟩
        · rw [hd, List.cons_append]
        · exact ShufflePlayW.cons hrev hstep hπ
        · intro pre post hpp y hrun
          cases pre with
          | nil =>
              rw [List.nil_append] at hpp
              subst post
              have hy : y = s₀ := by
                have h2 : (some s₀ : Option State) = some y := hrun
                injection h2 with hcon
                exact hcon.symm
              rw [hy]
              exact hs
          | cons p t =>
              rw [List.cons_append] at hpp
              injection hpp with hp htl2
              subst hp
              obtain ⟨smid, hsd, hrt⟩ := State.run_cons hrun
              have hsm : smid = s₁ := Option.some.inj (hsd.symm.trans hstep)
              rw [hsm] at hrt
              exact hpre t post htl2 y hrt
      · -- slide: the rung rides verbatim; the walk continues
        subst hc
        obtain ⟨e, w, w₁, π, rest', hd, hπ, hline, hes, her, hcr, hrv, htl,
          hpre⟩ :=
          ih (by
              have hcarry := lowslab_rung_delta_tabToTab hstep τ
              omega) hk
        refine ⟨e, w, w₁, Move.tabToTab c bb :: π, rest', ?_, ?_, hline, hes,
          her, hcr, hrv, htl, ?_⟩
        · rw [hd, List.cons_append]
        · exact ShufflePlayW.cons hrev hstep hπ
        · intro pre post hpp y hrun
          cases pre with
          | nil =>
              rw [List.nil_append] at hpp
              subst post
              have hy : y = s₀ := by
                have h2 : (some s₀ : Option State) = some y := hrun
                injection h2 with hcon
                exact hcon.symm
              rw [hy]
              exact hs
          | cons p t =>
              rw [List.cons_append] at hpp
              injection hpp with hp htl2
              subst hp
              obtain ⟨smid, hsd, hrt⟩ := State.run_cons hrun
              have hsm : smid = s₁ := Option.some.inj (hsd.symm.trans hstep)
              rw [hsm] at hrt
              exact hpre t post htl2 y hrt

/-- **THE ELEVATION CROSSING** `lowslab_elevation_crossing` (
zero-sorry, the take-over pass) — the mechanical content the
raise/reveal/waste/pull routes' steps 1-2 re-derive per call, banked
as one row: from any witness journey between a FORK and an ELEVATED
class member (the twin side past the fork point), the twin-suit rung
walk crosses the fork threshold on a RAISE OF THE COVERED TWIN
ITSELF — `tabToFound x.twin` fires at a boundary member `w` whose
twin rung reads the fork point EXACTLY (so `w` is ON the slab), the
crossing leg rides the journey as a WITNESS leg (it is reversible:
per the banked census dichotomy, under-seat or bare-king at `w`),
the whole prefix `π` stays ON THE SLAB (every prefix landing reads
the twin rung at-or-below the fork point), and the boundary members
carry their class anchors (`r st w`, `r w₁ u` — both witnesses ride
the split journeys).  No WF, no census, no new hypotheses beyond the
fork parcel the callers already carry. -/
private theorem lowslab_elevation_crossing {st u : State} {x : Card}
    (hx : ForkWitness st x)
    (hmem : sameOrbitSetoid.r st u)
    (helev : ¬ familyBelowFrontier u x) :
    ∃ (w w₁ : State) (π rest : List Move),
      ShufflePlayW st π w ∧
      rungAt w x.twin.suit = x.rank.toIdx ∧
      familyBelowFrontier w x ∧
      State.step w (Move.tabToFound x.twin) = some w₁ ∧
      reversibleAtW w (Move.tabToFound x.twin) ∧
      sameOrbitSetoid.r st w ∧
      sameOrbitSetoid.r w₁ u ∧
      ShufflePlayW w₁ rest u ∧
      (∀ (pre post : List Move), π = pre ++ post →
        ∀ z, st.run pre = some z → familyBelowFrontier z x) := by
  obtain ⟨ρ, hρ⟩ := sameOrbit_forward hmem
  have hstart : rungAt st x.twin.suit = x.rank.toIdx := by
    have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
    rwa [Card.twin_rank] at h2
  have hhigh : x.rank.toIdx < rungAt u x.twin.suit := by
    have h1 : ¬ (rungAt u x.twin.suit ≤ x.rank.toIdx) := helev
    omega
  obtain ⟨e, w, w₁, π, rest, -, hπ, hline, hes, her, hcr, hrv, htl, hpre⟩ :=
    lowslab_rung_walk (τ := x.twin.suit) (k := x.rank.toIdx) hρ
      (Nat.le_of_eq hstart) hhigh
  have hcard : e = x.twin := by
    have hrank : e.rank = x.twin.rank := by
      have h1 : e.rank.toIdx = x.twin.rank.toIdx := by
        rw [Card.twin_rank]
        exact her
      exact Rank.toIdx_inj h1
    rcases e with ⟨es, er⟩
    rcases x with ⟨xs, xr⟩
    simp only [Card.twin] at hes hrank ⊢
    rw [hes, hrank]
  rw [hcard] at hcr hrv
  refine ⟨w, w₁, π, rest, hπ, hline, ?_, ?_, ?_, ?_, ?_, htl, ?_⟩
  · unfold familyBelowFrontier
    omega
  · exact hcr
  · exact hrv
  · exact lowslab_journey_class hπ
  · exact lowslab_journey_class htl
  · intro pre post hpp z hrun
    exact hpre pre post hpp z hrun

/-- **THE RAISE-LIKE REPLAY RESIDUE** `fork_lowbridge_raise` [H] —
given the ELEVATED commit of kind raise-like (a committed
`tabToFound c` from `u` into `v`), a slab member `u₀` carries a
same-target-class step (the commit grade is the glue row's free
read).

ROUTE (complete; each step priced):

1. THE ELEVATED READ: `helev` is the twin suit's rung strictly past
   the fork point — at the WF grade, the covered twin is FOUNDED at
   `u` (`Orig/SlabEquiv.twin_slab_tableau`) and left the tableau
   down the witnessing journey (hidden lists pinned,
   `shuffle_hiddenPinned`).
2. THE CLASS ANCHOR: the fork itself sits on its slab
   (`fork_self_low`), and both witnessing journeys ride the class
   (`sameOrbit_forward` on `hmem` and its setoid mirror) — the slab
   is never vacuous inside the class, the descent journeys priced
   per-leg reversible.
3. THE CENSUS OF RAISES — POST-SWAP, TWO BANKED ADJUNCTS: (a) the
   ride-shape discipline at ONE witness row
   (`census_tabToFound_witness`): a riding under-raise exposes a
   below-card `z` of OPPOSITE family at the raised index + 1,
   UNFOUNDED, with the census moving exactly the raised card's and
   `z`'s cells — the takeback-host bracket the old route hoped for,
   now theorem-grade; the bare-riding raise is king-only
   (`witness_bare_lift_king`).  (b) THE COMMIT-MODE BAR: the
   census's own §2 pin `bare_lift_irreversibleAt` (with the banked
   reveal bar) closes the raise-commit census at theorem grade — a
   committed raise REVEALS or strips a bare NON-KING; the modes no
   longer need hoping.  The leg shapes ride
   `journey_raise_shape`/`journey_raise_seatUnfounded` as before.
4. THE SEAT RE-FIRE [THE OPEN STEP, priced against the SHRUNK
   `lowslab_top_census`]: the seat transport is now banked (the
   step-2 ledger family of the census row's route); the surviving
   open content is (a) the CARD-level bootstrap (which member's
   journey the transport rides, the card identity itself) and (b)
   the RUNG BRACKET — matching `c`'s suit's rung at `d` to its read
   at `u` so the same `tabToFound c` (or the seat's counterpart
   raise) re-fires as `m₀`.  PER THE SEATS-VS-RUNGS ADJUDICATION the
   census is deliberately rung-blind: the bracket census
   (`witness_rung_census`) is this tree's own pricing and REMAINS
   the flagged open step.
5. THE CLASS LINKS: the re-firing state shares the origin class by
   step 2-3's prefix composition (`ShufflePlayW_append`); the
   target-class match rides the re-flighted leg's own reversibility
   census; the commit grade is the glue row's free read.

PROBE NOTE (Orig/LowSlabProbe.lean, decide-grade): the twin-lift
round trip exercises exactly this row's tabToFound legs with live
one-move mirrors (the `lb1a_raise` family at the `lb0` economy), so
the bracket mechanics of steps 2-4 have a worked board example; the
rung-bracket open step of 4 (`rungAt d c.suit = rungAt u c.suit`)
REMAINS EXPLICITLY FLAGGED — untouched by both the probe and the
census.

HOSTCENSUS POST-COMMUTATION-SWAP (ASSESSED, HONESTLY): the new
congruence rows do NOT license this row's bracket — `step_congr_board`
transports legs along `boardEq` pairs (draw-dashed contexts), while
`d` and `u` here are ρ-IMAGES (the witnessing journey moved their
boards), so `rungAt d c.suit = rungAt u c.suit` does not ride the
congruence; the probe's structural armor (§9–§13 of
`Orig/LowSlabProbe.lean`: bare non-king lifts never ride witness
journeys, so no witness leg can move a bare commit card's rung;
the bracket datapoint 3=3 on record) remains the evidence.  The row
therefore CONSUMES the congruence only where it actually bites —
the re-fire assembly's draw-dashed contexts are the waste kind's
own named weld (`lowslab_waste_targetclass`; the draw row's former
(A)-transport is RETIRED with its landing) — and the survivors are
unchanged: the rung bracket (this row's own, per the
seats-vs-rungs adjudication) + the card-level bootstrap.  Earlier
consumptions (`census_tabToFound_witness`, `witness_bare_lift_king`,
`bare_lift_irreversibleAt`) stand.

FINALE TRANSCRIPTION (2026-10-13 — the bare-lift structural bar
made explicit; the row survives priced at [H]): on BOTH sides of the
raise census the dichotomy is banked — a WITNESSED raise is
UNDER-SEAT XOR BARE-KING (`census_tabToFound_witness`: the under-arm
exposes a below-card of OPPOSITE family at the raised index + 1,
unfounded, the census moving exactly in the two named cells; the
bare arm is king-only, `witness_bare_lift_king`), and the commit
side carries the matching bar (`bare_lift_irreversibleAt`: a bare
non-king lift commits outright — consistent with this row's `hiv`).
So any `σ := c.suit` raise LEG riding the witnessing journey is
under-seat or bare-king at its own site, and the rung ledger
(`witness_rung_census`: `rungAt u σ + pullsOf ρ σ = rungAt st σ +
raisesOf ρ σ`) reduces THE BRACKET to the σ-letter NET CENSUS —
whose TRANSFER MECHANICS ARE NOW LANDED IN-FILE as the isolated
small row (`lowslab_bracket_transfer`: a net-zero σ-letter journey
carries the σ-rung verbatim across the class, so the re-fire
member's `r = r` read is free GIVEN the census).  What remains open
is the census itself — no banked row nets it: the benign boards
(elevations that never touch the commit suit — the `bb_bracket`
datapoint's 3 = 3) exhibit the zero case, and a commit raising a
HIGHER pair-suit card is the live counterexample family.  The
σ-letter net census and the card-level bootstrap remain this row's
own priced pieces, per the seats-vs-rungs adjudication.

SESSION-2 ADDENDUM (2026-10-13, the take-over pass): the descent
datum of steps 1-2 is now BANKED IN-FILE as
`lowslab_elevation_crossing` (proved, zero-sorry, §4.2.0 above): any
witnessing journey out to an elevated member crosses the fork
threshold at a RAISE OF x.twin ITSELF, at a boundary member whose
twin rung reads the fork point EXACTLY — the whole prefix staying on
the slab, the crossing riding as a witness leg.  The row's open
  content thereby narrows to its two honest pieces: the σ-letter net
  census at the re-fire member (the crossing row prices the
  UNCLOSED REGION precisely: a commit card of the ALREADY-RAISED twin
  suit ABOVE the fork point — the waste note's D5-family — has
  `nextUp` fail at EVERY slab member, so a bracket transfer has
  nothing to carry there) and the card-level bootstrap of step 4.

  SESSION-3 ASSESSMENT (2026-10-13, the third succession — the
  assembly re-attempted): the bracket transfer instantiates cleanly
  wherever a KNOWN member also reads the commit suit's exact rung —
  the benign boards (the probe's `bb_bracket` 3=3 datapoint) and, by
  `lowslab_pair_netcensus`, every re-fire site whose witnessing
  journey back to `u` is witnessed to carry `nextUp c` at both ends.
  What no banked row licenses remains the two named pieces — the
  σ-letter net census in the general case (a climbing journey — the
  D5-family region with nothing for a bracket to carry), and the
  card-level bootstrap of the re-fire site (the wild copy corners
  fence every WF-free mirror kit — the undos' premises are honest —
  and the one-founding door is WF-gated upstream), so no witness
  journey between the replay landing and the commit landing can be
  built at the statement's grade.  The row CARRIES at [H], statement
  byte-frozen; the commit face any sequel needs is banked beside it
  (`lowslab_raise_commit_shape_wf`: at a WF site the raised card is a
  LONE top — the census's two commit species exactly), and the
  re-fire bracket mechanics remain the landed `lowslab_bracket_transfer`.
  -/
private theorem fork_lowbridge_raise {st : State} {x : Card}
    (hx : ForkWitness st x)
    {u v : State} (hmem : sameOrbitSetoid.r st u)
    {c : Card} (hstep : State.step u (Move.tabToFound c) = some v)
    (hiv : irreversibleAt u (Move.tabToFound c))
    (helev : ¬ familyBelowFrontier u x) :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      sameOrbitSetoid.r v₀ v := by
  sorry

/-- **THE REVEAL REPLAY RESIDUE** `fork_lowbridge_reveal` [H] — given
the ELEVATED commit of kind reveal (a committed run relocation
`tabToTab c b` from `u` into `v`), a slab member `u₀` carries a
same-target-class step.

ROUTE (complete; each step priced):

1. THE ELEVATED READ and THE CLASS ANCHOR: exactly the raise row's
   steps 1-2 (the twin consumed at `u`; the fork self-anchored; the
   descent journeys priced).
2. THE HIDDEN PIN: the stripping path's hidden head is a class
   invariant — `shuffle_hiddenPinned` pins every pile's hidden list
   along both journeys, so the reveal's input card exists under the
   SAME deck at every class member: the stripping path re-schedules
   off a deck the whole class shares.
3. THE HOST RE-FIRE — POST-SWAP, THE TRANSPORT IS BANKED: the
   relocation's source seat (the run head `c`'s pile) and its landing
   base (the base card's top seat) are both at-or-below-frontier
   pile-tops read through `canPlace`'s own guards.  The census now
   prices the cargo legs outright: a RIDING `tabToTab` is
   census-NEUTRAL cell-for-cell — the consumed host `z` is replaced
   by the exposed below-card `y` of the SAME CELL, unfounded
   (`census_tabToTab_inr_witness`; the king-headed empty-anchor arm
   `census_tabToTab_inl`) — and the SLIDE-COMMIT MODES are both
   banked at theorem grade: the reveal slide (the journey bar) and
   the bare-burn slide (`bare_burn_irreversibleAt` +
   `witness_tabToTab_never_burn` — a committed slide REVEALS or
   burns a bare source's seat with no replacement).  So (a) the
   "which mode am I replaying" analysis is closed, and (b) the
   cell-level transport is closed; the OPEN remainder is the
   CARD-level bootstrap (the specific `c` and base re-present at ONE
   slab member — `lowslab_top_census`'s surviving content) plus the
   same-fit guard assembly of `m₀`.
4. THE CLASS LINKS: as the raise row's step 5 (prefix-composition
   membership; target-class match by the re-flight's reversibility;
   commit grade free by the glue).

PROBE NOTE (Orig/LowSlabProbe.lean, decide-grade): this row's
replay shape is EXERCISED END-TO-END ONCE — the reveal-commit at the
twin-elevated `lb1` (the `lb2_step` slide) has its slab duplicate
CONSTRUCTED and kernel-verified at `lb0` (`lb2_dup`: the full
five-tuple, the commit grade confirmed both directly by the
hiddenTotal monotone and through this file's `fork_lowbridge_commitGlue`
— the glue row's first on-board consumption), with the target classes
matched by re-fired class legs (`lb2_class`).  The row's remaining
content is the general-commuting form of that one board.

HOSTCENSUS POST-COMMUTATION-SWAP: ASSESSED — no new license for this
row beyond its step-3 survivals (the assembly contexts are ρ-images,
not `boardEq` pairs — the congruence rows do not reach them); the
draw-dashed fragments of the assembly are the waste kind's own
named weld (`lowslab_waste_targetclass`; the draw row's former
(A)-transport is RETIRED with its landing).  The earlier consumptions
stand: `census_tabToTab_inr_witness`, `census_tabToTab_inl`,
`bare_burn_irreversibleAt`, `witness_tabToTab_never_burn` (transport
+ commit modes); the seat-side deep support is
`lowslab_top_census`'s banked step-2 family plus its surviving
card-level bootstrap.

FINALE ASSESSMENT (2026-10-13): the LOAD-BEARING receipt is on
record (§12(b) of `Orig/LowSlabProbe.lean`: the reveal at the
POST-exhumation member is duplicated at the PRE-exhumation member
by the SAME slide, the two committed targets joined by ONE
posterior pull, `xb1_dup` kernel-verified — the loan repaid exactly
as `excursion_issues_noNewSeat` reads) and the hidden-list pinning
is banked (`shuffle_hiddenPinned`, instantiated at `xb_revealContent`).
THE SLIDE's MECHANICAL LEG IS NOW LANDED IN-FILE as the isolated
small row (`lowslab_slide_board_refire`: the slide consults piles
only, so at any member BOARD-EQUAL to the commit site the same
slide re-fires and lands board-equal).  The survivors stay, now
sharpened: the CARD-level re-scheduling — producing the
board-equal slab member presenting the run head (or its
counterpart-slide variant), the defusing inventory of §12(b) — and
the same-fit guard assembly of `m₀`; the probe's exhibit is the
  general form's worked example.

SESSION-2 ADDENDUM (2026-10-13, the take-over pass): the elevated
  read and class anchor of step 1 are now BANKED IN-FILE as
  `lowslab_elevation_crossing` (proved, zero-sorry, §4.2.0 above) —
  the witness journey to any elevated member crosses at a reversible
  `tabToFound x.twin` at a fork-exact boundary member, the prefix
  never leaving the slab, both split journeys carrying their class
  anchors.  The card-level re-scheduling (the §12(b) defusing
  inventory) remains the row's entire open content, as sharpened.

  SESSION-3 ASSESSMENT (2026-10-13, the third succession): the route's
  step-2 hidden pin is now a banked read (`lowslab_class_hiddenPinned`
  — the deck the whole class shares, welded to any candidate's anchor
  by `lowslab_top_census_hidden`), the slide's re-fire mechanics ride
  the landed `lowslab_slide_board_refire`, and the §12(b) receipt
  stays board-local in its ONE-LEG posterior pull.  The
  general-commuting form — producing the pre-side slab member whose
  boards present the run head (up to the counterpart-slide variant)
  and welding the two landings across the class journey — remains the
  row's honest remainder: a witness journey `v₀ ⇝ v` is the whole
  missing content (the dashed transport), the same re-threading the
  waste rows' named weld prices from the other side, and no banked
  row builds it at the WF-free grade.  The row CARRIES at [H],
  statement byte-frozen. -/
private theorem fork_lowbridge_reveal {st : State} {x : Card}
    (hx : ForkWitness st x)
    {u v : State} (hmem : sameOrbitSetoid.r st u)
    {c : Card} {b : Base}
    (hstep : State.step u (Move.tabToTab c b) = some v)
    (hiv : irreversibleAt u (Move.tabToTab c b))
    (helev : ¬ familyBelowFrontier u x) :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      sameOrbitSetoid.r v₀ v := by
  sorry

/-! ### §4.2.a The guard-refusal transport (finale, proved) -/

/-- **THE SHIFTED-CURSOR REFUSAL** (the guard-refusal transport — the
round-2 probe's negative verdict at theorem grade,
`Orig/LowSlabProbe.lean`'s `wbW_noFire` datum, closed): if a member's
waste head is NOT the guard's named card, BOTH waste letters refuse
to fire outright — the guard reads the head (`wasteIs c` is a head
compare, `State.wasteIs_cons`), and the fired-step inversions hand
the contradiction.  The waste kind's cursor rail consumes this
one-way: a member whose cursor is shifted off the commit card cannot
host the re-fire — the shift kills the GUARD, never the class. -/
private theorem waste_head_refusal {x : State} {c c' : Card} {t : List Card}
    (hw : x.waste = c' :: t) (hne : c' ≠ c) :
    (∀ s₁ : State, State.step x (Move.wasteToFound c) ≠ some s₁) ∧
      ∀ (b : Base) (s₁ : State), State.step x (Move.wasteToTab c b) ≠ some s₁ := by
  constructor
  · intro s₁ h1
    obtain ⟨hg, -⟩ := step_wasteToFound_inv h1
    rw [State.wasteIs_cons hw c, Bool.and_eq_true] at hg
    exact hne (of_decide_eq_true hg.1)
  · intro b s₁ h2
    obtain ⟨hg, -⟩ := step_wasteToTab_inv h2
    rw [State.wasteIs_cons hw c, Bool.and_eq_true] at hg
    exact hne (of_decide_eq_true hg.1)

/-- **THE BOARD-JOURNEY ZONE FLAT** (the cursor-coincidence
transport's draw-free leg, closed): a BOARD-ONLY witness journey
carries the two-zone cycle VERBATIM from source to landing — the
stock, the waste and the deal size at the journey's end are the
origin's own.  This is the refl-pair application of the sibling's
`board_run_congr` (`Orig/HostCensus.lean`: the board play runs from
both ends of the identity pair, and the source-side flats read the
landing's zone equal to the source's); `cycle_zone_pin`
(`Orig/SlabEquiv.lean`) remains the membership-flavored companion
upstream.  Together with `waste_head_refusal` this closes the CURSOR
COINCIDENCE at every draw-free member: the guard reads the same
head, so the re-fire's `wasteIs` conjunct is carried, and the
refused side is bounded one-way. -/
private theorem witness_zone_flat {st u : State} {ρ : List Move}
    (hρ : ShufflePlayW st ρ u) (hboard : ∀ m ∈ ρ, boardMove m) :
    u.stock = st.stock ∧ u.waste = st.waste ∧ u.drawStep = st.drawStep := by
  obtain ⟨-, -, -, hz1, hz2, hz3, -, -, -⟩ :=
    board_run_congr ρ hboard st st ⟨rfl, rfl⟩ u (ShufflePlayW_run hρ)
  exact ⟨hz1, hz2, hz3⟩

/-- **THE WASTE RE-FIRE GUARD SHAPE** — the two-letter disjunction the
waste-kind replay routes over (the statement-facing shape shared by
the waste rows' named pieces): a founding re-fire needs the named
card at the waste head and next-up; a seating re-fire additionally
consults the landing base's placement guard. -/
def WasteGuard (W : State) (m : Move) : Prop :=
  (∃ c, m = Move.wasteToFound c ∧ W.wasteIs c = true ∧ W.nextUp c = true) ∨
  (∃ c b, m = Move.wasteToTab c b ∧ W.wasteIs c = true ∧ W.canPlace c b = true)

/-- **THE WASTE HEAD** (private kit) — a guard that reads the waste
top true pins the waste as the named card over a tail. -/
private theorem lowslab_waste_head_of {w : State} {c : Card}
    (hw : w.wasteIs c = true) : ∃ t, w.waste = c :: t := by
  cases hwst : w.waste with
  | nil =>
      rw [State.wasteIs_nil hwst] at hw
      exact absurd hw (by simp)
  | cons y t =>
      have hy : y = c := by
        rw [State.wasteIs_cons hwst c] at hw
        exact of_decide_eq_true hw
      exact ⟨t, by rw [hy]⟩

/-- **THE WASTE GUARD FIRES** (proved, the take-over pass) — the
guard package alone fires its letter: the waste-top read pins the
waste nonempty (the head row), so the letter's asserted guards carry
the step's own condition and the move lands.  This is the mechanical
half of the waste target-class residue, extracted per the isolating
discipline: `lowslab_waste_targetclass` below now claims only the
class-mateship of the two landings. -/
private theorem lowslab_waste_guard_fires {w : State} {m : Move}
    (hfu : WasteGuard w m) :
    ∃ v, State.step w m = some v := by
  rcases hfu with ⟨c, rfl, hw, hn⟩ | ⟨c, b, rfl, hw, hcp⟩
  · obtain ⟨t, hcon⟩ := lowslab_waste_head_of hw
    refine ⟨{ w.setFound c.suit (w.found c.suit ++ [c]) with waste := t }, ?_⟩
    show (if w.wasteIs c && w.nextUp c then
        match w.waste with
        | _ :: ws => some { w.setFound c.suit (w.found c.suit ++ [c]) with
            waste := ws }
        | [] => none
      else none) = _
    rw [hw, hn, hcon]
    rfl
  · obtain ⟨t, hcon⟩ := lowslab_waste_head_of hw
    refine ⟨{ w.putCard c b with waste := t }, ?_⟩
    show (if w.wasteIs c && w.canPlace c b then
        match w.waste with
        | _ :: ws => some { w.putCard c b with waste := ws }
        | [] => none
      else none) = _
    rw [hw, hcp, hcon]
    rfl

/-- **THE PAIR NET CENSUS** `lowslab_pair_netcensus` (proved, the
take-over pass) — the datum the waste rows' hot rail lacked a banked
row for, landing for free where BOTH members carry the next-up read:
along any witness journey between two members that BOTH read `c`
next-up, the `c.suit` raise count equals its pull count (the rung
ledger nets the two reads).  The dashed-witness re-threading of
`lowslab_waste_targetclass` thereby only ever has to handle NESTED
brackets of the commit suit, never an open net — the bracket
transfer's missing census half, paid exactly where the guard carries
it. -/
private theorem lowslab_pair_netcensus {u u₀ : State} {ρ : List Move} {c : Card}
    (hρ : ShufflePlayW u₀ ρ u)
    (hboth : u₀.nextUp c = true ∧ u.nextUp c = true) :
    raisesOf ρ c.suit = pullsOf ρ c.suit := by
  obtain ⟨hn₀, hn⟩ := hboth
  have hledger := witness_rung_census hρ c.suit
  have hr₀ : c.rank.toIdx = rungAt u₀ c.suit := of_decide_eq_true hn₀
  have hr : c.rank.toIdx = rungAt u c.suit := of_decide_eq_true hn
  omega


/-- **THE WASTE RE-SEAT RESIDUE** `lowslab_waste_reseat` [H, named at
the waste-shrink pass] — the two waste arms' shared first fighter: at
SOME low-slab member of the class, the committing waste letter's own
guard shape holds again.  TWO RAILS must land at ONE member:

* THE CURSOR RAIL — the two-zone cells must hold the card at the
  waste head.  For board-only witnessing journeys the zone cells are
  carried verbatim (the leg-shape discipline `witness_leg_letters`
  bars the waste letters; the placement/foundation writes touch
  piles and founds only — this tree's own zone-keep kit; play-level
  `board_run_congr`), so the cursor reads the same at every
  board-only prefix landing.  Reversible draw legs genuinely MOVE
  the cursor (the empty-stock recycle-deal peels cards into the
  waste, `Phase.lean`'s loop algebra), and the round-2 probe's
  `wbW_noFire` datum records the shifted-cursor site refusing the
  re-fire OUTRIGHT — the FIG-2 duplicate rode IDENTICAL cursors at
  the two commit sites.  The open content is the zone excursion: the
  commit itself pins one orbit point (the card IS at the head at
  `u`), and the reseat must re-schedule onto an at-head point of the
  loop orbit at a slab member — priced against Phase's rotation
  arithmetic (the `draw_landings_sameOrbit` engine's own pool
  rotations) with the no-waste-letters census (the card never leaves
  the two-zone cells along the journey).
* THE HOT RAIL — the founding arm's `nextUp c` is a RUNG question
  (THE HOT-BRACKET, the same unclosed bracket family the raise row
  flags per the seats-vs-rungs adjudication): some slab member's
  `c.suit` rung must read `c.rank.toIdx`, priced against the landed
  bracket transfer (`lowslab_bracket_transfer`, over the rung
  ledger `witness_rung_census`) and the raising legs' Dyck
  serialization (`Orig/BracketDecomp.lean`); probe-verified benign
  at every tried shape (the elevation legs of the probe boards never
  touched the waste-head's suit).  The seating arm's `canPlace`
  consults the landing base's top seat — `lowslab_top_census`'s
  surviving card-level bootstrap is its deep support.
* THE COINCIDENCE — the two rails commute (the cursor orbit is
  zone-only, the rung rail is found-only), and the reseat must land
  one member carrying both; the slab crossing (the twin rung at-or-
  below the fork point) exists by `fork_self_low` and the crossing
  analysis.

HOSTCENSUS DISCIPLINE: no consumed row rides the sibling's residue
`witness_leg_mint_confined`.

FINALE NOTE (2026-10-13): the cursor rail's transport pieces are now
  LANDED IN-FILE and consumed here at term grade —
`witness_zone_flat` (the board-only leg's zone carry, closed: a
board-only witness journey reads the same stock/waste/drawStep at
its landing) and `waste_head_refusal` (the shifted-cursor refusal,
closed: a member whose waste head is not the commit card refuses
both waste letters outright) — so the rail's OPEN content is
  exactly the ZONE EXCURSION PAST A DRAW LEG (the orbit re-scheduling
above), nothing more.

SESSION-2 ADDENDUM (2026-10-13, the take-over pass — the hot rail
priced honestly AGAINST the statement): at this WF-free, rank-blind
statement the hot rail is not merely open — there is a LIVE
REFUTATION CANDIDATE (hand-derived; probe certification pending, the
refuter-first Q(B) shape of the header): a committed waste letter
whose card rides the ALREADY-RAISED TWIN SUIT ABOVE the fork point
(economy: the `lb0` fork with its twin `D4` raised, the twin suit's
next card `D5` — one past the fork point 3 — at the waste head,
where no black four exists anywhere as its pull-back base; admitted
by no premise here).  Then
`WasteGuard u₀ m` demands `nextUp c` at a slab member — the commit
rung read EXACTLY — while the elevated read pins that suit's rung
strictly past the fork point at `u` and the slab pins it at-or-below
the fork at every slab member: the guards are UNREACHABLE together,
so the row as stated would be FALSE on such an economy, and the two
waste routers inherit the same datum (their conclusion's target
class pins the raised rung two past the fork while no slab
member's ONE move reaches past one).  The missing rank discipline
is exactly `lowslab_top_census`'s `hlow` (the commit card
at-or-below the fork point); it cannot be added here without
cascading past the byte-frozen main statement, so it is recorded as
a priced boundary datum, per the never-force discipline — NOT
 smuggled in as a premise.  What DID close for the waste pair is
  banked below: `lowslab_pair_netcensus` (the two guards' nextUp
  reads net the commit suit's letters to zero along any witnessing
  journey between the members — the re-threading's remaining work is
  purely the nesting) and `lowslab_waste_guard_fires` (the guard
  fires its letter unconditionally).

  SESSION-3 ASSESSMENT (2026-10-13, the third succession): the cursor
  kit stands (`witness_zone_flat` + `waste_head_refusal` — the
  board-only rail closed one-way) and the firing half is
  `lowslab_waste_guard_fires`; the live refutation candidate is
  UNPERTURBED and unperturbable in-session: a twin-suit commit card
  one past the fork point puts the founding arm's `nextUp` guard
  outside every slab member's rung while the premise pack admits the
  economy, so any closure here would force past the recorded
  counterexample family — probe certification stays the pending gate.
  The row CARRIES at [H], statement byte-frozen.

  SESSION-4 VERDICT (2026-10-13, the fourth succession — REFUTED AT
  THE FROZEN STATEMENT, THE GATE CERTIFIED): the pending probe gate
  is now DISCHARGED, in-file, at decide grade —
  `lowslab_waste_reseat_refuted` below (§4.2.a.R, zero-sorry): the
  tw-suit D5 economy of the session-2 candidate, CERTIFIED.  The
  economy needs no cursor-orbit engineering at all: the fork board
  `wr_st` itself heads its waste with `5♦` (the twin suit's next
  card one past the fork point), the two-leg board-only witness
  journey (cover hop, twin raise — both reversible by their
  one-move mirrors) carries the waste head verbatim to the elevated
  class-mate, so every premise of the row READS TRUE on the board —
  while the conclusion is UNREACHABLE: the founding-arm guard at any
  re-seated member demands the ♦ rung exactly 4 (`nextUp 5♦`), the
  slab conjunct pins it at-or-below the fork point 3, and the seat
  arm does not apply to the founding letter.  The row as stated is
  therefore FALSE; it keeps its sorry and hosts at [H, REFUTED].
  The owner's recourse is the statement-level rank premise the
  session-2 candidate already priced (`lowslab_top_census`'s own
  `hlow`: the commit card at-or-below the fork point); nothing is
  smuggled per the never-force discipline, and the downstream
  routers stay honest AT ECONOMIES WHERE THE EXTRA PREMISES HOLD —
  at the exhibited board the founding letter's own commit grade
  fails (its giveback re-fires onto the vacated twin seat `5♣`), so
  the routers' and main row's statements are untouched by this
  board: what the refutation retires is the reseat UNCONDITIONAL
  claim alone. -/
private theorem lowslab_waste_reseat {st u : State} {x : Card} {m : Move}
    (hx : ForkWitness st x)
    (hmem : sameOrbitSetoid.r st u)
    (helev : ¬ familyBelowFrontier u x)
    (hfu : WasteGuard u m) :
    ∃ u₀ : State,
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      WasteGuard u₀ m := by
  sorry

/-! ### §4.2.a.R THE RESEAT REFUTATION BOARD (the fourth succession)

THE PENDING GATE, CERTIFIED IN-FILE: the session-2 hand-derived
refutation candidate for `lowslab_waste_reseat` — probe certification
was the recorded gate, and the probe economy needs NO cursor-orbit
engineering at all: a board whose WASTE already carries the commit
card at the head reads the guard verbatim at every board-leg landing
(the two-leg journey below writes piles and founds only).  THE
FAMILY (the "twin-suit D5-over-fork" economy):

* the fork board `wr_st`: family rungs ♥ 3 / ♦ 3, blacks 0 — the
  covered twin `4♦` buried under its fitting black-three cover `3♠`
  over the live takeback seat `5♣`; the live member `4♥` topped over
  `5♠`; the WASTE heads `5♦` — the twin suit's next card, ONE PAST
  the fork point 3.  `ForkWitness wr_st 4♥` is certified at decide
  grade through `Orig/ForkStateSB.lean`'s `forkWitnessRowSB` (the
  pair-saturation iff over `Card.universe` and the orientation pin,
  both decided) — the only new import of this pass, itself below the
  transitively-already-present `Orig.PairName → Orig.ForkWeaker`
  chain, so no cycle.
* the class member `wr_u`: the two-leg witness journey — hop the
  cover off the twin (`tabToTab 3♠ (inr 4♥)`, reversible by the
  un-hop), then raise the twin (`tabToFound 4♦`, reversible by its
  giveback onto the re-exposed seat) — leaves the twin suit at rung
  4 (ELEVATED) while carrying the waste head VERBATIM, so
  `WasteGuard wr_u (wasteToFound 5♦)` holds by two decides.
* the CONTRADICTION the conclusion would buy: a re-seated `u₀` must
  satisfy `familyBelowFrontier u₀ 4♥` — the ♦ rung at or below 3 —
  while the founding-arm guard demands `nextUp 5♦` there — the ♦
  rung reading EXACTLY 4.  The guards are UNREACHABLE together; the
  seat-arm of the guard disjunction does not apply to the founding
  letter.  So `lowslab_waste_reseat` is FALSE as stated, exactly as
  the session-2 candidate read, and `lowslab_waste_reseat_refuted`
  below is the certified negation.

REPAIR NOTE (owner's recourse, the `lowslab_top_census` precedent):
restore the rank discipline the row's docstring always meant — the
commit card at-or-below the fork point, `lowslab_top_census`'s own
`hlow` — as a premise; the founding guard then reads a rung the
slab CAN carry.  What CANNOT be added is the engineer's burden the
old route priced (the cursor-orbit re-scheduling): with the commit
card at the head of the CLASS-SHARED waste the cursor rail rides
verbatim along board legs, and the honest open content of the waste
rail is thereby sharpened for whatever repaired row follows. -/


/-- The two-leg board's private card/step kit. -/
private def wrC (s : Suit) (r : Rank) : Card := ⟨s, r⟩

private def wrStep (st : State) (m : Move) : State :=
  match st.step m with
  | none => st
  | some s' => s'

/-- The forty buried cards — every card not on a foundation, not
face-up, and not at the waste head, in one hidden deck. -/
private def wr_deck : List Card :=
  [wrC .spade .ace, wrC .spade .two, wrC .spade .four, wrC .spade .six,
   wrC .spade .seven, wrC .spade .eight, wrC .spade .nine, wrC .spade .ten,
   wrC .spade .jack, wrC .spade .queen, wrC .spade .king,
   wrC .heart .five, wrC .heart .six, wrC .heart .seven, wrC .heart .eight,
   wrC .heart .nine, wrC .heart .ten, wrC .heart .jack, wrC .heart .queen,
   wrC .heart .king,
   wrC .diamond .six, wrC .diamond .seven, wrC .diamond .eight,
   wrC .diamond .nine, wrC .diamond .ten, wrC .diamond .jack,
   wrC .diamond .queen, wrC .diamond .king,
   wrC .club .ace, wrC .club .two, wrC .club .three, wrC .club .four,
   wrC .club .six, wrC .club .seven, wrC .club .eight, wrC .club .nine,
   wrC .club .ten, wrC .club .jack, wrC .club .queen, wrC .club .king]

/-- THE FORK BOARD — family rungs pinned at 3, blacks at 0; the
twin tower `5♣ / 4♦ / 3♠` at p1, the live member `4♥` over `5♠` at
p2, the waste heading `5♦`. -/
private def wr_hmap : Suit → Nat
  | .heart => 3 | .diamond => 3 | .spade => 0 | .club => 0

private def wr_st : State where
  found := fun s => s.upCards.take (wr_hmap s)
  piles := fun a => match a with
    | .p1 => ⟨wr_deck, [wrC .club .five, wrC .diamond .four, wrC .spade .three]⟩
    | .p2 => ⟨[], [wrC .spade .five, wrC .heart .four]⟩
    | _ => ⟨[], []⟩
  stock := []
  waste := [wrC .diamond .five]
  drawStep := 1

/-- THE ELEVATED MEMBER: cover hopped off the twin, twin raised. -/
private def wr_s1 : State :=
  wrStep wr_st (Move.tabToTab (wrC .spade .three) (Sum.inr (wrC .heart .four)))

private def wr_u : State :=
  wrStep wr_s1 (Move.tabToFound (wrC .diamond .four))

/-- THE FORK PARCEL, DECIDED — the saturation iff and the orientation
pin over the whole universe, through the SB door. -/
private theorem wr_st_wf : wr_st.WF := by
  refine ⟨fun s => ⟨wr_hmap s, rfl⟩, ?_, ?_, ?_⟩
  · intro a
    cases a <;> rfl
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

private theorem wr_fork : ForkWitness wr_st (wrC .heart .four) := by
  have hrow : forkWitnessRowSB wr_st (wrC .heart .four) = true := by decide
  exact (forkWitnessRowSB_iff wr_st_wf).1 hrow

/-- the hop fires; its mirror is the un-hop at the hopped member. -/
private theorem wr_hop_fires :
    State.step wr_st
      (Move.tabToTab (wrC .spade .three) (Sum.inr (wrC .heart .four))) =
      some wr_s1 := by
  rfl

/-- the un-hop at the hopped member lands back at the fork, exactly. -/
private def wr_st' : State :=
  wrStep wr_s1 (Move.tabToTab (wrC .spade .three) (Sum.inr (wrC .diamond .four)))

private theorem wr_st'_eq : wr_st' = wr_st := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

private theorem wr_unhop_fires :
    State.step wr_s1
      (Move.tabToTab (wrC .spade .three) (Sum.inr (wrC .diamond .four))) =
      some wr_st := by
  rw [← wr_st'_eq]
  rfl

/-- the twin raise fires; its mirror is the giveback at the raised
member. -/
private theorem wr_raise_fires :
    State.step wr_s1 (Move.tabToFound (wrC .diamond .four)) =
      some wr_u := by
  rfl

/-- the giveback at the raised member lands back at the hopped
member, exactly. -/
private def wr_s1' : State :=
  wrStep wr_u (Move.foundToTab (wrC .diamond .four) (Sum.inr (wrC .club .five)))

private theorem wr_s1'_eq : wr_s1' = wr_s1 := by
  refine State.ext (funext fun σ => ?_) (funext fun a => ?_) ?_ ?_ ?_
  · cases σ <;> rfl
  · cases a <;> rfl
  · rfl
  · rfl
  · rfl

private theorem wr_giveback_fires :
    State.step wr_u
      (Move.foundToTab (wrC .diamond .four) (Sum.inr (wrC .club .five))) =
      some wr_s1 := by
  rw [← wr_s1'_eq]
  rfl

/-- **THE ELEVATED CLASS-MATE** — the fork and the two-leg landing
are joined by witness shuffles BOTH ways (the hop/raise pair and
their exact mirrors). -/
private theorem wr_class : sameOrbitSetoid.r wr_st wr_u :=
  ⟨[Move.foundToTab (wrC .diamond .four) (Sum.inr (wrC .club .five)),
     Move.tabToTab (wrC .spade .three) (Sum.inr (wrC .diamond .four))],
    ShufflePlayW.cons
      ⟨wr_s1,
        [Move.tabToFound (wrC .diamond .four)],
        wr_giveback_fires, run_one wr_raise_fires⟩
      wr_giveback_fires
      (ShufflePlayW.cons
        ⟨wr_st, [Move.tabToTab (wrC .spade .three) (Sum.inr (wrC .heart .four))],
          wr_unhop_fires, run_one wr_hop_fires⟩
        wr_unhop_fires
        (ShufflePlayW.nil wr_st)),
    [Move.tabToTab (wrC .spade .three) (Sum.inr (wrC .heart .four)),
     Move.tabToFound (wrC .diamond .four)],
    ShufflePlayW.cons
      ⟨wr_s1,
        [Move.tabToTab (wrC .spade .three) (Sum.inr (wrC .diamond .four))],
        wr_hop_fires, run_one wr_unhop_fires⟩
      wr_hop_fires
      (ShufflePlayW.cons
        ⟨wr_u,
          [Move.foundToTab (wrC .diamond .four) (Sum.inr (wrC .club .five))],
          wr_raise_fires, run_one wr_giveback_fires⟩
        wr_raise_fires
        (ShufflePlayW.nil wr_u))⟩

/-- the twin suit read strictly past the fork point at the member. -/
private theorem wr_helev : ¬ familyBelowFrontier wr_u (wrC .heart .four) := by
  intro hc
  have hr : rungAt wr_u (wrC .diamond .five).suit = 4 := rfl
  have h3 : (wrC .heart .four).rank.toIdx = 3 := rfl
  have hs : (wrC .heart .four).twin.suit = (wrC .diamond .five).suit := rfl
  unfold familyBelowFrontier at hc
  rw [hs] at hc
  omega

/-- the founding guard at the member: the waste head is the commit
card, and the twin suit's next card is next-up. -/
private theorem wr_guard :
    WasteGuard wr_u (Move.wasteToFound (wrC .diamond .five)) :=
  Or.inl ⟨wrC .diamond .five, rfl, rfl, rfl⟩

/-- **THE RESEAT RESIDUE IS REFUTED** — `lowslab_waste_reseat` is
FALSE at its byte-frozen statement: the exhibited fork class above
satisfies every premise — the decided fork parcel, the two-leg
elevated class-mate, the twin suit a full rung past the fork point,
the founding guard reading the class-shared waste head — while the
conclusion is unreachable: the slab conjunct pins the twin suit's
rung at-or-below the fork point at any re-seated member, the
founding-arm guard demands it ONE PAST IT, and the seat arm does
not apply to the founding letter.  The row keeps its sorry (the row
as stated is FALSE); the owner's recourse is the statement-level
rank premise the session-2 candidate already priced — the commit
card at-or-below the fork point, `lowslab_top_census`'s own `hlow`. -/
theorem lowslab_waste_reseat_refuted :
    ¬ ∀ (st u : State) (x : Card) (m : Move),
      ForkWitness st x → sameOrbitSetoid.r st u →
      ¬ familyBelowFrontier u x → WasteGuard u m →
      ∃ u₀ : State,
        sameOrbitSetoid.r st u₀ ∧
        familyBelowFrontier u₀ x ∧
        WasteGuard u₀ m := by
  intro h
  obtain ⟨u₀, hclass, hslab, hguard⟩ :=
    h wr_st wr_u (wrC .heart .four) (Move.wasteToFound (wrC .diamond .five))
      wr_fork wr_class wr_helev wr_guard
  rcases hguard with ⟨c, heq, -, hn⟩ | ⟨c, b, heq, -, -⟩
  · injection heq with hc
    subst hc
    have hr : (wrC .diamond .five).rank.toIdx
        = rungAt u₀ (wrC .diamond .five).suit := of_decide_eq_true hn
    have hs : (wrC .heart .four).twin.suit = (wrC .diamond .five).suit := rfl
    have hc' : rungAt u₀ (wrC .heart .four).twin.suit
        ≤ (wrC .heart .four).rank.toIdx := hslab
    rw [hs] at hc'
    have h4 : (wrC .diamond .five).rank.toIdx = 4 := rfl
    have h3 : (wrC .heart .four).rank.toIdx = 3 := rfl
    omega
  · injection heq

/-- **THE WASTE TARGET-CLASS BRIDGE RESIDUE**
`lowslab_waste_targetclass` [H, named at the waste-shrink pass] — the
two waste arms' shared second fighter (THE DASHED-WITNESS TRANSPORT
family): when the guard shape holds at a member and at a re-seated
low member, the re-fire at the low member lands CLASS-MATE to the
original commit's target.

ROUTE (complete; the transport's own content):

1. THE DASHED CHAIN — for each leg of a witnessing journey between
   the two members, the waste-commit's dash (the card popped from
   the waste, founded or seated) must re-fire at the dashed state
   and land on the dashed successor.  Board legs whose suits differ
   from the commit card's dash cleanly (the mirrors re-fire over
   the guard-blind congruence, `step_congr_board`-family); the
   same-suit founding legs SHIFT the dashed card one rung up — the
   open content is the per-suit Dyck re-threading (`Orig/BracketDecomp.lean`'s
   stack discipline: the LIFO pull law + the bracket closure), the
   same nesting the waste rows' hot rail prices from the other side.
2. THE ZONE DASH — the waste commit pops the two-zone head, so the
   dashed zone is the commit-successor's zone; board letters are
   blind to it, and the draw legs' orbit excursions ride Phase's
   loop algebra (the probe's FIG-2/3 mixture rows witness the
   commutation on-board).
3. THE WELD — the per-hop certificates compose into the two
    witness shuffles welding `v₀` to `v` (the round-trip-engine
    pattern of `chain_assembly`'s scaffold; the glue consumes only
    the class links).

SESSION-2 SHRINK (2026-10-13, the take-over pass): the FIRING half
of the conclusion is now PROVED mechanically (`lowslab_waste_guard_fires`:
`WasteGuard` alone fires the letter, no second member needed), so the
  row is restated over both landings GIVEN and claims ONLY the
  class-mateship `r v₀ v` — the dashed-witness weld, the row's honest
  and entire remaining content, consumed by the two waste routers
  which obtain the low landing from the guard-fires row.  NEW BANKED
  SUPPORT: `lowslab_pair_netcensus` — the two guards' nextUp reads
  net the commit suit's raises against its pulls along any witness
  journey between the members, so the per-leg re-threading below only
  ever has to handle NESTED brackets, never an open net.

  SESSION-3 ASSESSMENT (2026-10-13, the third succession): the net
  half is banked (`lowslab_pair_netcensus`) and the per-leg mirrors
  exist one-by-one at WF grades; the missing content is exactly the
  Dyck re-threading of the nested same-suit brackets — the dashed
  commit must be re-seated inside the bracket word, past every
  same-suit raise/pull leg of the witnessing journey — and no banked
  row builds that confluence at the WF-free grade; the only banked
  confinement row (`witness_leg_mint_confined`) is the sibling's own
  named residue and stays unconsumed per the house discipline.  The
  row CARRIES at [H], statement byte-frozen. -/
private theorem lowslab_waste_targetclass {u u₀ v v₀ : State} {m : Move}
    (hclass : sameOrbitSetoid.r u₀ u)
    (hfu : WasteGuard u m)
    (hfu₀ : WasteGuard u₀ m)
    (hstep : State.step u m = some v)
    (hstep₀ : State.step u₀ m = some v₀) :
    sameOrbitSetoid.r v₀ v := by
  sorry

set_option linter.unusedVariables false in
/-- **THE WASTE-JUMP REPLAY ROW** (pop-to-foundation arm)
`fork_lowbridge_waste_found` [SHRUNK at the waste-shrink pass to a
router over the two named pieces] — given the ELEVATED commit of
router over the two named pieces] — given the ELEVATED commit of
kind waste-jump (a committed `wasteToFound c` from `u` into `v`), a
slab member `u₀` carries a same-target-class step.  The row's own
proof is now PURE ASSEMBLY OFF THE STEP'S GUARD: the commit's own
guard reading (`step_wasteToFound_inv`) packages the waste-head and
next-up facts into `WasteGuard u`; the shared named residues carry
the priced content — `lowslab_waste_reseat` (the cursor rail + the
hot-bracket at ONE slab member) and `lowslab_waste_targetclass`
(the dashed-witness transport welding the two landings).  The
commit grade `hiv` enters only through the dispatcher's glue row;
the commit's `cycleCount`-drop mechanism plays no role
(`Orig/Irreversible.lean` Table 1). -/
private theorem fork_lowbridge_waste_found {st : State} {x : Card}
    (hx : ForkWitness st x)
    {u v : State} (hmem : sameOrbitSetoid.r st u)
    {c : Card} (hstep : State.step u (Move.wasteToFound c) = some v)
    (hiv : irreversibleAt u (Move.wasteToFound c))
    (helev : ¬ familyBelowFrontier u x) :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      sameOrbitSetoid.r v₀ v := by
  obtain ⟨hg, -⟩ := step_wasteToFound_inv hstep
  rw [Bool.and_eq_true] at hg
  have hfu : WasteGuard u (Move.wasteToFound c) :=
    Or.inl ⟨c, rfl, hg.1, hg.2⟩
  obtain ⟨u₀, hmem₀, hslab₀, hfu₀⟩ := lowslab_waste_reseat hx hmem helev hfu
  have hclass : sameOrbitSetoid.r u₀ u :=
    sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm hmem₀) hmem
  obtain ⟨v₀, hstep₀⟩ := lowslab_waste_guard_fires hfu₀
  exact ⟨u₀, Move.wasteToFound c, v₀, hmem₀, hslab₀, hstep₀,
    lowslab_waste_targetclass hclass hfu hfu₀ hstep hstep₀⟩

set_option linter.unusedVariables false in
/-- **THE WASTE-JUMP REPLAY ROW** (seat arm) `fork_lowbridge_waste_seat`
[SHRUNK at the waste-shrink pass, as the pop-to-foundation arm] — the
`wasteToTab` arm of the waste-jump kind: the same router over the
two shared named residues, the guard package now reading the
placement guard of the landing base (`step_wasteToTab_inv`); the
hot rail's `canPlace` consults the landing base's top seat with
`lowslab_top_census`'s surviving card-level bootstrap as the
seat-side deep support. -/
private theorem fork_lowbridge_waste_seat {st : State} {x : Card}
    (hx : ForkWitness st x)
    {u v : State} (hmem : sameOrbitSetoid.r st u)
    {c : Card} {b : Base}
    (hstep : State.step u (Move.wasteToTab c b) = some v)
    (hiv : irreversibleAt u (Move.wasteToTab c b))
    (helev : ¬ familyBelowFrontier u x) :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      sameOrbitSetoid.r v₀ v := by
  obtain ⟨hg, -⟩ := step_wasteToTab_inv hstep
  rw [Bool.and_eq_true] at hg
  have hfu : WasteGuard u (Move.wasteToTab c b) :=
    Or.inr ⟨c, b, rfl, hg.1, hg.2⟩
  obtain ⟨u₀, hmem₀, hslab₀, hfu₀⟩ := lowslab_waste_reseat hx hmem helev hfu
  have hclass : sameOrbitSetoid.r u₀ u :=
    sameOrbitSetoid.iseqv.trans (sameOrbitSetoid.iseqv.symm hmem₀) hmem
  obtain ⟨v₀, hstep₀⟩ := lowslab_waste_guard_fires hfu₀
  exact ⟨u₀, Move.wasteToTab c b, v₀, hmem₀, hslab₀, hstep₀,
    lowslab_waste_targetclass hclass hfu hfu₀ hstep hstep₀⟩

/-- **THE PLACEMENT ZONE-KEEP KIT** (private, per-file — the house
copy of the placement half of the sibling's zone-keep kit): a card
placement reads and writes piles only, so the two-zone cycle is
untouched. -/
private theorem lowslab_putCard_zone (s : State) (c : Card) (b : Base) :
    (s.putCard c b).stock = s.stock ∧ (s.putCard c b).waste = s.waste := by
  cases b with
  | inl a => exact ⟨rfl, rfl⟩
  | inr z =>
      simp only [State.putCard]
      split <;> exact ⟨rfl, rfl⟩

/-- A run placement likewise keeps the two-zone cycle. -/
private theorem lowslab_putRun_zone (s : State) (run : List Card) (b : Base) :
    (s.putRun run b).stock = s.stock ∧ (s.putRun run b).waste = s.waste := by
  cases b with
  | inl a => exact ⟨rfl, rfl⟩
  | inr z =>
      simp only [State.putRun]
      split <;> exact ⟨rfl, rfl⟩

/-- **THE WITNESS CYCLE PIN** (private kit) — every leg of a witness
journey keeps the cycle count: board letters keep the two-zone cells
verbatim (the foundation write and the placement writes touch piles
and founds only), and a draw leg conserves the count
(`stepDraw_cycle` reads the deal/recycle split arithmetic).  So a
witness journey's two ends read the same cycle-count, and a draw
that fires at one end fires at the other. -/
private theorem lowslab_witness_cycle_pin {st : State} :
    ∀ {ρ : List Move} {w : State},
      ShufflePlayW st ρ w → cycleCount st = cycleCount w := by
  intro ρ w h
  induction h with
  | nil u => rfl
  | @cons u m s₁ rest w' hw hstep hrest ih =>
      have hleg : cycleCount s₁ = cycleCount u := by
        obtain hmd | ⟨c, hc⟩ | ⟨c, bb, hc⟩ | ⟨c, bb, hc⟩ :=
          witness_leg_letters hstep hw
        · subst hmd
          exact stepDraw_cycle hstep
        · subst hc
          obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
          rw [hs]
          rfl
        · subst hc
          obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv hstep
          rw [hs]
          have hz := lowslab_putCard_zone
              (u.setFound c.suit (chop (u.found c.suit))) c bb
          exact cycleCount_eq_of_stock_waste hz.1 hz.2
        · subst hc
          obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv hstep
          rw [hs]
          have hz := lowslab_putRun_zone
              (u.setPile a (Pile.afterRunRemoved (u.piles a)
                (below c (u.piles a).faceUp)))
              (fromCard c (u.piles a).faceUp) bb
          exact cycleCount_eq_of_stock_waste hz.1 hz.2
      exact hleg.symm.trans ih

set_option linter.unusedVariables false in
/-- **THE DRAW-CURSOR REPLAY ROW** `fork_lowbridge_draw` [CLOSED at the
chain-scaffold pass] — given the ELEVATED commit of kind draw-cursor
(a committed `draw` from `u` into `v`), the FORK ITSELF is the
duplicate: the same `Move.draw` re-fires at `st` (the witnessing
journey keeps the cycle count, and `u`'s firing certifies a positive
cycle), and the two landings are class-mates by the sibling's CLOSED
interleave scaffold.

ROUTE (assembled; every step banked, zero own content):

1. THE CLASS ANCHOR: `sameOrbit_forward` unpacks the membership into
   a forward witness journey `ρ : ShufflePlayW st ρ u`; the fork
   self-anchors on its slab (`fork_self_low`), so `u₀ := st` and
   `m₀ := Move.draw` carry the first two conjuncts by reflexivity and
   the self-slab row.
2. THE RE-FIRE — THE CYCLE PIN: every leg of `ρ` keeps `cycleCount`
   (board letters keep the two-zone cells verbatim — the placement
   and foundation writes touch piles and founds only; draw legs
   conserve `stepDraw_cycle`), so `cycleCount st = cycleCount u`; the
   commit step fired at `u`, so `EdgeKit.stepDraw_pos_cycleCount`
   hands a positive cycle at `u`, hence at `st`, and
   `EdgeKit.stepDraw_of_pos_cycleCount` fires the same draw there.
3. THE TARGET MATCH — NO (A)/(B) DICHOTOMY: the sibling's chain
   scaffold (`chain_assembly` over `interleave_leg_conjugation`,
   both WF-free statements, both closed zero-sorry in
   `Orig/HostCensus.lean` §9.3) conjugates the outcome draw past
   EVERY reversible leg of `ρ` — board letters by the class weld and
   the banked draw push, draw letters by `stepDraw_cycle` — so
   `sameOrbitSetoid.r v₀ v` for the re-fired landing `v₀` and the
   commit target `v`, with no draw-free case split and no per-leg
   mirror kit.

HONEST GRADE NOTES (what the closure prices):

* The commit premise `hiv` and the elevation premise `helev` are
  NOT consumed: the row holds for EVERY draw that fires at a class
  member — the commit grade never enters the replay, and the fork's
  own slab self-anchoring makes the twin-side elevation clause
  irrelevant to the draw kind.  The statement is kept byte-frozen
  (the caller's contract); the unused binders are silenced below.
* THE (B)-CARRY's WF GATE is AVOIDED, not paid:
  `interleave_phase_align`'s vestigial `u₀.WF` premise is a
  statement artifact of its landing — the scaffold rows it rides are
  WF-free, so this row cites `chain_assembly ∘ interleave_leg_conjugation`
  directly and the old WILD-grade (B) gap is closed outright.
* THE DASHED-WITNESS TRANSPORT is RETIRED here: the closed scaffold
  welds the leg pair into the macro class (`class_leg` + the round-trip
  engine) and hands the dashed landings to the banked draw push, so
  no per-leg `reversibleAtW` re-firing certificate is ever needed.
* THE CURSOR FACT need not be invoked: firing is the cycle pin
  alone (the cursor fact — `lowslab_draw_emptyReversible` — stays
  this tree's own [M] piece for consumers of the fired/no-op
  dichotomy, not for the class replay).

PROBE NOTE (Orig/LowSlabProbe.lean, decide-grade): both ends of
this row are instantiated on-board — the commit side twice
(`lb0_drawCommit`/`lb1_drawCommit`, pristine-grade via Phase's banked
row) and the duplicate side END-TO-END (`lb1_dup`: the draw-commit's
slab duplicate fully assembled, class legs commuting with the zone
move pointwise, kernel-equal composites).  The assembled proof is
the general form of that one board. -/
private theorem fork_lowbridge_draw {st : State} {x : Card}
    (hx : ForkWitness st x)
    {u v : State} (hmem : sameOrbitSetoid.r st u)
    (hstep : State.step u Move.draw = some v)
    (hiv : irreversibleAt u Move.draw)
    (helev : ¬ familyBelowFrontier u x) :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      sameOrbitSetoid.r v₀ v := by
  -- step 1: the forward witness journey and the self-anchored slab
  obtain ⟨ρ, hρ⟩ := sameOrbit_forward hmem
  -- step 2: the cycle pin — the journey keeps the count, so the
  -- draw fires at the fork exactly as at the elevated member
  have hpin : cycleCount st = cycleCount u := lowslab_witness_cycle_pin hρ
  have hpos : 0 < cycleCount u := EdgeKit.stepDraw_pos_cycleCount hstep
  have hpos' : 0 < cycleCount st := by omega
  obtain ⟨v₀, hd₀⟩ := EdgeKit.stepDraw_of_pos_cycleCount hpos'
  have hdstep : State.step st Move.draw = some v₀ := hd₀
  -- step 3: the target match, by the closed chain scaffold
  exact ⟨st, Move.draw, v₀, sameOrbitSetoid.iseqv.1 st, fork_self_low hx,
    hdstep, chain_assembly interleave_leg_conjugation st ρ u hρ v₀ v
      hdstep hstep⟩

/-- **THE PULL REPLAY RESIDUE — THE WILD REMAINDER** `fork_lowbridge_pull`
[H, shrunk at the probe-triage pass] — given the ELEVATED commit of
kind pull (a committed foundation giveback `foundToTab c b` from `u`
into `v`), a slab member `u₀` carries a same-target-class step.

PROBE EVIDENCE FIRST (Orig/LowSlabProbe.lean, decide-grade): both
engineered instantiation attempts — the twin takeback at `lb1`
(`lb1_pullRev`) and the KING giveback to an empty anchor on the
dedicated `kb` economy (`kb_pullRev`) — came out mirror-reversible,
kernel-verified.  The general WF mirror row is now PROVED in this
very file (`lowslab_pull_wf_undo`, promoted from the [M] residue at
this pass), and its corollary `lowslab_pull_never_commit_wf` closes
the arm outright: AT A WF MEMBER THE PULL NEVER COMMITS.  The row is
kept (not retired) because the main statement is WF-free by design
and the dispatcher cannot case on WF without classical machinery —
the wild members of a fork's class still arrive here, and the
residue's live content is exactly that remainder.

ROUTE (shrunk; each step priced):

1. THE ELEVATED READ and THE CLASS ANCHOR: as the raise row's steps
   1-2.
2. THE WF ARM IS CLOSED, not census-hoped: `lowslab_pull_never_commit_wf`
   (this §4.1) is a plain contradiction row now — at a WF member the
   `hiv` premise is impossible.  For a WILD member the commit means
   NO return play exists, so the giveback's landing seat and the
   foundation's chopped row are pinned by the step's own guards
   (`step_foundToTab_inv`: `foundTop = some c`, the placement held).
3. THE WILD REPLAY [THE OPEN STEP — the row's whole remaining
   content]: the duplicate giveback at a slab member reproducing the
   chopped foundation row and the placement seat — priced against the
   same census brackets as the raise row's step 4 (the rung ledger of
   the involved suit along the two journeys;
   `foundToTab_pops_currentTop` for the popped current top), with the
   wild corners (doubled cards, miscounted rungs) named honestly: the
   replay must not assume card uniqueness.
4. THE CLASS LINKS: as the raise row's step 5.

POST-COMMUTATION-SWAP: ASSESSED — UNCHANGED: the congruence rows
live at `boardEq` pairs and WV-normal members; this row's live
content is the WILD remainder (where `boardEq`-blindness of the
draws is not even the relevant instrument), so no consumption and
no shrink are honest there.

FINALE ASSESSMENT (2026-10-13, re-verified): the WILD-REMAINDER
stance stands — no cheap wild argument surfaced this pass: wild
members carry no WF discipline (doubled cards, free rungs), the
congruence kit is `boardEq`-blind where wild boards are exactly the
worry, and a wild giveback replay would need its own bracket census
without the WF fence.  The row carries honestly as [H,
WILD-REMAINDER ONLY]; the WF arm stays retired in the proved
`lowslab_pull_wf_undo` + `lowslab_pull_never_commit_wf` pair above.

SESSION-2 ADDENDUM (2026-10-13, the take-over pass): the elevated
read and class anchor of step 1 (the route's "as the raise row's
steps 1-2") are now BANKED IN-FILE as `lowslab_elevation_crossing`
(proved, zero-sorry, §4.2.0 above): the witnessing journey to the
elevated member crosses the fork threshold at a REVERSIBLE raise of
the covered twin itself, at a fork-exact boundary member on the
slab — so any future wild-replay construction starts from that
boundary member's own geometry instead of re-deriving it.  The
  row's grade is unchanged: [H, WILD-REMAINDER ONLY].

  SESSION-3 ASSESSMENT (2026-10-13, the third succession): grade
  unchanged, [H, WILD-REMAINDER ONLY] — the WF arm stays retired in
  the proved `lowslab_pull_wf_undo` + `lowslab_pull_never_commit_wf`
  pair, and the wild replay still has no WF-free mirror: the pull
  undos' rank and search premises name the very doubled-card and
  miscounted-rung corners the wild members live in (each premise of
  `foundToTab_undo` fences exactly one), so the row hosts as the
  campaign's final honest wild-remainder carry per the owner's
  third-succession instruction, statement byte-frozen. -/
private theorem fork_lowbridge_pull {st : State} {x : Card}
    (hx : ForkWitness st x)
    {u v : State} (hmem : sameOrbitSetoid.r st u)
    {c : Card} {b : Base}
    (hstep : State.step u (Move.foundToTab c b) = some v)
    (hiv : irreversibleAt u (Move.foundToTab c b))
    (helev : ¬ familyBelowFrontier u x) :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      sameOrbitSetoid.r v₀ v := by
  sorry

/-! ### §4.3. The dispatcher (proved) -/

/-- **THE ELEVATION SPLIT — THE DISPATCHER** — the non-empty arm of
the sufficiency, in the twin-side refinement's reading: `helev` says
the member `u` has CONSUMED THE TWIN (its suit's rung is strictly
past the fork point — by the one-founding row's door complex the
live member is then necessarily out; at the WF grade the twin is
out of the tableau, `Orig/SlabEquiv.twin_slab_tableau`).  The row is
a pure dispatch: the six constructor arms of the committed move
route to the six per-kind replay residues, the assembly into the
main statement's five conjuncts being the assemble row's; the
`ForkWitness` parcel is carried for the per-kind routes' census
readings (the fork point and the family saturation), nothing else;
the row adds NO content of its own — zero-sorry by construction.

Hypothesis package, honestly: the fork (`hx`, the per-kind census
readings), the class membership (`hmem`, both journey extractions),
the committed step and its grade (`hstep`, `hiv` — the grades are
never re-derived, only routed), and the case fact (`helev`, the
dispatcher's caller derives it from the empty arm's dichotomy).  No
WF anywhere; hypotheses that would be derivable (the elevated rung
read, for instance — one `omega`) are derived in the consumers, not
re-stated. -/
private theorem fork_lowbridge_elevated {st : State} {x : Card}
    (hx : ForkWitness st x)
    {u v : State} (hmem : sameOrbitSetoid.r st u)
    {m : Move} (hstep : State.step u m = some v)
    (hiv : irreversibleAt u m)
    (helev : ¬ familyBelowFrontier u x) :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      irreversibleAt u₀ m₀ ∧
      sameOrbitSetoid.r v₀ v := by
  cases m with
  | draw =>
      exact fork_lowbridge_assemble hmem hstep hiv
        (fork_lowbridge_draw hx hmem hstep hiv helev)
  | wasteToFound c =>
      exact fork_lowbridge_assemble hmem hstep hiv
        (fork_lowbridge_waste_found hx hmem hstep hiv helev)
  | wasteToTab c b =>
      exact fork_lowbridge_assemble hmem hstep hiv
        (fork_lowbridge_waste_seat hx hmem hstep hiv helev)
  | tabToFound c =>
      exact fork_lowbridge_assemble hmem hstep hiv
        (fork_lowbridge_raise hx hmem hstep hiv helev)
  | foundToTab c b =>
      exact fork_lowbridge_assemble hmem hstep hiv
        (fork_lowbridge_pull hx hmem hstep hiv helev)
  | tabToTab c b =>
      exact fork_lowbridge_assemble hmem hstep hiv
        (fork_lowbridge_reveal hx hmem hstep hiv helev)

/-! ### §4.4. THE MAIN ROW -/

/-- **THE LOW-SLAB SUFFICIENCY** — the fork's exploration budget: any
COMMITMENT out of a fork's macro class — any `irreversibleAt` move,
the program's own commit grain — is matched by a LOW DUPLICATE: a
commitment from a class member on the low slab (the twin side: the
covered twin not founded, at the WF grade the twin still in the
tableau), into the SAME TARGET CLASS.  An explorer of the
neighboring macro classes therefore only ever needs to probe the low
slab.

Hypotheses read (unchanged from the original landing, the slab
conjunct refinements traveling through the def alone): `st` is the
fork (witness `x`, fork point `x.rank.toIdx`); `u` rides the fork's
class and `m` commits there (`hstep` names the successor `v`; `hiv`
the commit — no play of any grain returns;
`commit_exits_class` derives the setoid-class exit for consumers of
that reading).  Conclusion: a slab member `u₀` of the same class, a
move `m₀` from it with successor `v₀`, ITSELF a commit
(`irreversibleAt u₀ m₀` — free by the glue row once the replay
rows produce the class links), with `v₀` IN THE SAME TARGET CLASS.

This is the NEIGHBOR form of the reach-corridor claim ("to explore
any reachable macro class, twin-consumed states never need be
inhabited"): the corridor form follows by recursion over the macro
descent, each frontier class spending its own slab — deferred until
this tree's residues land.

THE RESIDUE TREE (each virus-[graded; complete routes in the
per-行的 docstrings):

* The empty arm is PROVED: `fork_lowbridge_empty` — a committing
  slab member is its own duplicate.
* The elevation split is PROVED: `fork_lowbridge_elevated` — a
  twin-consuming member dispatches to the per-kind rows.
* The class-link glue is PROVED: `fork_lowbridge_commitGlue` —
  the duplicate's commit grade is free from the class links.
* The census consumption rows: `lowslab_pull_wf_undo` [PROMOTED,
  proved] and `lowslab_draw_emptyReversible` [LANDED at the
  2026-10-13 finale, zero-sorry — the long-waste cursor loop's block
  induction]; `lowslab_top_census` [H] survives (the card-level
  bootstrap + the slab-side landing) — the facts the kind routes
  price their open steps against.
* The per-kind replay rows: `fork_lowbridge_draw` LANDED at the
  chain-scaffold pass (zero-sorry, over the sibling's closed
  commutation kit — the fourth kind this campaign added to the
  taxonomy is thereby retired); `fork_lowbridge_raise` [H],
  `fork_lowbridge_reveal` [H] survive (the rung bracket + the
  card-level bootstrap; the re-scheduling + the same-fit assembly);
  `fork_lowbridge_waste_found` and `fork_lowbridge_waste_seat` are
  PROVED ROUTERS (the waste-shrink pass), their graded content
  riding the two shared named residues `lowslab_waste_reseat` [H]
  and `lowslab_waste_targetclass` [H];
  `fork_lowbridge_pull` [H — plausibly vacuous at a WF gate; the
  wild remainder carried honestly for the WF-free statement].

INTEGRATOR MAP: the draw kind is CLOSED (the sibling's commutation
kit paid it in full — `chain_assembly` + `interleave_leg_conjugation`
cited WF-free; the two-zone pin `cycle_zone_pin` stays
`Orig/SlabEquiv.lean`'s for the membership readings); the waste
kind's remaining algebra lives entirely in the two shared named
residues (the cursor-orbit re-scheduling onto a slab member — the
round-2 probe's shifted-cursor refusal on record as the boundary
datum — and the dashed-witness weld); the raise and reveal rows
share the seat census (`lowslab_top_census`) — together with it the
[H]-graded nontrivial leaves the mission predicted (the elevation
mechanism's arrangement face and the crane replay); the pull row is
the wild-regime safety net, first candidate for retirement.

REFUTER-FIRST — the probe boards (the `CrossFamilyProbe` harness):
Q(A) do fork boards carrying lone above-frontier twin-cover tops
admit witness round-trips past the twin's founding door (twin-lift
realizable in-class: hop the cover off the twin, then `tabToFound`
the twin with a live takeback — the refinement's own probe
emphasis)?  Q(B) at twin-consuming members, is every legal
COMMITMENT matched by a slab-departing commitment into the same
target class?  The draw-cursor kind (see
`fork_lowbridge_draw`'s census note) makes Q(B) strictly stronger
than the original three-kind reading — a single Q(B)
counterexample board reshapes the frontier (per-suit relaxation),
the repair documented alongside — the `pullEscape` precedent.

Grading: [H] research-grade overall, per the residue list above;
the statement is byte-frozen; the fresh heads audited below. -/
theorem fork_neighbor_lowbridge {st : State} {x : Card}
    (hx : ForkWitness st x)
    {u v : State} (hmem : sameOrbitSetoid.r st u)
    {m : Move} (hstep : State.step u m = some v)
    (hiv : irreversibleAt u m) :
    ∃ (u₀ : State) (m₀ : Move) (v₀ : State),
      sameOrbitSetoid.r st u₀ ∧
      familyBelowFrontier u₀ x ∧
      State.step u₀ m₀ = some v₀ ∧
      irreversibleAt u₀ m₀ ∧
      sameOrbitSetoid.r v₀ v := by
  rcases Nat.lt_or_ge (x.rank.toIdx) (rungAt u x.twin.suit) with h | h
  · exact fork_lowbridge_elevated hx hmem hstep hiv
      (by
        unfold familyBelowFrontier
        omega)
  · exact fork_lowbridge_empty hmem
      (by
        unfold familyBelowFrontier
        exact h) hstep hiv

/-! ## The audit battery

`#print axioms` per fresh head: the slab def is statement-facing;
`fork_self_low`, the run-append compose, both commit-grade rows are
zero-sorry and read banked-chain grade; the §4.0 arms and the
dispatcher are zero-sorry; the probe-triage additions
(`lowslab_draw_reversible_phase`, `lowslab_pull_wf_undo`,
`lowslab_pull_never_commit_wf`) are zero-sorry; the waste-shrink
pass's engine kit, the finale's engine kit and the finale's
guard-refusal transport pair (`lowslab_witness_cycle_pin`,
`zone_loop_terminal`, `zone_loop_return`, `waste_head_refusal`,
`witness_zone_flat`, `lowslab_bracket_transfer`,
`lowslab_slide_board_refire`) are zero-sorry; the take-over pass's
journey mechanism kit (the class-weld copy
`lowslab_shuffleW_of_round`/`lowslab_class_leg`, the membership walk
`lowslab_journey_class`, the four per-leg rung deltas, the rung-walk
engine `lowslab_rung_walk`, the ELEVATION CROSSING
`lowslab_elevation_crossing`, and the waste trio
  `lowslab_waste_head_of`/`lowslab_waste_guard_fires`/
  `lowslab_pair_netcensus`) are zero-sorry; the session-3 pins
  (§4.1.5: `lowslab_fork_pair_rungs`, `lowslab_class_hiddenPinned`,
  `lowslab_top_census_hidden`, `lowslab_raise_commit_shape_wf`) are
  zero-sorry; the two LANDED residues read
  `[propext, Quot.sound]` (`lowslab_draw_emptyReversible` — the
  finale's block induction over the Phase wrapper;
  `fork_lowbridge_draw` — the chain-scaffold landing over the
  sibling's closed commutation kit).  `fork_neighbor_lowbridge`
carries the SIX named residues of §4.1-§4.2 (`lowslab_top_census`
(as REPAIRED this pass, the `ForkWitness` parcel restored),
`fork_lowbridge_raise`, `fork_lowbridge_reveal`,
`lowslab_waste_reseat`, `lowslab_waste_targetclass` (as SHRUNK this
pass, claiming only the class-mateship), `fork_lowbridge_pull`, the
last through the two PROVED waste
routers `fork_lowbridge_waste_found`/`fork_lowbridge_waste_seat`)
and NOTHING else flows into it.  NONE of the consumed rows rides
the sibling's residue `witness_leg_mint_confined`; the sorry COUNT
is exactly the six, and `fork_neighbor_lowbridge`'s profile must
stay `[propext, sorryAx, Quot.sound]` with no new inflow — verified
below.  THE SESSION-4 ADDITION (the reseat refutation board,
§4.2.a.R): every board row is zero-sorry at decide/defeq grade —
the SB-door fork parcel (`forkWitnessRowSB wr_st 4♥`, one decide)
bridged by `forkWitnessRowSB_iff`, the step facts and state
ext-dances riding `funext` — with NO `Classical.choice` anywhere
(the one new import, `Orig.ForkStateSB`, sits below the already
transitively-present `Orig.PairName → Orig.ForkWeaker` chain, so
no cycle and no new inflow); `lowslab_waste_reseat_refuted` — the
certified negation of the reseat residue's own statement — is
ZERO-sorry, and the sorry count stays exactly the six. -/

#print axioms lowslab_draw_reversible_phase
#print axioms lowslab_pull_wf_undo
#print axioms lowslab_pull_never_commit_wf
#print axioms lowslab_witness_cycle_pin
#print axioms fork_self_low
#print axioms commit_exits_class
#print axioms commit_blocks_class_return
#print axioms fork_lowbridge_empty
#print axioms fork_lowbridge_commitGlue
#print axioms zone_loop_terminal
#print axioms zone_loop_return
#print axioms waste_head_refusal
#print axioms witness_zone_flat
#print axioms lowslab_bracket_transfer
#print axioms lowslab_slide_board_refire
#print axioms lowslab_shuffleW_of_round
#print axioms lowslab_class_leg
#print axioms lowslab_journey_class
#print axioms lowslab_rung_delta_draw
#print axioms lowslab_rung_delta_tabToTab
#print axioms lowslab_rung_delta_tabToFound
#print axioms lowslab_rung_delta_foundToTab
#print axioms lowslab_rung_walk
#print axioms lowslab_elevation_crossing
#print axioms lowslab_waste_head_of
#print axioms lowslab_waste_guard_fires
#print axioms lowslab_pair_netcensus
#print axioms lowslab_draw_emptyReversible
#print axioms lowslab_fork_pair_rungs
#print axioms lowslab_class_hiddenPinned
#print axioms lowslab_top_census_hidden
#print axioms lowslab_raise_commit_shape_wf
#print axioms lowslab_top_census
#print axioms fork_lowbridge_raise
#print axioms fork_lowbridge_reveal
#print axioms lowslab_waste_reseat
#print axioms lowslab_waste_targetclass
#print axioms fork_lowbridge_waste_found
#print axioms fork_lowbridge_waste_seat
#print axioms fork_lowbridge_draw
#print axioms fork_lowbridge_pull
#print axioms fork_lowbridge_elevated
#print axioms fork_neighbor_lowbridge
#print axioms wr_st_wf
#print axioms wr_fork
#print axioms wr_hop_fires
#print axioms wr_st'_eq
#print axioms wr_unhop_fires
#print axioms wr_raise_fires
#print axioms wr_s1'_eq
#print axioms wr_giveback_fires
#print axioms wr_class
#print axioms wr_helev
#print axioms wr_guard
#print axioms lowslab_waste_reseat_refuted
