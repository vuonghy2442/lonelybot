import Orig.PairName
import Orig.BracketDecomp
import Orig.SlabEquiv
import Orig.Reach
import Orig.Classify
import Orig.HostCensus

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
* §4 THE RESIDUE TREE (post probe-triage AND census swap): the
  sufficiency, routed.  **THE EMPTY ARM** `fork_lowbridge_empty`
  (proved): a committing member already on the slab closes by
  itself.  **THE CLASS-LINK GLUE** `fork_lowbridge_commitGlue`
  (proved): the duplicate's commit grade is free from the class
  links alone.  THE PROVED CENSUS ROWS: `lowslab_draw_reversible_phase`
  (the deduped Phase wrapper for the ≤-deal draw fragment),
  `lowslab_pull_wf_undo` (PROMOTED at the probe-triage pass) with its
  corollary `lowslab_pull_never_commit_wf` (the pull arm is VOID at
  WF, theorem-grade).  THE NAMED RESIDUES (EIGHT, post-swap grades):
  `lowslab_top_census` [H, SHRUNK at the swap: the seat transport is
  banked (`Orig/HostCensus.lean`'s ledger family); the survivors are
  the card-level bootstrap and the slab-side landing],
  `lowslab_draw_emptyReversible` [M, shrunk to the long-waste cursor
  loop], `fork_lowbridge_raise` [H: transport + commit-modes banked
  (`census_tabToFound_witness`, `bare_lift_irreversibleAt`); the
  rung bracket survives per the seats-vs-rungs adjudication],
  `fork_lowbridge_reveal` [H: cargo transport + commit-modes banked
  (`census_tabToTab_inr_witness`, `bare_burn_irreversibleAt`); the
  card-level re-scheduling survives],   `fork_lowbridge_waste_found`
  [M — the CURSOR COINCIDENCE is now theorem-grade (the commutation
  swap: `board_run_congr` carries the zone verbatim; the probe's
  shifted-cursor refusal transports); the survivors are the
  HOT-BRACKET (a rung question, the raise row's family) and the
  shared DASHED-WITNESS TRANSPORT],
  `fork_lowbridge_waste_seat`
  [M: same, the landing base census-priced],   `fork_lowbridge_draw` [H — SUBCONTRACTED at the commutation swap:
  the draw-free case rides `drawfree_commute_ reach`/`_witness` (the
  dashed thread lands PHASE-EXACTLY, banked upstream) plus one named
  [M] piece (the DASHED-WITNESS TRANSPORT); the interleaved case is
  CITED as `interleave_phase_align` (the sibling's own single
  residue, WF-graded, its sorryAx flowing transitively when cited
  in a built proof — the wild-grade (B) is the flagged gap); at a
  WF gate the draw-kind closes to assembly + cite],
  `fork_lowbridge_pull` [H, WILD-REMAINDER ONLY: the WF arm retired
  into the corollary; the row survives for the WF-free statement's
  wild members].  Each residue carries a complete priced route with
  the probe evidence folded in (`Orig/LowSlabProbe.lean`); the census
  swap is applied row by row (the old HOSTCENSUS SWAP-POINT labels
  now read POST-SWAP with the consumed rows named), and NOTHING
  consumes the sibling's own residue `witness_leg_mint_confined`.
  The private dispatcher `fork_lowbridge_elevated` (proved,
  zero-sorry) routes the six constructor arms through the assemble
  row.  The main head concludes by the empty/elevated dichotomy —
  its proof is a short routing skeleton and nothing else.

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
additive leaf below `Orig.BracketDecomp`, so no cycle); every fresh
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

/-- **THE CURSOR LOOP ROW** `lowslab_draw_emptyReversible` [M,
shrunk at the probe-triage pass] — an empty-stock draw at a positive
step size is UNDOABLE, so a COMMITTED draw can never fire at an empty
stock.

ROUTE (post-dedup; each step banked, mechanical, or the rows this
tree names):

1. DICHOTOMY at the draw: `hstep` at an empty stock forces the waste
   nonempty (the both-empty draw refuses to fire: the recycle is the
   identity and the deal at an empty stock is `none`), and `draw_unfold`
   (`Orig/Play.lean`) reads the leg as one recycle then one
   `dealUpTo` — the two-zone arrangement of the same multiset
   (`cycle_zone_pin`, `Orig/SlabEquiv.lean`).
2. THE ≤-DEAL FRAGMENT IS BANKED — OUTSOURCED, not re-derived: Phase's
   `draw_reversible_selfRecycleW`, cited through the proved wrapper
   `lowslab_draw_reversible_phase` above: when the whole waste fits
   one deal the draw is a no-op.
3. THE LONG-WASTE CURSOR LOOP — THE ROW'S WHOLE OPEN CONTENT
   (`waste.length > drawStep`): the block induction on the recycled
   arrangement's length: each draw peels at most `drawStep` heads of
   the current stock into the waste (the measure: the intermediate
   stock length; the invariant: `waste = the reversed peeled prefix`),
   and the TERMINAL CLIPPED DEAL — the stock shorter than one deal —
   saturates the take and restores the pre-draw arrangement exactly
   (`dealUpTo_eq_take_drop`'s take/drop split plus
   `sequ_mem_of_reverse`-flavored arithmetic).  THE WITNESS: the
   concatenated draw play of the inductive length.
4. PROBE NOTE (`Orig/LowSlabProbe.lean`, decide-grade): the
   contrapositive side is instantiated on-board — draws at NONEMPTY
   stock are pristine-grade commitments at the lb-boards
   (`lb0_drawCommit`/`lb1_drawCommit`), and the draw-commit's slab
   duplicate is exhibited end-to-end (`lb1_dup`) — the row's consumer
   `fork_lowbridge_draw` has worked evidence at both ends.

HOSTCENSUS SWAP-POINT: the sibling census program's deals-draw rows
(guaranteed-restore draw censuses) may replace step 3 wholesale; the
swap target is this row's step-3 induction. -/
private theorem lowslab_draw_emptyReversible {u s₁ : State}
    (hds : 0 < u.drawStep)
    (hempty : u.stock = [])
    (hstep : State.step u Move.draw = some s₁) :
    reversibleAtW u Move.draw := by
  sorry

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
row's card-level bootstrap crosses ρ-images; the dashed-thread
fragments of its consumers' assemblies share the DASHED-WITNESS
TRANSPORT named in the draw row.  Consumers:
`fork_lowbridge_raise` step 4 and
`fork_lowbridge_reveal` step 3. -/
private theorem lowslab_top_census {st u : State} {x : Card} {c : Card}
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
the re-fire assembly's draw-dashed contexts share the DASHED-
WITNESS TRANSPORT of the draw row's case (A) — and the survivors
are unchanged: the rung bracket (this row's own, per the
seats-vs-rungs adjudication) + the card-level bootstrap.  Earlier
consumptions (`census_tabToFound_witness`, `witness_bare_lift_king`,
`bare_lift_irreversibleAt`) stand. -/
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
draw-dashed fragments of the assembly share the DASHED-WITNESS
TRANSPORT of the draw row's case (A).  The earlier consumptions
stand: `census_tabToTab_inr_witness`, `census_tabToTab_inl`,
`bare_burn_irreversibleAt`, `witness_tabToTab_never_burn` (transport
+ commit modes); the seat-side deep support is
`lowslab_top_census`'s banked step-2 family plus its surviving
card-level bootstrap. -/
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

/-- **THE WASTE-JUMP REPLAY RESIDUE** (pop-to-foundation arm)
`fork_lowbridge_waste_found` [M] — given the ELEVATED commit of kind
waste-jump (a committed `wasteToFound c` from `u` into `v`), a slab
member `u₀` carries a same-target-class step.

ROUTE (complete; each step priced):

1. THE ELEVATED READ and THE CLASS ANCHOR: as the raise row's steps
   1-2.
2. THE CYCLE CENSUS — THE CURSOR COINCIDENCE IS NOW THEOREM-GRADE:
   the witnessing `st ⇝ u` journeys are board-only, and the
   sibling's `board_run_congr` carries the ZONE VERBATIM through
   them (`z.stock = x.stock ∧ z.waste = x.waste ∧ z.drawStep =
   x.drawStep` at the image — not merely the membership pin): the
   committed card `c` is the waste HEAD at `st` exactly as at `u`,
   and `cycle_zone_pin` (`Orig/SlabEquiv.lean`) remains the
   membership-flavored companion.  The round-2 probe's negative
   datum transports theorem-grade: the shifted-cursor site refuses
   the re-fire because the GUARD reads the zone, and the zone is
   invariant along the class — the shift cannot happen in-class.
3. THE REMAINING [M] CONTENT, shrunk to two named pieces:
   (a) THE HOT-BRACKET — the head card is class-invariant, so the
   re-fire's `nextUp c` read is a RUNG question: some slab member's
   `c.suit` rung must read `c.rank.toIdx` (the same unclosed
   bracket family the raise row flags; probe-verified benign at
   every tried shape — the elevation legs of the probe boards
   never touched the waste-head's suit);
   (b) THE DASHED-WITNESS TRANSPORT (shared with the draw row's
   case (A), named there): the per-leg grades of the re-fire chain
   at the post-commit states.
4. THE CLASS LINKS: as the raise row's step 5.  The stock/waste zone
   is class-closed in the census sense; the waste-jump's grade
   mechanism itself (`cycleCount` strictly drops, Table 1 of
   `Orig/Irreversible.lean`) plays no role here — `hiv` is given.

HOSTCENSUS POST-COMMUTATION-SWAP (the cursor face is now
THEOREM-GRADE): the sibling's `witness_leg_letters` packages the
leg-shape discipline (no waste letter rides a witness journey);
`board_run_congr` carries the ZONE VERBATIM along the board-only
class journeys — the cursor-coincidence of step 2 is banked, and
the round-2 probe's negative datum (the shifted-cursor site refuses
the re-fire) transports theorem-grade: the guard reads the zone and
the zone is class-invariant; the shift cannot arise in-class at
all.  The seat side of any landing the re-fire consults rides the
census cell-transport family (`census_tabToTab_*`,
`census_foundToTab_inr`, `census_step_draw`) plus the
ledger/repayment family (`seatLedger_pair`,
`excursion_issues_noNewSeat`).  WHAT SURVIVES THE COMMUTATION SWAP
is the two named pieces of step 3: the HOT-BRACKET (a rung
question — the same family the raise row flags, per the
seats-vs-rungs adjudication) and the shared DASHED-WITNESS
TRANSPORT; the arrangement face the old route carried is retired
into `board_run_congr`'s flats.  None of the consumed rows rides
the sibling's residue `witness_leg_mint_confined`. -/
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
  sorry

/-- **THE WASTE-JUMP REPLAY RESIDUE** (seat arm)
`fork_lowbridge_waste_seat` [M] — the `wasteToTab` arm of the
waste-jump kind; route identical to `fork_lowbridge_waste_found`'s
(the cursor coincidence now theorem-grade via `board_run_congr`,
per that arm's step 2), with the re-fire additionally consulting
the landing base's top seat — census-priced upstream: the base
card's cell rides the ledger/repayment family (`seatLedger_pair`,
`excursion_issues_noNewSeat`) and the leg letters are one cited row
(`witness_leg_letters`).  POST-COMMUTATION-SWAP SURVIVORS: the
HOT-BRACKET (the rung question, as in the pop-to-foundation arm)
and the shared DASHED-WITNESS TRANSPORT, with
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
  sorry

/-- **THE DRAW-CURSOR REPLAY RESIDUE** `fork_lowbridge_draw` [H] —
given the ELEVATED commit of kind draw-cursor (a committed `draw`
from `u` into `v`), a slab member `u₀` carries a same-target-class
step.  [FOURTH KIND, flagged to the integrator: neither the original
three-kind taxonomy (raise-like / reveal / waste-jump) nor the
measure tables name the draw — but a draw at a NONEMPTY stock is a
genuine commitment: the stock's refills are wholesale reversals of
the waste, and the deal always fires after the recycle
(`draw_unfold`: `dealStock` at a nonempty recycled stock deals at
least one card at a positive step size), so the pre-draw arrangement
never recurs; the returning play's last cycle-writer would have to
re-grow the cycle zone, which no leg ever does.  The three-kind
routes must acquire this arm.]

ROUTE (complete; each step priced):

1. THE ELEVATED READ and THE CLASS ANCHOR: as the raise row's steps
   1-2.
2. THE CURSOR FACT (priced against `lowslab_draw_emptyReversible`,
   whose ≤-deal fragment is now BANKED through
   `lowslab_draw_reversible_phase`): a committed draw cannot fire at
   an EMPTY stock (the cursor loop returns), so at `0 < drawStep` it
   fires at a nonempty stock (the cursor-commit above); at
   `drawStep = 0` a nonempty stock is the identity (never a commit —
   the zero-deal reduces by `dealUpTo_eq_take_drop`'s drop/take at
   zero, Phase's `drawStep_zero_reversibleW`) and only the waste-
   bury arm remains (the empty stock recycling into the stock), the
   one genuine sub-kind the census sibling's draw rows must also
   carry.
3. THE CLASS-INERTNESS — TWO CITED ROWS NOW: the sibling's
   `census_step_draw` (every cell's seat census is unchanged: a draw
   writes no pile) and `witness_leg_letters` (the leg shapes).  The
   draw reads only the zone; the twin-door (a foundation event)
   commutes trivially with the draw's class behavior.
4. THE RE-FIRE, POST-COMMUTATION-SWAP — THE ROW IS NOW FULLY
   SUBCONTRACTED, both cases pinned to named rows:

   CONSTRUCTION (fixed): `u₀ := st` — the fork board is slab
   (self-anchored, `fork_self_low`), and the draw at `st` FIRES
   AUTOMATICALLY: the zone of `u` equals the zone of `st` verbatim
   (the witnessing journeys are board-only, and the sibling's
   board_run_congr carries the zone verbatim through them), the
   commit step fired at `u`, and a step at an all-empty zone
   refuses to fire — so the same move `m₀ := Move.draw` is legal at
   `st`; the guard congruence is the zone-blind half of the
   sibling's congruence kit.

   (A) THE DRAW-FREE CASE — the dashed thread is CLOSED by the
   sibling's `drawfree_commute_reach` (phase-exactness:
   `State.run w₀ ρ = some w`: the dashed play lands exactly ON the
   commit target, not merely up to class); the sibling's
   `drawfree_commute_witness` carries the same statement with the
   per-leg mirror witnesses priced in its route (`foundToTab_undo`,
   `tabToFound_undo_under`/`_bare`, the cargo mirrors).  THE
   REMAINING ASSEMBLY GLUE — named here as the row's own open
   piece: THE DASHED-WITNESS TRANSPORT [M], the per-leg
   `reversibleAtW` grades of the dashed chain itself (each board
   leg's one-move mirror re-fires at the boardEq-dashed successor
   and lands the dashed pre-state: per-letter, over
   `step_congr_board` + the guard-congruence reads + the public
   zone-carry keep rows; `boardEq` is exactly the draw's blindness,
   so the transport is mechanical leg-by-leg) — banking it turns
   the (A) target-match into assembly.

   (B) THE INTERLEAVED CASE — CITED: the sibling's
   `interleave_phase_align` concludes `sameOrbitSetoid.r w₀ w`
   verbatim (the target match, directly).  Its two open notes,
   honestly carried here: (i) it is the sibling file's own single
   named residue (its `[propext, sorryAx]` flows transitively into
   this row's audit the day it is cited in a built proof — the
   falsification channel it names is THE CLIPPING SIGNATURE: stock
   lengths straddling `drawStep` at the commit points, per its
   docstring; the round-2 probe armor — pristine-exit, loop-never-
   commit, regime-disjointness — is on record in
   `Orig/LowSlabProbe.lean` §11); (ii) its `u₀.WF` premise makes
   the carry WF-GRADED: this row's statement is WF-free by design,
   so the WILD-grade (B)-case remains the sibling row's own gap,
   flagged for the integrator (at a WF gate the draw-kind closes
   entirely: (A)-assembly + (B)-cite).

PROBE NOTE (Orig/LowSlabProbe.lean, decide-grade): both ends of
this row are instantiated on-board — the commit side twice
(`lb0_drawCommit`/`lb1_drawCommit`, pristine-grade via Phase's
banked row) and the duplicate side END-TO-END (`lb1_dup`: the
draw-commit's slab duplicate fully assembled, class legs commuting
with the zone move pointwise, kernel-equal composites).

HOSTCENSUS POST-COMMUTATION-SWAP: `drawfree_commute_reach` and
`drawfree_commute_witness` CONSUMED for case (A)'s dashed thread;
`board_run_congr` + `step_congr_board` CONSUMED for the zone
transport and the guard congruence; `interleave_phase_align` CITED
as the (B)-carry (WF-graded).  The phase content the old route
carried is now the sibling's two rows' own; the surviving content
is the dashed-witness transport [M] plus the wild-grade (B) gap.
The census does not price cycle phase — none of the five consumed
rows rides `witness_leg_mint_confined`. -/
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
  sorry

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
no shrink are honest here. -/
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
* The census consumption rows [M/H]: `lowslab_draw_emptyReversible`
  [M], `lowslab_top_census` [H], `lowslab_pull_wf_undo` [M] — the
  three facts the kind routes price their open steps against; the
  sibling census program's rows graft at the swap points named in
  the kind docstrings.
* The per-kind replay rows: `fork_lowbridge_raise` [H],
  `fork_lowbridge_reveal` [H], `fork_lowbridge_waste_found` [M],
  `fork_lowbridge_waste_seat` [M], `fork_lowbridge_draw` [H — the
  fourth kind this campaign added to the taxonomy],
  `fork_lowbridge_pull` [H — plausibly vacuous at a WF gate].

INTEGRATOR MAP: the waste and draw rows fall to the sibling census
program's cycle/cursor rows (the two-zone pin `cycle_zone_pin` is
already PROVED in `Orig/SlabEquiv.lean`; the cursor algebra is the
remaining swap); the raise and reveal rows share the seat census
(`lowslab_top_census`) — together with it the two [H]-graded
nontrivial leaves the mission predicted (the elevation mechanism's
arrangement face and the crane replay); the pull row is the
wild-regime safety net, first candidate for retirement.

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
`lowslab_pull_never_commit_wf`) are zero-sorry;
`fork_neighbor_lowbridge` carries the EIGHT named residues of
§4.1-§4.2 (`lowslab_draw_emptyReversible`, `lowslab_top_census`,
`fork_lowbridge_raise`, `fork_lowbridge_reveal`,
`fork_lowbridge_waste_found`, `fork_lowbridge_waste_seat`,
`fork_lowbridge_draw`, `fork_lowbridge_pull`) and NOTHING else
flows into it.  THE CENSUS SWAP PASS added no fresh heads — it
consumed `Orig.HostCensus.lean`'s proved rows inside the residues'
ROUTES (docstring-grade then, term-grade at the residues' own
future landings), none riding the sibling's residue
`witness_leg_mint_confined`.  THE COMMUTATION SWAP PASS assessed
the sibling's four new rows against every residue: consumed where
they bite (the draw row's dashed thread and the waste rows' cursor
coincidence), ASSESSED-NO-LICENSE where they do not (the ρ-image
chains of the raise/reveal rows — `boardEq` congruence is the
draw's blindness and does not reach them; recorded per row); the
sorry COUNT stays exactly the eight, and
`fork_neighbor_lowbridge`'s profile must stay
`[propext, sorryAx, Quot.sound]` with no new inflow — verified
below. -/

#print axioms lowslab_draw_reversible_phase
#print axioms lowslab_pull_wf_undo
#print axioms lowslab_pull_never_commit_wf
#print axioms fork_self_low
#print axioms commit_exits_class
#print axioms commit_blocks_class_return
#print axioms fork_lowbridge_empty
#print axioms fork_lowbridge_commitGlue
#print axioms lowslab_draw_emptyReversible
#print axioms lowslab_top_census
#print axioms fork_lowbridge_raise
#print axioms fork_lowbridge_reveal
#print axioms fork_lowbridge_waste_found
#print axioms fork_lowbridge_waste_seat
#print axioms fork_lowbridge_draw
#print axioms fork_lowbridge_pull
#print axioms fork_lowbridge_elevated
#print axioms fork_neighbor_lowbridge
