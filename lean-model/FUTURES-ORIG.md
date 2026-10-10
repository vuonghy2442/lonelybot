# FUTURES-ORIG — the futures-count route map for the Orig chapter

Doc-only design note (no Lean changes; no constant in the library is
cited as sorry, every file:line was verified in this worktree at
macro-game `d6b53fb`).  Purpose: settle-then-formulate support for the
chapter's ticket 7, "the futures count: a commitment leaves at most two
`sameFate`-distinct successors, per accommodation window — restated on
the original game, with the `Klondike` witness corpus re-derived here
first" (`lean-model/Orig.lean:77`, `Orig/Fate.lean:36`).  The old count
theorem's formulation is an OPEN user decision (the five-wave count
campaign: FARM.md waves 13–21); this note supplies the translations,
the fences the refutation ledger dictates, and the candidate
statements with their dependencies — a fresh card formulates from
here, it does not re-derive the campaign.

Reading order assumptions: `Orig/State.lean` (the physical position),
`Orig/Play.lean` (the six moves, `State.step`), `Orig/Fate.lean`
(`WinFrom`/`sameFate`/`succ`/`irreversibleAt`/`reversibleAtW`),
`Orig/Macro.lean` (`ShufflePlay`/`MacroStep`/`MacroWin`/`win_iff_macro`),
`Orig/Combine.lean` (`ShufflePlayW`/`RevEqW`/`sameOrbitSetoid`/the
window re-basing), `Orig/Phase.lean` (the draw classification rows),
`Orig/Mono.lean` (the measure bridges); the old corpus in
`Klondike/Macro.lean`, `Klondike/C2Streamlined.lean`,
`Klondike/Restriction.lean`, the twin-exchange family, and the
witnesses cited by name below.

In-flight siblings (dependencies, NOT citable files at this HEAD):
the conservation tickets (step-preserves-`WF`, initial-of-`Deal.WF`)
and search integrity are owned by the integrity card
(`farm/orig-integrity`); the spine port (`winFrom_em`) by the
progress-spine card (`farm/orig-progress-spine`); the physical
reachability recurrence + the invariant-preservation combinator
(`invariant_of_initialReachableR`'s analogue, the cleanliness gate) by
the reachability card (`farm/orig-reach`); the non-draw irreversibility
classification (`Orig.Irreversible`, registered as "in flight" at
`Orig.lean:70`) by the irrev-repair card (`farm/orig-irrev-repair`).

## 1. The vocabulary translation table, old → new

| old (Klondike) | new (Orig) | the load-bearing remark |
|---|---|---|
| engine `State` (board function + `topOf` edge graph, `heights`/`depths`, stock `Cycle` + cursor) | physical `State` (`Orig/State.lean:137`): foundations as build-order lists, piles carrying their own `hidden`/`faceUp` (`Orig/State.lean:83`), stock/waste as lists, `Pile.revealTop` (`Orig/State.lean:101`) the automatic flip | the physical dividend, four-fold: (a) phantom/cyclic boards are UNSTATEABLE (`cardCount c = 1`, `Orig/State.lean:235`); (b) "foundation-passed" = FOUNDED (found s = `upCards.take n` is a `WF` conjunct, `Orig/State.lean:233`); (c) visible runs are per-pile lists with strict rank descent (`runOK`, `Orig/State.lean:126`) — the braided walk shapes of w15 cannot be written down; (d) the reveal is part of the moving move (`Pile.afterRunRemoved`, `Orig/State.lean:109`) — there is no reveal move at all |
| `closureEq` (mutual `accommodates`, `Klondike/C2Streamlined.lean:245`; `Klondike/Theorems.lean:162`) | `sameFate` over `succ`-classes (`Orig/Fate.lean:50`) with the witness refinement `RevEqW` (mutual `ShufflePlayW`, `Orig/Combine.lean:118`; `RevEqW_sameFate`, `Orig/Combine.lean:222`) | the count's CONCLUSION grades at `sameFate` (the semantic verdict); the CONSTRUCTION delivers `RevEqW` (returning plays as data).  `RevEqW` is strictly finer than `sameFate` — §5.1 decides which grading the count speaks |
| `macroStep_engine_play` (a macro step IS an engine play, `Klondike/Macro.lean:488`) | already physical by definition: `ShufflePlay_run` (`Orig/Macro.lean:44`) and `macro_win`'s assembly (`Orig/Macro.lean:128`) fold `MacroStep` into σ ++ [m] | the `isEngine` filter has no work to do — the full move set IS the game; C1's forward half is a definitional fold rather than a theorem |
| accommodation window = the ∃ accommodated state inside `macroStep` (`Klondike/Macro.lean:53`) | the window is first-class DATA: `MacroStep st m st'' := ∃ st' σ, ShufflePlay st σ st' ∧ step st' m = some st'' ∧ irreversibleAt st' m` (`Orig/Macro.lean:71`) — σ explicit, tip `st'` (= u) explicit | free-float becomes a bookkeeping question: two successors may be named through different (σ, u)'s.  The uniform-window fix is to quantify (σ, u) OUTSIDE the successor claim (the old `c2_two_option_nonKing_windows`, `Klondike/C2Streamlined.lean:2448`, distilled this first) |
| window/free-float semantics (floating windows add split successors: `wk_nonking_c2_false`, `witnesses/NonKingWitness.lean:1637`) | where floating windows land: a witness shuffle at the FRONT rebases any window without touching its tip — `MacroStep_of_RevEqW` (`Orig/Combine.lean:250`), `MacroWin_of_RevEqW` (`Orig/Combine.lean:262`): "the commit fires at an unchanged tip, the start slides" | so windows modulo `RevEqW`-at-the-start name identical successor claims; every OTHER pooling of distinct tips is the open §5.4 decision (the wave-21 NEXT-3 relaxation) |
| channel labels `{direct, dig, borrow p, hole, toStack}` + `LabelLive` at the commitment ROOT (`Klondike/C2Streamlined.lean:212`, `:329`) + `SuccThrough` (`:399`) | no channel list survives: the enabling analysis reads the commit's own arms AT THE TIP u — `direct`: `u.canPlace c b` reads piles only (`Orig/State.lean:170`); `dig`: a `tabToFound` of the twin inside σ; `borrow p`: a `foundToTab p` inside σ; `hole`: the anchor arm `canPlace c (inl a)` (king + empty, `Orig/State.lean:172`); `toStack`: the foundation arm `wasteToFound c` (`Orig/Play.lean:99`) | the two root-live refutations (`witnesses/SuccLabeledWitness.lean:526`, `witnesses/NonKingWitness.lean:1563`) kill root-liveness labeling forever; the physical `MacroStep` definitionally names (σ, u), so the arm analysis is a case split, not a premise — P0 dissolves |
| rung (`X.rank.toIdx = st.heights X.suit`) / spend (the `Res` atoms, `Klondike/C2Streamlined.lean:168`) | rung = `u.nextUp c` (`Orig/State.lean:201`); spend lives inside the window as the enabling moves named above; arms = the foundation arm (`wasteToFound`) vs the tableau arm (`wasteToTab`), the physical `commitArmOf` (`Klondike/C2Streamlined.lean:376` counterpart) | the rung is EXTRACTED from the foundation arm's own guard (`step u (wasteToFound c) = some s ⟹ nextUp u c`, `Orig/Play.lean:100` — the physical `heights_of_applyDrawStackTo`, `Klondike/C2Streamlined.lean:2042`) |
| visClean (`Klondike/Restriction.lean:394`: every edge over a visible base fits; `initialReachable_visClean`, `Klondike/Restriction.lean:659`) | PROPOSED physical predicate below (§1.8) — the honest expectation: it collapses to `WF` plus a theorem | the three dirt families visClean guarded (phantom stacks, foundation-passed strays, in-pile braids) are all `WF`-theorems physically; the cross-pile crossed-twin shape (the w15 exchange corner) is REAL and stays a premise family of the exchange rows |
| reachable gates: `initialReachable` (deposit, `Klondike/Restriction.lean:75`), `initialReachableR` (recurrence, `Klondike/Restriction.lean:93`), the `invariant_of_initialReachableR` combinator (`Klondike/Restriction.lean:152`, deposit form `:164`) | the physical `Deal.WF` (`Orig/State.lean:248`) + `State.initial` (`Orig/State.lean:256`) seed the same recurrence — the combinator port is the reachability card's `invariant_preservation` (in flight) | the wave-20 lesson travels INTACT: the gate discharges `WF` and nothing else (`c2_two_option_reachable`, `Klondike/C2Streamlined.lean:2205`; the reachable countermodels `witnesses/SuccLabeledWitness.lean:1357`); the count's non-king/windowing premises are NOT gate-dischargeable |

### 1.8 The physical cleanliness candidate (PROPOSED)

The old `visClean` was invented when the exchange rows' refutation
repair needed to kill crafted states — the w15merge witness
(`probes/w15merge.lean`; FARM_MEMORY:2073) lived at a NON-WF board
(empty deal, heights past visible cards), and the killed shapes were
exactly: phantom stacks (unplaced cards "supporting" runs:
FARM_MEMORY:2023-2027), foundation-passed strays (FARM_MEMORY:2082),
and braided walks (twin inside a cargo run: FARM_MEMORY:1837-1839).
At the physical state, §1's dividend (a)–(c) makes every one of those
unstateable at `WF`.  The remaining, genuinely non-free content — the
founded-discipline that `founds_gone` carried — is provable outright:

```lean
-- PROPOSED (this note; never yet stated).  The physical reading of
-- visClean: all visible runs braid-free.  Packaged as the
-- downstream-facing fence; the paired card proves:
--   (committed) the found-discipline conjunct is redundant at WF;
--   (committed) survives every step at WF states.
def State.visCleanO (st : State) : Prop :=
  st.WF ∧
  (∀ a c, c ∈ (st.piles a).faceUp →
     st.foundHeight c.suit ≤ c.rank.toIdx)
```

- The found-discipline conjunct is a `WF`-theorem in embryo: if a
  face-up `c` sat below its suit's height, the `WF` prefix conjunct
  (`Orig/State.lean:233`) already has `c` founded, contradicting
  conservation (`Orig/State.lean:235`).  It is packaged here so downstream
  fences cite one name; a five-line card retires it into `WF`-land.
- The preservation obligation is owed at three points: the
  cleanliness GATE discharges through the combinator — seed
  `visCleanO (State.initial d s)` from `Deal.WF` (the integrity card's
  initial-`WF` ticket, `Orig.lean:63`), preserve along `State.step`
  (the integrity card's `apply_wf` ticket, `Orig.lean:62`), and run the
  reachability card's `invariant_preservation` (the
  `invariant_of_initialReachableR` analogue, `Klondike/Restriction.lean:152`) —
  the physical `initialReachable_visClean` (`Klondike/Restriction.lean:659`).
  No gate ever re-proves a run induction.
- What is deliberately NOT in the predicate: any cross-pile twin
  clause.  The w15 exchange corner (cargo `z` seated on `t` in one
  pile, `z`'s twin on `t`'s twin in another) is a legal, realizable
  physical shape — it is a PREMISE FAMILY of the exchange rows, not a
  cleanliness conjunct; the count candidates below never consult it.
  Deciding evidence for keeping it out: the w15circ probe family
  (`probes/w15circ.lean`, FARM_MEMORY:2104-2122) — at WF the crafted
  forced-merge casts all DIE (the anchor-relocation collapse), so the
  merge corner is expected to fall to irreversibility arguments, not
  to a dirt predicate (open decision §5.5).

## 2. The refutation ledger as formulation fences

Formulation discipline: every old refutation below is a PERMANENT
premise demand on the Orig statement.  For each: what died, where the
witness lives (all citations verified at this HEAD), what it kills on
the physical game, and the premise that must therefore appear.

**F1 — the premiseless exchange dying at crafted states (w15merge).**
Old: `solvable_cargoTwin_exchange` at `Klondike/TwinExchange.lean:1254`
carries `hwf` precisely because the premiseless form was refuted at a
crafted non-WF state (`probes/w15merge.lean`, the witness and its
re-verification protocol recorded at FARM_MEMORY:2073-2075) — the win
REQUIRES the merge while the exchanged state is frozen.
Physical reading: the crafted state is UNSTATEABLE (§1.8), so the
physical fence is weaker than the old one but not EMPTY: (a) any claim
of the shape "crossed twin-pair positions are verdict-equivalent" must
carry `hwf` (physically `st.WF`), which is what makes the physical
twinLicensed analogue (`Klondike/TwinQuotient.lean:3702`'s license, physical
spelling: both hosts face-up, both fits by `canSitOn`, the piles'
emptiness facts) provable — the old `+hwf` repair (`+hvc` form PROVEN
at `Klondike/TwinQuotient.lean:3800` with no bridges) is the template;
(b) the count statements must NOT import exchange equivalences except
at fenced shapes — Candidate A's route below consults none of them.
PREMISES DICTATED: `hwf` on every exchange-flavored row; and nothing
about the count beyond "do not lean on unfenced exchanges".

**F2 — the king-anchor free-anchor corner.**
Old: `wk_c2/same_pin/p2_direct/crease_as_stated_false`
(`witnesses/C2KingAnchorWitness.lean:378`/`:395`/`:408`/`:422`): one
pristine WF state, a climb-blocked stocked ♠K, seven free anchors, all
landings pairwise closure-SEPARATED (the landed king can never leave).
Physical reading: the landing splits' physical root is the automatic
flip — the king lands on an empty pile (`canPlace c (inl a)`,
`Orig/State.lean:172`), the pile's `faceUp` becomes `[c]`, and the first
`tabToFound` that unseats it flips a hidden card permanently (the
hidden count strictly descends — an `Orig/Mono.lean:82`/`:97`
instantiation, one measure row of the irrev-repair card's tables).
Different anchors flip different cards ⇒ distinguishable successors.
It kills: every premiseless "≤2 via joins" at KING commitments, in
EVERY grading — the revealed card is permanent, state-visible evidence.
PREMISES DICTATED: the king side must go by the destination/orbit
route (Candidate C), or be excluded (`hNK`, Candidate A).  The gate
does not rescue it: the dealt-corner addendum (`rState_reachable`,
`witnesses/SuccLabeledWitness.lean:931`; `wk_c2_reachable_false`,
`:1357`; the split `rLand_split`, `:1337`) shows reachable roots split
at six free anchors — reachability discharges `WF` only
(FARM.md:1698-1751, (A) vs (B)).

**F3 — the non-king twin split at the incomplete rung (nk_split).**
Old: `nk_split`, `witnesses/NonKingWitness.lean:657` (+ the three
non-king refutations `:676`/`:686`/`:697`): X = ♠6 stocked, its two
destination twins ♥7/♦7 free, all heights 0 — both landings live, both
stuck ⇒ closure-separated.  Boundary datum: the count SURVIVES here
(`nkSuccessorsExhaustTwo`, `:758`; `nkTwoOptionHoldsHere`, `:784`).
Physical reading: **SUPERSEDED (2026-10-06, the user's reformulation)
— the split does NOT transport.**  The physical game's unrestricted
`tabToTab` joins the twin landings by ONE cross-move plus its mirror,
RUNGLESSLY: from the ♠6-on-♥7 landing, the ♦7 host is still a pile
top (its pile untouched by the landing), `canSitOn ♠6 ♦7` is the same
fit both step hypotheses already carry, and the moved run is [♠6]
over a nonempty below-run ⇒ noreveal, reversible by its mirror.  The
rung was an artifact of the engine's restricted move set, not game
truth.  nkState re-casts as the corpus's POSITIVE datum: exhibit the
cross-move CLOSING the old gap, not a split.  What survives of F3:
the rung stays load-bearing only inside Candidate B's own statement,
where the foundation arm's guard extracts it.  PREMISES DICTATED
(updated): the count's (T,T) leg takes the CROSS-MOVE join
(Candidate A′ below); the destination-bound/pigeonhole apparatus of
the old §16 assembly is RETIRED.

**F4 — the non-king free-float three-split (ffState).**
Old: `wk_nonking_c2_false`, `witnesses/NonKingWitness.lean:1637`:
THREE pairwise closure-separated macro successors at ONE WF non-king
root — the root commit plus TWO window commits reached through
windows playing "irrelevant" content (the ♥A promotion:
`ffWin_stuck`, `:1422`; window successors genuine macro steps).  And
`wk_nonking_succLabeled_false`, `:1563` — even the five-channel
labeling restricted to non-kings is false (`ffSucc_unlabeled`,
`:1532`: the promotion's heart-height change is named by NO root-live
channel; `direct` LIVE at the root — `ffDirectLive`, `:1085` — but
its empty-window signature commits the ROOT, whose heart height 0
separates from the route's 1).
Physical reading, with a crucial physical TIGHTENING: the ffState
window contains the one-move PROMOTION `[pileStack ♥A]` — a
foundation ascent, which in the physical game is `tabToFound` with
`nextUp` — a COMMITMENT (an `Orig/Mono.lean` measure row; a strict
measure move).  Physical `ShufflePlay` windows (`Orig/Macro.lean:36`)
bar such moves AT EACH STEP: the physical free-float residue is
strictly SMALLER than the old one.  What survives: windows may wander
with `foundToTab` worry-backs, `tabToTab` re-homing, `tabToFound`-free
content, and in-phase draws, ending at tips that carry different
heart-heights — the ffState refutation's geometric residue (a
`foundToTab`-float can temporary-divert a foundation) still splits.
It kills: every count over free windows even at non-kings, and every
residual root-liveness labeling.  PREMISES DICTATED: the per-window
form — fix (σ, u) outside the successor claim; and the window
vocabulary depends on the classification (the irrev-repair card) for
what a physical window may contain at all.

**F5 — succ_labeled's phantom anatomy (the unseat route).**
Old: `wk_succ_labeled_as_stated_false`,
`witnesses/SuccLabeledWitness.lean:526` (uState: all seven anchors
occupied by dealt heads, ♠K stocked at position 0, spade-freeze): the
window `pileStack ♥A` UNSEATS the anchored head, the king lands on the
vacated anchor — hole-SHAPED at the tip, dead at the root; no
`LabelLive`-at-`st` channel names it.  The missing-channel
characterization (the `anchorHead` one-liner, `:59-64`) and the
`(a) channel atom vs (b) window gate` decision list live at
FARM.md:1571-1586 and FARM.md:1800-1803.
Physical reading: P0 DISSOLVES — `MacroStep` (`Orig/Macro.lean:71`)
definitionally names (σ, u); there is no root-live channel list to be
incomplete.  The unseat route becomes an ordinary arm case at the tip
(the anchor arm with a window that emptied an anchor — and note: a
physical window can only EMPTY an anchor by moving its sole face-up
card away, which flips its next hidden card — an irreversible exit,
so such windows END the phase, they do not wander; the physical
anatomy is sharper than the old one).  It kills: any attempt to port
the `hlab` premise family into Orig.  PREMISES DICTATED: none — the
formulation consequence is structural (arm analysis at the tip), and
Candidate A/C bake it in.

**F6 — the crease (the same-channel chains).**
Old: `wk_crease_as_stated_false` (`witnesses/C2KingAnchorWitness.lean:422`) and
the reachable crease `wk_crease_reachable_false`
(`witnesses/SuccLabeledWitness.lean:1403`) killed the Sublist-alone absorption;
the honest replacement `crease_absorbed_reachable`
(`Klondike/C2Streamlined.lean:2176`) carries `hwin : u = u'` explicitly.  It
kills the shape "two windows of one channel join because the second's
accommodation list extends the first's".
Physical reading: the physical counterpart of `hwin` is the
endpoint-equality of windows; the ONLY general join mechanism between
different endpoints is `RevEqW` — `MacroStep_of_RevEqW`
(`Orig/Combine.lean:250`) re-bases at the FRONT; it says nothing
about tips.  PREMISES DICTATED: any cross-window join claim cites
`RevEqW`-class evidence (witness reversible plays), never chain
containment.  The mixed-window candidate machinery (§4) is bound by
this fence.

**F7 — the cursor/pace fences (the window's draw side).**
Old: `solvable_iff_pure_cursors` needed `0 < drawStep`
(`Klondike/Macro.lean:1076`, the PaceStepZero repair) and
`window_firstDraw(_macro)` (`Klondike/Macro.lean:1844`/`:1958`)
located the exclusive window between cursors.  Physical: already
RE-DERIVED — `draw_irreversible_offset` (`Orig/Phase.lean:900`) makes
offset draws commitments; `draw_irreversible_pristine` (`:930`),
`draw_irreversible_of_wasteShape` (`:948`),
`draw_reversible_selfRecycle(W)` (`:961`/`:968`),
`drawStep_zero_reversible(W)` (`:881`/`:888`), and the lex variant
(`:1225`) are the rows.  PREMISES DICTATED: count statements quantify
over windows with the Phase rows in hand; any "windows may draw"
clause cites the classification (draw rows done; the in-phase
round-trip head is the remaining Phase ticket per its file header).

## 3. Candidate statements on Orig

Three candidates + one assembly policy.  All per-window; all state
commitments AT the tip u; all conclusions available in the two
gradings (the §5.1 decision): constructive (`sᵢ = sⱼ ∨ RevEqW sᵢ sⱼ`,
sameFate by `Orig/Combine.lean:222` + `Orig/Fate.lean:52`) or verdict
(`sameFate sᵢ sⱼ`).  A shared spelling:

```lean
/-- The commit arms of the drawn card `c` at the window tip `u`:
the tableau arm over any fitting base, and the foundation arm. -/
def CommitOf (u : State) (c : Card) (s : State) : Prop :=
  (∃ b, State.step u (Move.wasteToTab c b) = some s) ∨
    State.step u (Move.wasteToFound c) = some s
```

### 3.1 THE MAJOR THEOREM — a non-king move is (at most) TWO-well-defined on macro states (user formulation 2026-10-06; supersedes A/A′ and the windowed count)

**ROUTE REVISION (the user's canonical-openings program, 2026-10-10):**
the count is analyzed ENTIRELY IN THE CANONICAL WORLD.  The three
dividends that make it work: (1) clearing raiseable junk is
IN-CLASS — at a canonical state every licensed raise is consumed
already, so candidate landings blocked only by raiseable material
cost nothing; the analysis reduces to the UNRAISEABLE OBSTRUCTION
INVENTORY — the canonical state's residue profile — which IS the
"clean condition" reading: branch behavior = a profile function of
(c, the canonical form); (2) both ends close canonically for free
(canon_in_class for the successor; the PHASE-PROGRESS lemma — a
class-relation from a commit successor back would BE the returning
play, so every commit strictly exits its class — gives the
per-phase pigeonhole); (3) in-phase stock rotations are
class-invisible, so "c reachable-to-hand" enters the profile as a
clean draw-pool condition (Phase machinery), not a separate
obstacle.  THE BRIDGE THE PROGRAM NEEDS: the commit-transport
lemma — for every commit firing at a tip of class C there is a
canonical-launched accommodation (a reversible path from canon C
making m landable, then m) whose post-commit class equals the
actual successor's class — the per-cell transported-move
constructions, ABSORBING ticket 8's commute kit as this theorem's
first milestone.  THE COUNT's ANATOMY per new card c: the raise
arm (rung read off foundations, ≤1 class); the direct landings
(the twin-pair fitting hosts, unobstructed — the residue
exhibit's lesson applies to the landed-result classes); the
obstruction-resolved landings (the 2×2 worry lattice — same-card
retraces vanish mechanically, the twin-picker survives — with the
SINGLE-OBSTRUCTION DISCIPLINE as the hard half: the accommodating
chain intersects at most the one twin-choice; the seat-lock-grade
arithmetic from the mirroring engine's kill family is the
prototype).  THE HONEST BOUNDARY: the old three-live-successors
ghost is re-hunted in the CANONICAL-PROFILE language — a profile
witnessing a third class bounds the theorem; none found — the
 count.  ASSEMBLY MILESTONES: transport bridge (absorbs the kit) →
profile lemmas (obstruction inventory, in-class clearing,
hands-from-draw-pool) → per-arm enumeration (raise/direct/
obstructed cells, the worry 2×2 mechanized) → the two-class count →
the boundary note.

**ARM-TYPING REFINEMENT (user, 2026-10-10, the case table's rows):**
the commit families sort by BRANCH STRUCTURE, not by irreversibility
cause.  UNIQUE-SUCCESSOR ARMS — committal draws (deterministic,
no parameter — misaligned draws commit with exactly one successor,
in-phase draws class-invisible: "not the issue"), wasteToFound (c
pinned = waste top), tabToFound per firing — each contributes
count-1 trivially; cite and move on.  BASE-CHOICE ARMS —
wasteToTab c b and tabToTab c b — the ONLY cells needing the
accommodation analysis (twin-pair hosts, worry lattice, obstruction
inventory: the analysis-bearing surface is TWO move-kinds, not
six).  THE FOURTH FAMILY (user's own seat-physics rows, 2026-10-10
refinement of the tri-taxonomy): the BARE-NON-KING VACATE — a
committed tabToTab of a dealt bare non-king off its anchor commits
by seat physics alone (no reveal, no waste, no draw); in
canonical-profile terms these are exactly the obstruction-inventory
"bare non-king on an anchor" entries (deal-only sources — no move
seats a non-king bare; one-way doors), same twin-pair base choice,
distinctive successor signature: a FREED KING-SEAT (new landing
capacity).  PRECISION LOCK (the two-option-card lesson): the ≤2
claim is PER-MOVE — one fixed m across the class's m-legal tips
visits at most two successor classes; the across-moves multiplicity
 at a single tip (several available reveals + vacates + waste
 placements) is NOT bounded by 2 and needs no bound — a phase
commits one move and the theorem prices each choice.

**THE RESERVOIR-TRANSIT UNIFICATION (user, 2026-10-10):**
wasteToTab and the tabToTab-reveal are the SAME ANALYSIS OBJECT —
new-card-ENTRY events from face-down reservoirs: the waste (entry
position CHOSEN) vs the hidden zone (entry position PINNED at the
source); both relocate other content only class-transparently
(twin landing choices of freshly-mobile runs merge by the
noreveal cross-shuttles EXCEPT at the residue-exhibit cells);
the landed measure tables were reservoir-monotonicity all along
(hiddenTotal never rises = the hidden reservoir never refills;
cycleCount = waste-transit consumption) — so the per-move
class-visible residue = (the new card's entry position mod
twin-symmetry) + (the obstruction inventory delta), and the
genuine branch source in both families is the same thing: the
ACCOMMODATION-PREFIX FREEDOM — which reversible stretches from
canon C make m launchable — priced by the SAME obstruction-inventory
 function.  The analysis-bearing case table is effectively ONE
analysis with two position-polarity cases.

**THE TWO-AXIS GRID (user's tabToTab+tabToFound merge, 2026-10-10):**
the commit families decompose along TWO ORTHOGONAL AXES —
SOURCE EFFECT (none / reveal / seat-door) × ARRIVAL (chosen
twin-pair host / pinned / unique) — every family is a grid cell
(tabToTab-reveal = reveal × chosen; tabToFound-reveal =
reveal × unique — no base parameter, so its successor class is
a function of the accommodation prefix alone, the prefix
carrying only the same class-transparent-mod-residue clearing
landings; the vacate = seat-door × chosen; wasteTo *
= no-source × chosen/unique; draw = no-source × none).
THE CONCRETE UNIFIER: both tabToTab and tabToFound go through
the SAME afterRunRemoved machinery (pre = below-run, the same
reveal rule, the same hiddenTotal guard) — ONE removal-reveal
SPINE lemma, parameterized by the removed segment's depth
([c] for the raise, fromCard c for the run), proven once;
then THREE arrival-tail analyses (chosen / pinned / unique)
proven once each.  Spine + three tails replaces six case
studies — the user's merge is exactly one spine + two tails.
THE MERGE'S CAUTIONS: the arrival tails differ in KIND of
profile delta (tableau arrival = a POSITION ENTRY in the
obstruction inventory; foundation arrival = a HEIGHT INCREMENT
with the card leaving the inventory — the profile vocabulary
carries both, a union not an identification); the depth
parameterization keeps the moves' genuinely-different
precondition sets separate; and NO merged move definition
enters State.step — six constructors stay the semantics of
record, the combination lives in the analysis layer only.

**THE CANONEDGE NORMAL FORM (user proposal, corrected and
recorded 2026-10-10):** the definitional layer the assembly
opens with.  A macro transition does NOT have a unique underlying
MOVE (the twin-landing merge — being proven in the waste-entry
cell — is one edge, two moves), but every macro transition HAS
A UNIQUE NORMAL FORM: (reversible padding π from the canonical
representative) + EXACTLY ONE COMMIT + class-closure — anchored
uniquely (canon_unique) and carrying a single commit slot
(structurally: by the phase-progress lemma a chain's first commit
already exits the class, so multi-commit edges are impossible —
every subsequent commit is its own edge).  DEFINITION:
structure CanonEdge (C D) := (π : pure-reversible from C) ×
(m : one commit firing at π·C, irreversibleAt there) × (D =
⟦landing⟧).  PRESENTATION THEOREM: MacroStep-edges ↔
CanonEdge-schemes — the (⇐) direction trivial (a scheme IS a
window-plus-commit MacroStep), the (⇒) direction is the
transport bridge (the assembly's milestone one; the waste-entry
cell bypasses it with c literally in hand).  WHAT IT BUYS:
"the branches of a macro state" gains its clean predicate (the
CanonEdge successor-class set at C; the per-card count reads
c's schemes reach ≤ 2 classes); the window ambiguity dies
 definitionally (every edge anchored at one fixed
 representative — "regardless of micro state" becomes
 definitional); and the solver-level reading: the macro graph is
 a well-defined labeled graph (canonical vertices, commit-scheme
 edges).

**THE EDGE-LABELING THEOREM (the user's proposal, refined through
the 2026-10-10 dialogue; the assembly's SECOND milestone, ahead of
the count): every directly-adjacent class pair carries a UNIQUE
label, and the label alphabet is TRIpartite (user's final form):
`draw` | `wasteToTab`-family (the waste-card entry, card-orbit
labeled) | `reveal a specific stack` (the tableau family,
POSITION-labeled).  THE TWIN PRINCIPLE DIVIDING THE ALPHABET:
the conjugation permutes CARD IDs only and FIXES the position
structure — so POSITION-valued labels are twin-blind BY
CONSTRUCTION (no orbit device), while the waste family's label
must touch card values (its source is the single-zone waste, no
position to name) and is the card-orbit {c, c.twin} + kind
(raise-vs-land).  THE FAMILIES UNDER THE THIRD LABEL: the
reveal-move names the revealed stack's position (the revealed
card is pinned in the successor profile — the position NAMES the
event); the VACATE rides the same positional family as the
degenerate no-reveal case (emptying the stack rather than
revealing-through — the freed anchor is the position).  WHY
UNIQUEENESS HOLDS: labels are CLASS-PAIR FINGERPRINTS — (1) the
guard measures are class-invariants (the never-rise rows are
stronger than class-invariance), so the edge's (∆cycleCount,
∆hiddenTotal, foundation-deltas) separates draw vs waste-entry
vs tableau-family; (2) within waste-entry the card is pinned by
ARITHMETIC (at canonical A only the suite's next-up card is
rung-raiseable — B's foundation-delta identifies c = upCards σ
[B's height] literally; the landing case pins c as the new
visible entry); within the tableau family the event's stack is
read off the source-side profile delta; (3) well-definedness is
functionality of the fingerprint map (final A, final B) — the
same anchor every time, which is exactly what CanonEdge buys.
THE DRAW-VS-CARD DISJOINTNESS is a small milestone cell (the
phase-delta argument).  THE COUNT-ANATOMY BONUS: reveal-moves
from CANONICAL states have their raise-arm STRUCTURALLY DEAD
(the departing run's head is the faceUp BOTTOM — never a
licensed raise target — and the run's top was never
licensed-raiseable, the saturation consumed all such), so the
reveal family branches PURELY over the departed run's twin-pair
landing: ≤ 2, residue-exceptions only — cleaner than the waste
case's rung-split (there the rung case collapses everything to
1; here it cannot occur); the per-label count anatomy is
UNIFORM: each label's event has at most 2 outcome classes, the
residue profile deciding the collapse to 1.  THE ONE HONEST
CAVEAT (recorded with the anchor language): canon is a function
on STATES, not a unique class representative — the residue
exhibit proved a class can hold two genuinely different Final
states — so class-level statements say "anchor canon A, read the
pair, PROVE class-invariance," never "the representative of
the class."

```lean
theorem apply_two_macroOutcomes {t₁ t₂ t₃ : State} {m : Move} {s₁ s₂ s₃ : State}
    (h₁₂ : ⟦t₁⟧ = ⟦t₂⟧) (h₁₃ : ⟦t₁⟧ = ⟦t₃⟧)   -- ⟦·⟧ : Quotient sameOrbitSetoid, the
                                              -- LANDED macro state: reversible journeys
                                              -- ∪ twin conjugation
    (hnk : (movedCard m).rank ≠ Rank.king)
    (h₁ : State.step t₁ m = some s₁) (h₂ : State.step t₂ m = some s₂)
    (h₃ : State.step t₃ m = some s₃) :
    ⟦s₁⟧ = ⟦s₂⟧ ∨ ⟦s₁⟧ = ⟦s₃⟧ ∨ ⟦s₂⟧ = ⟦s₃⟧
```

GRADING NOTE (the user's twin-choice correction, 2026-10-06): the
canonicalization itself can fork — sometimes you must PICK either
twin to put up / pull back as the substrate, and the two picks give
outcomes that are TWIN-CONJUGATE, not `RevEqW`-connected.  So the
revEqW-GRADED variant of this theorem is FALSE (the twin-choice
triple — canonical, worried-♥, worried-♦ — has three `RevEqW`-
distinct outcomes); the fourth disjunct of `sameOrbitSetoid`
(earned by the Combine card's transitivity countermodel) is
precisely what folds the twin pick and keeps the count at the
{canonical, worried} pair.  The sameOrbit-graded form above is the
theorem; the twin-choice triple is the corpus card's first-class
certification datum.

The hypothesis IS the macro state ("three micro states that can apply
the same move and are connected by reversible move sequences" —
`RevEqW` carries the dances as data); the conclusion IS the ≤-2
("at least two outcomes share a macro state"): **the window
premise is deleted, not fenced** — F4's float is absorbed by the
∃ inside `RevEqW`, and "regardless of the current micro state" is
literal (no root, no shared tip, no σ-uniformity).  Corollaries: the
twin-coarsened form ⟦sᵢ⟧ = ⟦sⱼ⟧ on `Quotient sameOrbitSetoid`, and
the per-window count as a special case (window tips are class-mates).

THE PROOF ARCHITECTURE (the residence calculus — corrected per the
user 2026-10-06, second pass):
1. RESIDENCES ARE KIND-INVARIANT under reversible dances: `c` moves
   pile↔pile only between fitting tops and pile↔foundation via the
   `noreveal tabToFound`/`foundToTab` round trip; waste→pile is a
   commit (never in a dance), so the firing tips hold `c` in one
   RESIDENCE KIND.  The move's own guard pins the rest: raises pin
   the foundation at `c.suit` to the exact rung content at every
   firing tip; the waste-head residence is literally the waste top;
   under-`c` content is frozen (nothing below `c` moves without
   moving `c`).
2. THE RESIDENCE WANDERING IS **ONE MACRO CLASS** (the user's
   correction — NOT the source of the 2): moving `c` to either
   twin is the same macro class (pile-to-pile is reversible), and
   tableau-vs-foundation joins too (the `noreveal tabToFound`/
   `foundToTab` round trips).  WHERE `c` fires from contributes NO
   multiplicity; the residence calculus delivers the one-class
   wandering lemma, and `m`'s guard merely selects the firing tips
   inside that one class.
3. THE 2 IS THE **ORDERING DICHOTOMY OF CRITICAL LOCAL SQUARES** —
   and the critical family is THE WORRY-BACK PATTERN (the user named
   it, 2026-10-06): the class's tours differ by canonicalization
   maneuvers — stuff raised to the foundation, then a worry-card `x`
   pulled BACK DOWN (`foundToTab x`) to serve as the substrate at
   `m`'s landing site for the new card.  Before `m`, the excursion
   round-trips freely — that is exactly why the tips are
   class-mates.  The fork: in the WORRIED face `m`'s placement
   consumes the substrate, killing the excursion's raise-back leg
   (`x` buried under the landing / sandwiched below `c` in the
   foundation / reveal-locked) — irreversibly visible after `m`;
   in the CANONICAL face the leg still replays.  The criterion is
   SITE-LEVEL BINARY — `m`'s landing site is either fed by a
   worry-back or canonical, and at most one substrate occupies a
   site, so all worry-cards collapse into the single worried face:
   the ≤ 2 is robust because the excursion-vs-`m` ordering is
   binary and local.  A whole-dance difference with no critical
   member transports entirely (≤ 1 truth); a genuine two-face
   witness (the worried face's return leg dying under a fired `m`)
   is the corpus's TIGHTNESS    datum — the old w15/merge anatomy
   and the `foundTotal_step_noworry` fragment discipline were
   pointing at this pattern all along.

   ### 3.0 THE CANONICALIZATION THEOREM — the macro state made decidable (user formulation 2026-10-06; the FIRST ticket, feeding §3.1) — **V2 REVISION (2026-10-06, user-endorsed mid-flight): the canonicalizer takes REVERSIBLE stacking only**

**V2 doctrine**: a raise enters the canonicalizer exactly when it
carries its own one-move reversible undo from the landed family —
under-seat raises (`pre ≠ []`, undo = `foundToTab` onto the exposed
base, per `tabToFound_undo_under`) or bare-KING raises (undo slides
the king back, per `tabToFound_undo_bare`).  OUT: revealing raises
(`hiddenTotal` strictly drops — never rises: a commitment), bare
NON-KING raises (the seat-physics rows — they split the fiber),
and waste pops (`wasteToFound` strictly drops `cycleCount`, which no
play raises — the measure tables arbitrate this design).  The
canonicalizer leaves the whole stock/waste zone untouched; a
saturated state may still hold a raw-stackable waste head.

Consequences (the V2 dividend):
- **THE NEW CORE THEOREM is `canon_in_class`**: `u ⟶* canon u` is a
  `ShufflePlayW` (each licensed raise carries `reversibleAtW` from
  the undo family; the reverse undo-ladder composes the return), so
  ⟨⟦canon u⟧ = ⟦u⟧⟧ — the canonical form is a DISTINGUISHED MEMBER
  of its macro class, not a commit-shifted descendant.
- CLAIM 1 stands with its waste-prefix corner EVAPORATED (no pops ⇒
  no prefix consumption); order-independence of the licensed
  subsystem is fuel + literal diamonds.
- CLAIM 2 collapses into compositionality around `canon_in_class`
  (any reversible journey gives equal wrapped canons by passing
  through canon; same-macro iff equal-wrapped-canon + swComp),
  with the relocation-residue witness still Demoting literal
  canon-equality to the ⟦·⟧-wrapped form.

```lean
-- CLAIM 1 (confluence, licensed subsystem)
theorem canon_unique (h₁ : StackRun u w₁) (h₂ : StackRun u w₂)
    (hf₁ : Final w₁) (hf₂ : Final w₂) : w₁ = w₂

-- THE CORE (class membership)
theorem canon_in_class (h : StackRun u (canon u)) : ⟦canon u⟧ = ⟦u⟧

-- CLAIM 2 (characterization, composed)
theorem same_macro_iff :
  SameMacroO u v ↔ (⟦canon u⟧ ≈ ⟦canon v⟧ ∧ swComp …)
```

Doctrine recorded from the formulating dialogue:
- CANONICALIZATION IS FORK-FREE (user retraction of the earlier
  twin-pick-forks-canonicalization claim): stack all stackables;
  the worry-back/ladder material belongs to §3.1's commit side,
  not here.
- Proof route for claim 1: termination trivial (total foundation
  length strictly rises, ≤ 52); confluence by MONOTONE
  STACKABILITY — stacking is pure removal + foundation saturation
  (never covers anything), so stackability once true stays true
  until exercised, stacking c never blocks c', reveals only ADD
  stackables.  THE SUBTLE CORNER: the waste pops only at the head,
  so which prefix is consumed depends on foundation states during
  the run — saturation-order-independence there is the real work
  (the Phase machinery's territory).
- CLAIM 2: SameMacroO (the canon fiber — definitional reading per
  the user: "different macro ⇒ different canonical is from the
  def") with the INVARANCE FAMILY proving the journey notions land
  inside it: reversible single moves preserve the canonical level;
  twin conjugation conjugates canon; in-phase stock/waste rotations
  preserve it (swCompat = Phase's in-phase relation, pending the
  user's confirm).  ~~OPEN DESIGN QUESTION, MID-FLIGHT: literal
  canon-equality vs the ⟦·⟧-wrapped form~~ — **RESOLVED, by exhibit
  (2026-10-10)**: the WRAPPED form is correct and necessary;
  `residue_reloc_exhibit` (Orig.Canonical, decide-graded) is a
  reversible one-move tabToTab relocation of an unstackable residue
  between twin hosts, both endpoints WF + Final (so canon is the
  identity there), canon u ≠ canon v literally, same-macro holds —
  full-state literal dies on draws (trivially), tableau+foundation
  literal dies on this exhibit; `SWComp` (the draw-pool + in-phase
  residue) is proven JOURNEY-NECESSARY by `swComp_of_orbit`.  The
  sameFate tie is DEFERRED.
- The major theorem (§3.1) consumes this as its normalizer: its
  hypothesis becomes the decidable canon-fiber check.



LOCKED CARDS: Residences (`Orig/Residence.lean`: movedCard,
kind-invariance, twin-pair bound, pinned contexts) → Transport
(`Orig/Transport.lean`: the commutation squares, foundation
diamonds, same-residence transport) → Assembly (the theorem +
pigeonhole-3 + quotient corollaries).  Corpus note: a physical
2-outcome exhibit (twin residences with differing reveals) is
TIGHTNESS data now, not a threat; `ffState` cannot inhabit the
hypothesis (promotions are barred inside physical windows).
DEPENDENCIES: the classification oracle (in flight — dances are
made of the moves it certifies reversible), Shuttle/TwinExchange
relocation lemmas, Integrity search pins, `RevEqW` as data.

### 3.2 Candidate B — the foundation shuttle (the rung join core)

```lean
theorem shuttle_join {u : State} {c : Card} {b₁ b₂ : Base}
    (hwf : u.WF) (htop : u.wasteIs c = true) (hrung : u.nextUp c = true)
    {s₁ s₂ : State} (h₁ : State.step u (Move.wasteToTab c b₁) = some s₁)
    (h₂ : State.step u (Move.wasteToTab c b₂) = some s₂) :
    RevEqW s₁ s₂ ∧ RevEqW s₂ s₁   -- one bundled round trip; see the route
```

- **Route**: the two-move physical round trip — at s₁ (on a card base:
  `c` face-up pile-top, the pile nonempty beneath it since `c` is a
  non-king on a card), `tabToFound c` fires (`nextUp c` + pile top),
  landing a mid state whose foundation holds `c`; `foundToTab c b₂`
  fires there (`canPlace c b₂` survives: piles were untouched), and
  the result is literally s₂ (the waste/stock/pile/read books all
  match: same splice, same chop-back).  The reverse direction is the
  symmetric pair.  Both legs are `reversibleAtW` at their own states
  (`Orig/Fate.lean:92`) — the shuttle IS a `RevEqW` witness pair,
  which is why the conclusion is constructive-graded.
- **Threats**: nk_split (F3 — `hrung` is the witness-proven
  load-bearing premise; dropping it is exactly the refuted
  `commitTableau_class`-without-rung form at NonKingWitness:676);
  the crease family (F6 — no chain-form weakening);
  king-anchor family (F2 — and here the exclusion is STRUCTURAL:
  kings cannot land on card bases at all, so B needs no explicit
  `hNK`; the reveal corner that killed the old unrestricted shuttle
  (`afterRunRemoved`'s flip when `faceUp` empties — the physical root
  of the king splits) is UNREACHABLE on B's domain).
- **PREMISES**: `hwf`, the rung, card-bases only.  **Dependencies**:
  integrity tickets only; witness-direct; classification-free.  This
  is the smallest self-sufficient join row — the obvious FIRST COMMIT
  for the formulating card.

### 3.3 Candidate C — the king/anchor side (the frozen corner, graded)

```lean
theorem king_anchor_side {u : State} {c : Card}
    (hwf : u.WF) (htop : u.wasteIs c = true) (hK : c.rank = Rank.king)
    (hfrozen : FrozenSuit u c.suit)        -- no card of c.suit can ascend
                                          -- (spade-freeze analogue)
    {s₁ s₂ s₃ : State}
    (h₁ : CommitOf u c s₁) (h₂ : CommitOf u c s₂) (h₃ : CommitOf u c s₃):
    ... -- the regime-staged conclusion below
```

- **The physical anatomy replacing the old proof split**: under `hK`
  the tableau arm over card bases is dead (`canSitOn` arithmetic),
  so the successors are: the foundation arm whenever the suit has
  ascended to the king's rung (unique, deterministic) and the ANCHOR
  landings — one per genuinely-empty pile `{a : u.piles a | isEmpty}`,
  each flipping the anchor's next hidden card (a strict descent in
  the hidden-count measure — an `Orig.Mono` commitment row).
  Anchor-landing states pair up: s(a), s(a′) carry the two revealed
  cards hₐ, hₐ′ — EQUAL iff the anchors' flips coincide (impossible
  at a state where they're distinct) ⇒ pairwise `RevEqW`-unrelated,
  and fate-distinct whenever the reveals play differently.
- **The physical proof-plan split is graded by regimes** (all named,
  none fully settled — this candidate is a program, not a single
  sprint): (i) the ONE-anchor regime (≤ 1 genuinely empty pile —
  the wave-19 corpus register proportions FARM.md:2309-2314) has at
  most ONE anchor successor ⇒ at most TWO classes trivially
  (the physical `same_pin_hole_oneAnchor`, `Klondike/C2Streamlined.lean:2077`);
  (ii) the FROZEN one-anchor corner gets the
  `c2_two_option_king_frozen` (`Klondike/C2Streamlined.lean:2143`) treatment
  with the flip extracted; (iii) the multi-anchor worlds go by the
  pile-permutation symmetry — physically a relabeling of `Anchor`
  commutes with `step`/`run`/`isWin`/`WF` (the wave-22 content: the
  "(2 + 1)" grading of `pristine_commit_firstCut`,
  `witnesses/PileQuotientCorollaries.lean:176`, its four-futures
  grading `:210`, the fates reading `:260` — physical counterpart
  nearly free since pile transposition is an honest state symmetry
  here, not a quotient construction).
- **Threats**: the rState reachable corner (F2/wave-20 addendum —
  `witnesses/SuccLabeledWitness.lean:1156`/`:1357`) — a DEALT-INITIAL state
  presenting six usable anchors: gates do not fence this; C must
  carry real regime or symmetry content.  The corpus numbers are the
  evidence for the regime order (§5.2).
- **Dependencies**: the irrev-repair card (the flip/hidden measure
  row — the revealed-permanence classification), integrity, and for
  the frozen definition either a physical spade-freeze port (the
  `witnesses/SuccLabeledWitness.lean:32-40` argument replayed physically — its
  state-level walk survives the physical translation wholesale) or its
  classification-side derivation.

### 3.4 Assembly policy (the gated umbrella, `c2_two_option_reachable`'s port)

```lean
theorem two_option_reachable {st : State} (hreach : InitialReachableO st) ...
```
with the same conclusion as A over windows at `u` reachable from `st`,
is the LAST row, assembled from regimes: the gate discharges `u.WF`
(and `visCleanO`) via the reachability card's combinator and NOTHING
else (the `c2_two_option_reachable`
`Klondike/C2Streamlined.lean:2205` pattern, wave-20's honest regime list
FARM.md:1778-1783).  Each new proven regime "slots straight in"
(FARM.md:1806-1807).  The one arm with NO Orig analogue yet: the
never-refuted `hball` residue (the stack-plus-two-live-balls corner,
`Klondike/C2Streamlined.lean:1251`) — physically the worry-ray geometry of the
`stack_ball_corner` plan (`Klondike/C2Streamlined.lean:1700`).  STATE IT OPEN:
the physical raise-ray (deterministic same-suit rank-mate ascent —
physically: founding a rung-matched card is unique per suit) is
expected-true-unproven; the formulating card names it, does not
pretend it.

## 4. The window-content atom, translated to physical windows

Wave-21's ticket 1 (FARM.md:2435-2441) asks for a `windowContent`
atom — the window's own move multiset as a signature — to fix BOTH
the king unseat route and the non-king free-float lane, or else keep
the gated reading.  Translated:

**σ : List Move is already the natural free signature, because the
physical `MacroStep` carries windows as DATA.** The old atom's job
(label successors the root-channel list cannot name) is done away
with by the arm analysis at the tip (F5).  The atom's REMAINING job
in Orig is one step harder: deciding WHICH windows to pool — the
wave-21 NEXT-3 relaxation (FARM.md:2447-2449: per-window founder pairs
for three DIFFERENT u's), which is exactly the question the free-float
refutations left open.

What the atom must quotient away, and why:

1. **Front differences** — MANDATORY: `MacroStep_of_RevEqW`
   (`Orig/Combine.lean:250`) re-bases any window along a witness
   shuffle at its start; two windows differing by a `RevEqW` at the
   front name provably-identical successor claims.  An atom finer
   than this re-opens the free-float disease INSIDE the signature.
2. **Excursion-pair noise** — MANDATORY: a window and itself with a
   `[foundToTab c b; tabToFound c]`-shaped reversible round-trip
   inserted or deleted net to the same state along the same
  observations (the cancel identities: the excursion pair's
  `stackPile_pileStack_return`-shaped net-zero, recorded beside
  `run_worryback_pair_excise` at FARM.md:1316).  The multiset
  COUNTS such pairs — it must not distinguish on them.
3. **Endpoint identifications** — OPEN, THE OBSERVED LOAD-BEARING
   RESIDUE: pooling `RevEqW u u'` related tips (same commit move,
   both windows shuffle-linked there) is NOT covered by Combine:250 —
    that lemma moves starts, never tips.  The deciding evidence: ffWin
    (tips whose commit-relevant reads differ — the heart height —
    MUST stay distinguished: `ffSucc_unlabeled`,
    `witnesses/NonKingWitness.lean:1532`) versus w15circ (suggests at WF extra
    content tends to be absorbable — the anchor-relocation collapse,
    FARM_MEMORY:2112-2118); between them, the boundary is the
    classification of the window's own content — a promotion cannot
    occur inside a physical window at all (it is irreversible;
    ShufflePlay bars it), so the ffState cast itself becomes
    UNSTATEABLE physically: the physical atom question is strictly
    about worry-back/re-home/in-phase-draw differences.
   Whether ANY surviving physical float separates tips is a
   CORPUS QUESTION (§7, first re-derivation list item).
4. **Draw-copy blindness** — like the old cursor-blindness
   (`accommodates_cursor_blind`, `Klondike/Macro.lean:717`): the
   same effective window drawn at different in-phase cursors must
   pool; the Phase rows (in-phase draws reversible, offset draws
   barred from windows) make this a FINER residual than the old
   mask arithmetic — the draw-arm analysis falls out of the
   classification, not from the atom.

Net formulation advice: state every count per-window (exact sigma
shared); treat the atom ONLY as the future relaxation device — the
equivalence-closure of rules 1, 2 (sound unconditionally by
Combine:250 + the cancel identities) with 3, 4 added when decided
by the re-derived corpus.

## 5. Open design decisions, each with the deciding evidence named

1. **The count's grading: constructive (state-equality ∨ `RevEqW`) vs
   verdict (`sameFate`).**  `sameFate` is the chapter plan's own coin
   ("two `sameFate`-distinct successors", `Orig.lean:77-79`) and
   matches the physical vocabulary; BUT it is observable-cheap at dead
   pairs (any two
   unwinnable successors are `sameFate`), which is exactly what
   the nkState corner exhibits (nkSuccessorsExhaustTwo is a genuine
   count but its sameFate reading there is carried trivially).
   Candidate A/C above are stated constructive-graded with the
   sameFate form as the corollary — the wave-22 precedent (counts on
   constructive classes, verdicts read through:
   `closureEq_solvableCW_iff`, `witnesses/PileQuotientCorollaries.lean:69`;
   `c2_two_option_fate`, `:99`) supports this.  DECIDING EVIDENCE:
   find (or fail to find, corpus-side) a physical state with three
   LIVE sameFate-distinct commit-successors at one window — that
   witness separates the gradings; none exists yet.
2. **The king corner's route: regime premises vs anchor-orbit
   symmetry.**  DECIDING EVIDENCE: the wave-21 corpus numbers —
   the ≥2-anchor regime is 7.4% of the blocked-king world
   (FARM.md:2309-2314), the unseat route's raw material a 4-12%
   phenomenon with king landings the reversible-except-route class
   (FARM.md:2334-2340) — and the reachability fact that the rState
   corner is zero-move reachable (F2).  If the orbit route (3.3(iii))
   lands cheap, spend no time on graded regimes beyond one-anchor.
3. **Exchange rows: sequenced before or after the count.**  The
   fences dictate the count never consults unfenced exchanges (F1);
   Candidate A's route, scope-excluding the exchange family, says
   count first.  DECIDING EVIDENCE: the w15 corpus re-derivation
   (§7) — if the physical exchange rows land WITHOUT new premises
   (expected: the w15circ collapse), they may be scheduled any time;
   if they demand premises, the count must not wait on them.
   UPDATE (2026-10-10): the family is landing FENCED, exactly the
   §2-F1 shape (`hwf` + the BothOcc license: both hosts face-up,
   both fits; supporting kit the kill family + `seat_lock`) — the
   both-occupied mirroring engine, three of six transport rows
   green, all 26 public heads audited on main since today
   (`0c5cf87` + `bcd2197`; recorded §8).  Candidate A's
   scope-exclusion stands unchanged — it consults none of them;
   the three remaining rows (foundToTab / tabToFound / tabToTab)
   and the plan's tail (`go_gen`, the bare iff, the
   quotient-widening corollary) are sequenced in §8, none of
   them a count dependency.
 4. **The endpoint-pooling atom (§4.3).**  OPEN; deciding evidence:
   the re-derived ffWin question (does ANY physical float separate
   tips?) + the in-flight in-phase round trip (Phase's remaining
   ticket), which decides how much of the old cursor-window residue
   survives at all.
5. **`visCleanO`'s final shape.**  Keep the packaged predicate or
   retire the conjunction into WF-land after the five-line card.
   DECIDING EVIDENCE: the first physical exchange card's fence
   inventory — if the merge-corner fences need only `WF` + Mono
   measure rows, retire; if a genuine cross-pile discipline
    surfaces, keep and strengthen.  (The old evidence — the refit of
    `initialReachable_visClean` onto the combinator, recorded at
    FARM.md:1836 with the lemma at `Klondike/Restriction.lean:659` —
    says the combinator route works either way.)
6. **Which irreversibility facts the window vocabulary may assume.**
   The windows quantified over in A/B/C are THEORIES about
   `ShufflePlay`; as the classification lands, richer windows become
   provable (in-phase draws, worry-back content).  DECIDING EVIDENCE:
   the irrev-repair card's tables (the non-draw rows: flips,
   foundToTab reversibility, the foundTotal no-worry row per
   `Orig.lean:71-73`) — richer windows = stronger counts; none of
   A/B/C's STATEMENTS change.

## 6. Tickets for the formulating card (the recommended order)

1. THE RESCUE ORDER (updated 2026-10-06, second revision): B is
   LANDED (Orig.Shuttle, `67dfbf1`); the non-king lane is now THE
   MAJOR THEOREM (§3.1): Residences → Transport → Assembly, then C
   by regimes (one-anchor + frozen first), then the gated umbrella
   — whose non-king leg is the major theorem itself.
2. The corpus re-derivation FIRST (per `Orig.lean:78-80`, "the
   `Klondike` witness corpus re-derived here first") — §7's list.
3. The five-line card: `visCleanO` found-discipline redundancy
   (the cleanliness gate discharge via the reachability card's
   `invariant_preservation`).
4. The flip/hidden-count Mono instantiation (revealed-permanence) —
   shipped to the irrev-repair card's measure tables if that card
   takes it; else owned by C's card.
5. The open arm named honestly in every gated assembly: the physical
   raise-ray residue (`stack_ball_corner`'s port — expected-true,
   unformalized; no sorry stubs in stubs' clothing).
6. The α-bridge (Orig.lean ticket 5) gets its CONSERVATION TRANSPORT
   lemma named in advance (user instinct, 2026-10-06): for any
   physical realization `p` of an old-WF engine state `st` (the B1
   data, `Klondike/Realizability`), `p.WF` holds — the old six-
   conjunct zone bookkeeping (`vis_off_cycle`/`found_off_cycle`/
   `founds_gone`/`vis_not_hidden`/`stock_wf`/deal-noDup)
   transports to the ONE census (`cardCount = 1`) under
   realizability.  Cheap once the decode exists; rides INSIDE the
   bridge card, never a standalone card.  The verdict
   correspondence (`solvable st ↔ ∃ p realizing st, WinFrom p`)
   stays gated on the refuted-converse corpus until the bridge's
   formulation is cut whole — the day's lesson about unsettled
   formulations.
7. THE RUNOK RELAXATION AUDIT (user instinct, 2026-10-06): the 141
   `runOK` citations (Reach 56, TwinExchange 38, Integrity 27,
   Classify 17, State 3) cluster in ONE pattern — the seam kit:
   `runOK` is the state-carried memory of placement-guard history
   (reveals only produce singletons, so the invariant captures
   exactly the placement trace, nothing more).  Relaxation is
   structurally cheap: Reach generalizes verbatim (non-creation
   proofs), and the concentrated consumers (undo under-rows,
   exchange joints, Classify's cells) re-absorb the fits as
   explicit `canSitOn` premises — `canSitOn` is ALREADY the variant
   parameter, `runOK` only its remembered trace.  SEQUENCED: not
   now (four in-flight cards cite `WF` in every proof); post-
   landing as a SEAM-REDUCTION REFACTOR ticket (`WF0` = prefix +
   census + drawStep, ⊕ the fit-memory conjunct) whenever the
   solitaire-variant transport question becomes real.
8. THE COMMUTE KIT (user question 2026-10-10, sequenced deliberately
   AFTER the in-flight consumers): Orig/Commute.lean as an
   EXTRACUTION-UNIFICATION card, not a parallel derivation — the
   raw material arrives inline with canon-core's per-cell
   transported moves and the mirroring engine's g-induction legs;
   plus the parked Transport draft (2405b1b, 13 theorems, the
   zoneDisjoint→square predicate) as seed; plus the target-clash
   counterexample with its trough-transport (foundToTab x (inr z)
   vs tabToFound z — either order blocks the other; the routed
   move r* = undo-c ∘ r).  The kit's OWN new content is one
   piece: the master disjointness schema (disjoint write-sets +
   co-fire ⇒ literal commutation, the zone-effect-indexed
   statement subsuming the draws-rows and cross-suit rows) +
   the zone-effect index itself (each move kind's write-set) +
   the consumers' digest.  DO NOT grow the full 6×6 lattice —
   scope = consumed pairs only.  The major-theorem assembly card
   waits one cycle for this kit so it CITES the schema instead of
   writing the fourth inline copy.

## 7. The corpus re-derivation list (witnesses to re-derive physically)

**STATUS 2026-10-06 — THE CORPUS IS RE-DERIVED** (four Witness-lib
files, `360cd95`/`a69e253`/`c9d5896`/`1ab5611`, all `#eval`-recorded
via `#guard_msgs` and decide-proved; every head `[propext, Quot.sound]`
or fewer, zero Classical.choice; their verdicts recalibrate the fences:

- **F1** OrigExchangeWitness (the physical w15merge): the
  premiseless-exchange refutation SURVIVES as a wild-pair fence
  (`xA_xB_notSameFate` — xA wins THROUGH the merge, xB frozen;
  `wk_exchange_premiseless_false`) — but the **FIT-LADDER
  CONTRADICTION** says more: a legal-edge helix is rank-impossible,
  so the merge anatomy FORCES a braided wild slice — at `WF` the
  merge killer is UNWRITABLE (§1(c) now witnessed).
- **F2** OrigKingAnchorWitness: the old seven-landing split
  COLLAPSES physically — landed kings `RevEqW`-RELINK between empty
  anchors by one-move reversible relocations (`kaL_revEqW`) — the
  §5.2 orbit expectation, witnessed; king-anchor splits are a
  dead fence in the full game.
- **F3** OrigNonKingWitness: `nk_draw_commit` (the draw is the
  commit; `draw_irreversible_pristine` cited), the in-hand arms are
  EXACTLY the twins, and **`nk_relinked : RevEqW nkS1 nkS2`** — the
  engine's stack-only twin separation is physically refuted by the
  landed card's shuttle — third independent confirmation of the
  cross-move collapse (after §2-F3's supercession and the shuttle).
- **F4** OrigLabeledWitness: the **NAIVE-TIP BARRIER**
  (`lU0_noLanding` — the drawn ♠K has NO landing until the promotion
  unseats it, `lT0_aceStep`) — the accommodation-maneuver datum the
  ladder narrative needs; the ONE post-unseat landing is the
  reachability lane's consumable; the competing-♦K/♣K census is
  data.  Label anatomy stays vocab-absent pending the count.

RESIDUE EVIDENCE for §3.0's open literal-vs-wrapped question: all
crafted residues so far RE-LINK (`RevEqW`-level, not merely
twin-conjugate) — supportive of the literal comparison, not
conclusive.  The dedup overlaps with `Orig.Integrity` (marked
private sections: decSt instances, canPlace unfolds, search
extractions) stay parked per house discipline; the `decSt`
(DecidableEq State) promotion rides the tidy ticket.

UPDATE (2026-10-10): two of the three marked sections are UNPARKED
— the canPlace unfolds landed home as State's public readers
(`c661eb0`: `canPlace_inl_unfold` / `canPlace_inr_eq` /
`canPlace_inr_located`, plus Play's putCard/putRun readers and
Integrity's `ne_of_canSitOn`), and the search extractions collapsed
into consumption (`4941d33`: TwinExchange's marked
`pileHolding_mem` / dead `pileOfTop_mem` deleted, the
search-completeness blocks rebuilt on Integrity's
`pileOfTop_eq_some_iff` / `pileHolding_eq_some_iff`; §8).  The
`decSt` instances alone stay parked; the promotion still rides
the tidy ticket's residue.

Per the ticket's own words, before or alongside the formulations —
expected difficulty and expected verdicts, all pre-cited:

- nkState + nkSplit (NonKingWitness:657-758): STRAIGHTFORWARD to
  re-cast (pristine physical deals; every prior witness ingredient is
  physical already — a spade stock card, twin dealt heads, heights
  0).  Expected verdict: the split lands verbatim in the
  constructive grading; the `sameFate` reading collapses to trivial
  at the dead pair — the grading separator (§5.1) this corpus
  provides for free.
- ffState (NonKingWitness:1563-1665): the CAST ITSELF
  SELF-DESTRUCTS physically (the promotion inside the window is a
  commitment — barred from `ShufflePlay`); the re-derivation is the
  NEW search for a warrant-borne float (worry-back/re-home/phase-draw
  content separating tips) — deciding §4.3/§5.4.  Either outcome is
  publishable: no float ⇒ coarser pooling is sound; a float ⇒ the
  uniform-window premise is load-bearing in the physical regime too.
- rState (SuccLabeledWitness:931, the addendum): nearly verbatim —
  it is a dealt INITIAL state; the addendum's split and unseat
  arguments (rStep:1077, rSucc_unlabeled:1133, rLand_split:1337,
  rFrozen_seat_step:1239) translate to physical flips and guards.
  Expected verdict: the splits LAND (the physical game is faithful
  here) — this corpus anchors C's regime premises.
- C2KingAnchorWitness (the pristine world, :378-:422): re-castable;
  the pristine stock/freeze arguments are physical; expected
  verdict: splits land (the flip differences), and the wave-19B
  reachability verdict (`witnesses/KingAnchorReachProbe.lean:435`/`:449`/`:473`)
  awaits the physical combinator's own unreachability rows once the
  reachability card lands.
- The w15 family (probes/w15merge.lean, w15circ.lean,
  w15wfmerge.lean; FARM_MEMORY:2073, :2104): the merge witness is
  UNSTATEABLE physically (F1 — the crafted state violates WF); the
  re-derivation is the WF-recast hunt (the w15circ pattern), with
  the EXPECTED outcome per the collapse kit (FARM_MEMORY:2112-2122
  and `Klondike/TwinCollapse.lean`'s anchor-relocation lemma family):
  the casts die at WF — the physical exchange rows are expected to
  be premise-light (hwf and twinLicense only).  Schedule late
  (§5.3).

*Coda — what the note deliberately did not do*: no Lean was touched;
no channel list was resurrected; the `anchorHead` atom question
(SuccLabeledWitness:46-67, "orchestrator scope") is DEFERRED to the
old-side orchestrator — the physical design dissolves its motivation,
but the decision there is not this note's to make.  House doc
discipline: this file adds no sorries, cites none, and should be read
against `witnesses/README.md`'s regression-layer protocol
(`witnesses/README.md:13-22`) and the census header (FARM.md:3).

## 8. The session ledger (UPDATE 2026-10-10: the both-occupied
harvest + the post-merge cleanup session, branch `macro-game`)

**STATUS 2026-10-10 — THE BOTH-OCCUPIED MIRRORING ENGINE IS ON MAIN
AND THE EXCHANGE CHAPTER NOW RIDES THE PACK.**  Six landings, raw
hashes below, zero sorry, zero choice anywhere.  What landed, where
it lives now, what it changes for the remaining rows:

- **The campaign merge `0c5cf87`** (`farm/orig-twinexch-both-v2`,
  tip `56c6925`): the M1–M5g program landed at
  `Orig/TwinExchangeBoth.lean` (+2158 lines) — the M1 kit, the
  BothOcc license + σ-representation (M2+M3), the kill family +
  `seat_lock` (M4), the congruence ministry + `braid_splice` with
  the braid family WF-automatic (M5a), and three of six transport
  rows GREEN (draw M5b; wasteToFound M5c; wasteToTab M5d–M5g, the
  row the last stretch died on, landed through the
  anchor-swapped-mirror landing anatomy — the fresh-write and snoc
  cases paid by `bothOcc_freshWrite` / `splice_snoc` /
  `swapAnch_ne`, the pile equations by the three reseat packs
  freshWrite/swollenSelf/swollenOther) — zero sorry, every head
  audited at `[propext]`/`[propext, Quot.sound]`.
- **The harvest wiring `bcd2197`**: `import Orig.TwinExchangeBoth`
  at the `Orig.lean` root, after MergeWalls (the module's own
  imports: MergeWalls / TwinExchangeQuotient / Integrity / Reach)
  — the merge's deferred integration step; root battery green at
  24 jobs, and all 26 public heads of the merged module externally
  re-audited at `[propext]`/`[propext, Quot.sound]`.
- **The census inversion `e319ac6`** (`Orig/Integrity.lean`, +234
  lines, zero choice): the same-pile half
  (`mem_faceUp_not_hidden` / `mem_hidden_not_faceUp` — the gap
  `mem_pile_unique` left open, its projection quantifying only
  over OTHER piles); the zone sides (`mem_found_unique` /
  `mem_stock_unique` / `mem_waste_unique`); and the compound
  one-liners the exchange rows cite (`mem_faceUp_only` /
  `mem_hidden_only`: one membership pins every other zone at
  once).  Kit: the suit splits (`preSuits`/`sufSuits`,
  `zones_split_found_pre`/`_suf`), the two-founds / found-stock /
  found-waste / stock-waste pair kills, and the intra-pile double
  count `count_ge_two_pile_self` on `flatMapSingleton` — the piece
  the `hZP` idiom had been re-deriving per consumer.
  Dedup-marked against TwinExchange's private ccn kit; all splits
  decidable, zero excluded middle; all seven heads externally
  probed at `[propext, Quot.sound]`.
- **The TwinExchange simplification `4941d33`** (−90 lines, every
  statement untouched): the realizations ride the search-integrity
  + census pack — `import Orig.Integrity` (TwinExchange joins
  Classify as a pack consumer); the duplicate root search readers
  deleted (`pileHolding_mem`, Integrity's verbatim statement-twin,
  and the dead `pileOfTop_mem`, zero uses repo-wide), so every
  unqualified use in the tree resolves to the single Integrity
  constant; the twice-duplicated `hZP1` ccn block extracted as
  the private `not_mem_below_of_cargo` (the cargo head never sits
  in its own host's below-prefix — one count, paid once instead
  of verbatim in both realizations); fwd's `hZP2` now cites
  `mem_faceUp_only`; and the search-completeness re-derivations
  COLLAPSE to Integrity's iff one-liners — fwd's `hptb` (10
  lines) / `hphz` (14) and bwd's `hphz` (21) / `hpta` (33, the
  braided j-arm analysis) all land as `(pileOfTop_eq_some_iff /
  pileHolding_eq_some_iff _).mpr` under `hwf := State.wf_exchangeTwin
  hwf h1 h2 hne`, the license-descent theorem doing the arm
  analysis's work; dead haves pruned (fwd's ct1, bwd's cz1').
  Deliberately untouched: the mid-step σ-block searches
  (intermediate `setPile` states carry no WF in scope — the
  cardCount-form `pile_mem_unique` and the `*_eq_of_unique`
  validators remain their tool) and `pile_mem_unique` itself;
  battery green at 24 jobs with every consumer rebuilt against
  the reduced export surface.
- **The record-reader kit `c661eb0`** (the tidy card the exchange
  chapters' dedup marks had named): the setPile / canPlace /
  afterRunRemoved readers beside their defs in `Orig/State.lean`
  (`setPile_topOf_ne`, `setPile_piles_ne`, `setPile_piles_self` in
  Reach's implicit-binder shape, `setPile_found` in Irreversible's
  point-free shape, `canPlace_inl_unfold`, `canPlace_inr_eq` = the
  UNFOLD form, the form two prior private copies already used,
  `canPlace_inr_located` = the located rewrite TwinExchange's
  realizations consume); the putCard/putRun readers plus the
  found-passthrough trio in `Orig/Play.lean`
  (`putCard_inl_found` / `putCard_inr_found` — the staged
  foundToTab kit, now on main — plus `putCard_inr_eq` /
  `putRun_inr_eq`); `ne_of_canSitOn` in `Orig/Integrity` (the
  rank ladder's first public step).  FIFTEEN private copies
  collapsed across the six chapters (TwinExchange 7,
  TwinExchangeBoth 3, Shuttle 1, Irreversible 1, Reach 2,
  MergeWalls 1), all name- and statement-compatible rewrites —
  zero proof-body changes at call sites except TwinExchange's two
  located rewrites, renamed `canPlace_inr_located`; root battery
  green at 24 jobs across all nine touched files; the new heads
  probed `[propext]` or fewer (the rfl-grade trio carry no axioms
  at all), `twin_exchange_bare_iff` and the `exch_step` rows
  unchanged at `[propext, Quot.sound]`.
  BANKED PROCEDURE LESSONS (the tidy card's standing procedure —
  cited, not relearned): (a) THE GREP-COLLISION SWEEP — before
  landing any public reader, grep the new name across EVERY
  chapter first; this sweep caught four same-named constants,
  including MergeWalls' differently-shaped `canPlace_inr_eq`;
  (b) THE CANONICAL-NAME POLICY — the bare name goes to the form
  the existing copies already use, the variant gets the new name
  (State's `canPlace_inr_eq` is the unfold; the located rewrite
  enters as `canPlace_inr_located`).
- **The dead-code pass `0f538a2`**: TwinExchange's
  `ccn_ge_two_of_double` deleted (zero uses — a leftover from the
  private count kit era whose consumers all moved); both's
  private `canPlace_inl_eq` deleted, its three use-sites renamed
  to State's public `canPlace_inl_unfold` from the reader kit
  (identical statement, zero body changes); root battery green at
  24 jobs.

WHAT THIS CHANGES FOR THE REMAINING WORK: the next transport rows —
foundToTab (its staging kit `putCard_inl_found` / `putCard_inr_found`
is now PUBLIC on main), tabToFound (the freedom row), tabToTab
(seat-lock legs + merge-walls legs), then `go_gen`, the bare iff,
the quotient-widening corollary (per the chapter's own plan,
`0c5cf87`) — now cite the public readers (`ne_of_canSitOn`,
`canPlace_inl_unfold`, `canPlace_inr_eq`/`_located`, the
setPile/putCard/putRun kit) and the census one-liners
(`mem_faceUp_only` / `mem_hidden_only`) instead of private copies
and fresh `hZP`-style double counts.

