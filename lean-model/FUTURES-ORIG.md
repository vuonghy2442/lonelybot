<!-- TOC auto-generated 2026-10-13; titles only, stable under appends -->
<!-- /TOC -->

- ## 1. The vocabulary translation table, old → new
- ## 2. The refutation ledger as formulation fences
- ## 3. Candidate statements on Orig
- ## 4. The window-content atom, translated to physical windows
- ## 5. Open design decisions, each with the deciding evidence named
- ## 6. Tickets for the formulating card (the recommended order)
- ## 7. The corpus re-derivation list (witnesses to re-derive physically)
- ## 8. The session ledger (UPDATE 2026-10-11: the (A) reserve row lands
- ## 8-prior. The both-occupied harvest (2026-10-10 earlier, branch `macro-game`)
- ## 10. The exchange-canon commutation card (2026-10-11, branch `orig-exch-canlaw`, rebased onto macro-game `47b1ad9`; landing-1 probe battery GREEN, the inherited backlog's first falsifier candidate FIRED)
- ## 9. The pull-multiset determinism family — session orig-macro-determinism (STATUS 2026-10-11)
- ## 9. The canon-side completion card (2026-10-11, branch `orig-canon-decompress`; landing-1 probe battery GREEN, all verdicts in)
- ## 11. The V3-canonicalizer gating census (2026-10-11, branch `orig-canon-v3`, rebased onto macro-game `5ebef39`; the scaffold-pull fork-fix card, landing 1 AND the card's whole content — the census returns EMPTY, the doctrine closes)
- ## 12. The corrected conjugation theorems — session orig-conjugate-proof (STATUS 2026-10-12, branch `orig-conjugate-proof`, rebased onto macro-game `07247ec` per the 8a0e121 recipe; the probe-first battery `probes/ConjugateProbe.lean` landed BEFORE any proof, all gates decidable #evals, all boards conservation-checked)
- ## 13. The no-lock pairClass capstone — the orphan-seat axes close (STATUS 2026-10-12)

# FUTURES-ORIG — the futures-count route map for the Orig chapter

Doc-only design note (no Lean changes; no constant in the library is
cited as sorry, every file:line was verified in this worktree at
macro-game `d6b53fb`).  AMENDMENT 2026-10-10 (later): this doc no
longer describes a sorrry-less Orig — the to-foundation dominances
port headlined in §8 landed four named stubs at
`Orig/Dominance.lean`; everything else stands.  Purpose:
settle-then-formulate support for the chapter's ticket 7, "the
futures count: a commitment leaves at most two `sameFate`-distinct
successors, per accommodation window — restated on the original
game, with the `Klondike` witness corpus re-derived here first"
(`lean-model/Orig.lean:77`, `Orig/Fate.lean:36`).  The old count
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

## 8. The session ledger (UPDATE 2026-10-11: the (A) reserve row lands
on `farm/orig-dom-a-reserve` + the §5.1 bare-floor skeleton on
`farm/orig-dom-n-ground` @ `7bf0ccc` + the (N) rung-occurs
extraction and the §12.1 first-passage port on
`farm/orig-dom-extract-port`; UPDATE 2026-10-10: the to-foundation
dominances port + the both-occupied harvest + the post-merge cleanup,
branch `macro-game`)

 HEAD
**STATUS 2026-10-11 (wave 24 cont., branch `farm/orig-dom-extract-port`,
commits `06af140` + `5d7189c` + `2f1f28d`) — THE (N) ROW'S (a)
PREREQUISITE AND THE (C) ROW'S PORTED GAP ARE LANDED SORRY-FREE.**
Two mechanical pieces, both audited `[propext, Quot.sound]` fresh
in-file, zero new sorry, census pinned (`Dominance.lean` 6 expected
6 — the (N) residue stays; its remaining content is now ONLY (b),
the α/β spread):

* **The first-passage port (PUBLIC machinery, `Orig/Play.lean`)**:
  `run_append_split` (the append-decomposition reader of the run
  dialect) and `run_firstPassage_split` — the §12.1 family
  despecialized from the Klondike side's heights-crossing
  `climb_firstPassage` to any decidable state predicate: a successful
  play whose start fails `P` and whose end satisfies `P` splits at
  its first crossing — prefix landing on a failing state, ONE move
  onto a passing state, every prefix-visited state failing `P` (the
  minimality clause, the generic replacement for the source's
  carried pre-passage invariants).  Both consumers are recorded in
  the docstring: the (N) extraction below and the (C) residue
  `draw1_worry_spread_residue` (instantiate at `x`-foundedness; the
  window-accounting bullet's UPDATE row marks the gap closed).
  Transcription was physical throughout — no corner resisted; the
  only real work was the `(match State.step st m with …)` unfold idiom
  at the induction split (the banked `run_cons`+inj recipe).
  Dedup note: Progress's `run_append_elim` and this file's
  `ground_run_split`/`run_append_split1` remain private — hoisting
  them onto `run_append_split` is a harvest-wave call, not taken
  here (other rows' sites untouched).

* **The rung-occurs extraction (PRIVATE, `Orig/Dominance.lean`, at
  the (N) route note's point)**: `ground_rung_crossing` — from a WF,
  tableau-held corner, every winning play must raise `c`; the first
  `c`-founding crossing is entered by `tabToFound c` (the waste twin
  `wasteToFound c` is impossible by conservation: the crossing state
  still holds `c` in a pile — the kit's tableau-zone invariant
  `tabHeld_step`/`tabHeld_run` plus `mem_pile_unique` keep it out of
  the waste — and no other move kind writes onto a foundation).  The
  position packages the prefix (with `c` unfounded AND tableau-held
  at EVERY state it visits — the pre-passage window facts), the fired
  raise, and the tail running on to the win.  The zone invariant's
  six-kind ledger needed the WF premise exactly once
  (`canPlace_inr_target_pile_ne` rules out the run-move
  self-landing that would void the landing search; every other arm is
  guard-reading, no WF).  Companion: `ground_firstBlocked_split` —
  the packaging the lift's direct line consumes: any winning play
  splits at its FIRST blocked move — compliant prefix, boundary move
  either the rung pass itself (SETTLE: `ground_settle_transport`
  closes verbatim) or a genuinely blocked move (the α/β residue's
  window state, carrying the same window facts at the split); the
  raise cannot occur inside the prefix, read off the crossing
  minimality.  Local readers dedup-marked: `g_below_fromCard_or`
  (kin of TwinExchange's public `below_aboveIn_split` —
  Dominance imports neither), the `g_putCard_piles_*` pointwise
  pair (kin of EdgeLabel's privates), `g_firstWhere_mem_ne_none`
  (the WF-free search-completeness half Integrity's exact rows
  don't cover).

Battery `lake build Klondike Witnesses Orig` green on all three
targets (Witnesses' first passes hit the transient Windows
`.olean.private` read storms; serial per-module build + retry is
green).  The (N)/(C) attack order note: with (a) landed, the (N)
lift's remaining content is the α/β SPREAD alone — the residue's
consumer can now start from `ground_firstBlocked_split`'s window
state directly; the (C) residue's restack-location leg is ready to
cite the port the same way the (N) row does.

**EVIDENCE-RECOVERY APPENDIX (2026-10-11, branch `orig-comm-canlaw`,
the canon-commutation card).**  The card's two probe artifacts —
authored OUTSIDE the workspace per the card's own discipline (temp
path `canlaw-probes/…`), referenced commit-message-only — were
recovered from session storage and COMMITTED as runnable files add
to this branch so the audit trail carries the artifacts, not the
prose:

* `lean-model/probes/CanLawProbe.lean` — the landing-1 census: six
  full-deck WF states, the E1-LITERAL rung-shadow witness (committed
  state saturates 3♥ to height 3 while the un-re-saturated route
  stays at 2 — both with both shapes firing), E1-HONEST clean on
  all six, E2 clean including deliberate d-shapes, the merged
  founding leg (`step … = none` at the canonical form), the quintet,
  the legality-transport refutations (R→L canon-enables; the tab
  seat evaporates), the draw mirror (deal 1/3, recycle, none-sync).
* `lean-model/probes/CanLawProbeTwin.lean` — the twin-contention
  verdicts: the contended-seat fork real (either stacking
  forecloses the other), the exclusivity at the crafted family
  (rung-ready ≠ lift-licensed bare; canon fixed at base, empty
  trivially-reversible schedule), the fork surviving INTO the
  canonical grade (each child licenses its claimant; canonical
  finals differ), and the absorb composite (foundation-book twin
  relabel ∘ p1↔p2 anchor rotation with in-pile relabel) — with the
  strict `State.twinMap` and bare pair-swap forms REFUTED.

Both verified `lake env lean` green on the branch; zero sorry,
zero `native_decide`, kernel-decided rows throughout.  The commit
messages on the landing batch name the temp paths; these are the
same files, landed.
TUS 2026-10-11 (wave 24.5, farm-orig-dom-n-ground @ `7bf0ccc`)
— THE (N) BARE-FLOOR RESIDUE IS A PROVEN SKELETON OVER ONE NAMED
SUB-RESIDUE.**  `tabToFound_dominant_of_ground` is PROVEN.  The
statement is untouched; the proof is the assembly

`tabToFound_dominant_of_ground` ← `tabToFound_groundNormalForm`
(the single named sub-residue, full route note at its site) +
`ground_replay_go` (the verbatim replay, PROVEN):

* **The divergence field** `GroundSplit st c k u v`: the replay's
  `c`-suit foundation runs `[c]` ahead, every other suit/found and
  the draw zone are verbatim, pile `k` holds `afterRunRemoved` of
  the source pile — the revealed counterpart of `c`'s seat
  (`ground_split_init`: the raise itself establishes it).
* **The per-kind ledger** `ground_split_step`: all six move kinds
  carry the field through a non-blocked move (reader-rw chains; the
  compliance's three arms are exactly the kinds whose legality
  reads what the field changed — parks on `c`'s seat, `c`-suit
  worry-backs, `c`'s own relocation).
* **The rung convergence** `ground_converge`: the source's own
  `tabToFound c` writes exactly the ahead half — the two threads
  coincide from the pass on, so the replay tail is untouched.
* **The replay induction** `ground_replay_go`: a compliant play
  `π₁ ++ tabToFound c :: π₂` from the source replays from the
  raised state as `π₁ ++ π₂` — the raise is front-loaded.
* **The channel-A quantitative spine, PROVEN**: `ground_streak_founded`
  (B&G Cor. 3 physically — a third fit-step over `c`'s seat lands on
  a founded card, so no `hsafe`-consistent streak is three deep).
* **The battery** `witnesses/OrigGroundWitness.lean`: both corner
  arms co-realized at razor's-edge safety heights; the raise is a
  true commitment (the hidden-total measure at the reveal-seat arm;
  the 59-base no-reseat census at the emptied-pile arm); every
  compliance arm inhabited by a legal move AND every replacement
  decided-live (the end-to-end streak raise-channel, the diamond
  commutation of raise and tenant-raise, the relocation's dig
  parity — the raise digs the same reveal).
* **The residue's remaining content**: `tabToFound_groundNormalForm`
  — the B&G Thm-1 transform's normal-form half (α: park
  substitution by streak-raises under the two-rank bound + B&G
  Case-2 displacement; β: c-suit worry-skip, the worry/restack pair
  nets to identity — the pair-deletion template pairs with the C
  session's `foundToTab_return`; γ: relocation absorption via the
  dig parity), believed-true (the refutation needs the
  tight every-winning-play-carries-a-banned-move world), decide
  battery at the corner states, census №
  `tabToFound_groundNormalForm` (the residue's refute-first gate is
  its own paragraph in Dominance.lean).  Axiom grade:
  `tabToFound_dominant_of_ground` `[propext, sorryAx, Quot.sound]`
  — `sorryAx` ONLY via the named residue.

The §5.1 name moved: the open piece below is now
`tabToFound_groundNormalForm` (the skeleton carries the old row's
name forward); `tabToFound_safe_dominant`'s sorryAx also rides only
that residue now.

**STATUS 2026-10-11 (wave 24.6, branch `farm/orig-dom-gap-ground` off
`11f3373`) — THE (N) TRANSFORM MACHINERY BEGAN LANDING; ONE ARM
COMPONENT PROVEN, THE OTHERS FULLY PLANNED.**  Zero new sorries; the
census stays pinned (`Dominance.lean` 6 expected 6).

* **LANDED, sorry-free, audited `[propext, Quot.sound]`**:
  `wastePark_restack` (+ its private read inverses `parkStep_inv`,
  `restackStep_inv`, `pile_isEmpty_inv`) — the α1-ADJACENT Case-1
  collapse: park the waste head on any legal base and immediately
  re-raise it from the parked seat = the direct waste raise, an
  EXACT state equality (the seat restores without a reveal at
  either `putCard` branch, the foundation gains exactly the mover,
  the waste pops once).  Together with `foundToTab_return` this
  closes EVERY ADJACENT case of the α1 and β/α2 substitutions —
  the SPREAD carry (other moves between the move and its
  cancellation) is the (N) row's remaining content on those arms.
* **The γ plan, fully derived (see the site note for the parts
  list)**: at a bare window, `step v (foundToTab c b) = step st
  (tabToTab c b)` where `v = step st (tabToFound c)` — the raised
  world re-embody any relocation of a bare `c` in ONE move, so a
  γ-leading play satisfies the RESIDUE VERBATIM (`π₁ = P` clean) by
  `WinFrom_of_runTo`.  Singleton run (`fromCard c [c] = [c]`) makes
  `putRun [c] b ≡ putCard c b`; the dig parity is literally the same
  `afterRunRemoved p []` on both threads; `chop_snoc` returns the
  found; `canPlace c b` survives at `v` because `b`'s seat misses
  pile `k` (the `inl` target is empty so not `k`; the `inr` base
  card is neither `c` nor the revealed card).  Write it structuring
  after `wastePark_restack`.
* **Residue ⟺ dominance**: a lifted `WinFrom s₁` IS the residue
  with `π₁ = []` — do not manufacture a nonempty compliant prefix
  when a lifted win is in hand (the assembly replays either).
* **Protocol finding for the spread arms**: FIRST-blocked
  eliminations sit at quartet windows but meet WILD tails with the
  safety slack possibly SPENT (clean other-suit worry-backs — the
  (C) route's warning, now probe-confirmed: the streak-raise
  substitution needs `hsafe` AT the window and cannot re-derive it
  from `hsafe st c`); LAST-blocked eliminations keep the
  to-the-rung segment clean but wild the window.  The α/β spread
  bottoms at the same content as the (C) residue's storage prong —
  close it by the streak-raise reshape (B&G's own Case-2 sketch
  requires the moved card to avoid ALL safely-buildable cards, a
  step the printed proof does not spell out — the "covered park"
  corner), or record gated sub-residues honestly.
* **Probe evidence**, compiled (`OrigProbes/GroundRes.lean`, `lake build
  GroundRes`; probes README row): the `K♠` razor corner and its
  eroded/queued variants sustain C1 and C2 across the corpus —
  every raised-world win is the source win minus the rung; the
  erode towers self-heal by c-blind raises before the tenant raise.
  The paper's App. B.1 was fetched and read (Blake & Gent, JAIR 85,
  2026 — the transform reference for the whole §5.1 family).
* **ATTACK KIT LANDED (+`d3b11d0`/`bb8652f`/`ab77a7e`, on the
  `f0b3315` restage)**: every transport layer of the win-lift is
  SORRY-FREE at the (N) site — `ground_run_split` /
  `ground_run_join` / `ground_run_wf` (the play readers, local
  pre-statements to demote against §5.2 at the merge),
  `ground_prefix_carry` (the divergence field carried along a
  raise-free `groundBlocked`-clean prefix), `relocate_resettle`
  (**THE γ BRIDGE**: at a bare-window WF corner the raised state
  re-embodies any legal relocation of `c` in ONE `foundToTab c b` —
  the singleton run makes `putRun [c] b ≡ putCard c b`, the dig
  parity is the same `afterRunRemoved p []` on both threads, the
  foundation round-trips by `chop_snoc`, and `canPlace c b` survives
  because `b`'s seat provably misses the dug pile), and
  `ground_settle_transport` (**THE SETTLE CASE**: a compliant
  winning play — clean prefix, the raise at its first
  `tabToFound c` — lifts verbatim to the raised state: run-split,
  field-carry, `ground_converge` at the lifted seat, run-join).
  With `wastePark_restack` (the α1-adjacent identity) every head
  case of the first-blocked elimination is closed EXCEPT the α/β
  residue.  Remaining inside `ground_lifted_win`: the
  rung-occurs extraction (a winning play from a state with `c` in
  the tableau raises `c`: the found-membership crossing move is
  `tabToFound c ∨ wasteToFound c`, and the waste entry is
  impossible by conservation) and the α/β spread residue (the
  adjacent cancellations landed; the spread carry is the
  (C)-storage-family content — see the lift's route note for the
  protocol findings and the probe evidence above).  Battery note:
  `lake build Klondike Witnesses Orig` — all three targets green
  (the Witnesses first pass hit a transient Windows
  `.private`-olean read storm; the retry is green); census pinned
  OK throughout.
* **RESTAGE (2026-10-11, `f0b3315`-based branch commits `8c5a18f`
  → `476124b`)**: the (N) content now lives at `ground_lifted_win`
  (hwf hsafe hk hnext hbare hcorner hstep hsolv → WinFrom s₁) — the
  named-residue site became the WIN-LIFT (no play existential, no
  compliance predicate); `tabToFound_groundNormalForm` is PROVEN
  from it by the empty-prefix equivalence (the row keeps its
  statement, so the assembly and (C)'s conclusion-only cite are
  untouched).  Axiom grades: `ground_lifted_win` `[propext,
  sorryAx]`; the row and the assemblies `[propext, sorryAx,
  Quot.sound]` (sorryAx only via the lift).  Direct-attack kit at
  the ready: `wastePark_restack` (adjacent park = raise),
  `foundToTab_return`, the γ bridge plan, `ground_streak_founded`,
  the GroundRes harness.
* Axiom grades pre-restage: `tabToFound_groundNormalForm`
  `[propext, sorryAx]`, `tabToFound_dominant_of_ground` and
  `tabToFound_safe_dominant` `[propext, sorryAx, Quot.sound]`
  (`sorryAx` only via the row).  The (C) residue's storage-prong
  cite of the (N) row is UNCHANGED — Landing has not happened.

**STATUS 2026-10-11 (wave-24 cont., branch `farm/orig-dom-spread-core`
off `921bdf9`, commits `8eccb4c` → `c7c811a` → `4e27609`) — THE
SHARED SPREAD CORE: THE PROBE EXTENDED GREEN, STAGED INSTANCE 1
(THE DIAMOND) LANDED SORRY-FREE, AND THE WINDOW-CARRY CORE FULLY
DESIGNED + PROBE-SUSTAINED, STAGED AT BOTH CONSUMING ROWS.**  Zero
new sorries; census pinned (`Dominance.lean` 6 (expected 6),
inventory OK).

* **The probe (commit `8eccb4c`)**: `OrigProbes/GroundRes.lean` grew
  the club-rung mirror (`K♣` razor + its two erodes — a genuinely
  different seed, not a relabel), the slack-1 coverable world, and
  EIGHT spread-window carry cases: W1/W1'/W3 (α1-spreads, incl. the
  mirror and the queued variant: the waste tenant parked on `c`'s
  seat with c-blind tower raises inside σ, the deleted thread
  running σ' verbatim plus the DELAYED waste closer at the window
  end), W4 (the β spread: foundation worry onto another suit's
  tenant, a cross-suit raise between, the pair DELETING
  state-identically), W5 (the covered fT-park bubble: cover;
  eviction; restack nets to ZERO as a three-move unit), W6 (the
  covered α1-park at the slack-1 heights: the same net-zero with
  σ raised verbatim), W2/W2' (both diamonds, exact-key equal).  All
  plays oracle-run, slice ends compared by exact state keys: ALL
  SUSTAINED, no falsifier anywhere; the exe throws on any
  ill-formed member or asymmetry, and it CAUGHT two hand-play
  bugs of the session's own (a duplicated raise; the rank-slip
  10-covers-Q — the correct cover is a jack), which is the gate
  working as designed.
* **Probe finding — the razor PREEMPTS the α1 cover**: at razor
  heights the parked waste tenant's covers are the c-suit card at
  rank r−2 — FOUNDED TWO DEEP (its own worry-back is LIFO-dead) —
  and `c`'s dig partner (hidden under `c` until the rung raise):
  the covered-α1 corner is not constructible at razor states; the
  W6 member needed h♣ = 11 (`safeToFound`-consistent slack-1) to
  fire the cover at all.  Consequence: the covered/storage family
  lives, if anywhere, exactly at the slack-spent windows this
  route's own warning names — the rows' hsafe premise does not
  reach there; the slack re-derivation problem stands as the named
  residue, now with the probe exhibit.  Second consequence: the
  fT-origin covered bubble NETS TO ZERO with no streak-raise at
  all (delete the three-move unit) — only the re-seat moves
  (mid-window `tabToTab` of the worried card itself) remain as
  genuine window-carry content.
* **LANDED, sorry-free, audited `[propext, Quot.sound]`** (commit
  `c7c811a`, mid-file between the (N) kit and the win-lift):
  `ground_diamond_raise` — the DIAMOND: if `y`'s and `c`'s raises
  both fire from a WF state (distinct suits; distinct source piles
  DERIVED, not premised — one card one face-up seat), then both
  orders fire and LAND AT THE SAME STATE; the digs are disjoint by
  the census pack, the founds gain each card exactly once in
  either order.  This is the substitute-raise commutation the
  (N) α-route and the (C) spread squares front-load past the rung
  pass.  Helpers landed beside it: `w_chop_mem` (chop-sublist
  membership) and `w_notMem_afterRunRemoved_faceUp` (the run-
  removal absence reader covering both the chop-sublist and the
  reveal branches).
* **STAGED at both rows (commit `4e27609`)**: the window-carry
  core — the two-mode divergence field (foundation-origin: the
  deleted thread holds the worried card founded, its foundation
  length pinned at the card's index; waste-origin: founds all
  equal, the waste head locked under the parked card), the
  per-window blindness discipline (foundation-origin: no mid-
  window suit-worry [the LIFO top differs], no mid-window
  suit-raise [the restack is the only one a real window can
  fire], no placement-on-the-worried-card [the covered family —
  except the net-zero bubbles of W5/W6], no run move off the
  seat pile; waste-origin: no waste spends and no draws — the
  head is locked until the delayed closer), the convergence
  spellings (restack-time state identity; the delayed closer
  firing at the window end), and the two assemblies to write
  (`worry_pair_delete`, `waste_park_carry`) now live in the (N) `l
ifted_win` and (C) `draw1_worry_spread_residue` route notes with
  this evidence attached — the general carry is ONE lemma for
  both rows, per the row's original mandate, and its remaining
  content is the re-seat/covered/residue family above.
* Battery: `lake build Klondike Witnesses Orig` GREEN (109 jobs;
  the first passes hit the banked Windows `.private`-olean read
  storm — serial 20s-gap retries plus the final plain pass cured
  it); the GroundRes exe green; census pinned; the branch stays
  unmerged.

**STATUS 2026-10-11 — `(A) draw1_sameCycle_sameFate` IS PROVEN,
SORRY-FREE, ON `farm/orig-dom-a-reserve@c0c751b`** (+1075 lines in
`Orig/Dominance.lean`, raw hash row: the branch tip; the wave-24
census-pinned Orig four is now three, the row's own stub gone).  The
route, versus the Klondike mirror `draw1_cursor_solvable`: the mirror
spliced draws before EVERY consuming move, resyncing the twin to the
source's cursor exactly; the physical proof is one refinement
lighter — the whole invariant is the four `sameCycle` fields
themselves, with `cycleOf` kept LIST-EQUAL at every copied move,
because (i) a copied `draw` rotates both cycles in lockstep
(`draw_cycleOf`: a step-1 draw moves the presented cycle's head to
its tail, regardless of the phase), (ii) the waste top IS the
presented cycle's LAST card (`cycleOf_eq_snoc`,
`waste_head_of_cycle`), so whenever the twin's waste is nonempty it
fires the same `wasteTo*` verbatim (all guards are found/piles
reads, carried by the congruence readers), and (iii) the one genuine
corner — the twin at FULL STOCK (waste `[]`, stock = the cycle) —
splices `drain_full` (`drain_positions_one` at `drawStep = 1`: q
consecutive draws move the stock's first q cards onto the waste,
list-exact) for the whole cycle length: the drain puts the cycle's
last card in hand, keeps the cycle list, and the consumption leaves
both threads on the same stripped cycle.  Foundation transfers
close the invariant each step; `isWin` reads found only, so the
replayed play wins — both iff directions via the symmetric instance.
Arithmetic surprise, banked: at `drawStep = 1` the k-th draw
delivers `cycleOf[k-1]` PHASE-INDEPENDENTLY (the waste-head equals
the cycle-last law that makes the direct-fire case tick), but the
phases themselves are NOT mutually reachable (a full-stock state
drains and never re-stocks fully — the orbit misses it), which is
exactly why the mirror's exact-resync had to be replaced by the
list-invariant replay.  Refute-first: decided probe over all four
phase-configs of three tail-cycle orders (J-Q-K, J-K-Q, Q-J-K) plus
the splice family Q-K-J, with negative controls; it caught three
hand-schedule slips before any proof effort was committed.  Axiom
grade: `[propext, Quot.sound]` (no `sorryAx`, no `Classical.choice`).
Battery green at 104; census pinned OK.  **Bankable for (B)/(C)**:
the row is now a plain cite — any square landing up to `sameCycle`
transports through it; `drain_full` + the lockstep rotation are
reusable if (B) prefers verbatim draws over rotation composites; the
FARM_MEMORY B-note's pristine-waste suspicion applies only to (B)'s
composite squares — (A) needs no exact-state resync, the multiset
ledger never written.

**STATUS 2026-10-10 (later) — THE TO-FOUNDATION DOMINANCES ARE
FORMULATED ON THE PHYSICAL GAME, HALF PROVEN.**  `Orig/Dominance.lean`
is on main, wired at the `Orig.lean` root (chapter registry row at
`Orig.lean:114`); zero-sorry-Orig is over by exactly four named,
route-carrying stubs — the Klondike wave-24 rows in FARM.md name the
same family:

- **§5.1 PHYSICAL (the safe `tabToFound`)— the R-halves PROVEN.**  The
  statement `tabToFound_safe_dominant` (a legal raise of a
  `safeToFound` card preserves `WinFrom`) is a PROVEN assembly over
  the LANDED undo family: the under-seat case rides
  `tabToFound_undo_under` (the fit from `runOK_snoc_sit`, the search
  from the new `pileOfTop_after_tabToFound` — WF uniqueness at the
  source), the bare-king case rides `tabToFound_undo_bare`; both
  close through the new play-lift `WinFrom_of_runTo` /
  `WinFrom_of_undo` (axiom-clean `[propext]`).  The one open piece
  is the named bare-floor residue `tabToFound_dominant_of_ground`
  (below-run empty AND (reveal seated a fresh top OR no king)) —
  the old [GAP] channel-A/B reshape in physical dress; the locked
  guard has NO physical analogue (the reveal is part of the move),
  and the old deal-adjacent bases ARE this residue's geometry.
- **§5.3 PHYSICAL (draw-1 deck dominance) — the layer split,
  named.**  `stock_dominance_draw1` (front `c ∈ st.stock` with
  `nextUp` + safety as a deal-out-and-stack play) is PROVEN plumbing
  over `(C) draw1_compliant_normalForm` and `(B) draw1_compliant_replay`
  (safety-free, the same nine-case ledger as the Klondike chapter's
  B, with `sameCycle`/`(A) draw1_sameCycle_sameFate` — the physical
  stock-as-reserve rotation, `cycleOf := stock ++ waste.reverse` —
  replacing the old cursor twins).  The compliance is the rung
  discipline (`rungHeldUntilExit`: only `c`-suited worry-backs are
  banned pre-exit — for a stocked rung card no other shape reads
  its slot).
- **New vocabulary**, all physical: `safeToFound` (Keller's rung
  condition through `foundHeight`), `sameCycle`/`cycleOf`,
  `Move.leavesWaste`, `Move.lowersRung`, `rungHeldUntilExit`,
  the transports `WinFrom_of_runTo`/`WinFrom_of_undo`.  Axioms:
  `tabToFound_safe_dominant` `[propext, sorryAx, Quot.sound]` (the
  sorryAx is exactly `..._of_ground`),
  `stock_dominance_draw1` `[propext, sorryAx]`.
- **Refute-first gates** (each stub's note): a bare-floor state whose
  every win parks on `c`'s fresh seat before the suit climbs; a
  sameCycle rotation that is not fate-preserving at draw 1; a
  compliant-less corner for (C); a (B) square that is not an
  equality/sameCycle landing.

**UPDATE 2026-10-10 (B session, branch `farm/orig-dom-b-replay`) —
(B)'s engine kit landed sorry-free; the assembly open.**  The draw-1
`draw1_compliant_replay` keeps its named stub; the session landed
the full private development the nine cases read, in
`Orig/Dominance.lean`: the list surgery and the dealt composites
(`drain_positions1`/`base_positions1`/`drain_run1`/`redeal_run1`,
dedup-marked `Phase` ports), the two fronting engines —
`front_stock` (c stocked at depth `|pre|`: `|pre|+1` drains, landing
`⟨bump c, suffix, pre.reverse ++ waste⟩`) and `front_waste` (c
wasted: drain + recycle-deal + `|postW|` deals, landing `⟨bump c,
preW.reverse ++ stock, postW⟩`) — the raised-form spend step
(`wtf_step_raised`), the `lower_foundToTab1` worry-back leg ported
from Shuttle for the `wasteToTab c b` exit, and `bump2_comm` (the
two foundation bumps commute at distinct suits).  Probed route
corrections, recorded at the stub's STATUS note: (i) the induction
is WF-free — the `π = []` corner is isWin-vs-nextUp alone
(`toIdx < 13` against the 13-cap; no step-preserved WF anywhere,
which is `Orig`'s open ticket anyway); (ii) the consuming-move
squares land up to a pure-draw ROTATION of the same cycle (mutual
reachability lifts the win with no transport), not up to
`sameCycle` as the original note claimed; (iii) the one genuine
(A) citation is the waste-form fronting's pristine corner
(`postW = []`: the 13-slot is dealt back at the last recycle, the
fronted twin's cut never re-closes) — a TIGHTER (A)-use than the
route map's.  Axioms unchanged: `stock_dominance_draw1` still
`[propext, sorryAx]` exactly through (B)+(C)+(A).

**UPDATE 2026-10-11 (B2 session, branch `farm/orig-dom-b2-replay`,
head `66c648d`) — (B) IS LANDED: `draw1_compliant_replay`
SORRY-FREE.**  The probed route closed.  In `Orig/Dominance.lean`:
the `FrontOK` motive (stock `|pre|+1` draws / waste
`stock.length+|postW|+1` draws, engine-literal landings pinned
field-by-field by `front_stock_shape`/`front_waste_shape`); the
nine-case kit — `front_nil` (WF-free isWin-vs-rung), the six-arm
`front_draw` absorb (`draw_shape_plain`/`_base`; the a=c and b=c
pristine arms land the engine's own raisedMid literal — the
u-conclusion is the FRESH `([draw; wtf c])` form, and the
`base+b=c` arm's `([], bs⁻¹)` shape replaced the route-note's
prepended data; both arms re-crystallized the rw-count
equivalence on `u.stock.length` first); `front_board_tf/tt/ft`
(the equality squares through the new
`chop_bump_comm`/`double_bump_comm`/`setFound_found_congr` kit);
the four consuming waste-head squares
(`front_consume_{wtf,wtt}_{stock,waste}`: the rotation resync
as explicit composites — segment A plain drain `|preW|+1` to
x's hand, the x-spend, then CROSSING (drain `|u.stock|` + redeal
`|postW|` onto the reversed spine) or PRISTINE (`postW = []`:
the twin R `([], u.stock⁻¹ ++ preW)` is sameCycle-adjacent to
the s₁-landing; `cycleOf R = preW⁻¹ ++ u.stock`; the win rides
`(A) draw1_sameCycle_sameFate |>.mpr hwin₁` — the ONE genuine
(A) cite, exactly as probed); `front_exit_wtf/wtt` (tail
verbatim; `lower_foundToTab1`); and the dispatcher
`replay_front_aux` (W5's sixth commit) — the rung-discipline
split routes the five non-c-leaving heads to census exfalsos,
the two c-exits to the exit engines, and the clean arm carries
the per-kind bundle (`hn1` through the found readers, the
cycle-disjunct through `draw_inCycle` and the per-kind
stock/waste rw-bridges) into the IH at `rest`.  The final
theorem reads k off the motive data.  Session discipline
[commit after every green engine] paid off once [the W1 report
below]: a shell-slicing accident after the wtt_waste engine
went green cost one recompile's worth of rebuild, restored
clean from the W2 checkpoint — the twice-oracle-validated
route note rebuilt it FIRST-COMPILE-green.  **Audits:
`draw1_compliant_replay` = [propext, Quot.sound] — SORRY-FREE**
(the earlier imported-olean reads at [propext, sorryAx] were
stale; the in-file fresh print is the oracle); all twelve
engines clean; `stock_dominance_draw1` = [propext, sorryAx,
Quot.sound] with the sorryAx ONLY through
`draw1_compliant_normalForm` into the (C) residue
`draw1_worry_spread_residue` — precisely the landing spec.  The
(N) stub stands untouched.  ZERO new sorries; census pin-compare
is the merge wave's (Dominance's count now [N]+[C] only); the
branch stays unmerged.  Banked-and-transferring for the (C)
residue: the `putCard`-forward-step recipe (`wasteIs_cons` +
`decide_eq_true rfl`), the found-chains for raise-squares
(`hG'fLit`-style `rw [hG'f]; rfl` — opaque-tuple crafts, never
in-line rewrites), and for [GAP]: `zone_two_hits_ne` (one card
at most once per zone, the in-zone census bound) and the
`by_cases + obtain-cons` pattern (never `cases` a name you
still need).

**STATUS 2026-10-10 (the farm-orig-dom-c-normform session, row
`00b3ea1` on `farm/orig-dom-c-normform`) — (C) IS A
PROVEN SKELETON.**  `draw1_compliant_normalForm` left the stub list:
the normal-form case split is `normform_aux`'s (strong induction on
the washing play with the rung-cycle bundle `{WF, drawStep = 1,
nextUp c, c in the stock or waste}` — the nil play and the lone
worry die on the cycle's win blockade `inCycle_notisWin`; an exit
head is compliant verbatim; a clean head transfers the bundle and
recurses; the ADJACENT window `[foundToTab x b; tabToFound x]`
cancels through `foundToTab_return` — the two-step worry-undo
identity at WF, proven — recursing two moves shorter at the same
state).  ONE named residue remains for the row:
`draw1_worry_spread_residue` — the window-spread world (a c-suit
worry-back followed by a non-restack), whose route note owns:

- the **window accounting**: the win founds `c` so the restack exists
  in the window — but LOCATING it needs the §12.1 first-passage
  family, not yet ported to Orig (the recorded gap);
- the **spread squares**: the `wasteToFound y` square is LANDED
  (`foundToTab_wasteToFound_square`, composite-equal, its
  `putCard_piles_eq_of_eq` twin-carrier channel the pattern-kernel
  for the rest); `draw` reduces to the recycle-triple channel
  (`draw_unfold` at both states plus the three `recycle` readers);
  `wasteToTab`/`foundToTab` square only off the worry-created seat
  (the storage family); `tabToFound y` order-locks at base `inr y`;
  `tabToTab` corners when the run passes through `x`; worry-worry
  pairs never square (the second reads the post-first top — LIFO);
- the **storage prong**: name-cites (N)'s
  `tabToFound_dominant_of_ground` as the bare-floor win-lift, with
  the slack analysis recorded — the repair wants `safeToFound`-at-x
  by slack one under the root's `hsafe`; the engine does NOT carry
  safety (an other-suit worry-back on a clean prefix can spend the
  slack), so the residue either re-derives the slack at the window
  or earns a premise repair; (C)'s statement keeps `hsafe` at the
  root for exactly this prong.
- **Refute-first gate (this row's stub)**:
  `witnesses/OrigSpreadCoReal.lean` — the residue's premises co-fire
  at a crafted WF draw-1 state (hearts/clubs one king short, spades
  and diamonds complete) with a spread-shaped WINNING play
  (`[worry ♥Q onto ♣K, draw, restack, c-exit stack, ♣K raise]`), the
  repair's positive instance (the compliant two-moves-shorter play)
  and the adjacent-pair identity, all decide-anchored; no
  countermodel was findable by the bounded corner probes (the
  52-card full search is outside decide reach) — the premises'
  honesty is what the witness pins.
- **Audits**: `draw1_compliant_normalForm` = [propext, sorryAx (via
  `draw1_worry_spread_residue` ONLY), Quot.sound];
  `draw1_worry_spread_residue` = [propext, sorryAx].  (N) does not
  taint (C) directly (route-level citation only): when (N) lands, the
  storage prong's win-lift half closes by citation, and the residue
  stays the only sorry between (C) and the Harvester until its own
  squares and window accounting land.  Orig stub count: FOUR
  unchanged in number — the (C) stub was replaced by the (C)
  residue (routes moved in, not out); census stays Klondike-pinned
  per FARM.md.

## 8-prior. The both-occupied harvest (2026-10-10 earlier, branch `macro-game`)

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

## 10. The exchange-canon commutation card (2026-10-11, branch `orig-exch-canlaw`, rebased onto macro-game `47b1ad9`; landing-1 probe battery GREEN, the inherited backlog's first falsifier candidate FIRED)


## 9. The pull-multiset determinism family — session orig-macro-determinism (STATUS 2026-10-11)

Branch `orig-macro-determinism`, based on macro-game `b8a1584`; the
untracked MacroInternal skeleton was copied in and committed as the
branch base (`05be2b5`); the determinism rows landed (`2f6795f`) and
the decide battery with them (`5d7b1b6`).  Partition honored: the
floor session's rows (every other sorry-stub in the skeleton) are
untouched; no merge to macro-game.

LANDED, sorry-free, audited in-file (`lake env lean
Orig/MacroInternal.lean` prints the battery; `lake build Orig`
stays green at 28 jobs — the module is deliberately not wired into
the root):

- `rung_found_prefix` — RESTATED per the real banked invariant: the
  skeleton's placeholder (`∃ cs, found = cs.take rung ∧ True`) was
  trivially true; the honest row is `WF.found_prefix`
  (`Orig/Integrity.lean`) spelled at the rung (`found s =
  s.upCards.take (rungAt w s)` at `WF`), plus the key consequence
  `rung_found_congr` (same rung count ⇒ same founded content —
  at a fixed height-tuple every fiber member's foundations agree
  card-for-card; why mixed-residence exchanges never arise
  in-fiber).  `[propext]`.
- THE NEW THEOREM (nobody had it): the descent-determinism of the
  pull letter.  `ConeLedger` (the pop ledger: a List-indexed
  inductive over ConePath) with `cone_ledger_of_path` (every cone
  path carries one), `cone_rung_mono` (rungs only fall along cone
  descents), the master `cone_pop_window` (the per-suit pop ledger
  is exactly the forced window — `popWindow l j := (l.drop
  j).reverse` read at `(anchor.found s, rungAt member s)` — a
  function of the anchor's founded content and the height tuple
  ALONE, never of the path: pops are forced top-down by the raw
  `foundTop = some c` guard of the `foundToTab` step), the
  multiset grading `cone_pop_countP`, and the INTRA-ARM form
  `cone_pulls_congr_tuple` (two cone-descendants of one `WF`
  anchor at the same tuple pulled equal multisets).  All
  `[propext, Quot.sound]`, zero choice.
- `flat_into_dance` — proved by straight structural induction
  (post-merge FlatStep carries no exchange letter: cargo IS a
  `ConeStep.slide` shape, draw likewise; the net-flat reading
  follows from the slide/draw found-writers).
  `[propext, Quot.sound]`.

RESIDUAL (gated, the family's one sorry): `cone_pulls_congr_crossarm`
— the cross-arm tuple-mate equality, stated CONDITIONALLY on the
envelope's corridor (`hcorr : ConePath A₁ (conjl A₂)` — the
envelope's own conjl-disjunct shape).  BLOCKED on rows this branch
does not own: the envelope itself (the decompression card) and the
conjugation family's laws (`conjl_involutive`/`conjl_inClass` and
the pop-window transport through the conjugate — the conjugation
rows).  The obstruction is recorded in the docstring: between
genuinely distinct arms the Final tuples are fork-flipped
(`saturated_tuple_orbit`'s flip branch) and cone legs are
rung-monotone (`cone_rung_mono`), so a literal cone bridge between
the arm anchors cannot exist — the conjl-corridor is the only
route, and pricing it is the envelope card's business.  sorryAx
rides exactly this one row, per the in-file audit.

PROBE: `probes/DeterminismProbe.lean` (README row added; recorded
numbers pinned in-file): the census engine over legal pull/slide/draw
plays at two WF-crafted full-deck cells (the interleaving cell; the
twin-king cell consuming the canon-v3 craft conventions), D1
(pulled card IS the current top, everywhere in the census), D2 (the
pop list IS the forced window, every walk), D3 (the ranked negative:
same-tuple differing-multiset violators ABSENT — 0 among
3346/46208 pairs — with order-differing pop lists and
different-tuple different-multiset pairs both present, plus the
interleaved twin-suit ♥Q/♦J routes visible at the twin-king cell).

COORDINATION (why this note is here):

- **canon-v3-scaffold (owns the mirrors)**: the skeleton's
  `rung_found_prefix` statement is RESHAPED at this branch (the
  placeholder was provable by `take_all`; the honest form adds the
  `WF` premise and the upCards reading) — mirror accordingly; the
  reshape is content-ADDITIVE (the placeholder was a vacuous
  shape, so no consumer can break).
- **orig-macro-floor (owns the other rows)**: untouched here; when
  your rows cite the founded-content machinery, the consumable
  heads are `rung_found_prefix`/`rung_found_congr` (the fixed-tuple
  founded-content identity `fiber_iff_flat`'s engine needs for
  mixed-residence-freedom), and the writer/window kit (ConeLedger,
  popWindow, cone_pop_window, cone_pulls_congr_tuple) is this
  family's harvest for the capstone assembly — cite, do not
  re-derive.
- **the capstone (fiber_iff_flat's engine)**: the pull letter's
  descent determinism is now certified at the intra-arm grade; the
  cross-arm pricing waits on the decompression card's envelope.


 HEAD
Section numbering note: §9 is the canon-side completion card's
ledger, recorded on `orig-canon-decompress` (landing 1, commit
`8a0e121`, base `f0b3315`) — this section reserves §10 on this branch
so the two append-only ledgers merge cleanly in either order.  This
card owns the follow-on that §9's "FOLLOW-ON EXCHANGE-CANON CARD"
menu named: territory `Orig/TwinExchangeQuotient.lean` + the twin
quotient's canon-facing spine, the physical twin-exchange commutation
laws.  The inherited menu's items are cited by their §9 names
(`canonQ_of_physOrbit`, `exch_free`, `exch_le_sameOrbit`, the
decomposition, the interpretive doctrine).

**LANDING 1** (`lean-model/probes/ExchCanLawProbe.lean` — external,
lake-env-runnable, gates throw on failure, kernel-decided through the
house `decSt` bridge; the README row landed): every verdict below
decided at honestly WF-crafted full-deck cells BEFORE any proof
effort.  The probe's stock-crafting mover (`exStock`, the exclusion
list includes the FOUNDED cards) is deliberate and worth recording:
the first run's B-cells double-counted foundation cards in the stock
and failed their own WF gates — the census mirror caught what the
hand-write missed; every recorded number below is from the fixed,
census-clean battery.

* **A — the wiggle cube mirrored (canon vacuous).**  The §9-A1 board
  (♠Q between the red kings p1/p5, ♣J between the red queens
  p3/p4, foundations empty, rest in stock): all four corners WF and
  canon-FIXED (nothing rung-ready — canon is the identity); every bit
  licensed at every corner, both orientations (the pair law at each
  corner), each bit writes EXACTLY its own two seats (the K-bit
  leaves the Q-pair piles verbatim — the per-pair locality datum);
  the four corners pairwise distinct; the two-bit composite is
  order-free; and canon images of exchange-mates DIFFER literally —
  at saturation-vacuous cells the wiggle survives canon outright
  (canon seats nothing), so the canon-image connection IS the bit
  itself.
* **B1 — the benign cell (saturation fires, literal commutation
  holds).**  K-pair with a RUNG-READY residue (♠Q over ♥K, spades
  climbed A..J): the canon lifts the residue off either seat to ONE
  saturated state — `canon (exchange st) = canon st` LITERALLY (the
  saturation erases the bit); the exchange at the saturated state is
  the both-bare identity; the license SURVIVES saturation as the
  DEGENERATE both-bare license.  This is the cell where the literal
  square and the exchanges-only row were expected to hold — they do.
* **B2 — THE WORRIED-KING FORK (the first falsifier candidate FIRED;
  the inherited menu's exchanges-only pinch is REFUTED at this
  exhibit, and the refutation is the card's central datum).**  Hearts
  and diamonds both climbed A..Q; ♥K BARE on p1 (a rung-ready bare
  king), its twin ♦K carrying the non-twin residue ♣Q on p5.  ONE
  licensed exchange at the K-pair (bare clause on the p1 side,
  realized step-exact by the noreveal slide `tabToTab ♣Q (inr ♥K)`)
  moves ♣Q onto ♥K — and the two trajectories then fork the
  SATURATION ITSELF: `canon st` lifts the bare ♥K
  (hearts A..K, found-length 13), `canon (exchange st)` lifts the
  bare ♦K (diamonds A..K) — the founds split 13/12 vs
  12/13, `canon` differs, the literal square dies AND the
  re-saturated square dies (the exchange at `canon st` is the
  identity — the host is FOUNDED, the engine half "licensing
  preserved at the canon images" dies with it: `exOKB` reads false
  at BOTH canon wings).  **Why no exchanges-only quotient can join
  the wings: `State.exchangeTwin_found` — an exchange writes piles
  only, so `found` is invariant along every `ExchChain`; the wings
  differ in foundation content, so `⟪canon u⟫ = ⟪canon v⟫` would
  force equal founds.**  This is §3.1's grading-note fork
  (canonical / worried-♥ / worried-♦ — "three `RevEqW`-distinct
  outcomes") met at the canon level, the residue-exhibit cell the
  card named as the first falsifier family.  The honest witness is
  the A2 anatomy, probe-verified step-exact:
  `canon u --foundToTab ♥K (inl p1)--> u --exchange--> v
  <--foundToTab ♦K (inl p5)-- canon v` — pull, exchange, pull,
  every leg reversible.  So canon images of physical class-mates ARE
  joined — by PULLS + the exchange, the sameOrbit world, never by
  exchanges alone.
* **C — licensing drift.**  Around the 2² cube: no drift (every bit
  licensed at every corner, both orientations).  Along chains: each
  bit is its own involution; re-asking the K-pair at the twin member
  `(♥K → ♦K` after the Q-bit`)` toggles the same bit home; chains
  compose in either order at disjoint seats.  Against saturation:
  the fork cell KILLS the license at the canon wings (a host is
  founded), the benign cell preserves it as degenerate — the license
  is NOT saturation-invariant in either direction, driver discovered.
* **D — the freeness census (the deck-partition evidence).**  The
  3-bit board (K-, Q-, J-pairs at p1/p5, p3/p4, p2/p6 — pairwise
  disjoint host seats, twin-legal residues riding): all EIGHT composite
  corners WF and canon-fixed, the composites equal the crafted
  corners (each bit writes exactly its own corners), pairwise
  DISTINCT (the 2³ torsor witnessed), every bit licensed at every
  corner (drift-free at disjoint seats), order-free composites.
* **E — the negative controls and the identity pricing.**  The
  licensed BOTH-BARE bit is the IDENTITY (`exchangeTwin = st`) —
  freeness must price identity-valued bits at ZERO; `exch_free` is
  AMENDED accordingly below.  Hidden-member (♠Q's twin ♣Q lost in
  stock) and waste-resident (♦Q in the waste) pairs are never
  licensed and never generate a step (identity exchangeTwin at
  every unlicensed shape probed).
* **Census numbers (the pinned data):** licensed nondegenerate pair
  representatives: 6 at the 3-bit cube (three pairs, both
  orientations), 2 at the fork cell (the K-pair), 0 at the fork
  cell's canon images (saturation founded the hosts), 4 at the
  2-bit cube; fork wings 13/12 vs 12/13; the benign erase `true`;
  the fork split `false`.

**THE HONEST GRADE (the menu corrected, recorded per the interpretive
doctrine — physical first):** the inherited `canonQ_of_physOrbit`
formulation — `PhysEq u v → ⟪canon' u⟫ = ⟪canon' v⟫` over the
EXCHANGES-ONLY quotient — is REFUTED by the B2 exhibit at every
canon grade (`canon_draw` composes on the zone, never the founds;
the wings split founds).  The refutation is not a boundary artifact:
it conflates "the exchange connects `u` to `v`" (true — the bit is
the class road) with "the exchange connects their canon images"
(false at fork cells — the exchange acts on seating, canon acts on
rung-readiness, and at a twin pair of rung-ready bare kings the
exchange swaps WHICH member canon consumes).  The ⟪⟫-behavior at
fork cells is a FEATURE — the physical receipt that the worried-twin
fork is one genuine bit (the `exch_free` torsor separating the
worried-♥ wing from the worried-♦ wing is the quotient doing its
job).  The COMPOSED correction, per the coordinator's landing-3 call
(this response to this probe report), two layers:

1. **SPINE (theorem grade, Option 1):** `canonQ_of_physOrbit'` over
   `PhysEq` (the generator closure: refl + `RevEqW` shuffle legs +
   `ExchStep` exchange legs + trans) stated at the macro-state
   quotient: `u.WF → PhysEq u v → ⟦canon u⟧ = ⟦canon v⟧` — refl is
   rfl, the shuffle case rides the banked `canonQ_of_orbit`
   (`RevEqW` is a sameOrbit edge), the exchange case the landing-2
   `exchange_leg_sameOrbit` (the one-move `RevEqW` realizations,
   both-bare degenerate = refl) + `canonQ_of_orbit`, trans
   composes; a WF-propagation row (`step_wf` for the shuffle walks,
   `State.wf_exchangeTwin` for the legs) buys the single-gate form.
   NO BLOCKED PIECE REMAINS at this grade — the §9 menu's
   BLOCKED-ON-DECOMPRESS shuffle leg (the literal
   `canon'_shuffleEq`) is superseded by the regrade; it remains the
   decompression card's own two-letter content.
   **RECORD-CLOSED:** `PhysEq u v → ⟪canon u⟫ (= ⟪canon' u⟫) = ⟪canon
   v⟫` over the exchanges-only quotient stands REFUTED-BY-EXHIBIT
   (B2): exchange legs never write `found`
   (`State.exchangeTwin_found`), the fork wings split founds, so no
   exchange chain joins them, at any canon-composed grade.
2. **ANALYSIS LAYER (Option 2, probe-evidenced):** on a saturation
   fiber where canon does not fork (the B1 regime), the exchanges-only
   row holds LITERALLY (canon erases the bit; the exchange at the
   canon image is the both-bare identity) — this is evidence-grade,
   the probe certifies the cells, no general theorem claimed here.
   `exch_free` lands at the disjoint-seat grade with the probe's
   amendment: identity-valued bits (the both-bare degenerate bits,
   `exchangeTwin = st`) price at ZERO — the torsor counts `2^k'`
   over the NON-IDENTITY licensed bits; the licensed-chain reading
   rides the license-stability row (a disjoint-seat family's
   licenses survive one another's bits — the drift-free cube datum
   as theorem).

**THE COMPOSED DECOMPOSITION (the card's capstone, recorded with its
DEPENDENCE DIRECTION; not forged here):** one sameOrbit class ≈
(the canon anchor + the pull ladder — the decompression card's
two-letter fiber, THEIR `finalWiggle_reach` / `canon_draw` landing)
× (the licensed swap bits, priced by the landing-2 `exch_free`)
⊎ (the conjugation shadow — twin pairs with no physical witness,
hidden/waste-resident).  **The worried-twin bit is EXCHANGE-PRICED
AT THE TIP LEVEL**: this card's B2 A2-highway witness (canon u
–pull→ u –exchange→ v –pull→ canon v) is its price tag — the
exchange lives in the ACCOMMODATION PREFIX between the canon images,
never at canon level.  This decomposition is BLOCKED-ON-DECOMPRESS
(the canon-prime normalizer and the two-letter padding are their
landing-2 content); this card lands the swap-bit side (freeness,
locality), the forgetful map, and the spine — the composed
statement assembles when their fiber lands.

**COORDINATION NOTES (relayed through the coordinator's
landing-3 call):** (i) the twin-kings cell is COMMON MATERIAL — this
battery and the decompression card's A-next probes share it; (ii)
the B2 witness REINSTATES THE SLIDE LETTER in the decompression
card's cone alphabet: their σ-absorption of slides is refuted at
this cell (a cargo-covered member is pull-unreachable — the slide
leg is load-bearing in the accommodation prefix); their §9 menu's
`canon'_shuffleEq` inherits the same fork warning this battery
recorded at the canon grade.

**LANDINGS 2 AND 3 — COMPLETED (2026-10-11 later, same branch;
`Orig/TwinExchangeQuotient.lean` §5–§8, all heads audited fresh,
in-file):**

* **Landing 2** (commit follows the landing-1 probe verdicts): the
  realizations went PUBLIC (`step_realize_fwd`/`_bwd` in
  `Orig/TwinExchange.lean`, the two-line pathway the chapter header
  itself named).  `exch_leg_RevEqW`: every licensed bare exchange
  is a ONE-MOVE witness shuffle both directions (cargo-side via the
  realization-pair, twin-side through `State.exchangeTwin_pair`,
  both-bare reflexive); `exch_chain_RevEqW` walks chains;
  `exch_le_sameOrbit` is the coarsening row;
  `exchOrbit_to_sameOrbit` the forgetful map (surjective via
  `Quotient.exists_rep`, NOT injective by the B2 exhibit's
  meaning).  `exch_local_pair` (per-pair locality, named per the
  card); `exch_pileHolding_off` (off-seat cards keep their seat —
  the location half of the old private relocate census done in
  four lines through Integrity's search-exactness iff);
  `exchange_piles_congr` (the seat-data congruence of the single
  exchange); `exch_superpose` (the disjoint-family superposition:
  a pair-distinct seat-disjoint fold is the per-pile union of the
  BASE-DATA single writes — every pile off the seats verbatim,
  WF-gated, license-free); `exchangeTwin_ne_self_pile` (the probe's
  identity-pricing amendment as the engine row);
  `exch_free` (the torsor freeness at the disjoint-seat grade,
  non-identity bits only — the 2³ census as theorem);
  `exchAll_wf` + `twinExchOK_exchAll` (the drift-free cube datum as
  theorem: a disjoint-seat family's bit executions preserve every
  other pair's license — the licensed-chain reading of the torsor).
* **Landing 3** (the composed spine, per the coordinator's call):
  `PhysEq` — the physical generator closure, the card's working
  definition (refl + `RevEqW` shuffles + `ExchStep` exchanges +
  trans); `physEq_wf` (the closure preserves `WF`: witness shuffles
  are legal walks through `step_wf`, licensed exchanges ride the
  located license — note: `step_wf` needed
  `import Orig.Reach`, the same one-import addition the canlaw
  session used for Canonical, cycle-free both times);
  `exch_canon_comm` — one licensed exchange's canon row at the
  Option-1 macro-state grade (`canonQ_of_orbit` over the sameOrbit
  edge of `exch_leg_RevEqW`); `revEqW_canon` — the shuffle leg's
  row; and **`canonQ_of_physOrbit'`** — THE SPINE, single-gated:
  `u.WF → PhysEq u v → ⟦canon u⟧ = ⟦canon v⟧`.  Refl reflexive,
  the shuffle case rides the banked `canonQ_of_orbit` (the
  BLOCKED-ON-DECOMPRESS shuffle leg of the menu's literal canon
  form is superseded by the regrade — the literal
  `canon'_shuffleEq` remains the decompression card's own
  two-letter content, with this battery's fork warning recorded),
  the exchange case cites `exch_canon_comm`, trans composes.  The
  exchanges-only literal form is RECORD-CLOSED in-file (the §8
  tombstone) and here: refuted by exhibit, the founds split is
  structural (`State.exchangeTwin_found`), and the ⟪⟫-separation is
  the worried-twin bit's receipt.
* **Audits**: every new head — `exch_leg_RevEqW`,
  `exch_chain_RevEqW`, `exch_le_sameOrbit`, the forgetful map trio,
  `exch_local_pair`, `exch_pileHolding_off`, `exchange_piles_congr`,
  `exch_superpose`, `exchangeTwin_ne_self_pile`, `exch_free`,
  `exchAll_wf`, `twinExchOK_exchAll`, `exch_canon_comm`,
  `revEqW_canon`, `physEq_wf_canon`, `physEq_wf`,
  `canonQ_of_physOrbit'`, the `PhysEq` constructors — audited
  fresh in-file at `[propext]` or `[propext, Quot.sound]`; ZERO
  sorry, zero native_decide, zero `Classical.choice`; `lake build
  Orig` green at 28 jobs.
* **What deliberately did NOT land**: the fiber-restricted literal
  exchanges-only row (analysis layer) stays probe-evidenced (the
  B1 cell certifies the benign fiber; no general theorem claimed —
  the saturation-interplay is the decompression card's
  `canon_slide` world, and the fork cell stands as the boundary);
  the composed macro-class decomposition (≈ (canon anchor + pull
  ladder) × licensed swap-bits ⊎ conjugation shadow) stays
  BLOCKED-ON-DECOMPRESS, ledgered above with its dependence
  direction and the B2 highway as the worried-twin bit's price
  tag; no `canon'` content was forged.

* **STATUS (2026-10-11, branch `orig-successor-completion` — the
  successor-program completion card: the waste-entry datum upgrade,
  the third-row stack-event spec, and canlaw's tab-seat base check
  audited)**:
  - **Priority 1 LANDED** (cd7a358): the datum fiber's canon-side
    computable reading — `MacroDatums.of_canon` + `datumOf_canon`
    (the canon-computable `datumOf` kernel: the datum bundle is
    canon-invariant through every licensed lift, so the computed
    read at `canon u` is the member's own and the residue exhibit's
    literal canon-divergence inside a class does NOT bite the read);
    `tipEdge_wasteEntry_datum_canonical` (the pre-pinned upgrade
    shape EXECUTED: the `wasteNext` class map computed AT THE
    CANONICAL REPRESENTATIVE, the raw-member fiber row kept as the
    member-grade soundness the computation rides); and
    `tipEdge_wasteEntry_canonFiber` (the lease graded canon-side: at
    a `CanonicalTip` under the rung both exits' canonical images
    COINCIDE at the saturated computed founder,
    `wasteEntry_bothRoutes_canonical` consumed, the quintet
    underneath, `wasteEntry_mergedLeg` the cited boundary note — one
    cite one site). The parked cross-mate class-collapse stays
    parked (the phase-shift and tab-seat corners still own it).
  - **THE TAB-SEAT BASE CHECK (canlaw's section-5 finding) DISCHARGED
    AT THE PREMISE GRADE AND LEDGERED**: the audit of EdgeLabel's
    successor-commutation rows found the tab-seat reads exactly
    where the member grade wants them — `tipEdge_wasteEntry_target`'s
    seated arm (`e.c.canPlace c b = true` at the raw member),
    `waste_edge_outcome`'s same-shaped hypothesis, and
    `waste_entry_composite`'s `hcp` (all member-grade soundness rows,
    by design); the draw-successor rows carry NO `canPlace` (zone
    moves). NO RAW→CANON TRANSPORT OF THE SEAT EXISTS OR IS CLAIMED
    anywhere in EdgeLabel — the canlaw probe's refutation stands as
    the boundary (the licensed lift may consume the seat card, the
    seat evaporates under canon, the transport fails both ways at
    WF). The canon-side successor consumption lands at the
    CANONPREMISE GRADE instead: `tipEdge_wasteEntry_canonFiber`
    carries `CanonicalTip`, so the seating's `canPlace` leg reads at
    a member that IS the canonical form — re-checked at canon by
    construction, never transported. **THE CAVEAT, FOR EVERY FUTURE
    CANON-SIDE CONSUMER**: a canon-side row that wants the seat must
    add the `CanonicalTip` premise (or an explicit canon-side
    `canPlace` re-check); raw-grade `canPlace` hypotheses do NOT
    carry through `canon`/`comm_wasteToFound_sat`/
    `wasteEntry_bothRoutes_canonical`.
  - **Priority 2 LANDED** (934245e): the third TipEdge label row —
    stack-bare-a, the share of the vacate/reveal pair, purely
    additive (import `Orig.Vacate` added, no cycle):
    `tipEdge_stackEvent_determination` (the sub-cell dichotomy with
    the four channel facts per cell — the reveal pops the seat's
    hidden head and seats the revealed card's own root read; the
    vacate leaves every hidden stack verbatim, the seat literally
    BARE, its non-king root departed — the tabToTab half through the
    engine's free_slot row `vacate_emptiesPile`, cited one-site from
    `Orig/Vacate.lean`), and `tipEdge_stackEvent_target` (the
    target's class data is one of TWO computable images
    `MacroDatums.stackRevealAt`/`stackVacateAt` — the third row of
    the uniform `≤ 2`-per-label count anatomy at the datum grade).
    The cross-mate collapse stays refused with the corridor
    inventoried at the section head (`step_square` for the draw legs,
    the vacate case map in `Orig/Vacate.lean`'s recorded ledger, the
    worry capstone's `stackPile_worry_prunableAt` for the worry legs).
  - Battery `lake build Orig` green at 29 jobs per commit; every new
    head audited `[propext, Quot.sound]` worst (the two datum-image
    defs carry none), zero sorry, zero native_decide, zero
    `Classical.choice`.



## 9. The canon-side completion card (2026-10-11, branch `orig-canon-decompress`; landing-1 probe battery GREEN, all verdicts in)

The §3.0 completion this card owns, in the final folded shape after
the mid-flight user refinements (R1-R3 + the backlog family, all
recorded here verbatim for the follow-on card): (A) DECOMPRESSION
REACHABILITY — the reverse of the canonicalization theorem, every
class member reachable from a FINAL anchor by the two-letter padding
(foundToTab pull-downs + noreveal tabToTab slides, every tabToFound
raise leg the exact undo of a pull-down leg, the V2 undo family
`tabToFound_undo_under`/`_bare` and the residence calculus :499-507);
(B) DRAW-PHASE NORMALIZATION — `canon_draw : State → State` as a
NAMED compositional step, `canon' := canon_draw ∘ canon`, identity
off its pure domain, junk-safe, the TARGET presentation
probe-pinned (the pinning rule), the offset side a commitment
boundary (`draw_irreversible_offset`, Phase.lean:823).

**LANDING 1** (`lean-model/probes/CanonDecompressProbe.lean` —
external, lake-env-runnable, gates throw on failure; the README row
records it): every verdict below is decide-graded with negative
controls. Loading note for the card's memory cites:
`draw_passBase_reversibleW` lives at `Orig/Classify.lean:1252`
(cite-read; NOT Phase.lean), consumed by `tipEdge_draw_shape`
(`Orig/EdgeLabel.lean:1426-1457`) together with
`draw_reversible_inphaseW` (`Orig/Phase.lean:1513`).

* **A1 — the finalWiggle cube (beyond length 1, LIVE).** Two
  independent twin-host residues (♠Q between the red kings p1/p5,
  ♣J between the red queens p3/p4), foundations empty, everything
  else in stock: all four WF Final corners are joined by noreveal
  tabToTab slides, one move per relocated residue, and the length-2
  composites reach the far corner in EITHER leg order (the
  disjoint-pile commute). Why the old residue hunt (the corpus note
  at :958-961) never found these: length-2 instances need EITHER
  multi-residue boards (A1) OR a pull-down bridge (A2) — the hunt
  searched one-residue, foundations-empty casts.
* **A2 — the worry-back BRIDGE (LIVE).** Residue ♠J on its tableau
  host ♦Q; the twin host ♥Q trapped in the FOUNDATION (hearts
  climbed A..Q); the landing site is a bare ♠K pile. The
  wiggle-mate is reached ONLY by `foundToTab ♥Q (inr ♠K)`
  (pull-down) then `tabToTab ♠J (inr ♥Q)` (the slide onto the
  pulled substrate); the direct slide is barred (♥Q not tableau —
  search fails); the return journey uns lides first, then performs
  the pull's EXACT-UNDO raise (the residence calculus's
  pile↔foundation noreverse pair, REORDERED after unburying). Both
  endpoints WF + Final. This is §3.1's worry-back anatomy landed as
  a Final-to-Final class-mate family: the moved substrate is buried
  under the arriving run at the mate, and only the unslide
  re-enables its return leg.
* **A3 — the ONE-LETTER refutation (R3's target, REFUTED).** At the
  re-derived residue-reloc exhibit (♠3 between ♥4/♦4,
  foundations empty): the pure `foundToTab` fire-set at the anchor
  is EMPTY (pinned datum: no foundation holds any card), so the
  pure-pull reachable set is {anchor} ∌ the wiggle-mate, while the
  two are same-orbit (one-move round trip). Structural, so it
  scales: pure pulls only seat FOUNDATION material; an unstackable
  residue's card is never in a foundation; a residue's seat is
  frozen along every pure-pull play. VERDICT: (A)'s reachability
  target is the TWO-LETTER grade; the one-letter survives only as
  the per-member free lemma (the reversed undo-ladder,
  `stackRun_returnW`). `canon_slide` fixes the anchor-EQUALITY half
  (equal slide-seated canons for the exhibit pair), NOT the
  reachability half — recorded honestly, no credit bought.
* **B — pristine UNREACHABLE; the target REPLACED per the pinning
  rule.** Non-pristine pure orbits (drawStep 1 and 3; pools 7, 9,
  10, 11 — the partial-final corners r = 1 and 2 included; observed
  orbit sizes 10, 3/3, 4/4, pass-base start 3), NONE contains a
  pristine (empty-waste) member; pristine orbits are singletons
  (their draws out commit, `draw_irreversible_pristine`). The
  predicted first falsifier (the (A)-card tension, FARM_MEMORY
  b4f32e4: "a full-stock state drains and can never re-stock fully")
  is CONFIRMED as the mechanism. Structural reason (probe-backed,
  a landing-2 lemma): no draw ever LANDS a waste-empty zone — plain
  draws prepend a nonempty chunk, pass-base draws deal at least one
  card after the recycle. THE STRONGEST PROBE-CERTIFIED REACHABLE
  NORMAL FORM: the UNIQUE PASS BASE `([], drawPool st, drawStep)` —
  reachable from every pure non-pristine zone by in-phase draws
  (every drain leg fires phase-aligned, so every leg is
  `draw_reversible_inphaseW`-licensed, the short-stock boundary
  deal included), and unique per orbit: every reachable zone has
  `S = (P.take m).reverse`, `W = P.drop m` (the stock-head count m
  pins the split), and the pass base is `m = 0`. **`canon_draw`'s
  target IS the pass base** (not pristine); RESIDUAL RECORDED:
  pristine and offset zones stay un-normalized BY DESIGN (a
  pristine zone's draws commit — normalizing it would exit the
  class; offsets are genuine class data per the commitment
  boundary). The canonDraw loop is the drain: draw while
  `stock ≠ [] ∧ waste ≠ [] ∧ |waste| ≡ 0 (mod drawStep)`; identity
  otherwise; terminates ≤ |pool| legs; idempotent (the pass base is
  the loop's refusal point).
* **C — purity IS saturation-invariant (LIVE).** `canon` (which
  computes) preserves stock/waste/drawStep verbatim and the
  `inPhase` line, on pure, offset AND pristine zones (gates at all
  three); the three saturated forms of one board differ only in
  the zone (boards literally equal); the license is zone-blind
  (`pick` survives a draw). The R1 commutation is probe-certified
  LITERAL at all three zone shapes: `canon (drawn u) = drawn (canon
  u)` — the draw is a field-local function (reads/writes the zone
  only) and the saturator reads/writes found/piles only. These are
  the landing-2 theorem rows, now licensed.
* **D — offsets are NOT normalizable (LIVE, the negative
  control).** No reversible draw edge leaves any offset (or
  pristine) presentation — the orbit closures are singletons.
  `canon_draw` is the identity there, exactly as the
  commitment-boundary doctrine demands.
* **E — the canon_slide menu.** E1: seating CONFLUENCE at the cube
  (every corner reaches the canonical seating — ♠Q@p1, ♣J@p3 — by
  ≤ 2 slides, either order). E2: the occupied-twin-host negative
  (an unfit top on the twin host bars the slide). E3: the
  revealing-slide negative (the slide legally fires but
  `hiddenTotal` strictly drops — a commitment, barred from the
  seating license by the measure rows). E4: the interaction is LIVE:
  a legal noreveal slide CAN expose a licensed raise (`canRaiseB`
  flips false → true at the crafted WF Final state) — the slide
  pass and `Final` are NOT disjoint, so any `canon_slide` must be
  an alternating fixpoint (slide; re-saturate; slide; …) whose
  termination/confluence is NOT free (the E4 state is the
  counterexample to single-pass disjointness; "verify legally, not
  intuitively" paid). E5: the same-pair transposition DEADLOCK: two
  residues over ONE twin-host pair (♠Q/♣Q over ♥K/♦K) — the
  residue-queens have NO legal slide at either pairing (empty
  anchors take kings; the only card-tops are the other queen), no
  pull fires (foundations empty), the bounded slide closure (depth
  4, 42 states) excludes the transposition while every state in it
  keeps the queen-on-king co-location: the host kings may relocate
  (a king's run carries its rider), but the residue-to-host
  PAIRING is class data — a seating rule must read it from the
  state, not assign it. Honest residual: full
  journey-disconnectedness of the transposition is unprobed
  (bounded negative evidence, origmerge-style).

**THE PINNED STATEMENT MENU (landing-2 targets, all
probe-licensed):**

- (A) the two-letter decompression at the zone-fixed grade —
  statement family over the banked machinery (`StackRun`/`Final`,
  `canon_unique`, `raise_undo_under_step`/`raise_undo_bare_step`,
  `zone_keep_others`, `oneMoveRevEqW`): the per-state reverse free
  (the reversed undo-ladder IS `stackRun_returnW`, restated); the
  orbit-witness draw-stripping (draws bubble to the journey front
  by the C-commutation, leaving a zone-preserving board-only
  witness play — the padding-generation order-freedom lemma,
  R1's corollary); and the ONE named residue
  **`finalWiggle_reach`** (Final-to-Final within one class by
  pulls+slides) — the A1/A2 exhibits now certify the positive
  family; the general theorem stays prove-or-pin (landing-2 lands
  the proven sub-family and pins the rest, `sorryAx` printed in
  the audit).
- (B) `canonDraw` in a NEW file (`Orig/Decompress.lean` — nothing
  in the do-not-touch set moves): the computable drain; the drain
  journey's `ShufflePlayW` (legs cite `draw_reversible_inphaseW`;
  the pass-base arrival shape is new); `canonDraw` identity rows
  (offset/pristine/frozen); `canonDraw_in_class`;
  `canonDraw`-preserves-pool; the canonDraw∘canon consequences, in
  the R1-refined shapes: (i) field-disjointness of the two
  normalizers (confluence-for-free — no new confluence problem);
  (ii) the draw-side laws isolated from the stacking side
  (`canonDraw ∘ stepDraw / stepDraw ∘ canonDraw` phase-machinery
  only); (iii) the literal draws-kill elimination: pure-zone
  class-mates with literally-equal canons normalize to literally
  equal `canon'` (the draw-rotation splits die at the pass
  base — the residue exhibit remains the only literal kill,
  BLOCKED-ON-CANLAW for its canon_slide half); (iv) the
  `same_macro_iff` swComp accounting shrinks to the
  consumed-zone cases (offset/pristine splits are the only
  surviving zone residue).
- BLOCKED-ON-CANLAW (canlaw mid-flight in Canonical.lean): any
  `canon`-composite change (the canon_slide fixpoint, the
  canon'-fiber theorems that need editing `canon`'s own lemmas'
  home, the same_macro_iff re-grading). This card lands its
  sides in `Orig/Decompress.lean` + probes only; the plan above is
  the transfer note.

**THE FOLLOW-ON EXCHANGE-CANON CARD — the backlog inherited from
this session's dialogue (recorded here, none of it pulled into the
current scope; territory `Orig/TwinExchangeQuotient.lean`, no active
owner):**

- The PHYSICAL SETOID (closure of RevEqW shuffle legs + licensed
  bare ExchStep legs, no decree identifications) and the PINCH
  theorem as the destination: `PhysEq u v → ExchChain (canon' u)
  (canon' v)`, engines `canon'_shuffleEq` (this card's
  shuffle-leg half — the literal canon-invariance for RevEqW
  mates in the two-letter world) + `exch_canon_comm` (the
  follow-on's forgery: licensing preserved at the canon images and
  the swap commuting with saturation, at the expected honest
  re-saturated grade; residue-exhibit cells the falsifier
  battery). With the USER'S CORRECTION (fold verbatim): the
  quotient ⟪·⟫ is the EXCHANGES-ONLY closure (the banked
  `exchSetoid`, bare twin-cargo chains) — `canon_in_physOrbit :
  ⟪canon u⟫ = ⟪u⟫` must NOT appear (the saturation run is not a
  chain of exchanges; that folding is the decompression theorem
  instead). The corrected spine: `canonQ_of_physOrbit : (huwf :
  u.WF) (hvwf : v.WF) (h : PhysEq u v) → ⟪canon' u⟫ = ⟪canon'
  v⟫` by leg-induction (refl `rfl`; shuffle case cites
  `canon'_shuffleEq`, zero-length chain, degrading honestly if the
  seating-pass probes fail; exchange case cites `exch_canon_comm`;
  trans composes). Role split: canon_in_class's old content now
  lives as TWO theorems — `decompress_reach` (the saturation
  direction, within-point) and `canonQ_of_physOrbit` (the
  between-points stability); conjugation has NO disjunct anywhere.
- TORSOR FREENESS — `exch_free`: at a licensed base point,
  distinct twin-pair swap-subsets produce distinct states (proof
  shape: twin pairs partition the deck, a swap touches exactly its
  own two members at two distinct seats, so the
  symmetric-difference witness card sits differently); one named
  prerequisite row (per-pair locality of the exchange composite,
  derivable from the landed TwinExchange.lean iff bundles); one
  genuine probe-residual (which subsets are reachable at all —
  licensing drifts along a chain; probe-battery, not a lemma).
  Dividend: the canon fiber becomes a bijective 2^k torsor,
  sameOrbit classes split into physical classes exactly as finely
  as the licensed swap bits, and §3.1's worried-♥/worried-♦ fork
  becomes literally one free exchange bit (two RevEqW-distinct
  states joined by a licensed exchange — the grading-note triple
  read physically).
- THE COARSENING ROW: `exch_le_sameOrbit : ExchChain a b →
  sameOrbitSetoid.r a b` (chain induction; the one wrap to forge:
  `exchange_leg_sameOrbit`, riding the banked
  `TwinExchOK_exchangeTwin` + `ExchStep_symm` + the bare iff
  bundles — wrapper-grade); the forgetful map
  `exchOrbit_to_sameOrbit := Quotient.lift (fun u => ⟦u⟧ …)`
  (surjective, NOT injective). Dividends: (1) every landed
  sameOrbit-grade theorem (`canonQ_of_orbit`, `drawNextQ`, the
  `tipEdge_*_target` successor rows, the §3.1 banked machinery)
  pulls back along the forgetful map for free — physical
  class-mates inherit the count program at the coarser grade;
  (2) the macro class decomposition: one sameOrbit class =
  (canon'-point + pull ladder, the decompression fiber) ×
  (licensed swap bits, priced by `exch_free`) ⊎ (the decree-only
  conjugation shadow: twin pairs with NO physical witness —
  hidden/waste-resident members). That decomposition is the
  fourth disjunct's purchase, itemized.
- THE DESIGN DECISION (sixth refinement, user-stated): the
  physical macro-state assignment is ONE map, `u ↦ ⟪canon' u⟫`;
  `PhysEq u v := ⟪canon' u⟫ = ⟪canon' v⟫` IS the kernel; the
  inductive closure is the WORKING definition only (kept for its
  induction principle); the two leg rows give
  generator-closure ⊆ kernel; `decompress_reach` gives the
  pull-fiber content; the CLOSING COROLLARY to spec:
  generator-closure = kernel, which retires the inductive
  relation as a lemma. The two reasons a member-level class
  notion exists at all: (1) §3.1's premise is member-level (one
  fixed m across the class's m-legal tips) and every landed
  sameOrbit-grade row quantifies over member-level class-mates;
  (2) the decomposition theorem above.
- INTERPRETIVE DOCTRINE (user meta-note, binds the whole project):
  the user's native mental model has ALWAYS been the physical
  register — the bare twin-cargo exchange quotient where
  conjugation is only what licensed exchanges earn and saturation
  freedom is theoremed, never quotient-folded. When a
  user-proposed statement looks WRONG at the current landed
  (virtual sameOrbit) grade, FIRST restate it in the physical
  register before judging it — tonight's sequence (canon-equality,
  pull-only reachability, draw-commutation, the exchange-bit
  reading of the ≤2 fork) were all "false" wrapped, all true or
  conditionally-true physical. Future refinements get recorded
  physical-first, virtual-grade translation second.

**LANDING 2 (branch orig-canon-decompress, commit fc0569f).**
`Orig/Decompress.lean` is in the battery (29th job) and green: the
(A) per-state reverse landed — `lift_undo_pullW` (the banked
`lift_undoW` engine re-graded with its leg-shape data; the under-arm
re-derived through the PUBLIC `runOK_snoc_sit`/`pileOfTop_eq_some_iff`
rows rather than Canonical.lean's private `lift_under_facts`),
`stackRun_return_pulls` (from any licensed run's end the return
shuffle is PULL-DOWNS ONLY), and `decompress_pulls` (from the
canonical form, the witness shuffle back to u is pure pulls); the
draw-letter formal ground landed (`drawLanding_waste_ne` — no draw
ever lands an empty waste at a positive draw step, pristine
unreachability at theorem grade; the `ZoneShape` presentation
algebra with `zoneShape_self` and the three leg rows; the draw's
board/pool/drawStep keeps); the saturator's zone and board rows
landed (`satStep_zone_keep`/`canon_zone_keep` — the canonicalizer
never touches the zone; the determination chain
`firstWhereCong → canRaiseB_congr → pick_congr → satStep_board_det
→ canonBoard_det` — the canonical form's board depends only on the
board input); the commutation minis (`stepDraw_eq_none_iff`,
`stepDraw_zone_det`) landed for the follow-up.  `canon_draw_comm`
(the padding-generation order-freedom lemma) is DEFERRED with its
working route recorded in the module (no sorry, no phantom claim):
the per-budget induction route — the step case is the ONE-STEP
satStep/stepDrawn square, all of whose halves are already landed
here.  `finalWiggle_reach` — the card's ONE named residue — is
pinned at the THREE-letter alphabet the corrections fixed (PULLS +
SLIDES + PURE DRAWS; see the probe amendment below), carrying its
live dependency notes (canlaw's twin-cargo pick-fork probe; the V3
contention probe; the exchlaw twin-kings cell).  Audits:
`[propext, Quot.sound]` or fewer on every landed head; the stub
reads `[propext, sorryAx]` — the only sorry on a landed head, printed
in the file's audit block.

**THE CONE ALPHABET CORRECTION (exchlaw's refuted pinch, adopted).**
The sigma-absorption of the SLIDE letter is REFUTED at the
twin-kings cell: the saturated mates split the found channel
(13/12 vs 12/13), foundTotal equal so no pure-pull play joins them,
the mates reach their raw twins by one pull each, the raw pair is
joined only by the SLIDE, and the naive one-way composite cannot
even run.  Probe (a) is AMENDED and committed: Family W in
CanonDecompressProbe mirrors the exchlaw cell with credit
(orig-exch-canlaw:probes/ExchCanLawProbe.lean).  Hence: the main
theorem's cone alphabet is PULLS + SLIDES + PURE DRAWS — three
letters, all reversible, class-honest; `mem_macro_iff`/`cone_image`
restate accordingly (the up-to-swap sigma-clause stays for
identity-content ambiguity only); slides-as-padding are a
requirement again; the canon_slide seating pass remains probe-gated
and probably dead; and the class's anchor SET is allowed to straddle
the fork — the multi-anchor cans-predicate design anticipated
exactly this.

**THE CORRECTIONS FOLDED THROUGH THE SESSION (recorded against the
section 9 menu above).**  canon_draw is DROPPED from the card's
scope (the tenth refinement): the draw stays a separate padding
letter; offset zones are commit records either way, the pure
rotations are exactly what the padding's draw letter absorbs, and
with the slide restored and the draw kept as padding the ENTIRE
reverse program touches no canonicalizer — the anchor stays "any
saturated member" over the landed saturating canon, nothing waits on
canlaw even for coordination.  canonDraw goes into the ledger as the
NAMED OPTIONAL POLISH ROW post-merge (its value: kills the
draws-trivially site of the literal canon-iff, folds swComp into
the normal form, tightens the cone to pure pulls), gated on the
pristine-reachability probes, which this session's B-family battery
already answered (pristine UNREACHABLE; the unique reachable normal
form is the PASS BASE) — so the polish row, if ever taken, drains
to the pass base, not to pristine.  Design principle recorded: the
tableau earns canonicalization because saturation is confluent and
hard; the draw zone needs at most a rotation, whose normal form is
trivial padding material, not anchor material.  Probe (b) resolved:
pure-rotation orbits ride RevEqW DIRECTLY (the swCompat line
resolves cheaply at the trivial reading — swComp collapses to the
consumption/offset cases only); the B-probe closure numbers are the
certificate.

**THE V3 CANONICALIZER EXTENSION CARD — the backlog family (spawn
waits on canlaw's fork verdicts; nothing lands meanwhile).**
The user's V3 skeleton, ledgered verbatim: five definitions
(TwinContended — both twins licensed-raise with each stack
foreclosing the other, the exact Foreclose read PINNED by canlaw's
probe instance; Unblocker — a foundToTab y b licensed that
re-licenses the raise of x; HardContended — contention with no
unblocker, the only surviving stop case; FinalV3 — no licensed
raise except across hard contentions; the runner as TWO macro-legs:
"raise" refusing to fire at contentions so the fork lane cannot
leak, and "scaffoldCycle" — the Unblocker pull welded with its
immediately-enabled stack plus the cleanup re-raise of y, ONE
constructor); design wins (serialization kills scaffold-scaffold
interference; the boundary measure Phi = foundation length strictly
increases at EVERY leg boundary — raise legs +1, scaffoldCycles net
+2, dips inside the macro-leg only — clean well-founded termination,
no amortization; all guards decidable so canonV3 is COMPUTABLE and
the probe discipline applies verbatim); five target theorems
(canonV3_in_class via both leg kinds reversible; canonV3_unique
PROBE-GATED — scaffold-choice convergence plus conjugate-route
agreement, pin-as-named-stub if refused; canonV3_final_shape — full
saturation modulo hard contentions only; canonV3_conj — the twin-
blind rule, conjugation-equivariance; canonV3_wf); doctrine (the leg
alphabet gains exactly one reversible pull kind; accommodation
ladders stay section 3.1 commit-side; canlaw's E-law re-derivation
debt RECORDED, not absorbed).  File structure decided: NEW FILE
Orig/CanV3.lean (import Orig.Canonical — the undo family, monotone
stackability, canon_unique; no cycles; the bridge rows there too),
probe battery probes/CanonV3Probe.lean; Canonical.lean is canlaw's
dense hot file and stays untouched.  END-STATE decided: the final
architecture is SINGLE-CHAPTER — the old V2 machinery in
Orig/Canonical.lean is REMOVED once V3 supersedes, not a permanent
parallel chapter; ordering gates: Phase 1 V3 lands alongside (five
theorems green); Phase 2 the BRIDGE family proves transport
lossless — the key row canonV3 = canon on contention-free
saturation runs, satStep REUSED as V3's raise-leg engine (REUSE not
removal; canlaw's landing-2 locality kit survives), consumers
re-targeted one-site-at-a-time with battery green at every commit;
Phase 3 the removal sweep deletes the V2 core — removal WAITS on
canlaw's merge (the in-flight V2-stated work is the re-derivation
source) and on the bridge rows.  NEW PROBE ITEM for the V3 battery:
decide whether the residue_reloc_exhibit's twin-host relocation is
CONTENTION-DRIVEN — if yes, V3's scaffold cycles may literalize
canon equality exactly where V2's non-uniqueness lived, and the
exhibit's reason for existing vanishes with the old chapter.

**THE PRESENTATION TARGETS (statement-shape decisions for the main
landing).**  Membership-characterization form:
`MacroState.cans s := {w | w in s and Final w}` as a PREDICATE,
deliberately not a choice function (a class may hold several
genuinely different Final states — the exhibit family plus now the
twin-kings found-split mates; picking would smuggle the anchor
back); `pullDrawCone w` — the pulls+slides+pure-draws reachable
set, the three letters restored per the correction above; MAIN
`mem_macro_iff : u in s iff EX sigma : TwinSwap, sigma * u in
pullDrawCone w for ANY w in cans s` (the LEFT arrow the cheap
soundness leg — cone legs non-committal, swaps ride the class's
conjugation fold, canon_in_class-style cites; the RIGHT arrow the
reverse theorem proper) plus the one-line class-image corollary
`cone_image : the class-image of pullDrawCone w IS s`; anchor-free
supersession: for ANY saturated member w of the class every member
u is reached FROM w (fixed-anchor demoted to lemma; the
anchor-mobility rows: exchange bits absorbed by the same full-swap
relaxation the conclusion carries, the parked-residue wiggle
absorbed iff probe (a) — now REFUTED at BOTH cells, hence the slide
letter back in the cone, phase rotations absorbed by the draw
letter).  Consumer split: the class-image form serves every
class-graded consumer (the count, the successor program's
pull-backs — a criterion, not just coverage); the sigma-explicit
iff side is the strength door the physical layer consumes
(the pinch, torsor freeness, licensed-only re-derivation — the
follow-on exchange-canon card whose backlog rows sit at the top of
this section; the anchor machinery survives V3 untouched, and if
canonV3_unique lands literally the anchor story TIGHTENS).

#### §M-FLOOR-1 — the MacroInternal FLOOR wave lands (branch `orig-macro-floor`, session of 2026-10-11; the Tier-0/1 rows of the 2026-10-11 skeleton, rebased onto macro-game `b8a1584` per the determinism session's base-fix recipe)

THE LANDINGS (all sorry-free, all `[propext, Quot.sound]` or `[propext]`, battery
`lake build Orig` green + `lake env lean Orig/MacroInternal.lean` zero errors at
every commit; commit chain on the branch): `stackable_now_rungexact` (CALIBRATED:
one-directional — the iff's reverse face is refutable by a buried/stocked at-rung
card; the 0-based `toIdx` encoding needed NO offset adjust — `nextUp` is literally
`decide (rank.toIdx = foundHeight)`), `canon_rung_mono` (satStep holds-or-raises,
composed along canonAux), the new `cone_step_heights` (the floor card's own row
name; the per-move rung semantics: slides/draws flat, a pull pops exactly one
founded top), `cone_step_fiber`, `dance_step_grading` (the trichotomy, restored
to the constructor case split), `flat_heights`, `cone_inClass` + `dance_inClass`
(the class-stays rows), `exch_is_cargo` (THE BRIDGE ROW, via the de-privatized
one-move realizers — see below; CALIBRATED: the degenerate both-bare step is
`ExchStep a a` and no successful tabToTab is a fixed point, so the face carries
`... ∨ a = b`, exactly the "degenerate bit priced at zero" the skeleton's own
docstring anticipated), `surely_imp_sat` (new row; CALIBRATED with the WF-member
premise — a bare quotient can lack Final members), `benign_sat_iff_surely`
(same premise; the fork-free direction is decidable-branch pure logic), and
`canusOf_nonempty` (the canon u + ConePath.refl + Or.inl witness the card names).

THE ENGINE BANKS (private in MacroInternal, available for promotion at merge):
`shuffleW_of_round` / `class_leg` — the LOOP-CLOSURE BRIDGE, and it is the row
the other sessions should read first: a single `reversibleAtW st m` leg plus its
step lands `sameOrbitSetoid.r st s₁` with NO physics (the σ side is the move
itself; the τ side splices the return play per step by looping the remainder:
suffix ++ [m] ++ front).  This dissolves what looked like a draw-leg obstacle
(the Phase in-phase draw witnesses are multi-draw replays).  Plus the per-move
rung locality four (`step_tabToTab_rungs` / `_draw_` / `_tabToFound_` /
`_foundToTab_`), and the fork half-banks: `piled_rung`, `canRaiseS_rung_pin`
(the BARE twin's exact pin along theCascade), `forkPoint_cargo_strand` (the
cargo's strict strand, reductio through the reversible licensed raise + class_leg).

CARRIER EDIT (merge note): TwinExchange's `step_realize_fwd` / `step_realize_bwd`
are now PUBLIC (commit 69fbaa8, no statement changes) — exactly the deprivatization
this chapter's TwinExchangeQuotient ledgered its RevEqW-refinement as blocked on;
`exch_is_cargo` consumes the fwd leg.  MacroInternal also grew `import
Orig.Dominance` (the leaf cites the one public home `mem_upCards_take`).

THE BLOCKED ROWS (four sorries, each with its BLOCKED note in-file): 
`founded_implies_atRung` (the pops-backward walk needs the LANDING-EXISTENCE
leg — neck/envelope grade, the decompression card's `mem_macro_iff` family);
`forkPoint_trial`, `forkPoint_pins`, `forkPoint_exclusive` — all three gated on
the corrected forkEvidence GAP FORM (§11-L4.2's `CanRaiseS x.twin ∧
¬CanRaiseVanilla x.twin ∧ coveredIn x.twin` legs) that the skeleton's
`forkPointC` under-carries: the trial needs x topping a pile AT the point and the
covered twin's rung AT the pair rank; the pins' covered half and the sandwich's
cross-cases ride the same missing leg.  COORDINATION (the no-duplication note):
canon-v3's ledger already records `forkPoint_trial`'s sorry as its own next
closure — when that session lands the gap form, the three rows close on it
trivially (the bare pins and cargo strands are already banked here).

AUDIT FLAG (recorded in-file): `canusOf_nonempty` reports
`[propext, sorryAx, Quot.sound]` — the sorryAx enters at the STATEMENT level via
the skeleton's designated `conjl := sorry` carrier in `canusOf`'s second
disjunct; the proof rides `Or.inl` and never forces it.  The flag clears when
the conjl carrier lands (canon-v3's ledgered def work).



## 11. The V3-canonicalizer gating census (2026-10-11, branch `orig-canon-v3`, rebased onto macro-game `5ebef39`; the scaffold-pull fork-fix card, landing 1 AND the card's whole content — the census returns EMPTY, the doctrine closes)

Section numbering note: §9 lives on `orig-canon-decompress` (commit
`8a0e121`), §10 on `orig-exch-canlaw` (commit `834ebdc`); this section
reserves §11 on this branch so the three append-only ledgers merge in
any order.

THE CARD AND ITS TWO BRANCHES.  The V3 canonicalizer was designed
against the exchlaw B2 worried-king fork exhibit: a five-definition
skeleton (quoted verbatim below as DORMANT DESIGN) whose
two-macro-leg runner refuses its raise legs at contentions and
instead performs a `scaffoldCycle` — an unblocking pull welded with
its immediately-enabled stack and the cleanup re-raise — with the
boundary measure Φ = foundation length strictly increasing at every
macro-leg boundary.  The card gated everything on one census
question, decided FIRST, before any proof effort (probe first,
prove-or-pin): is `TwinContended` inhabited at WF?

```
TwinContended st c := both twins licensed-raise at st
                   ∧ stacking either forecloses the other
```

**THE VERDICT: `TwinContended` is EMPTY at WF — under every pinned
FORECLOSE reading.  Branch (b) fires: the scaffold-pull rule
retires as unneeded; the census battery + this closure are the
card's sole content.**

* **The pinned FORECLOSE read (marked, per the card).**  The
  reading that could carry content at WF is LICENSE-DEATH: the
  landed state `s'` of either twin's licensed raise forecloses the
  other's license (`¬ CanRaise s' c.twin` at the landed `s'`).  The
  alternates were probed at the cells and struck:

  - RAW-stackability death — struck: the licenses read
    zone-disjoint components (each twin's OWN suit rung via
    `nextUp`, each twin's OWN pile seat via `pileOfTop` +
    `chop (piles a).faceUp`/`hidden`), and a licensed lift writes
    exactly its own card's two zones (`setFound c.suit`, pile `a`,
    `Orig/Play.lean`'s `tabToFound` branch) — the twin's zones
    survive verbatim;
  - FINAL-divergence — struck by V2's banked confluence
    (`canon_unique`, all diamonds local): both greedy orders of a
    licensed twin pair land at `canon st`, decided literally at
    every positive cell;
  - UNDO-death — struck: after the double saturation each twin
    pulls back (`foundToTab`) onto its exposed bases and every
    pulled excursion re-saturates home — the round trip is the
    landed undo family's content (the V2 five-cell, decided).

* **The systematic half is THEOREM-GRADE and rides the bank.**  The
  house monotone-stackability row `canRaise_lifted`
  (`Orig/Canonical.lean:1162` — "after a licensed lift of another
  card, `c`'s license survives", `[propext, Quot.sound]`) was probed
  for its axioms (`#print axioms` — clean) and instantiated at the
  twin seats in the battery file:

  - `v3Card_twin_ne` — twinning is fixed-point-free (a pair is
    always two seats), `[propext]`;
  - `v3twin_raise_independent` — at WF, both twins licensed and
    `c`'s lift fires ⇒ `CanRaise s' c.twin` at the landed `s'`
    (`canRaise_lifted` at the twin seats), `[propext, Quot.sound]`;
  - `v3TwinContended_empty_at_wf` — **THE CENSUS VERDICT:
    `TwinContended st c → False` at `WF`**, `[propext,
    Quot.sound]`, zero sorry, zero native_decide;
  - `v3TwinContendedB_true_iff` — the decide-graded census Bool
    (`v3TwinContendedB`) speaks the Prop (`v3ForecloseB` reads the
    landed state through the fire; both licensed lifts fire by the
    banked `raise_eq_some_of_canRaise`), `[propext]`.

  The WF fence is load-bearing and honest: at wild states the
  duplicated-card world breaks locality (the banked
  `wild_confluence_fails` witness of `Orig/Canonical.lean`) — but
  wild states are unstateable in the physical register (`WF` is the
  realizability doctrine), so the census closes where the game
  lives.

* **The census battery** (`lean-model/probes/CanonV3Probe.lean`,
  external, lake-env-runnable, gates throw on failure, README row
  landed; the full-deck cells are census-clean through the stock
  mover — the crafted numbers pinned):

  - **V1 both-bare twin kings** (hearts/diamonds climbed A..Q, ♥K
    bare p1, ♦K bare p5): both licensed, both fire, each keeps the
    other licensed (the monotone permission census over the whole
    universe), both orders land at ONE state, `canon` consumes BOTH
    twins (found 13/13, seats emptied) — the exchlaw freeness
    suggestion ("the both-bare bit is IDENTITY") verified from the
    canonicalizer side: the both-bare pair is the independence
    fixture, no foreclosure anywhere.  Census numbers: licensed = 2,
    twin-candidates = 2, contented = 0.
  - **V2 both under-seat twin queens on conjugate bases** (♥Q on ♣K
    p1, ♦Q on ♠K p5, hearts/diamonds climbed A..J): independence and
    order-convergence hold at the seated pose; after the double
    saturation the undo round trip fires — four licensed pulls (each
    queen onto either bare black king) and ALL re-saturate home to
    `canon v3Under`.  Twin-blindness decided (`canon (twinMap st) =
    twinMap (canon st)`, the pile-swapped cell).  Licensed = 2,
    contented = 0.
  - **V3 the mixed-seat census point**: a licensed twin pair cannot
    sit mixed seat TYPES — a king sits under nothing (no rank
    above king), so twin kings license only both-bare and twin
    non-kings only both-under; the cell carries the cross-type
    coexistence (bare ♥K licensed, under-seat ♦Q licensed, the twin
    mates stock-resident and never licensed).  Licensed = 2,
    contented = 0.  Canon leaves the stock twin-residents verbatim
    (the canonicalizer never writes the stock zone).
  - **V4 the ENABLEMENT mediation** (♥J/♦J under-seat at rungs 10,
    plus ♥Q under-seat on ♣K one rung short): raising ♥J LIGHTS
    ♥Q's license (the rung arrives) and kills nothing — licensed
    2 → 2 through the lift ({♥Q, ♦J}), contented = 0 at every
    state of the chain, canon walks the enabled ladder (hearts
    A..Q, diamonds A..J), the bare ♣K never licenses (its suit
    never climbs).  THE MEDIATION RESULT: the only coupling a
    licensed lift induces anywhere is MORE license (monotone
    enablement), never foreclosure.
  - **V5 the B2 twin-kings fork family, consumed from the exchlaw
    battery's committed verdicts** (common material; the slide
    realization, the wing split, the A2 highway re-decided in the
    census language): at EVERY single state of the family at most
    ONE twin is licensed ({♥K} vs {♦K}, licensed = 1 both faces) —
    the TwinContended FIRST CONJUNCT dies here: **the observed fork
    is CROSS-MATE (across the twin exchange's noreveal slide
    realization), never intra-state.**  The wings split founds 13/12
    vs 12/13 (`canon v3Fork ≠ canon v3ForkX`, decided), the wings
    are Final (licensed = 0), and the wing pull-homes fire
    step-exact (`foundToTab ♥K (inl p1)` recovers `v3Fork` from its
    own canon wing).  THE SCAFFOLD QUESTIONS, answered at the real
    fork family: the unblocking pull EXISTS at every wing; the
    scaffold menu is sizeable (six licensed pulls per wing — the
    founded king onto the six empty anchors; kings sit under
    nothing, so no seat target exists) and ALL converge (every
    pulled excursion re-saturates to its own wing canon) — scaffold
    CHOICES CONVERGE; CONJUGATE ROUTES AGREE (canon commutes with
    twinMap on every face — the banked `canon_twinMap` decided);
    HARD-CONTENTION (a fork wing with no unblocker anywhere) WAS
    NOT FOUND in the family — every wing's founded twin pulls
    home.  No card in the universe registers contention at any
    face.
  - **V6 the negative controls**: the cargo corner (both twin kings
    carrying twin cargos ♣Q/♠Q — the §1.8 crossed pair, license 0;
    covered tops license nothing and black suits never climb here),
    the waste-resident mate (♦K in the waste: never licensed, its
    bare twin licensed — unlicensable shapes never register), the
    both-bare NON-KING seat bar (two rung-ready bare queens,
    license 0 — §3.0's OUT-list decided), and the hidden-under
    reveal bar (a rung-ready bare king pinned over a hidden ♠2:
    refused, though its free twin licenses).  Contented = 0
    everywhere.

* **The consumed sibling verdicts** (per the coordination note):
  the exchlaw battery's B-numbers and the twin-kings cell are
  consumed as committed (`834ebdc` on `orig-exch-canlaw`); the
  canlaw session's queued fork-instance tasks were NOT re-derived
  (no instance-level verdict has appeared in any committed
  `FUTURES-ORIG.md` yet — none to consume at this write; when they
  land they slot under this section as the instance-level view of
  the same census, and this section's theorem-grade half already
  answers their inhabited-or-empty question).

**THE CLOSURE DOCTRINE (the card's branch (b), verbatim in
spirit).**  Forks are EXCHANGE-STEERED, COMMIT-SIDE, PRICED BY THE
A2 WITNESS AT TIP LEVEL: the canonicalizer meets the worried-twin
fork only between EXCHANGE MATES (each single state licenses at
most one twin), the exchange seat permutes the residue onto the
covered member's host, and saturation then consumes whichever twin
the seating left bare.  The fork is priced at tip level by the A2
witness — pull the founded twin home (`foundToTab` onto its
vacated seat), exchange (the licensed noreveal slide), saturate —
every leg reversible, the sameOrbit world; and the canonQ spine
(`canonQ_of_orbit`, banked) joins the wings' canons at the
`⟦⟫`-grade through exactly that fold (the sameOrbit setoid's
twin-conjugation disjunct — §3.1's grading-note fold, applied to
the canon level).  V2 canon is twin-blind by theorem
(`canon_twinMap`), confluent by theorem (`canon_unique`), and
in-class by theorem (`canon_in_class`); the V3 skeleton's
`canonV3 = canon` on contention-free runs degenerates to the
identity AT WF outright, since contention never fires — so the
skeleton's other four theorems (in_class via the undo family,
final_shape, conj twin-blindness, wf) are all already banked in
V2's name.  Nothing about the canonicalizer needs fixing; the
scaffold-pull rule RETIRES.

**The DORMANT SKELETON, ledgered verbatim** (not landed, no
library file created — if a future card ever inhabits a genuine
intra-state contention family out of WF's reach, this is the
designed shape): five definitions — `TwinContended st c := both
twins licensed-raise at st ∧ stacking either forecloses the other
(the FORECLOSE read pinned by census: LICENSE-DEATH)`; `Unblocker`
(the pull that unlocks a contented pair); `HardContended` (a
contention with no unblocker anywhere); `FinalV3` (the saturated
shape the two-macro-leg runner reaches); and the two-macro-leg
runner — raise legs refuse to fire at contentions;
`scaffoldCycle` welds an unblocking pull with its
immediately-enabled stack and the cleanup re-raise; the boundary
measure Φ = foundation length strictly increasing at every
macro-leg boundary (ordinary legs +1; scaffold legs net +1: the
pull −1, the enabled stack +1, the cleanup re-raise +1).  The
census found no state for any leg of it to act on.

**COORDINATION NOTES:** (i) the twin-kings cell is common material —
this census consumed the exchlaw battery's committed verdicts and
added the canonicalizer-side reading (the intra-state vs
cross-mate distinction is the census's central datum); (ii) the
decompression card's A2-anatomy highway (pull, exchange, pull) is
the price tag this closure cites — the two cards are consistent;
(iii) the canlaw session owns `Orig/Canonical.lean` mid-flight —
this card touched no library file, consumed `canRaise_lifted` /
`raise_eq_some_of_canRaise` / `canon_twinMap` / `canon_unique` /
`canon_in_class` / `canonQ_of_orbit` by read-only citation only.

ENGINEERING NOTES FOR FARM_MEMORY (banked in the close-out): the
sibling-commit timing hazard (a sibling worktree's uncommitted diff
VANISHED mid-read — they committed mid-session; snapshot shared
material when you cite it), the stock-exclusion craft bug family
(seated BLACK cards must join the exclude list too — the WF gate's
cardCount census catches what the hand-write misses, exactly as
the exchlaw B-cell lesson predicted for FOUNDATION cards), and
the cite-before-craft discipline (the whole answer was already
banked as `canRaise_lifted` before any new mechanism was built —
grep the bank before designing).

### §11-L3 (landing 3, same branch — `pair_neighborhood_cases`: the lattice header, the row table, the closing containment corollary)

The verdict restructuring (the user's two-case shape), landed as a
battery section of `probes/CanonV3Probe.lean` (all gates green;
`lake env lean` runs the table; every row's witness is a census
cell):

* **THE LATTICE HEADER.**  Position-classification `pnPosTrich`
  [propext, Quot.sound]: at WF every face-up card is EXACTLY ONE of
  BARE top / UNDER top / COVERED (face-up under cargo, hence no
  pile top) — the twin pair reads the nine-cell product.
  `pnCoveredNotLicensed` [propext]: covered ⇒ unlicensed, so the
  covered slice carries AT MOST ONE licensed twin per state
  (`pnCoveredPairAtMostOne`) — the fork is structurally cross-mate.
  `pnLicPairSlice` [propext, Quot.sound]: the licensed slice
  collapses to TWO cells — BOTH-BARE (kings: `pnLicKingBare`, no
  rank 13+1 exists) or BOTH-UNDER (non-kings, twins share rank);
  the mixed licensed cells are VACUOUS.  Independence across the
  whole licensed slice rides the banked `canRaise_lifted`.
* **RANK FENCE POSTS** (deck-arithmetic-free): a covered king's
  cover is EXACTLY a queen — `pnKingSlider` + `pnCoveredKingQueen`
  [propext, Quot.sound] (the exchlaw falsifier's ♣Q is the whole
  class); ACES ARE NEVER COVERED — `pnAceNoSlider` +
  `pnCoveredAceAbsurd` [propext, Quot.sound]: the fork disease has
  a rank floor.  The two potential sliders of one host share rank
  and color — themselves twins — `pnSliderPair` [propext,
  Quot.sound].
* **THE CARGO TRIAD** closing the covered cells: (a) STACKS NOW —
  the cover's rung waits: `pnCasForkMerge` — canon from both faces
  lands at ONE saturated state (hearts 13 / diamonds 13 / clubs
  12), the fork MERGES; (b) PARKED — the slide class: the exchlaw
  standing fork re-graded, cross-mate, priced by A2; (c) INERT —
  hidden/waste/stock (landing 1 negatives).  The POST-CASCADE TOP
  SLOT is a function of rung deltas, decided per row
  (`pnRungDelta`): the both-under bases expose at delta 2 (the
  ±2 collapse — the ladder owes two climbs); the cross-neighbor
  jacks sit at delta 0, raw-stackable yet seat-barred; row A's
  parked queens (rung waits, seat bars) SLIDE legally onto the
  bare king — the row-A to row-C road, and the slid pose then
  MERGES (the waiting-rung cascade fires).
* **THE CLOSING COROLLARY — the LOCAL CONTAINMENT** (`pnContained`,
  scanned at every licensed pair of all sixteen census cells): each
  neighborhood cargo card either DISSOLVES into the pair's cascade
  (founded at canon) or PARKS VERBATIM at its seat (hidden or
  face-up in its original pile).  THE SHARPENED NEGATIVE: the
  global form is FALSE — a coupled cargo DOES exist in the wild
  (the standing fork's ♣Q) but only CROSS-MATE, where the pair is
  not both-licensed.  No fork-cargo fires intra-state; the case
  table exhausts the cases.

**The consumer** (§3.1's obstruction inventory, twin-pair host
entry): 'direct landings: twin-pair fitting hosts, unobstructed'
gains its exact boundary — obstruction happens only through
PARKED-RESIDUE cargo on a twin host (the slide family); a
delta-0 cover dissolves in-saturation and never obstructs.
Feeds the per-arm enumeration; hardens the single-obstruction
discipline's base (the fired commit kills the ladder's return leg
AT the bottleneck: the substrate consumption and the fork cell
are the same object, each supplying the other's witness).

### §11-L4 (landing 4, same branch — the class-anchored selector `Orig.CanV3`, the face-list battery rows, the consolidated design picture)

**The step change this landed** (the plateau exchange, consuming
landing 3's table): canonV3 is REDEFINED per the user's
restructuring — not a run machine (landing 1's verdict stands:
the scaffold rule retired) — but a member selector.  Landed as
the library chapter `Orig/CanV3.lean` (1stdlib import line in
Orig.lean; every head audited), the composite height-first
index, and the landing-4 battery rows in probes/CanonV3Probe.lean
(face-lists by application: constructor-of-record for every
member; `lake env lean` prints the numbers; all gates throw-green).

**The composite canonIdx w = lex (canonHtup w, canonPosKey w,
canonFormalKey w)**: founded content leads the fixed suit order
(fork wings incomparable componentwise — the fixed-order lex IS
the arm choice, the conjugate-arm price paid on a MEANINGFUL
quantity — founded content); the position key breaks wiggle ties
(conj-invariant by construction: twinMap relabels piles in
place, never moves anchors — proven `canonPosKey_twinMap`); the
formal decSt key is the last formality (equal formal keys imply
equal states; the setoid-flip world means it never hides a
symmetry violation). The selector `canonV3Arg` (Bool fold,
deterministic, bounded input, computable) rides `canonIdxLt`
(irrefl row proven). Rows: `canonV3Arg_mem`, `canonV3Arg_max`,
`canonV3Arg_final_of_all` (saturated-gated: the selection is
Final when the list is). `canonHtup_twinMap` proves the pair-
permutation row outright. `canonIdxLt_irrefl` after a sorryAx
excursion was rebuilt Classical-free (decide-free stance
preserved; class-audit confirmed: no Classical.choice, no
native_decide — pure Bool algebra).

**The dedup engine**: the composite key audit roles
`v3NatListLt`/`v3NatListEq` `the Nat.beq instance trap` — the
early `simp`-based irreflection pulled Classical.choice via the
`decide`-desugaring; the fix (LegalBool instances live in
Landing1's kit) — enumerated swaps stay in FARM_MEMORY.

**THE CONSOLIDATED DESIGN PICTURE** (through the six-part frame
that organizes the skeleton file Orig/MacroInternal.lean —
read-only; the user owns the skeleton; reconcile, don't
duplicate):

* (0) The object: a macro class is a STRUCTURED SPACE, not a
  quotient blob. State-level machinery computes; class-level
  statements quantify.
* (1) The four coordinates: ARM (which wing saturated; founded
  content; related by the NECK: pull-slide-re-saturate — never
  by exchanges: exchlaw's found-channel refutation), WIGGLE
  (parked-residue positions; related by the SLIDE; residue
  locational independence), TORSOR (identity bits on seated
  unfounded pairs; related by the EXCHANGE itself — the only
  layer where "everything else is twin-exchangeable" holds in
  full, exchlaw's freeness battery), DEPTH (de-saturation
  distance; related by the cone's PULLS). Coordinate
  irreducibility: exchanges never touch found, never move
  positions; pulls never cross arms (each pull terminates down
  one arm's down-set); slides don't cross arms either.
* (2) The canonical state as coordinate readout: canonIdx reads
  arm (heights) then wiggle (positions) then formal key
  (torsor); canus nonempty (σ=id cone-refl), class-invariant
  (mem_macro_iff pays), conj-closed, saturated-gated
  (proven row), σ-inside (the swap lives in membership, never
  in the selector: conj arms tie on κ = position key and
  split deterministically under the fixed formal order — the
  design is Load-Bearing: it makes the section iff hold
  literally for conjugate mates in distinct classes).
* (3) The membership envelope: mem_macro_iff (decompression
  card's cone rows — pulls/slides/draws up to swap;
  finalWiggle_reach the named open row there) — everything
  quantifying over class members conditions on it explicitly.
  This file's faces ride EXPLICIT member lists (by
  application) until that engine imports; the residue set =
  ⟨canus_class_inv, saturated_tuple_orbit, canonV3_lit_iff⟩.
* (4) The fork dossier: three detectors one fact —
  slide-sensitivity (forkState: the standing fork registers,
  the merge does not), bottleneck dip (wing_crossing: any
  reversible wing crossing crosses a forkState slide-edge),
  non-unionability (the union tuple unrealizable by the
  homeless-cargo obstruction). A2 certified MINIMAL.
* (5) The card map (who owns which layer): THIS CARD owns the
  selector/case-table/bottleneck/plateau capstone;
  decompression owns the envelope (mem_macro_iff); exch-law
  owns the torsor; canlaw owns the leg-commutation grammar
  (reused by all); §3.1 owns the consumer (the obstruction
  inventory as the residue-profile grade).
* (6) The downstream reading: §3.1's remaining questions become
  coordinate-lookup queries (arm/wiggle/torsor/depth).

**The Q-CARGO LAW, deductive** (the user's rank arithmetic, now
in the library): (A) `v3PiledRung` — a face-up card's suit rung
sits weakly below its rank index (higher rung = already founded;
conservation forbids two zones; proof rides mem_faceUp_only +
WF.found_prefix + the position-to-membership take-row
`v3GetInTake` + rank-get `v3RankGet`/`v3UpGet`); (B) `v3ForkPins`
— a standing fork pins the licensed twin's suit EXACTLY at the
twin rank and the parked cover's suit STRICTLY below its own;
(C) `v3ForkExclusivity` — the sandwich: two forks in both
colors cross-pin into `x < y ∧ y < x`, mixed-rank included,
same-color second forks die by pinning alone. AT MOST ONE FORK
PER CLASS, at any ranks, any colors. Consequences: arm space ≤ 2,
orbit = the single-pair flip of the forked pair (pair-dependent
Z/2; the (Z/2)² product was REFUTED), one neck, one bottleneck,
one unionability obstruction per class. The worried bit is a
PER-CLASS SINGLETON BY ARITHMETIC — the §3.1 count's last soft
spot now rigid. The crafted double-fork attempt becomes the
REFUTATION WITNESS row (decide-verified in the battery: the
arithmetic refuses the second standing fork).

**The organizing vocabulary** (the chapter's state-level
primitives, riding the banked canon — zero new machinery):
`satRung st s := (canon st).found s |>.length` (the saturation
ceiling; the arm VISIBLE as a ceiling asymmetry across
neck-mates: slide-sensitivity = ceiling-profile difference, the
fork detector as arithmetic), `neverStackable st c := c's rank >
satRung` (the permanently-parked population), `parkingMap` (the
seated anchored read of that population — the residue profile).
CLASS-LEVEL versions (`classRung C s := ⨆ w ∈ C, (w.found s).length`
— the canus filter removed from the definition's face; LEAN ON
the skeleton's classOf/rungAt names at merge) are the
STATEMENT-level faces; state-level defs here are the engine.
Two-level bookkeeping: class level for MEANING, state level for
COMPUTATION.

**EVIDENCE, decided at the battery** (the landing-4 rows): wing
consistency (query both face-list orders → same pick: the four
families' selector values printed; injectivity across distinct
classes → distinct picks); arm choice pinned (the standing-fork
class takes the heart wing 13/12; the merge class is a
singleton — canon equal from both faces; row-A takes the
DISSOLVED face; the under family splits deterministically);
sat-orbit spot rows (the wings' tuples differ exactly by the
hd-flip, suit-sums equal [0,13,12,0] ↔ [0,12,13,0]); the
nonempty+saturated gates (license census zero at every pick);
the fork detector census (the standing fork registers; the merge
does not; the row-A dissolve-extending slide REGISTERS —
slide-sensitivity properly CONTAINS the wing forks, the height
ordering discriminates: both its faces' union tuples REACHABLE
(the dissolved face dominates); the bare kings' anchor-slides
do not).

**COORDINATION (the skeleton reconciliation note)**: the
statement skeleton Orig/MacroInternal.lean (main tree, user
owned, untracked) fixes the convergent names: classOf, rungAt,
twinSuit, classRung, neverStackable, satStackable,
stackable_now_rungexact, canon_rung_mono, classRung_attained,
satStackable_iff, ConeStep/ConePath, cone_inClass, conjl + laws,
canusOf + canusOf_class_inv + canusOf_nonempty, posKey, lexLE,
canonKey, canonV3_witness, canonV3, canonV3_iff,
canonV3_section, forkState, forkEvidence, fork_pins,
fork_exclusive, saturatesTo, unionable, unionRung,
unionable_iff_unionTuple, fork_iff_nonUnionable, Journey,
wing_crossing_bottleneck, saturated_tuple_orbit,
saturated_classification, envelope, canonKey_rungs. DELTAS:
this file's `canonHtup/canonPosKey/canonFormalKey/canonIdxLt`
are the same reads with fixed names pending the merge rename;
this file's `v3ForkPins/v3ForkExclusivity` are the skeleton's
deterministically-proven fork_rows (state-shaped now,
class-shaped at merge via the envelope); saturated-gated row =
canonV3Arg_final_of_all; the skeleton's three sorry-carriers
(conjl's involutivity/class, posKey reuse, canonV3's choose
plumbing) are exactly where the def work lands next. The
skeleton's Journey/wing_crossing/unionable rows are RECEIVING
rows: the battery's next session consumes the plateau tools
here to lift the crafted-evidence rows (already in this commit:
the merge/standing-fork union realizability arithmetic; the
homeless-cargo obstruction for the (13,13) tuple) into the
skeleton's shapes.

#### §11-L4.1 — the forkEvidence SIGNATURE CORRECTION (amr_129d6300b, the user's detection discussion; landed same branch — battery + audit, decide-graded)

The corrected signature (read LIVE at the stall point, never
both-stackable — that reading is VACUOUS at real fork cells,
exactly consistent with this card's census verdict that
intra-state contention is empty at WF):

  forkEvidence stall x := CanRaise x (the bare twin) ∧
    coveredIn x.twin (∃ a, pileHolding = some a ∧ aboveIn ≠ [])
    ∧ ∃ cargo d, d.rank.toIdx + 1 = x.rank.toIdx ∧ ¬twinSuit
    d.suit x.suit ∧ rungAt d.suit < d.rank.toIdx (the PIN: the
    cargo cannot stack in place, the cascade cannot light it)
    ∧ THE OPERATIONAL TRIAL: st.step (.tabToTab d (Sum.inr x))
    = some st' ∧ CanRaise st' x.twin (the slide lights the
    covered twin — the other arm witnessed live).

Decided at the battery (probes/CanonV3Probe.lean, the
l4RowForkSigCorrected rows; all green):
- BOTH standing-fork stalls register (v3Fork and its mate) —
  the pin (clubs 0 < ♣Q's 11), the slide-trial to the other
  arm, the exposed twin licensed post-slide.
- The benign next-in-line MERGE cell REFUSES: the cargo's own
  rung waits (clubs 11 = its own index), so though the
  slide-trial alone fires, the full signature is false — the
  false-positive guard verified.
- The covered twins are UNLICENSED at the stalls (one licensed
  + one covered, never both); the same-color rungs pinned at
  the pair rank by the bare twin's stackable-now — the covered
  twin's pin by cargo/cascade arithmetic, NOT by CanRaise.

AUDIT (the consequence-2 checklist): the landed case-table rows
are CONSISTENT with the corrected signature — no row speaks of
both-stackable twins at a fork stall; the lattice rows state
the opposite (pnCoveredPairAtMostOne), the both-licensed rows
are exactly the independence slice (the NON-fork cells), and
the covered rows speak of cargo-above (pnCoverSit).  NO
VACUOUS ROWS FOUND.  Persistence (carrying the recorded bump
from stall to saturated form) is the next carrier work; the
canonicalizer reads the signature live during saturation, and
forkBump's forensics problem dissolves as the request states.

#### §11-L4.2 — the second signature correction (amr_129d79e2b; landed same branch — the swap-grade license in the library, the gap form decided)

CanRaiseS (the skeleton's exact shape) is now in Orig/CanV3.lean:
the swap-aware cargo-accounting license — 'now' (vanilla
CanRaise) | 'via' (∃ d b, a licensed REVERSIBLE tabToTab slide
then CanRaiseS at the landed state).  The vanilla CanRaise has
NO swap disjunct (confirmed by reading the def), and:

* **THE GAP FORM** (the corrected forkEvidence): CanRaiseS x ∧
  CanRaiseS x.twin ∧ ¬CanRaise-vanilla x.twin ∧ coveredIn
  x.twin ∧ cargo-shape (next-rank, opposite color, rung-pinned)
  — contention at the SWAP grade that is NOT contention at the
  vanilla grade.  Decided green at the battery
  (l4RowGapForm): fires at BOTH standing-fork stalls (the
  covered twin lifts only VIA the cargo slide), the derived
  trial (forkPoint_trial) decide-verified (the slide lands the
  mate cell exactly and lights the covered twin vanilla), the
  next-in-line merge REFUSES at the pin leg, the benign
  independence slice REFUSES at coveredIn.
* **THE TWO-PREDICATES DISTINCTION** (the consistency note): the
  census's TwinContended-emptiness was won at the VANILLA grade
  and remains INTACT — the fork is contention at the CanRaiseS
  grade.  No reader should misread the census as
  fork-refuting: the vanilla census says nothing about the swap
  grade, and the gap form is exactly the shape the census left
  open.  (The census batch's emptiness theorem rides the
  vanilla canRaiseB through `canRaise_lifted`; the swap-grade
  closure adds contention exactly at the fork stalls.)
* **THE CanRaiseS AUDIT** (the request's consequence-6): rows
  the battery had already proved as cascade facts under other
  names, now re-read at the new license: the parked queen of
  row A's pose lights VIA the dissolve-extending slide
  (vanilla false bare-queen-bar at the parked cell, vanilla
  true after the slide); the merge cargo lifts VANILLA (no
  slide needed — its own rung waits, exactly why the cascade
  dissolves the fork); the v3Chain enablement chain is
  vanilla-only; the earlier l4RowForkSigCorrected rows are the
  derived-trial content at depth one.  -/ AUDITED, no rows to
  RETIRE, no rows VACUOUS under the new grade.
* **Skeleton reconciliation**: my Orig/CanV3 mirrors CanRaiseS
  exactly; forkPoint's satStackable leg (macro grade) is the
  class-level residue — at the crafted cells the rung-pin row
  (v3RungAt st d.suit < d.rank.toIdx) is the live state-level
  functional form (the pin row is what the cascade arithmetic
  consumes; the macro satStackable reads the same fact through
  the quotient envelope).  forkPoint_trial's sorry is mine to
  close next; its decide-grade evidence is landed.

#### §11-L4.3 — the final vocabulary adoption (amr_129d9319a; landed same branch — names aligned, grades disambiguated, spec/computation separation audited)

The class-card grades (MacroInternal-aligned names): atRungInClass
(∃ st ∈ classOf, rungAt = toIdx — THE one-existential primitive),
satStackable (∃ st ∈ classOf, c ∈ found), strandedInClass (¬
atRungInClass — where the pinned cargos live), pendingForever
(atRungInClass ∧ ¬ satStackable — the CEILING POPULATION: covered
twins at Finals, buried stranded kings — the positional blockage
as a first-class grade), neverFounded (renamed from the conflated
neverStackable; toIdx ≥ classRung).

- STATE-LEVEL ENGINES (Orig/CanV3, computation-side, renamed +
  docstring-disambiguated): satRung (rides canon), neverFounded
  (the weak union), strandedAt (the rank-pinned read: below the
  canonical ceiling), pendingForeverAt (at-rung at the canonical
  ceiling ∧ not founded by the saturation — the position-blocked
  read), parkingMap (the seating read of the never-founded
  population).  All audit [propext]; build green.
- THE DISAMBIGUATION decided (battery l4RowGradeSplit rows):
  the standing fork's CARGO is STRANDED — rank-pinned (clubs 0
  < the queen 11, at both the stall and the wing state — the pin
  row is the stranded witness); the covered Final TWIN is
  PENDING-FOREVER — at-rung at the canonical ceiling (diamonds
  12 = its index) yet never founded, blocked by POSITION (the
  cargo above); TWO obstruction kinds the old one-word parked
  merged.  The merge cargo is NOT stranded (its own rung waits,
  it lifts vanilla — the cascade dissolves it).
- THE SPEC/COMPUTATION SEPARATION audited (consequence-2): the
  ∃-forms are spec-level — trivially class-invariant, NO
  carrier; every carrier/computability content stays in the
  classRung/forkBump channel.  My landed statements split
  accordingly: the census/case-table/selector rows are
  computation-side (state-level decides: pins, ceilings,
  coverage); the class-grade closure theorems
  (satStackable_iff, atRung_iff, stranded_iff, grade_partition)
  consume the ∃-forms and ride the envelope — named receiving
  rows in the skeleton, with the state-level engines landed
  here as their computable substrate.

#### §11-L4.4 — the final vocabulary SYNC (amr_129dda51d; the skeleton restructured by the user — read back, mirrored, no edit)

The class-card grades are now ALL existential at the spec level,
and the ceiling-bump family is GONE from the skeleton:
satStackable C c := ∃ st, classOf C st ∧ c ∈ st.found c.suit
(renamed from foundedInClass — DIRECT ∃-stacked); atRungInClass
:= ∃ st ∈ classOf C, rungAt st c.suit = c.rank.toIdx;
strandedInClass := ¬ atRungInClass; pendingForever :=
atRungInClass ∧ ¬ satStackable.  REMOVED: classRung,
classRung_attained, scanRung, forkBump, enumClass,
neverStackable, neverFounded, foundedInClass.

SYNCS APPLIED TO THIS BRANCH'S LANDINGS (the consequences):

1. ROWS RESTATED THROUGH THE ∃-GRADES — my prose now reads:
   founded = satStackable; ready-never-founded = pendingForever;
   below-every-rung = strandedInClass.  No spec-side statement of
   mine reintroduces ceiling arithmetic: the only ceiling
   machinery left on this branch is the COMPUTATION-SIDE engine
   channel in Orig/CanV3 (satRung / aboveCeiling [renamed from my
   engine-name neverFounded when the skeleton retired the name] /
   strandedAt / pendingForeverAt / parkingMap), all docstringed
   as engines computing witness readings at members, never
   defining the class grades.
2. grade_partition is CITED, not re-derived (proved sorry-free
   in the skeleton by a classical case split — the three grades
   partition every card); founded_implies_atRung (the pull-walk
   property: founding implies at-rung somewhere) is THE remaining
   grade-row stub, the envelope's next lift.  My battery's state-
   level facts (pins at-rung, ceiling coverage) feed exactly that
   stub's decide-side.
3. The battery's engine-name references updated (neverFounded →
   aboveCeiling in every print row and gate line); the library
   rename is body-preserving ([propext], build green 29 jobs);
   the gates all still green end-to-end.

The skeleton stays the user's file in the main tree — mirrored
here, never edited.

#### §11-L4.5 — the floor sweep opens (amr_129f4f9d2; the proof-readiness audit answered YES-for-the-floor, and the sweep starts landing on this branch)

The user's MacroInternal.lean (main tree, user-owned — mirrored,
never edited) is the statement reference.  This branch's sweep
section opens in Orig/CanV3.lean (the audits above), with the
tier plan ledgered as asked:

* TIER 0/1 OPENED with three PROVEN rows (zero sorry, the
  audits printed in the build):
  - `stackable_now_rungexact` [propext]: the licensed lift's rung
    sits EXACTLY at the card — one step through the vanilla
    license's nextUp conjunct.  DELTA NOTE, the honest one: the
    skeleton's biconditional as written is FALSE at covered seats
    (decided at the merge cell: the covered twin ♦K sits AT its
    rung, unlicensable under cargo) — the load-bearing halves are
    this direction plus `v3PiledRung` (a piled card's rung sits
    weakly below its index).  The skeleton row should either take
    the forward shape here or add the seat premise; the falsifier
    evidence is in the battery (canRaiseB pnCasForkMerge v3DK =
    false with the rung exact).
  - `canon_rung_mono` [propext, Quot.sound]: saturation only
    raises, per suit — by fuel induction on canonAux through the
    per-step row `satStep_rung_mono` (a fired lift raises one suit
    one and levels the rest via the banked `raise_foundTransport`;
    a frozen or failed step is the identity).
  - the mirrored `rungAt` (the skeleton's name).
* TIER 2 LANDED — PULL-MULTISET DETERMINISM (the fresh lemma,
  everyone's-blocker, self-contained, now PROVEN
  [propext, Quot.sound] throughout):
  - `fiber_founds_eq`: two WF states at equal per-suit rungs
    carry EQUAL FOUNDATIONS — the founds are fixed build-order
    prefixes, so the fiber's founded content is a function of
    the tuple alone.  (The take-past-length row `v3TakeGe` and
    equal-minim arithmetic close the two height-edge cases.)
  - `found_pullSegment` + `pullSegment`: a member's descent
    segment to any lower target IS the build segment (the founded
    prefix is the build prefix at its height);
  - `pull_multiset_determinism`: same fiber (equal rungs) ⇒ every
    member's descent pops the SAME CARDS per suit, top-down —
    the tuple deltas determine the popped cards, within one arm.
    THE ARM-SPLIT NOTE: the arm split is the twin pair's tuple
    swap itself (13/12 vs 12/13 — decided at the wing cells); the
    determinism holds within each arm, and the popped-card
    difference across arms is exactly the fork pair's segment
    difference — this is the core the fiber_iff_flat capstone
    rides, unlocked per the request.
* STILL OPEN, the honest sweep ledger (routes documented, no
  silent stubs): `flat_heights` (induction over the flat letters
  citing the per-move founds-invariant rows: tabToTab
  piles-only, draw board-stable, exchangeTwin_found banked), the
  grading trichotomy (`dance_step_grading`/`cone_step_fiber`:
  the same constructor splits through `raise_foundTransport`,
  the foundToTab inverse, and the flat rows), `cone_inClass`/
  `dance_inClass` (oneMoveRevEqW + the setoid closure; the
  general letter's whole-play return needs the witness-lift —
  the one-move-undo letters close now, noted), the forks'
  skeleton shapes (`forkPoint_trial` conditional on the
  pair-config lattice — the L3 case table + CanRaiseS machinery
  are the consume-pieces; `forkPoint_pins` = the v3ForkPins
  arithmetic at the skeleton's shape; `forkPoint_exclusive` =
  MY v3ForkExclusivity ALREADY LANDED DEDUCTIVELY, the shape
  conversion at merge), `founded_implies_atRung` (the pull-walk:
  the pop segments now determinate via the tier-2 rows; the
  reversibility-per-seat legs next), `benign_sat_iff_surely` and
  `surely_imp_sat` (both conditional on Finals-existence — the
  canusOf_nonempty gate).  The two gates stay conditional as
  instructed: canusOf_class_inv (= mem_macro_iff,
  decompression's finalWiggle_reach) and saturated_classification
  (exotic census) — no blocking on them anywhere above.

#### §11-L4.2a — the V2-calibrated forkPointC sync (amr_12a30bc3; superseding note to §11-L4.2's shapes)

The calibration consensus is three-way (two falsifiers struck the
earlier shapes, agreeing verdicts): CanRaiseS-only let the bare
twin hide behind slidables; cargoTop alone let the covered twin
sit stranded a rung short.  The CALIBRATED shape (the floor card's
batch F, now green in the user's MacroInternal.lean):

  CanRaise st x (vanilla pile-top, AT the point) ∧
  rungAt st x.twin.suit = x.rank.toIdx (the covered twin's pin AS
  PREMISE — the fork's own datum) ∧ cargoTop st d x.twin ∧
  d.rank.toIdx + 1 = x.rank.toIdx ∧ ¬ twinSuit d.suit x.suit ∧
  ¬ satStackable ⟦st⟧ d.

DECIDED at the battery (l4RowForkPointV2, gates green): BOTH
standing-fork stalls REGISTER the calibrated signature (the bare
twin vanilla NOW, the covered twin pinned at the pair rank as
premise, the cargo class-stranded over the by-application face
corpus); the MERGE cell REFUSES on the CLASS-GRADE conjunct this
time — every state-level conjunct holds there (vanilla bare
twin, twin pin, cargoTop, rank, color) — but the cargo IS
satStackable in the merge class (founded at the saturated
member): the cleaner refusal the calibration buys.  My V1
gap-form rows (§11-L4.2's l4RowGapForm) stand as
superseded-in-shape evidence; their cargo-pin read was the
fork-own-datum observation the calibration lifts to a premise.

CITED, not re-forged (the macro-floor engine bank, branch
orig-macro-floor, batch A/F): canRaiseS_rung_pin,
forkPoint_cargo_strand, the per-step rung locality rows, and the
de-privatized exchange realizers step_realize_fwd/_bwd (commit
69fbaa8); with the segment-existence rows (found_pullSegment /
cone_pop_window, branch orig-macro-determinism) unblocking
founded_implies_atRung at merge time — my §11-L4.5 route note
rides that.

#### §11-L4.6 — the mirror re-port + graft census (amr_12a3219b1; the two-evolutions-behind diagnosis acknowledged and repaired)

REPORTED: the user's MacroInternal.lean is now MIRRORED VERBATIM
into this branch (Orig/MacroInternal.lean, 521 lines, the main-tree
file read and copied) and STANDALONE-COMPILES GREEN (lake env lean
Orig/MacroInternal.lean): every theorem in it now elaborates
against this worktree's banked state; the sorries it retains are
its own by design (the user's skeleton file, mirrored — never the
main-tree file edited).

THE TWO CHANGES SINCE THE LAST SYNC, both carried:
(1) THE FLATSTEP CARGO-MERGE — FlatStep is now TWO letters only
(cargo = any tabToTab relocation, subsuming slides, reseatings,
and licensed exchanges per exchangeTwin's own suffix-swap
semantics; exch_is_cargo proved on orig-macro-floor).  This
branch's ledger phrasings that spoke of the exchange letter are
superseded: the exchange vocabulary survives as the RELATION-level
name only.  My not-yet-landed flat rows re-target the two-letter
shape at the next sitting.
(2) FORKPOINTC V2 — the calibrated stall-point signature, mirrored
and DECIDED at the battery (§11-L4.2a above): both fork stalls
register, the merge refuses on the class-grade conjunct — the
cleaner refusal.

THE GRAFT CENSUS (my landed proofs onto the new definitions —
def-orthogonal, re-verifying):
- canon_rung_mono GRAFTED PROOF-COMPLETE (the fuel-induction
  transplant from the floor sweep, 5a64bb4 — zero sorry);
- forkPoint_pins GRAFTED PROOF-COMPLETE at V2 (near-trivial by
  premise, per the calibration: the covered twin's pin IS the
  premise; the bare twin's pin is the vanilla license's nextUp,
  one step — zero sorry);
- stackable_now_rungexact STAYS the biconditional `sorry` in the
  mirror: my landed row is the FORWARD direction; the biconditional
  is FALSE at covered seats (the §11-L4.5 falsifier evidence,
  three-way-consensus ledgered).  The mirror's row should take the
  forward shape or add the seat premise — noted for the user.
- forkPoint_trial / forkPoint_exclusive REMAIN `sorry` in the
  mirror, BLOCKED-NOTED with the owner: the floor card's engine
  bank (branch orig-macro-floor, commits aaed5d5..0a72766 —
  canRaiseS_rung_pin, forkPoint_cargo_strand, the per-step rung
  locality rows, the de-privatized exchange realizers
  step_realize_fwd/_bwd, commit 69fbaa8) plus the determinism
  branch's segment rows (found_pullSegment / cone_pop_window)
  carry the rest of the closure; my census families witness the
  rank arithmetic (the wings, the pins, the sitting-standing
  refusal — all decided green in the battery).
- The mirror stays UN-WIRED from Orig.lean's import list (the
  name collisions with Orig/CanV3.lean's same-named rows are the
  merge-time reconciliation the ledger tracks: this branch's
  same-named rows drop in favor of the grafted mirror at merge).

DISCIPLINE NOTES: the mirror is a file-copy of the user-owned
main-tree file — mirrored per the re-port instruction, never
editing the main tree; the two grafts are proof-only (bodies
behind the mirror's own statements); battery remains green
end-to-end after the re-port; no merge to macro-game.

#### §11-L4.7 — the acknowledgment + the duplicate drop (amr_12a423a3d; the harvest in-tree, the mirror de-conflicted)

(1) forkPoint_pins AT V2 ACKNOWLEDGED — the fork dossier's first
row CLOSED by the calibration's promise: the covered twin's pin
enters as premise; the bare twin's pin is the vanilla nextUp
conjunct, one step (the grafted proof stands in this branch's
mirror, commit 10bebe4; the in-tree MacroInternal base carries
the same row per the harvest).

(2) THE HARVEST IS IN-TREE, cited for all merge-time work:
macro-game advanced through 651e2d4 (MacroInternal.lean TRACKED
as the canonical merge base, v2-calibrated), ff0eb62 (the
orig-macro-floor harvest: fifteen floor rows sorry-free — the
one-directional stackable_now_rungexact with the covered-seat
falsifier documented, canon_rung_mono, the per-move rung grading
family, per-step heights/fibers, cone_inClass / dance_inClass
through the LOOP-CLOSURE BRIDGE — any reversibleAtW leg plus
step gives class membership, dissolving the multi-draw
return-play obstacle this ledger had BLOCKED-noted — exch_is_cargo
with the realizers step_realize_fwd/_bwd PUBLIC, surely_imp_sat,
benign_sat_iff_surely, canusOf_nonempty), and 9cc9598 (the
orig-macro-determinism harvest: rung_found_prefix restated per
WF.found_prefix, rung_found_congr, ConeLedger, cone_rung_mono,
cone_pop_window (the master pop-ledger row), cone_pulls_congr_tuple
sorry-free, flat_into_dance, plus the tier-0/1 calibration rows
swept in passing and the DeterminismProbe battery — 0 violators
in 3346/46208 same-tuple pairs with order-differing and
different-tuple controls: determinism with teeth).

(3) THE DUPLICATE DROPPED: my mirror's canon_rung_mono graft is
retired (the stub restored, the docstring re-pointing at the
in-tree proofs — floor and determinism both landed it; my
CanV3 chapter keeps the floor-sweep copy for this branch's own
ledger trail).  Merge conflict saved per the recommendation.

(4) THE THIRD CONSENSUS NOTED: the one-directional
stackable_now_rungexact calibration (forward + falsifier) is
now landed independently by both harvest branches AND evidenced
by this branch — the biconditional honestly refuted three ways.

TRIAL/EXCLUSIVE, the continuation state: this branch's base does
not yet contain the harvest (a rebase is my choice, a re-port
not warranted mid-flight per the coordinator); the two remaining
fork rows stay BLOCKED-NOTED with the in-tree owners to cite at
merge — the engine bank (canRaiseS_rung_pin,
forkPoint_cargo_strand, the per-step locality rows, the
loop-closure bridge, the public realizers) plus the determinism
core (cone_pop_window and the pop-window family: the descent
arithmetic the trial's other-arm witness needs).  My census
families continue to witness the rank arithmetic decide-graded
(the V2 signature rows, the stall/merge register-refuse split,
all green).

#### §11-L4.8 — the fork dossier closes at the canon-v3 wake (amr_12a492e2; branch orig-canon-v3 rebased onto the harvested macro-game 6cdd9fb)

THE REBASE: this branch is now based on the harvest (floor
ff0eb62 + determinism 9cc9598 + canlaw d1a478b + the cushion
6cdd9fb); ledgers append-unioned; the doubled MacroInternal
union repaired to the IN-TREE file verbatim; lake build Orig
green 30 jobs; the whole battery replays green after the rebase.

THE DOSSIER, CLOSED 40 PERCENT IN-FILE (the v2 base made the
difference):
- forkPoint_pins PROVEN in-file (one step: the covered pin is the
  v2 PREMISE; the bare pin is the banked one-directional
  calibration `stackable_now_rungexact` — the same consensus this
  branch landed third).  The stale BLOCKED note retired.
- forkPoint_exclusive PROVEN in-file (the user's rank sandwich,
  now consuming exactly the v2 premises: two private helpers —
  `twinSuit_symm` + `suitfamily_antipodal` (four suits, two color
  families) — and the cross-pinch arithmetic row `cross_pin`: each
  cargo, opposite-colored to its OWN pair, sits INSIDE the other
  fork's pair suits where that fork's pins hold the rung AT its
  pair rank, while its strand demands strictly below its own —
  the two inequalities cross-pinch to Ry+2 ≤ Rx ∧ Rx+2 ≤ Ry,
  `omega`).
- forkPoint_trial — THE HONEST RESIDUE, analyzed at this wake:
  the v2 premises make the trial's EXPOSURE leg derivable (the
  rank-consecutivity of the pile runs forces the cargo to sit
  DIRECTLY on the covered twin — no intermediates possible
  between consecutive ranks), and the FIRE leg derivable (the
  slide's guards: the bare twin is a pile-top by CanRaise; rank
  and color by the premises), but the SEAT leg of the exposed
  twin is UNDER-CARRIED: a WF craft with the covered twin
  BARE-BOTTOM in its pile (faceUp = [twin, cargo], hidden = [],
  non-king pair ranks — e.g. the (Q, J) configuration: hearts
  A..J founded, ♥Q licensed seated on ♣K; diamonds A..J founded
  with ♦Q unfounded, sitting bare-bottom under ♠J; spades/clubs
  rung 0 with the aces stock-resident so the class closure never
  founds a black card) satisfies EVERY v2 conjunct yet the
  exposed twin at the slid state fails `CanRaise`'s seat leg
  (chop = [] and not a king — the same bare-non-king seat bar
  this branch's V6 negative controls decided).  RECOMMENDATION
  (the three-way-consensus pattern): add the covered twin's seat
  premise (chop ≠ [] ∨ bare king at its pile) or restrict the
  signature to king pairs; the crafted falsifier cell is the
  next sitting's probe-first step (the census battery already
  banks every needed row: the seat bar, the stock-resident
  negative controls).

THE CARD'S FINAL STATE: the census (L1), the case table (L3),
the selector chapter (L4), both signature corrections, the gap
form, the grade split, the name syncs, the re-port, and now the
dossier's pins + exclusive — all landed green on the rebased
branch; the trial carries the honest analysis and the crafted
falsifier recipe.  The battery's every gate still throws-green.

#### §11-L4.9 — the V3 directive (amr_12aaf07c1): the SEAT PREMISE lands, the falsifier probe decides V2-vs-V3, and the trial's fire leg proves in-body

(a) FORKPOINTC V3 LANDED (the in-tree file): the 7th conjunct —
the covered twin's pile runs `bs ++ [x.twin, d]` with the cargo
DIRECTLY on the twin (the run discipline's rank-consecutivity is
now the witness shape: consecutive ranks admit no intermediates)
and the seat package `bs ≠ [] ∨ (hidden = [] ∧ king)` — exactly
the premise the (Q, J) analysis prescribed.  NO global king
restriction (the sandwich never needed it; generic-rank forking
is honest with the seat clause).  The V2 unpack sites updated
(strand/pins/exclusive all still prove at V3 — the covered pin
still premise, the color-placement unneeded by rank).

(b) THE (Q, J) FALSIFIER PROBE LANDED, decide-graded green
(probes/CanonV3Probe.lean, the l4RowQJFalsifier rows): hearts/
diamonds climbed A..J, the licensed heart-queen under-seat on a
club king, the covered diamond-queen BARE-BOTTOM under the spade
jack, spades/clubs rung 0 with the aces stock-resident — every
V2 conjunct HOLDS, the trial's conclusion DIES at the slide (the
exposed queen bare-bottom non-king), and V3's seat premise
REFUSES (v3SeatPkgB false): the cell registers NO fork point at
V3, and the trial is restored by vacuity — the card's own
diagnosis, probe-first.

(c) FORKPOINT_TRIAL AT V3 — STAGED GREEN with one named residual
stage: the signature takes the honest WF premise (the
pile-holding uniqueness is WF-gated; the trial's fine print now
matches the dossier's siblings).  IN-BODY PROVEN: the full FIRE
leg — the walk bars (nodup_snoc_notmem private; below/fromCard
snoc reads via the banked below_append_stop/fromCard_append_stop
over the duplicate-free run), the membership route to
pile-holding, the color-bar (not_twinSuit_colors private: suit
families are colors), the place (canSitOn through canSitOn_eq
with the rank premise and the color bar), and the step's own
guards — the slide FIRES.  REMAINING (the residual stage,
marked `sorry` in-body with the staged note): the
successor-composition read through step_tabToTab_inv (the
putRun target-scan agreement; pile a's cleared content), the
exposure via pileOfTop_eq_some_iff at step_wf, and the license
assembly (rungs via step_tabToTab_rungs; the chop seat bar via
chop_snoc; nextUp via the twin-rank invariance).  Every piece is
banked or in-file; the composition is the next pass's mechanical
work — no new mathematics.

Battery green end-to-end; lake build Orig green 30 jobs; the
falsifier numbers pinned in the run output (v3WfB true, the
v2-conjuncts true, the class-strand false, the seat package
false, the trial conclusion dead, the row green).  No merge to
macro-game; additive only.

#### §11-L5 — THE FORKSTATE UNIQUENESS THEOREM lands mechanically (branch orig-forkstate-unique, base macro-game a772b23 per the 8a0e121 recipe; the slide-mate + king-shuffle halves complete, the maximality gate honestly named)

(a) THE ANATOMY FINDING (the chapter's headline): the
`conjugateForkState` composite, AS WRITTEN, never lands the mate —
it is NET-FLAT on the foundations (`conjugate_endpoint_netflat`:
raise writes +[x], slide writes nothing, pull chops it back) and
the pulled-back card RE-LICENSES at its fresh seat with the pin
restored (`conjugate_endpoint_relic`), so any forkState at the
composite endpoint witnesses the SAME card the composite started
from (`conjugate_endpoint_witness`; the dance reading rides
`conjugate_dancePath` per-leg-reversible).  THE MATE IS THE SLIDE:
one direct reversible `tabToTab` of the covering cargo onto the
witness — `forkState_slide_mate`.

(b) THE SLIDE-MATE ROW, FULLY PROVED — §11-L4.9's named residual
stages, closed and exceeded: the successor-composition read (the
mid-state `pileOfTop` scan pinned WF-free by
`firstWhere_find`/`mem_faceUp_unique`, `putRun_inr_eq`), the
exposure (`pileOfTop_eq_some_iff` at `step_wf`, seat package
verbatim through `afterRunRemoved_ne`/`chop_snoc`), the license
(`CanRaise s' x.twin`), AND the complete iff at the slid state:
the maximality transport at the slide closes by the four-case
parcel — the witness's BURIAL by the landed run, the cargo's
STRAND (its own license would have fired at `st`: nextUp false
through the iff itself, the strand now a CONSEQUENCE of the
detection), the off-triple cards' TOP-STATUS invariance (only
x.twin exposes, only x buries), and the rung nonwirth.  Plus the
leg's reversibility (`tabToTab_undo_under`, the classification's
under-cell) and the one-leg `CargoPath`.  Premises mirror the
in-tree `forkPointC` witness shape at the new reads (the covered
twin directly under the cargo; the fit `canSitOn d x`; the V3
seat package).

(c) THE KING SHUFFLE LANDED: `kingVacate_reversibleW` — a bare
king's whole-pile vacate onto an empty anchor is ONE REVERSIBLE
`tabToTab` (undo = the mirror vacate; license =
`tabToTab_undo_bare`, the classification's bare-king cell — the
`Orig/Vacate` channel's king-side complement, its own
`vacateShape` barring kings by design), with the seat's
re-springing (the source anchor empties) read off directly;
the whole orbit — a king wandering the vacant anchors, swapping
with its twin — is the `KingVacWalk` closure, every leg one
`FlatStep.cargo` (`kingVacWalk_cargoPath`), inside the class
(`kingVacWalk_class`).

(d) THE PIN TRANSPORT: `cargoPath_rungs`/`_foundCongr`/`_class`/
`_sameClass` (flat legs keep every rung, `WF` travels, the
founds agree card-for-card at `rung_found_congr`, the loop-closed
`class_leg` engine puts every cargo walk inside the macro state) —
the mechanical strand of the in-tree sorry'd `faceShape_rel`, and
the state-level pair exclusivity at the new reads
(`forkPair_not_twoColors_state`/`_twoRanks_state`: the iff's own
finch — no omega needed at the state grade).

(e) THE MAIN ROW `forkState_unique` (st₁ st₂ same class, both
forkStates ⟹ `FaceShape st₁ st₂`) carries EXACTLY ONE named
BLOCKED residue: the maximality-transport gate, diagnosed per
gate — G1 PAIR-TRANSPORT (the off-pair suits' rungs are free
data: the `forkPoint_exclusive` sandwich needs the class-grade
cargo strand, content the one-state iff carries only at itself),
G2 COVERAGE-DEGENERACY (classes whose twin is blocked without a
fitting cover realize with NO slid mate — the (Q,J)-falsifier
seats — and the claim degenerates to the witness's cargo orbit),
G3 THE SATURATED RESIDUE (non-covering cargo wiggle between
same-pair forkStates — the `saturated_classification`/
`canonFace_sameShape` tier).  Given any gate's closure the row
assembles from this chapter's halves; the gate is deliberately a
single `sorry` with the diagnosis in its docstring.

Battery: `lake build Orig` green (30 jobs, leaf not wired into
the root, mirroring MacroInternal's own discipline);
`lake env lean Orig/ForkStateUniq.lean` exit-zero with exactly
one `sorry` warning (the named row).  Audit battery per head:
every fresh row `[propext]` or `[propext, Quot.sound]` — ZERO
`Classical.choice` anywhere — and `forkState_unique` prints
`[propext, sorryAx]` exactly as the in-tree gated precedent
(`cone_pulls_congr_crossarm`).  The in-tree interface
(forkState/conjugateForkState/CargoPath/FaceShape) mirrored,
never redefined; zero contention (branch file additions only);
no merge to macro-game.

#### §11-L6 — THE LAST GATE, CLOSED BY FALSIFIER (branch `orig-forkstate-gate`, base macro-game `07247ec`; the maximality-transport G2 head REFUTED at theorem grade, the in-tree main row's residue identified as a FALSE CONJUNCT, and the surviving transport machinery landed)

(a) PROBE-FIRST, per the house discipline, and the probe SUCCEEDED:
`probes/ForkUniqProbe.lean` crafts TWO same-class `forkState`s — witness
5♥ seated ON the black next-up 6♠ (the witness is ITS OWN blocking
cargo), twin 5♦ bare-bottom non-king (the V6 seat bar), rungs (♠5 ♥4
♦4 ♣3) — and the two-leg journey `[tabToTab 5♥ (inr 6♣), tabToFound 6♠]`
with one-move mirror undos both ways: the successor is ITSELF a
`forkState` of the SAME pair {5♥, 5♦} with the SAME orientation, rungs
(♠6 ♥4 ♦4 ♣3).  The maximality iff pins licenses at the FIXED
arrangement; a flat cargo leg can relocate the witness and re-expose
the covered next-up without touching any rung.  The strict G2 head —
"two same-class, same-pair forkStates agree on every non-pair rung" —
is UNPROVABLE: it is FALSE.

(b) THEOREM-GRADE, `Orig/ForkStateUniqGate.lean` (additive, importing
ForkStateUniq + MacroInternal; NOT wired into the root battery,
mirroring the leaf discipline): the craft lifted to kernel-decided
rows — the WF audit (52-card census), the license census at both
endpoints (52 `decide` branches through the banked `canRaiseB`
bridge), the four leg equations (two `rfl`, two `State.ext`-pointwise:
the setFound/setPile record lambdas are stuck at variable suits but
collapse at each concrete index), the `reversibleAtW` witnesses, the
`sameOrbitSetoid` class packaging, and the two refutation heads:
`forkGate_strict_head_false` (the ∃-form: same class, same pair, same
orientation, ♠ rungs 5 vs 6) and `forkState_unique_refuted` — the
in-tree row's OWN statement negated, all premises satisfied.  The
07247ec re-validation: the corrected conjugate (`tabToTab x.twin`) and
the CROSS-BRIDGE FaceShape are closed at BOTH grades — the cargo grade
by `cargoPath_rungs`, the cross grade by `conjugate_endpoint_netflat`
whose loose `∃ d` absorbs `d := x.twin` verbatim (the composite is
net-flat whichever card the slide leg moves).

(c) THE SURVIVORS (all sorry-free, all `[propext]`/`[propext, Quot.sound]`,
zero `Classical.choice`): the journey-letter census (`wasteToFound`/
`wasteToTab` never ride — `irr_of_desc` over the cycle-count table;
the reveal-shaped `tabToFound`/`tabToTab` never ride — the hidden-total
reveal cells), `journey_raise_shape` (a reversible raise IS licensed, or
sits in the named bare-bottom residue — the (Q,J) corner whose
irreversibility is the future write-analysis card's row),
`journey_raise_seatUnfounded` (a seated raise burns an UNFOUNDED
opposite-family rank-(r+1) board card as its seat — the scarcity
certificate; the craft's witness-as-seat is exactly the loophole a
repaired statement must bar), `shuffle_hiddenPinned` (the hidden-depth
pin: hidden lists agree along witness journeys, leg by leg — the
reveal irreversibility via the per-pile dichotomy + `run_pile_hidden_le`),
and `forkState_content_of_rungs_agree` — THE CONDITIONAL G2′: same
class + equal rungs ⇒ founds agree card-for-card (`rung_found_congr`)
and hidden profiles agree.  A repaired `forkState_unique` consumes that
row as its finishing step once its class-grade fork premises buy the
rung agreement the counterexample proves unbuyable at the bare iff.

(d) THE HONEST DIRECTIONS the repair card must price: the paired
(V3-coverage) shape — both black-(r+1) twins consumed by the pair
geometry (the witness seat + the twin's under-seat) bars the
witness-relocation mechanism; the class-grade fork (`afterFork`/
`forkPointC`-carrying classes with a stranded cargo) excludes the
benign classes where the detection fires midstream (the craft's class
saturates THROUGH the pair — 5♥ raises reversibly at st₁, so the class
is not forked at the macro grade, and the uniqueness claim there is
just false).

Battery: `lake build Orig` green (30 jobs); the leaf trio
`lake build Orig.MacroInternal Orig.ForkStateUniq Orig.ForkStateUniqGate`
green, zero sorry in the gate file, every head audited, zero
`Classical.choice`; `probes/ForkUniqProbe.lean` exit-zero, all gates
throw-armed.  The in-tree interface is mirrored, never redefined; all
changes additive; NO merge to macro-game.

#### §11-L7 — THE FORK-STATE SPECTRUM card closed by falsifier, third formulation (branch `orig-fork-spectrum`, base macro-game `8e469a3` re-ported from the mis-created `41023bc` checkout; the three-generator `ForkSpectrum` completeness REFUTED at theorem grade, the delegated parentSwap conditional instantiated, and the repair ledger priced)

(a) THE ARC: the deliverable was restated twice mid-flight.  The
first formulation (the going-deeper restricted language
`SpectrumPath`: deepRaise + twinCycle + cargo, with the twin-unit
widening refinement) was superseded by the brief's third revision:
the game's OWN rules are the only constraint, the spectrum is the
closure under three named structural generators, and the inductive
`ForkSpectrum` (base | twinSwap | parentSwap-stub | cargo) landed
in-tree at cecab21/8e469a3 with `forkSpectrum_complete` sorry'd as
the target and the parentSwap conditional delegated to this card.

(b) THE PROBE-FIRST VERDICT, third landing of the §11-L6 family:
ALL THREE GENERATORS ARE FOUNDATION-FLAT — twinSwap's conjugate
composite is net-flat card-for-card (`conjugate_endpoint_netflat`,
the loose ∃d absorbing the corrected `d := x.twin` verbatim), cargo
is flat (`cargoPath_rungs`), and the parent trade is a cargo
composite.  So every `ForkSpectrum` endpoint shares the start's
height tuple — and the class carries same-pair same-orientation
`forkState`s whose NON-PAIR rungs differ (the gate's public export
`forkGate_strict_head_false consumed verbatim, cite-before-craft):
the craft's forward journey `[tabToTab 5♥ (inr 6♣), tabToFound 6♠]`
decomposes as ONE cargo leg plus ONE NON-PAIR RAISE, and NO
generator raises non-pair material.  The foundation bookkeeping the
brief called "already accounted for by the stack discipline" is
carried by no letter: the CASCADE — the user's own (a) generator
from the first formulation — is the missing generator.

(c) WHAT `Orig/ForkSpectrumProof.lean` LANDS (additive leaf, importing
MacroInternal + ForkStateUniq + ForkStateUniqGate — the refutation
consumes the gate's banked public counterexample export; NOT wired
into the root, mirroring the leaf discipline): §1 THE FLATNESS LAWS
(`forkSpectrum_rungsFlat` — every leg preserves all four rungs;
`forkSpectrum_wf`; `forkSpectrum_foundsFlat` — the endpoints read the
foundations card-for-card through the banked `rung_found_congr`), all
sorry-free all `[propext, Quot.sound]`; §2 THE REFUTATION
(`forkSpectrum_complete_refuted` — the in-tree row's own statement
negated, all premises satisfied, `[propext, Quot.sound]` sorry-FREE:
the row's sorry is a false conjunct, not a gate); §3 THE DELEGATED
CONDITIONAL instantiated honestly (ParentSwapShape + ParentSwap:
the structural endpoint read — the twins parent-seated, the (x+1)
cards trading piles, boards agreeing elsewhere — PLUS the
`CargoPath` premise as the fit-side carrier, exactly the "SOMETIMES
available" per-state availability; `parentSwap_spectrum` rides the
cargo constructor; `parentSwap_rungsFlat` is the headline: even
instantiated, the trade moves no rung, so the rescue cannot come
from THIS generator); §4 THE NON-VACUITY BATTERY (the closure
genuinely generates the face world: `faceShape_spectrum` — the
in-tree FaceShape embeds; `slidMate_spectrum` — the §11-L5 mate
orbit; `kingVacWalk_spectrum` — the king shuffle); §5 THE REPAIR
LEDGER with the equality-locked target `forkSpectrum_complete_locked`
named BLOCKED — the ONE sorry in the file, `[propext, sorryAx]` as
the gated precedent (the G1 pair-transport / G2 coverage / G3
board-normalization tiers restated at the equal-rung grade the craft
forces, with the banked `forkState_content_of_rungsAgree` naming what
the lock buys) — plus the cascade-letter direction: the honest full
spectrum is this closure PLUS a raising letter, and the craft's own
journey (slide-then-climb) is `cargo ∘ raise`: two generators, both
witnessed.

Battery: `lake build Orig` green (30 jobs); the leaf quad `lake
build Orig.MacroInternal Orig.ForkStateUniq Orig.ForkStateUniqGate
Orig.ForkSpectrumProof` green (26 jobs); exactly ONE sorry in the
new file (the named BLOCKED target); every fresh head audited
`[propext]`/`[propext, Quot.sound]`, ZERO `Classical.choice`.  The
in-tree interface (`ForkSpectrum`, `conjugateForkState`,
`CargoPath`, `forkState`, `FaceShape`) mirrored, never redefined;
all changes additive; NO merge to macro-game.

## 12. The corrected conjugation theorems — session orig-conjugate-proof (STATUS 2026-10-12, branch `orig-conjugate-proof`, rebased onto macro-game `07247ec` per the 8a0e121 recipe; the probe-first battery `probes/ConjugateProbe.lean` landed BEFORE any proof, all gates decidable #evals, all boards conservation-checked)

The card's arc, with every verdict probe-first:

* PROBE (A): the canonical swap fires at the docstring bases; the
  endpoint's ONLY raiser is the ORIGINAL witness x — the twins trade
  physical positions, the license stays home.  The §3 one-leg slide
  contrast FLIPS to x.twin: the mate is the slide, never the
  composite.
* PROBE (B): the (Q,J) corner (x.twin bare-bottom non-king) FIRES
  through the displaced base and lands TWO raisers — NOT a
  forkState: the seat package is load-bearing (the main row carries
  it as a premise, exactly the in-tree docstring's "checked on
  x.twin side").
* PROBE (C): the floating-covered displaced firing lands a
  VALID forkState with the twin UNSEATED: the raw
  `fires ⟺ seats` necessity is REFUTED at probe grade; the honest
  biconditional lives at the seat-swap-outcome grade.
* PROBE (D): the rank-12 pair fires through the empty-anchor
  letters both ways; the endpoint witnesses x again.

LANDED (leaf `Orig/ConjugateProof.lean`, all heads audited
`[propext]` or `[propext, Quot.sound]`, zero sorryAx):

1. §1 the corrected-def instances of the §4 anatomy rows —
   `conjugate_netflat`, `conjugate_relic`, **`conjugate_witness`**
   (THE WITNESS PIN: any forkState at the endpoint witnesses the
   composite's own raised card; the task's "witness x.twin"
   reading is refuted by the banked loose row instanced at
   `d := x.twin`, witnessed by probe A).
2. §2 the seat parcels — `TwinSeat` (the V3 form),
   `twin_pile_ne` (the runOK descent kills same-pile twins),
   `twin_not_top` (the exposed-twin impossibility at a forkState),
   `seated_top_under`, `runOK_join_head_sit`.
3. §3 the packing pins — `no_fit_king`, **`conjugate_fit_pin`**
   (the two (x+1) cards of x's opposite color exhaust the fitting
   bases).
4. §4 **THE MAIN ROW `conjugate_forkState_corrected`**:
   [st.WF + the three clauses at x + x.twin located in q with
   TwinSeat + ANY firing] ⟹ forkState w, witness THE SAME x — both
   channels: the non-king channel forces ba = z₀ and bb = z₁ (the
   packing + search-exactness reads; the intermediate putRun search
   spelled per pile), the king channel forces the empty-anchor
   letters; the iff transport closes every branch (the rider
   analysis, the x-vacate read, the untouched-pile license
   transport).
   Named `…_corrected` against the in-tree gated
   `MacroInternal.conjugate_forkState` (the SEAT-LESS shape is
   FALSE — probe B is the falsifier witness; the gated row stays
   sorry, untouched).
5. §7 **THE TOTAL FUNCTION `conjugateForkStateS`** (decidable,
   zero Classical, zero noncomputable) + the full bridge battery
   (`forkClause2B_iff`, `forkWitnessB_and3`, `forkWitnessB_iff`,
   `forkWitness_sound`, `forkStateB_iff`, `fireOver_some`) +
   **`conjugateForkStateS_correct`**: the identity-on-fail
   contract, and any move lands a state satisfying BOTH the
   composite's ∃-definition AND a (decidably checked, bridged)
   forkState.

REMAINING (routes analyzed, probe-validated, deliberately future):

(a) `conjugate_swap_fires` (the iff's EXISTENCE direction): the
    seat parcels fire the canonical composite via the public
    splice rows; the main row then lifts the endpoint.  The heavy
    pieces are already banked: z₀/z₁ exist by §2, the fits by
    §2/§3, the search reads by the if-rows, and the main row
    consumes the firing.
(b) `conjugate_seat_of_swap` (the swap outcome forces the twin's
    seat package — the honest biconditional's other half at the
    seat-swap-outcome grade).
(c) `conjugate_corner_notForkState` (probe B as a theorem): the
    singleton run lands apposed to the fitting base with a LIVE
    seat; the pull's rank arithmetic forces the second landing
    off it; x re-licenses via the relic — two raisers cannot
    witness one forkState iff.  The one delicate passage is the
    intermediate base search at the reveal-scarred vacated pile
    (the mover's own face-up membership in another pile crushes
    the scarred-top candidates by conservation).

Battery: `lake build Orig` green (30 jobs; the leaf is NOT wired
into the root, mirroring MacroInternal/ForkStateUniq's own
discipline); `lake env lean Orig/ConjugateProof.lean` exit-zero;
every head `[propext]`/`[propext, Quot.sound]`, zero
`Classical.choice`.  The in-tree interface mirrored, never
redefined; zero contention (branch file additions only); no merge
to macro-game.

## 13. The no-lock pairClass capstone — the orphan-seat axes close (STATUS 2026-10-12)

The fork-classification program's landing day: one capstone, two
axis collapses, one inertness dividend, one budget row.  House
norm holds — routes live in the chapter docstrings; this section
is the ledger row, every anchor verified in this worktree at this
HEAD.

**THE CAPSTONE — `forkState_pairClass` (`Orig/PairClass.lean:81`).**
Within one macro class ANY two forks agree as pairs: the second
fork's witness is the first's or its twin (`y = x ∨ y = x.twin`),
NO family hypothesis assumed.  Three moves over the proved halves:
the class lock `forkState_familyRigid` (`Orig/CrossFamily.lean:1403`)
— a fork cannot witness the OTHER color family inside the class —
delivers the FALSIFIER-FACING form `¬ (y.suit.color ≠ x.suit.color)`
(its `forkState` premises minted from the witnesses through the
trivial bridge `forkState_iff`, `Orig/PairName.lean:32`); the
CONSTRUCTIVE COLOR RECOVERY flips it by core's `Decidable.not_not` —
one theorem of `Color`'s derived `DecidableEq` instance, zero
`Classical.choice`, no Mathlib (`Orig/PairClass.lean:90`); the
SUIT-FAMILY SPLIT (`pc_suit_family`, the per-file copy) converts
the color into exactly the premise of
`forkState_family_pairClass` (`Orig/OriginLock.lean:4322`), whose
conclusion's twin-flip disjunct IS the answer.  Battery:
`[propext, sorryAx, Quot.sound]` — and the `sorryAx` is now PURELY
A LEDGER (the capstone's own glue adds no axiom).  WHAT REMAINS —
THE THREE-RESIDUE MAP:

1. **THE SEAT INDUCTION — `cross_orphan_seat`**
   (`Orig/OrphanSeat.lean:65`): a card FOUNDED at a witness
   journey's start and STANDING at its end sits face-up on some
   end-state pile, seated on a face-up BELOW-NEIGHBOR it fits under
   (the non-king premise load-bearing — a king could land bare with
   no below-neighbor at all; the full route, six steps priced, in
   the file's docstring).  THE SHARED RESIDUE two axes ride — and
   THE DEDUP THE CYCLE FORBADE: `Orig/CrossFamilyStatic.lean`
   imports `Orig.PairConfine`, so the residue could live in
   neither consumer; the hoist leaf imports only `Orig.PairName`'s
   closure, placing it BELOW both consumers, statement
   byte-frozen.
2. **THE ROAM DUAL — `conf_orphan_roam`**
   (`Orig/PairConfine.lean:2841`, PairConfine's one remaining
   seam): a non-king card SEATED on a fitting face-up below-neighbor
   at the journey's start is at the end either nowhere face-up or
   still seated on one (the seat residue's own Step-6 below-identity
   induction, restated in the roam form — dual-use).
3. **THE RE-MINT CENSUS TAIL — `pollutesCrash_rhoMover`**
   (`Orig/OriginLock.lean:3054`, the private mover dispatch under
   the card's single named residue `origin_foundedCover_pollutesCrash`):
   the ∃-mint restatement of the ρ-tail closed the FIVE MOVER FORKS down to
   the THREE LITERAL FOUNDED/COVERING CASES of the
   `pollutesCrash_rhoOpen` Bool (`:2977`) — the z-onto-mint pull
   burial closes in the dispatcher's open arm, and the residual
   family (the wash-back FOUNDED mint, the COVERED-mint burial
   slide) carries the file's two residual `sorry` calls
   (`:3134`/`:3145`), every other sub-fork closed in-body.

**THE ORPHAN-SEAT AXIS (the cross-family interlock's collapse).**
Three research-grade corner chases — the equal-rank material
competition, the consecutive/gap strata chases — collapsed to ONE
STATIC KILL, `cross_orphan_kill` (`Orig/CrossFamilyStatic.lean:185`):
the contradiction lives one stratum DEEPER than the routes chased
(not on the saturation-pinned covers but on the ORPHAN card, rank
index r₂ − 2 of the cover's suit), FOUNDED at one fork, EXILED at
the other, seated by the shared residue on a below-neighbor of the
FAR fork's family, rank r₂ − 1 — a cell the far fork's saturation
has ALREADY founded; face-up and founded cannot coexist.  No
census debt, no epoch chase anywhere in the route.
SUPERSEDED-not-deleted-history: the corner dossier stands at its
sites; CROSSFAMILY'S THREE CORNERS (`cross_equal_rank_kick`,
`cross_strata_consec`, `cross_strata_gap`) ARE ONE-LINE KILL CALLS
NOW (`Orig/CrossFamily.lean:47-51`), the axis's remaining leaf
residue being the shared `cross_orphan_seat` itself.

**THE UPWARD DOOR BYPASS (the backward-orphan route).**  The
crossing door's OSCILLATION COMPLEX — the LIFO seatCycle + freeze
family, ~1100 lines, one recorded failed attempt — was DELETED
WHOLESALE.  SUPERSEDED-not-deleted-history: the probe-graded
design record is kept at `Temp/upward_orphan_probe.lean` (the
backward-orphan read, all seams named).  The door now runs BACKWARD
OFF THE FIRING STATE: at the door state the elevated member is
FOUNDED and the firing member a bare pile TOP
(`crossing_door_exists`'s package, `Orig/PairConfine.lean:473`), so
the fork's twin-cover `d` — whose card-directed landing lattice is
exactly the pair — cannot sit face-up anywhere; zone closure (the
pinned hidden lists, the never-gaining stock/waste union) hands
`d` FOUNDED at the door, so its OWN ORPHAN (d.suit, r − 2) is
founded at the door yet EXILED at the fork (the cover pin reads
its suit two below) — and the shared residue seats it at the fork
on an (x-family, r − 1) below-neighbor whose cell the fork
SATURATES.  Contradiction.  PairConfine now rests on ONE seam
(`conf_orphan_roam`) plus the shared residue (the closed
`conf_orphan_topclash` beside it, `Orig/PairConfine.lean:2868`);
the chain `conf_door_orphan` → `crossing_door_barred` (`:3174`) →
`forkState_one_founding` (`:3210`) → the rankCeiling/samePair
corollaries (`:3243`/`:3296`) is unchanged in statement.

**THE DRAW-INERTNESS OF FORK FACTS (`Orig.SWRotInert`).**  The card
closed RESIDUE-FREE: five heads (`draw_step_canRaise`,
`drawPlayW_inert_canRaise`, `drawPlayW_inert_canRaiseS`,
`swRotW_inert_forkWitness`, `swRotW_inert_forkState` —
`Orig/SWRotInert.lean:71`/`:206`/`:213`/`:221`/`:231`), audited
`[propext]`/`[propext, Quot.sound]`.  Riding the factorization
biconditional (`sameOrbit_factor_full`, `Orig/OrbitFactorC`), the
draw component of every class journey is DEFINITIONALLY INERT to
every fork fact: THE DRAW HALF OF EVERY JOURNEY ANALYSIS VANISHES
for the fork grades.  Consumers ledgered in the file header: the
`forkState_pairClass` assembly, the mod-phase spectrum row, the
pair-fiber/bracket cards' phase-vacuity sections.

**THE EDGELABEL DEDUP — `EdgeKit`.**  The edge-label chapter's
transport kit (the board squares, the push core, the draw-frame
rows, the cycle-count census) is PUBLIC as the `EdgeKit` namespace
(`Orig/EdgeLabel.lean:2680`) — the dedup the farm markers stamped.
The ROOT-PROMOTION attempt FAILED on sibling private collisions
(same-named private variants live in sibling chapters, so flat
public names force a cross-file rename); THE NAMESPACE WAS THE
ENABLER — public rows under the owner chapter, sibling variants
untouched, the SWRotInert consume entering by `open EdgeKit` and
carrying no per-file copies.

**THE LOW-SLAB SUFFICIENCY (`Orig.LowSlab`).**  The fork's
exploration budget: every COMMITMENT out of a fork's macro class
is matched by a LOW DUPLICATE from the slab frontier — a commitment
from a class member whose covered twin is not founded, into the
same target class.  The commit-grade support rows are PROVED
zero-sorry (`fork_self_low`, `commit_exits_class`,
`commit_blocks_class_return`, with §3's setoid-exit bridge); the
routing content is ONE named residue — `fork_neighbor_lowbridge`
(`Orig/LowSlab.lean:749`), stated at the program's own commit
grain `irreversibleAt` — its audit pinning the sorryAx to its nine
priced sub-rows (`:776-781`); the TWIN-SIDE slab refinement (owner
decision 2026-10-12) rides the just-landed one-founding row so the
covered twin's side alone carries the content
(`familyBelowFrontier`, `:87`, statement byte-frozen).

COORDINATION NOTE: §12's REMAINING rows (`conjugate_swap_fires`,
`conjugate_seat_of_swap`, `conjugate_corner_notForkState`) stand
untouched — deliberately future, unchanged by this campaign.

## 14. The steered rank-first ascent — forks as fixed points of the deterministic scheduler (2026-10-17, branch `macro-game`; the owner-directed restructure superseding the every-run exhaustion head)

LANDED THIS PASS: `Orig/ForkAscentSteered.lean` — the leaf elaborates green (`lake env lean` exit 0), battery verified: the four gate instance rows at `[propext]` (raiseGate_refuses_coveredS / raiseGate_joint / raiseGate_dead / seatGate_refuses_nonjoint, one line each off the defs), the frozen candidate `steered_ascent_forks` at `[propext, sorryAx]` — exactly one `sorry`, the priced R1/R2 content, zero `Classical.choice`; probe verdicts PENDING per §14.5.

### 14.1 The steered alphabet (the two legal letters)

The raise arm carries the owner's TWIN GATE: `raiseS st c := CanRaise st c ∧ (CanRaiseS st c.twin → CanRaise st c.twin)` — raising `c` is refused exactly when the twin has a slide-future (the {slide · raise} cascade, `Orig/MacroInternal.lean:1184`) but is not raisable now: the gate protects the covered-S-live twin, precisely the `forkState` terminal's shape (`Orig.MacroInternal:1201`). JOINT PAIRS (twin raisable now) and DEAD PAIRS (no raise future) remain consumable; the gate bites only at the fork's horizon. The seat arm: `seatS st c b := fires ∧ reversibleAtW ∧ (MobileTwin st c → CanRaise st c ∧ CanRaise st c.twin)` — a pair member seats only while joint-now; non-pair cargo slides stay unrestricted.

### 14.2 The rank-first scheduler — `the` trajectory

Smallest rank first (`SteeredFirst`: the head is rank-minimal among steered-legal letters); within a rank the universe tie-break is R3's priced refinement. The model is Canonical's saturator (`satStep`/`pick`/`canonAux`, `Orig/Canonical.lean:1480-1493`) but RANK-MAJOR where `satStep` is universe-order; ties land exactly at twin pairs (same rank by construction), where the steer already speaks. Consequence, as a property not a quantifier: "every maximal run" collapses to "the" trajectory; the `fa0` multi-pair and `fcS`/`fcH` twin-contention branch pathologies become fixed-point properties of the one stepper.

### 14.3 The frozen candidate theorem

From a `WF` state below a reachable fork's frontier (the old head's premise, VERBATIM — `hbelow` was never the error), every steered trajectory to `SteeredStuck` exhausts AT a `forkState` (the S-grade detection); the manifested fork is one licensed leg away through the banked β-companion (`ascent_cover_pullback`, `ascent_rec_base_of_iff`, `ExhaustShapeRec` — all PROVED in ForkAscent; the exhaustion-shape ceiling `ascent_exhaust_shape_impossible` does not bite this terminal: its cover is the aftermath's first licensed leg, not a standing conjunct).

### 14.4 The residue ledger (each priced)

- (R1) TRAJECTORY LOYALTY — the reachable fork's witness path must be compatible with the steered trajectory; the parking/climb is order-forced by the rank spine (the old `ascent_climb_delivery`/`ascent_frontier_parking` content restated with new leverage). [H, the route's real load]
- (R2) THE TERMINAL CENSUS — a `forkState` admits no steered letter: raises self-refuse (the twin gate), pair seats self-refuse (joint clause); the residue is the third-card cargo census (fa2-class decide content; the fa3 resurrection channel's seating legs are steered-illegal; the fa1 member-liveness half is steered-forced by construction). [H-mini, decide-gradable]
- (R3) THE DECIDABLE BRIDGE — the `Bool` face of `CanRaiseS` (consume `Orig/ForkStateS`'s flat `canRaiseS_iff`) plus the within-rank universe tie-break; the stepper's function-grade and the probe re-verdicts ride it. [M]

### 14.5 Probe-first before freeze-consumption

In order: `fa2` legality (a forkState terminal stands as a legal steered-stuck world), `fa3` (the resurrection needs a steered-forbidden leg), `fa0` (multi-pair under determinism), `fcS`/`fcH` (contention splits die under the scheduler). Probes decide, proofs follow; any fired falsifier re-prices the residues before freeze.

### 14.6 Supersession and retirement plan

The old head keeps its standing — vacuity-or-false (the ceiling squeeze), its four sorries frozen as impossibility manifests — until the retirement pass: bank the in-flight ForkAscent arc, migrate the census buckets (vocabulary/toolkit/β-companion/fence-boards) into `Orig.ForkAscentSteered.lean`, rewire `Orig.ForklessCeiling`'s import, certify the cone, and retire the old leaf by its own commit (CHALLENGES truespeak carries the verdicts: the vacuity-never-decided status, the ceiling squeeze mechanism, the named residues' fates). House compliance: additive, no mathlib, zero `Classical.choice`, decide-grade probes with gates throwing on failure, `#print axioms` per fresh head, frozen statements byte-stable, HOT in-flight files untouched this pass.
