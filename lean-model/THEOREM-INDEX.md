# THEOREM INDEX — the proven library (2026-10-13)

A lookup aid, not an API doc. Names are the stable search keys — `grep
"theorem NAME"` jumps to the statement; grades are `#print axioms`
readings from the home batteries (all entries PROVEN, zero sorryAx;
`[propext]`/`[propext, Quot.sound]` is the house terminal grade).
Scope: the certified core (the pairClass cone) plus its public kits.
Open, priced, and refuted rows live in **CHALLENGES.md** — this file
indexes the proved library only.

## 0. AT A GLANCE (names by section — grep these)

- §1 capstone & invariants: forkState_pairClass, forkState_family_pairClass,
  forkState_family_rankFloor, forkState_rankDrop_locked,
  forkState_familyRigid, forkState_sameFamily_samePair,
  forkState_sameFamily_rankCeiling, forkState_one_founding,
  pair_lowFamily_founded, forkState_iff, forkState_pairUnique,
  forkState_nameUnique, forkState_witness_rungs,
  forkState_orientationUnique
- §2 exile laws: exodus_seating_census, ForkKit.fork_nextUpExile_crash,
  cross_orphan_seat, Below_stable, orphan_found_exodus
- §3 height: FoundKit.mem_found_iff_height, FoundKit.mem_found_of_rung,
  FoundKit.mem_found_rank_lt (+ posOf/get_in_take/upCards kit),
  mem_found_of_height, wf_foundRung_iff, WF.found_prefix,
  rung_found_prefix, rung_found_congr
- §4 card algebra: SeedKit.color_pair, SeedKit.rankColor_pair,
  SeedKit.suit_family, SeedKit.runOK_adjacent_fit, canSitOn_eq,
  below_aboveIn_split
- §5 fork cells: canRaiseS_iff, canRaiseS_rung, canRaiseS_free,
  canRaiseS_iff_or, canRaiseS_positionSeat, canRaiseS_runOrTwin,
  forkState_pins, forkState_pairS, forkState_twinBlocked,
  forkState_of_parcel, forkState_to_weak,
  forkState_witness_canRaise, forkStateSB_true_iff, forkWitnessB,
  forkWitness, forkWitness_sound
- §5b fixity & transport: cargoPath_rungs, cargoPath_class,
  conjugate_endpoint_netflat, conjugate_endpoint_witness,
  forkSpectrum_rungsFlat, forkSpectrum_keepsPhase
- §5c slab-forms: twin_slab_tableau, slabForms_split,
  slabForms_inclass, slabForms_bothFounded_barred
- §6 journeys: step_wf, witness_rung_census, witness_tuple_census,
  pull_factor, raise_factor, quiet_flat, sameOrbit_forward, RevEqW_sameFate,
  reversibleAtW_iff_reversible (also §13), foundToTab_pops_currentTop
  (+tabToFound_tops_currentSuit, keepsOtherTops), shuttle_join
- §7 zone discipline: mem_faceUp_only, mem_pile_unique,
  mem_faceUp_unique, mem_found_unique, witness_stockWaste_closed,
  cycle_zone_pin, plus the origin-lock kit (dress_legalSeats_pair,
  origin_dresser_frozen/_isolated, origin_lowerJourney_pulls,
  lower_sandwich, origin_lowerPairResident); §7b measures:
  cycleCount_step, hiddenTotal_step, foundTotal_step,
  foundTotal_step_noworry, stepDraw_cycle
- §8 computable faces: conjugateForkStateS, conjugateForkStateS_correct,
  conjugate_forkState_corrected
- §9 zone-census loop: mates_cycleZone_pin, class_zoneAgree_iff,
  wf_foundRung_iff, forkState_class_zoneSets (+rungVec/founds/foundRes/
  tabRes), interleave_phase_align, cross_orphan_kill
- §10 symmetry calculi: State.twin_step, twin_fate,
  WinFrom_swapPiles_iff, State.exchangeTwin_invol
- §11 canonical fiber: canon_class, win_iff_canon, canonQ_of_orbit,
  same_macro_iff', comm_draw_canon, canon_twinMap, exch_le_sameOrbit,
  canonQ_of_physOrbit', orbit_data, draw_landings_sameOrbit,
  sameOrbit_cycleCount
- §12 combinatorics: irr_of_desc/_asc, invariant_of_initialReachable,
  pigeonhole_le, step_congr_board, shuttle_join (also §6)
- §13 doctrine: reversibleAtW_iff_reversible, irreversible_iff_of,
  win_iff_macro, rung_found_congr
- §14 census ledger & dominance: witness_leg_letters,
  play_census_ledger, roundtrip_census_repay,
  excursion_issues_noNewSeat, commit_exits_class,
  lowslab_pull_wf_undo, lowslab_pull_never_commit_wf,
  draw1_sameCycle_sameFate, wastePark_restack, ground_diamond_raise,
  mem_upCards_take

## 0.5 QUICK ROUTES (need → cite)

- "Is card c on its own foundation?" → FoundKit.mem_found_iff_height (§3)
- "Which cards sit below the fork rank?" → pair_lowFamily_founded (§1)
- "A suit's rung dropped along a journey" → exodus_seating_census (§2)
- "Impossible fork at the end state" → ForkKit.fork_nextUpExile_crash (§2)
- "Residency flips along a witness play" → cross_orphan_seat (§2)
- "Below-forkstate, physically vs arithmetically" → twin_slab_tableau (§5c)
- "Do class-mates agree on zones?" → mates_cycleZone_pin +
  class_zoneAgree_iff (§9); "same founds ⟺ same rungs?" →
  wf_foundRung_iff (§9, no class premise!)
- "Count cells / bound seats" → pigeonhole_le (§12)
- "This move is irreversible" → irr_of_desc + the measure tables (§7b, §12)
- "Draws behave within a class" → draw_landings_sameOrbit +
  comm_draw_canon (§11)
- "Move to the saturated form" → canon_class (§11)
- "Twin-blindness / relabel" → twin_fate (§10)
- "Verdicts in one class coincide" → RevEqW_sameFate (§6)
- "Decidable fork detection" → forkWitnessB / forkStateSB_true_iff (§5, §8)

## 1. The capstone and the class invariants

- **`forkState_pairClass`** — `Orig/PairClass.lean` —
  `[propext, Quot.sound]`
  `(st₁ st₂) (hwf₁ hwf₂) (hcls : sameOrbitSetoid.r st₁ st₂) (x hx)
  {y} (hy : ForkWitness st₂ y) : y = x ∨ y = x.twin`.
  THE no-lock theorem: within one macro class, ANY two forks agree as
  pairs — no family hypothesis assumed. Use whenever you need "same
  class ⇒ same pair" in one line.
- **`forkState_family_pairClass`** — `Orig/OriginLock.lean` — the
  family-premise half (floor/ceiling sandwich forces equal rank, then
  `forkState_sameFamily_samePair`). `forkState_family_rankFloor` and
  `forkState_rankDrop_locked` are its engine rows (the origin lock:
  a same-class same-family fork cannot witness a LOWER rank).
- **`forkState_familyRigid`** — `Orig/CrossFamily.lean` — the
  cross-family half: one class cannot host forks of both color
  families (falsifier-facing `¬ (y.suit.color ≠ x.suit.color)`).
- **`forkState_sameFamily_samePair`** — `Orig/PairConfine.lean` —
  `[propext]`
  `{x y} (hys : y.suit = x.suit ∨ y.suit = x.twin.suit)
  (hrank : y.rank.toIdx = x.rank.toIdx) : y = x ∨ y = x.twin`.
  The bare card-naming lemma: suit family + rank pin name the card.
- **`forkState_sameFamily_rankCeiling`** — `Orig/PairConfine.lean` —
  the ceiling half of the sandwich.  **`forkState_one_founding`** —
  same file: the one-founding row (the low-slab refinement's engine;
  consumed by LowSlab and SlabForms).
- **`pair_lowFamily_founded`** — `Orig/PairConfine.lean` —
  `[propext, Quot.sound]`
  `(hwf) (hx : ForkWitness st x) (hcol : c.suit.color = x.suit.color)
  (hlt : c.rank.toIdx < x.rank.toIdx) : c ∈ st.found c.suit`.
  THE below-fork census: every family card strictly under the fork
  rank is foundation-resident. The fuse of the static kills
  (`cross_orphan_kill`, `ForkKit.fork_nextUpExile_crash`,
  `exodus_seating_census`); pair with `FoundKit.mem_found_iff_height`
  to move between "founded" and "under the rung" freely.
- **`forkState_iff`**, **`forkState_pairUnique`**, **`forkState_nameUnique`**,
  **`forkState_witness_rungs`**, **`forkState_orientationUnique`** —
  `Orig/PairName.lean` — the trivial bridge and the naming pins.
  `ForkWitness` itself is defined here (`ForkWitness st x`: the pair
  cell membership — pair-select liveness + twin saturation).
  **Intra-state witness uniqueness, both strengths**: S-package —
  `forkState_pairUnique` names the pair up to the twin flip (any two
  witnesses of one state are twins); bare-select —
  `forkPair_not_twoColors_state` / `forkPair_not_twoRanks_state`
  (`Orig/ForkStateUniq.lean`) pin the witness to *equality* and bar
  two-color / two-rank cohabitation at one state, four lines each.
  The naive unique-card version of the S-package is REFUTED on
  record (`forkState_unique_refuted` — see CHALLENGES.md).

## 2. The exile laws (tonight's engine: reuse these before re-deriving)

- **`exodus_seating_census`** — `Orig/OriginLock.lean` —
  `[propext, Quot.sound]`
  `(hwf₁) (hτ : ShufflePlayW st₁ τ st₂) (σ) : ∀ r, rungAt st₂ σ ≤
  r.toIdx → r.toIdx < rungAt st₁ σ → r ≠ king → ∃ a b, (Card.mk σ r)
  ∈ (st₂.piles a).faceUp ∧ b ∈ … ∧ canSitOn (Card.mk σ r) b`.
  THE interval law: a dropped rung exiles and SEATS its whole upper
  interval. The fit pins neighbor rank `i+1`, so width `w` forces `w`
  distinct opposite-color face-up cells — cell-counting replaces
  card-chasing against a saturated lattice.
- **`ForkKit.fork_nextUpExile_crash`** — `Orig/OriginLock.lean` —
  `[propext, Quot.sound]`
  `(hwf₁ hwf₂) (hy : ForkWitness st₂ y) (hplay) {d} (hd : d.ridx+1 =
  y.ridx) (hdcol) (hsq1) (hsq2) : False`.
  The static kill, ∃-premise-free: a fork at the end + an off-family
  cover card with the two-end rung squeeze is impossible. Cite when
  a corner needs "the third cell is census-full".
- **`cross_orphan_seat`** — `Orig/OrphanSeat.lean` —
  `[propext, Quot.sound]`
  `(hwf) (hτ) {e} (hnk) (hmem : e ∈ st.found e.suit)
  (hout : e ∉ st'.found e.suit) : ∃ a b, e ∈ (st'.piles a).faceUp ∧
  b ∈ … ∧ canSitOn e b`.
  The base law: a foundation-residency flip along a witness shuffle
  forces a fitted face-up seat at the end.
- **`Below_stable`** — `Orig/OrphanSeat.lean` — `[propext, Quot.sound]`
  The zone-transport: `(founded ∨ Below-seated)` is invariant per
  non-king card along witness journeys.
- **`orphan_found_exodus`** — `Orig/OrphanSeat.lean` —
  `[propext, Quot.sound]`
  The exodus wheel: a founded card that leaves its foundation departs
  through its own literal `foundToTab` pull leg (the leg extractor
  the seat rows ride).

## 3. Foundations and height (`FoundKit` + the rows beneath)

- **`FoundKit.mem_found_iff_height`** — `Orig/FoundKit.lean` (the
  shared-kit LEAF, stratum beside the kernel) —
  `[propext, Quot.sound]`
  `(hwf) {c} : c ∈ st.found c.suit ↔ c.rank.toIdx < st.foundHeight c.suit`.
  THE founding bridge, one line. Half-rows `FoundKit.mem_found_of_rung`
  / `FoundKit.mem_found_rank_lt`; the full kit also owns `posOf`,
  `posOf_take_lt`, `posOf_upCards`, `get_in_take`, `upCards_get`,
  `mem_take_of_pos`, `mem_of_take`, `mem_of_drop`, `found_suit`,
  `Rk` + `Rk_toIdx` (the rank-maker), `take_len_le`, `rung_le`,
  `take_ge_len` (take saturation), `found_congr` (equal heights ⇒
  equal content), `shuffle_wf` (journeys preserve WF), `zone_residency`
  (five-zone census), `dealUpTo_mem` + `_take`/`_drop` (the deal
  splitter).  The tree's founding physics has ONE home.
- **`mem_found_of_height`** — `Orig/Dominance.lean` — the public
  forward half (historical home; `rungAt = foundHeight` by `rfl`).
- **`WF.found_prefix`** — `Orig/Integrity.lean` — the canonical
  prefix: `st.found s = s.upCards.take n` — everything height-related
  bottoms out here.
- **`rung_found_prefix`** — `Orig/MacroInternal.lean` — the take-form
  read used by the bridge proofs.

## 4. Card algebra (`SeedKit` + the fit rows)

- **`SeedKit.color_pair`** — `Orig/RunOrTwin.lean` — `[propext]`
  `{a u v : Color} (h1 : a ≠ u) (h2 : a ≠ v) : u = v` — the two-color
  trichotomy.  **`SeedKit.rankColor_pair`** — equal rank + equal color
  name the card up to the twin flip.  **`SeedKit.suit_family`** —
  shared color names the suit up to the twin flip.
- **`SeedKit.runOK_adjacent_fit`** — `[propext]`
  `runOK (X ++ c :: d :: R) = true → canSitOn d c` — anywhere in a
  legal run, an adjacent pair fits.
- **`canSitOn_eq`** — `Orig/Basic.lean` — the fit iff:
  `canSitOn c b = true ↔ c.ridx + 1 = b.ridx ∧ c.color ≠ b.color`.

## 5. Fork cells and saturation

- **`canRaiseS_iff`** — `Orig/ForkStateS.lean` — `[propext, Quot.sound]`
  The pair-select saturation: at a WF state with a live pair member,
  `CanRaiseS` holds exactly for the pair (the third-card ban).
  Companions: `canRaiseS_rung` (the rung pin off `ForkWitness`),
  `canRaiseS_free` (the covered-card license), `canRaiseS_positionSeat`
  (PositionSeat), `canRaiseS_runOrTwin` (RunOrTwin).
- **`forkState_pins`**, **`forkState_pairS`**, **`forkState_twinBlocked`**,
  **`forkState_of_parcel`** — `Orig/ForkStateS.lean` — the cell pins.
- **`forkWitnessB` / `forkWitness` / `forkWitness_sound`** —
  `Orig/ConjugateProof.lean` — the DECIDABLE pair cell (`Bool`) and
  the sound Option search over `Card.universe`.
- **Journey-kind bans** — `Orig/ForkStateUniqGate.lean`
  (all battery `[propext, Quot.sound]`-band):
  `journey_never_wasteToFound`, `journey_never_wasteToTab`,
  `journey_tabToFound_never_reveal`, `journey_tabToTab_never_reveal`,
  `journey_raise_shape`, `journey_raise_seatUnfounded` — what a
  witness journey can never contain; plus
  **`shuffle_hiddenPinned`** (the hidden-zone pin) and
  **`forkState_unique_refuted`** / `forkState_content_of_rungsAgree`
  (the uniqueness family).
- **`canRaiseS_iff_or`** — `Orig/ForkStateS.lean` —
  `[propext, Quot.sound]`
  The readable disjunctive license:
  `CanRaiseS st c ↔ CanRaise st c ∨ (nextUp ∧ SeatOK ∧ coveredIn ∧
  pileOfTop c.twin ≠ none)` — the fastest route for hand census
  proofs at crafted states (the phase falsifier's own engine).
- **`forkState_to_weak`** — `Orig/ForkWeaker.lean` —
  `[propext, Quot.sound]`
  `forkState st → weakForkState st` with the same witness, rung pins
  traveling free — connects S-grade detection to the whole weak-class
  book (mate, conjugation, spectrum) in one cite.
- **`forkState_witness_canRaise`** — `Orig/ForkWeaker.lean` —
  `[propext, Quot.sound]`
  The two-conjunct parcel alone forces `CanRaise st x` for the
  uncovered member — the covered-twin geometry engine behind the
  pins, orientation uniqueness, and mate liveness.
- **`forkStateSB_true_iff`** — `Orig/ForkStateSB.lean` — battery-clean,
  kernel-decidable
  `forkStateSB st = true ↔ forkState st` — the whole S-parcel as an
  executable census (zero Classical); `forkWitnessSB_sound` hands
  back the verified witness.

## 5b. Cargo transport and the fixity laws

The cargo-transport cluster (`Orig/ForkStateUniq.lean`,
`Orig/ForkSpectrumProof.lean` — `cargoPath_foundCongr`, `cargoPath_class`,
`cargoPath_sameClass`, `cargoPath_keepsPhase`, `kingVacWalk_cargoPath`,
and the non-vacuity embeddings `faceShape_spectrum`, `slidMate_spectrum`,
`kingVacWalk_spectrum`) is uniformly fully proved — cite the family
rather than re-deriving:

- **`cargoPath_rungs`** — `Orig/ForkStateUniq.lean` —
  `[propext, Quot.sound]`
  `CargoPath st w → ∀ s, rungAt w s = rungAt st s` — the rung-fixity
  law under every reversible tableau slide (feeds `canRaiseS_rung`'s
  via-leg and both uniqueness falsifiers).
- **`conjugate_endpoint_netflat`** — `Orig/ForkStateUniq.lean` —
  `[propext, Quot.sound]`
  A firing raise–slide–pull composite is net-flat:
  `∀ σ, w.found σ = st.found σ` (loose `∃ d` shape — covers the
  corrected composite verbatim).
- **`conjugate_endpoint_witness`** — `Orig/ForkStateUniq.lean` —
  `[propext, Quot.sound]`
  The composite's raiser IS the iff-named witness (`y = x`) — the pin
  separating the conjugate composite from the mate.
- **`forkSpectrum_rungsFlat`** — `Orig/ForkSpectrumProof.lean` —
  battery-clean
  `ForkSpectrum st w → ∀ σ, rungAt w σ = rungAt st σ` — the
  height-tuple fixity over the whole generator closure; any
  rung-stated invariant transports along the spectrum for free.
- **`forkSpectrum_keepsPhase`** — `Orig/ForkSpectrumProof.lean` —
  battery-clean
  `ForkSpectrum st w → w.waste = st.waste ∧ w.stock = st.stock ∧
  w.drawStep = st.drawStep` — the phase-fixity invariant beside the
  tuple; any phase-sensitive completeness repair consumes this.

### 5c. The slab-forms equivalence: below-forkstate in two languages

"Beneath a fork" has TWO equivalent definitions — a physical one and
an arithmetical one — and the whole low-duplicate program lives on
the border between them:

- **Def A (residency)**: the twin witness still exists in the
  tableau — `∃ a, x.twin ∈ (w.piles a).faceUp ∨
  x.twin ∈ (w.piles a).hidden`.
- **Def B (height)**: the twin suit's foundation hasn't climbed past
  the fork rank — `rungAt w x.twin.suit ≤ x.rank.toIdx`
  (the twin shares `x`'s rank; "≤ x's rank" IS "at-or-below the
  fork rank").

- **`twin_slab_tableau`** — `Orig/SlabEquiv.lean` — fully proved
  (the leaf's single ticket-free landing, `[propext]`-band) —
  **Def A ⟺ Def B** at WF endpoints of a witness journey with the
  twin tableau-resident at the origin. The three-step why: the twin
  is somewhere (WF conserves the deck) → not in stock/waste
  (`cycle_zone_pin`) → not founded ⟺ `¬(rank < rung)`
  (`FoundKit.mem_found_iff_height`) — tableau-residency is the
  leftover zone. USE WHEN: you need to trade a 7-pile × two-surface
  existential SEARCH for a decidable `≤`-check, or back — seat and
  landing proofs want the tableau side; census and height proofs
  want the rung side.
- **`slabForms_split`** — `Orig/SlabForms.lean` — the definitional
  split of `familyBelowFrontier` (the twin-side refinement at
  `Orig/LowSlab.lean:87`, byte-frozen under def-refinement).
- **`slabForms_inclass`** — `Orig/SlabForms.lean` — the in-class
  iff: `familyBelowFrontier d x ↔ both-suits ∨ (x-founded ∧
  twin-on-tableau)` — the class-level statement of the equivalence.
- **`slabForms_bothFounded_barred`** — `Orig/SlabForms.lean` — the
  both-founded difference-shape corollary. All three ride
  `forkState_one_funding` — the pairClass certification pays
  directly into the slab border.
- **`forkState_mate_inClass`**, **`forkState_slide_mate`**,
  **`kingVacate_reversibleW`** — `Orig/ForkStateUniq.lean` — the slide
  mate and the king-vacate witness leg.

## 6. Journeys and the census

- **`step_wf`** — `Orig/Reach.lean` — WF travels one leg; iterate for
  whole journeys (per-file `*_shuffle_wf` wrappers induct on it).
- **`witness_rung_census`** — `Orig/BracketDecomp.lean` —
  `[propext, Quot.sound]`
  The per-suit balance along a witnessed shuffle:
  `rungAt end σ = rungAt start σ + raisesOf − pullsOf`.
  Tuple twin: `witness_tuple_census`. One-leg factors:
  `pull_factor`, `raise_factor`, `quiet_flat`.
- **`sameOrbit_forward`** — `Orig/BracketDecomp.lean` — `[propext]`
  The class's forward witness play extractor (same-class hands you
  the all-reversible play between the states).
- **The LIFO stack laws** — `Orig/BracketDecomp.lean` —
  `[propext]`-grade row quartet:
  `foundToTab_pops_currentTop` (`step st (foundToTab c b) = some s' →
  st.foundTop c.suit = some c`), dual `tabToFound_tops_currentSuit`,
  and the `…_keepsOtherTops` pair — the pull/raise discipline read
  straight off the step guard; every bracket/pull argument starts
  here.  **The step-inversion families** — `Orig/Irreversible.lean`:
  the public quintet `step_tabToFound_inv` / `step_foundToTab_inv` /
  `step_tabToTab_inv` (placement-grade existentials) PLUS the
  HEAD-grade pair `step_wasteToFound_inv_head` /
  `step_wasteToTab_inv_head` (separated guards and PINNED waste head
  — the conclusion the existential grade never carries; promoted
  from Dominance 2026-10-13) and public `step_draw_inv`
  (`Orig/Reach.lean`, the definitional alias) — cite the grade the
  destructure needs; the head-grade is strictly stronger.
- **`interleave_phase_align`** — `Orig/HostCensus.lean` — the
  interleave crossing's zero-own-content assembly (rides
  `draw_landings_sameOrbit`); byte-frozen statement for the LowSlab
  import.

## 7. Zone discipline (the exclusivity rows)

- **`mem_faceUp_only`** — `Orig/Integrity.lean` — a card occupies one
  zone; the `.2.2.2.2` projection is the founded-yet-face-up kill.
  The engine beneath the whole exclusivity pack is
  **`mem_pile_unique`** (same file): one pile seating pins the card
  absent from every other pile, zone, and foundation — cite it
  directly when the packaged projections do not fit.
- **`mem_faceUp_unique`** / **`mem_found_unique`** — `Orig/Integrity.lean`
  — per-card pile-membership uniqueness (the face-up/founded disjoint
  projections live here).
- **`witness_stockWaste_closed`** — `Orig/OriginLock.lean` —
  a card in stock-or-waste at both ends stays put over witness
  journeys (the origin-lock residency arm).

### 7b. Monotonicity and measure tables (`Orig/Irreversible.lean` —
zero-sorry module, [propext]-band)

All WF-PREMISE-FREE: `(h : State.step st m = some s') : Q s' ≤ Q st`.

- **`cycleCount_step`** — no legal single step ever raises `cycleCount`
  (stock+waste) — the constructor-uniform table under every "waste
  moves can never ride a witness journey" argument.
- **`hiddenTotal_step`** — no legal single step ever raises
  `hiddenTotal` (the piles' face-down count) — the reveal-side measure
  table; its strict `…_reveal` cells are the reveal-lock.
- **`foundTotal_step`** / **`foundTotal_step_noworry`** — any legal
  step keeps `foundTotal` non-increasing, and any step that is not a
  `foundToTab` keeps it ≤ — the cleanest one-liners for "only pulls
  take from foundations" and the no-worry monotone forms.
- **`dress_legalSeats_pair`**, **`origin_dresser_frozen`**,
  **`origin_dresser_isolated`**, **`origin_lowerJourney_pulls`**,
  **`lower_sandwich`**, **`origin_lowerPairResident`** —
  `Orig/OriginLock.lean` — the origin-lock kit (the dress/lattice
  machinery; cite before re-deriving seat lattices at forks).

## 8. Computable faces

- **`conjugateForkStateS` / `conjugateForkStateS_correct`** —
  `Orig/ConjugateProof.lean` — the TOTAL computable conjugation
  function (identity-or-conjugate, zero Classical) with its
  correctness row.  **`conjugate_forkState_corrected`** — the
  corrected conjugation theorem, `[propext, Quot.sound]`.

## 9. The zone-census loop (home: `Orig/ZoneAgree.lean`, the
census-stratum leaf + the fork-grade rows in `Orig/PairClassZones.lean`)

At WF class-mates the three census readings are ONE equivalence —
tableau sets ⟺ foundation sets ⟺ rung vectors — with the cycle side
pinned outright, and two legs of the loop do not even need the class:

- **`mates_cycleZone_pin`** — cycleRes iff for ANY class-mates
  (fork-free, no WF): the class relation's only load-bearing census
  work.
- **`class_zoneAgree_iff`** — same tableau set ⟺ same foundation set
  at any WF class-mates (mutual complements of the pinned cycle
  side; stated ∀-owner's draft as landed at 25852a8).
- **`wf_foundRung_iff`** — same foundation set ⟺ same rung vector at
  ANY TWO WF STATES — the boundary-card argument (the smaller rung's
  `Rk`-constructed index card founded at the larger-rung state by the
  upward bridge, pushed home by the agreement, refuted by the
  downward bridge); foundations speak for themselves, no class
  premise.
- **fork-grade family**: `forkState_class_zoneSets` and friends
  (`_rungVec` → `_founds` → `_foundRes` → `_tabRes`) — same-class
  canonical forks agree on EVERYTHING, with the third-suit rung
  agreement carried as the named `hthird` premise (the
  `canonFace_sameShape` sandwich cell — open, see CHALLENGES.md).
  When you only need the fork cells themselves, cite the
  unconditional trio: `forkState_witness_rungs`,
  `pair_lowFamily_founded`, `FoundKit.mem_found_iff_height`.
- Interleave — **`interleave_phase_align`** (`Orig/HostCensus.lean`;
  companions `step_congr_board`, `board_run_congr`,
  `drawfree_commute_reach`/`_witness`, `chain_assembly`,
  `interleave_leg_conjugation`).
- Cross-family static — **`cross_orphan_kill`**
  (`Orig/CrossFamilyStatic.lean`; `[propext, Quot.sound]`, inherits
  NOTHING).
- **The parent grammar** — `Orig/ParentMap.lean` (landed `21c047b`;
  heads `[propext, Quot.sound]`, the inr arm + CargoPath induction
  in flight): `tabParent_fits` (a seated card's parent fits it),
  `parent_pool` (a card's legal tableau parents are exactly a twin
  pair), `parent_twinHop` (WF states agree equal-or-twin on a card
  seated at both — pure deck arithmetic), `twinHop_iff_memAgree`
  (the crystallization: twin-hop at WF ⟺ parent-existence
  agreement, so all distinguishing content lives in the whitelist),
  `cargoLegKing_twinHop` (reversible bare-king relocation preserves
  the parent map exactly).  USE WHEN: an exchange/cargo corner
  needs the parent-map conservation instead of re-deriving which
  seats a card may lawfully occupy.
- **The fork detector** — `Orig/ForkCensus.lean` (landed zero-sorry
  at `76389fc`): `classCensusB_true_iff` and the
  pairCandidate-witness composite `[propext, Quot.sound]` — the
  DECIDABLE fork-in-class detector over the mobility filter and
  sealed-pin rows; the machine-executable answer to "is there a
  fork here?"

---

## 10. The symmetry calculi (`Orig/Twin.lean`, `State.lean`, `TwinExchange.lean`)

Three complete involution packages — cite the calculus, not the case split:

- **Twin relabeling**: `State.twin_step` —
  `(st.step m).map State.twinMap = st.twinMap.step m.twinMove` — the
  step-conjugation every twin-symmetry argument builds on;
  **`twin_fate`** — `WinFrom s ↔ WinFrom (State.twinMap s)` — the
  off-the-shelf verdict symmetry (through it: `twin_quotient`,
  `sameFate_twin`). Generator rows: `State.twinMap_twinMap`,
  `Move.twinMove_twinMove`, `Card.twin_inj`, `canSitOn_twin_twin`.
- **Pile transposition**: `State.step_swapPiles` +
  `WinFrom_swapPiles_iff` — the anchor-permutation symmetry.
- **Exchange twin**: `State.exchangeTwin_invol` / `_comm` — the
  corner-swap involution (completes with the `exch_*` torsor block,
  §11).  Run-splitting kit (TwinExchange.lean):
  **`below_aboveIn_split`** — `t ∈ l → l = below t l ++ t ::
  aboveIn t l` (`below_not_mem`, `fromCard_eq_of_mem`,
  `runOK_append_exact`) — the standard first cut of any
  exchange/seat proof.

## 11. The canonical fiber and the macro verdict (`Orig/Canonical.lean`,
`Orig/TwinExchangeQuotient.lean`, `Orig/EdgeLabel.lean`)

- **`canon_class`** — `(hwf) : RevEqW u (canon u)` — the single
  bridge from a state to its saturated form, inside the same
  reversible orbit.  **`win_iff_canon`** — the verdict tie via one
  `RevEqW_sameFate` hop.  **`canonQ_of_orbit`** — same-class states
  have EQUAL canon-images — the uniform fiber spine.
- **`same_macro_iff'`** — `⟦u⟧ = ⟦v⟧ ↔ ⟦canon u⟧ = ⟦canon v⟧` (the
  decidable one-comparison class test; the accountant twin
  `same_macro_iff` plus `swComp_of_orbit` supplies its residue).
- **`comm_draw_canon`** — canon and draw COMMUTE with equal results
  (no WF gate; `draw_fire_sync_canon` for the none side);
  **`canon_twinMap`** — the canonicalizer is twin-conjugated.
- **Exchange torsor block** (`TwinExchangeQuotient`):
  `exch_leg_RevEqW`/`exch_chain_RevEqW`/`exch_le_sameOrbit` (licensed
  exchanges fold into the witness world), `canonQ_of_physOrbit'` +
  `physEq_wf` (shuffles ∪ exchanges sit in ONE macro state,
  single-gated), `ExchOrbit.mk_eq_mk`/`exact`/`exch_superpose`/
  `exch_free`/`twinExchOK_exchAll`, `PhysEq refl/shuffle/exchange/trans`.
- **The class-invariant datum bundle** — `Orig/EdgeLabel.lean`:
  **`orbit_data`** — a same-class mate preserves WF, `cycleCount`,
  `drawPool`, per-pile hidden and `nzRoot` (packaged as
  `SameDatums`/`sameDatums_class`, lifted by `MacroDatums.of_class`)
  — "what a macro class cannot change", in one cite.
- **`draw_landings_sameOrbit`** — the draw is a well-defined class
  map: clique-mates draw together, land class-mates (companions
  `sameOrbit_cycleCount`, `draw_successor_unique`, `drawNext_sound`).

## 12. Measures, induction combinatorics, and generic counting

- **`irr_of_desc` / `irr_of_asc`** — `Orig/Mono.lean` —
  supply ANY `Q : State → Nat` non-increasing over steps with a
  strict one-step drop, read full `irreversibleAt` in one line —
  the measure-to-commitment converter, card-rules-free.
- **`invariant_of_initialReachable`** (`+R` recurrence twin,
  `initialReachableR_iff`) — `Orig/Reach.lean` — the generic
  induction combinator for fences/conservation over the reachable
  fragment.
- **`pigeonhole_le`** — `Orig/Encode.lean` —
  `allDistinct l → (∀ x ∈ l, x ∈ t) → l.length ≤ t.length` — the
  GENERIC cell-count cap (any type); the counting law the exodus
  census's fit-pinning feeds (`wf_zone_le : ≤ 52` included).
- **`RevEqW_sameFate`** — `Orig/Combine.lean` — macro-class mates
  share verdicts (`RevEqW s s' := ShufflePlayW both ways`) — the
  well-definedness license for every in-class verdict argument
  (setoid restatement `sameFate_orbit`).
- **`step_congr_board`** — `Orig/HostCensus.lean` — board letters
  are zone-blind: replay any board move on a board-equal mate with
  equal results (`board_run_congr` keeps the phase verbatim) — the
  engine behind the drawfree commutations.
- **`shuttle_join`** — `Orig/Shuttle.lean` — two legal landings of
  one rung-ready waste top are joined by an explicit two-move
  foundation round trip — the ready-made join witness for
  seat-choice forks.

## 14. The census ledger, zone pins, and dominance facts

- **`cycle_zone_pin`** — `Orig/SlabEquiv.lean` — `[propext, Quot.sound]`
  Along a witness shuffle, stock-or-waste membership is an IFF —
  the drop-in zone-closure line for any per-card trace (the public
  `mates_cycleZone_pin` and the ForkStateUniqGate bans ride it).
- **`twin_slab_tableau`** — `Orig/SlabEquiv.lean` — see §5c for the
  full treatment: the tableau ⟺ height equivalence underpinning the
  whole low-duplicate program.
- **`witness_leg_letters`** — `Orig/HostCensus.lean` —
  `[propext, Quot.sound]`
  The journey alphabet: any reversible leg is draw, `tabToFound`,
  `foundToTab`, or `tabToTab` — waste letters NEVER ride; kills two
  move kinds at the head of every journey induction.
- **`play_census_ledger`** — `Orig/HostCensus.lean` —
  `[propext, Quot.sound]`
  The exact per-cell pile-top inventory telescoped over ANY
  successful play: `hostCensus w + journeyBurn = hostCensus st +
  journeyMint` per column/row; corollaries
  `roundtrip_census_repay`, `excursion_issues_noNewSeat`, closed by
  `witness_leg_mint_confined`.  The draw-commutation kit around the
  indexed `interleave_phase_align` (companions `board_run_congr`,
  `drawfree_commute_reach`/`_witness`, `chain_assembly`,
  `interleave_leg_conjugation`) completes the census chapter.
- **`stepDraw_cycle`** — `Orig/Irreversible.lean` —
  `st.stepDraw = some s' → cycleCount s' = cycleCount st` — the
  draw's epoch-conservation law.
- **`sameOrbit_cycleCount`** — `Orig/EdgeLabel.lean` — the cycle
  count is a CLASS INVARIANT (a class draws together or not at all).
- **`commit_exits_class`** — `Orig/LowSlab.lean` — banked-chain clean
  `step u m = some v → irreversibleAt u m → ¬ sameOrbitSetoid.r u v`
  — the commit-grain → class-algebra bridge in one line.
- **`lowslab_pull_wf_undo`** — `Orig/LowSlab.lean` — at WF every
  foundation giveback has the one-move undo
  (`reversibleAtW u (foundToTab c b)`); the corollary
  `lowslab_pull_never_commit_wf` vacates a whole move kind at WF.

### 14b. Dominance pins (the proven tier)

- **`draw1_sameCycle_sameFate`** — `Orig/Dominance.lean` — PROVEN
  (clear of the file's residues): at `drawStep = 1` both ends, same
  cycle ⇒ same fate — the stock-as-reserve verdict conservation
  (how far the deck is dealt is invisible to solvability).
- **`wastePark_restack`** — `Orig/Dominance.lean` —
  `[propext, Quot.sound]`
  The park/restack window cancels into the direct waste raise in
  one move (the B&G Case-1 substitution as a single cite).
- **`ground_diamond_raise`** — `Orig/Dominance.lean` —
  `[propext, Quot.sound]`
  Distinct-suit raises COMMUTE with state EQUALITY (same landing
  state) — reorder adjacent raises without class-equivalence loss.
- **`mem_upCards_take`** — `Orig/Dominance.lean` — the public
  take-membership face (`posOf_upCards` is the private twin) — the
  build-order bridge the founding rows cite.
- Proven next tier worth a future pass: `ground_streak_founded`,
  `draw1_compliant_replay`, `WinFrom_of_runTo`/`WinFrom_of_undo`,
  `stackPile_worry_sequence` (itself `[propext, Quot.sound]`, only
  its DOWNSTREAM spread residue is open), the
  `dominantAt`/`prunableAt`/`dominates`/`suitLive` vocabulary.

- **`reversibleAtW_iff_reversible`** — `Orig/Classify.lean` —
  the doctrine bridge: at WF, reversibility ⇔ a CARRIED return-play
  witness — the uniform supply behind `ShufflePlayW` and the
  canonicalizer's reversible raises.
- **`irreversible_iff_of`** — `Orig/Classify.lean` — the Bool-oracle
  iff plus CHOICE-FREE decidability (`decidable_irreversibleAt_of_wf`
  off WF) — read the semantic predicate through the oracle shape.
- **`win_iff_macro`** — `Orig/Macro.lean` — the verdict ↔ phased
  macro-game license (single `by_cases` may read `Classical.choice`;
  zero sorry) — the entire Macro cone sits on it.
- **`rung_found_congr`** — `Orig/MacroInternal.lean` (CanV3 sibling
  `fiber_founds_eq`) — SAME RUNG ⇒ IDENTICAL foundation content —
  kills mixed-residence foundation worries in one cite (the
  PairClassZones founds row rides it).
- **`foundToTab`/`tabToFound` step gazette** — see §6's LIFO quartet;
  the State.lean micro-kit (`firstWhere_sound/find`,
  `lastOf_mem/snoc/eq_snoc/exists`, `chop_snoc`, `runOK_chop`,
  `setPile_piles_ne`, `canPlace_inl_unfold/inr_located`) is the
  dedup home 4-5 chapters already cite; Encode's radix-encoder
  (`encF_inj`, `stateEnc_inj` — WF states are code-reconstructable)
  and Play's `run_firstPassage_split` round out the low spine.

### Boundary

Open, priced, and refuted rows live in **CHALLENGES.md** — the
consolidated challenge ledger (research-grade residues with routes,
mechanical stubs, in-flight hot-mission territory, and the
never-retry refuted records). This file indexes the proved library
only; every entry here is battery-verified zero-`sorryAx`.
