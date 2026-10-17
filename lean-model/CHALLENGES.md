# CHALLENGES — the consolidated open ledger (2026-10-13)

The *challenge file* to THEOREM-INDEX.md's *proof library*: every open
row with its statement shape, its banked route, and its price. For
the strategic mission cards (campaign narratives, gating doctrine)
read FUTURES-ORIG; this is the tactical per-row layer an agent
consults before hunting. Tiers: **[H]** research-grade (needs new
mathematics), **[M]** mechanical (cleanup/refactor), **HOT** in-flight
(do not touch while a session owns the file), **REFUTED** (proven
false — never retry).

## [H] The named residues, with routes

- **`decompose_residue_nesting`** ← `reversible_equaltuple_decompose`
  (`Orig/BracketDecomp.lean:1175`) — the N-nesting raise induction:
  two orbit-mates with equal rung tuples decompose into bracket
  pieces. Proved frontiers to build on: `raise_free_closure`
  (zero raises), `one_bracket_closure` / `witness_one_bracket`
  (at most one raise), `BracketW_cargo_to_closure`,
  `flatPath_of_cargoPath`, `bracketClosure_of_cargoPath`. The last
  `sorryAx` anywhere beneath the capstone chain.
- **`canonFace_sameShape`** (`Orig/MacroInternal.lean`, sorry-carrying
  tier) — the honest form of "agreements ⟹ forks": same-class +
  same *shape* ⟺ identical-or-slide-mate. Why the naive biconditional
  is unsound (two constructible reasons, per 25852a8): reflexivity —
  every state agrees with itself, forkless included; and reversible
  in-tableau slides can expose a third pair's buried next-up without
  disturbing any zone or rung. The fork-grade zone rows
  (`forkState_class_zoneSets` family) carry this as the named
  `hthird` premise — landing this row vacates the premise.
- **Dominance's worry chip** — `stackPile_worry_spread_residue`
  (`Orig/Dominance.lean:9831`) → `stackPile_worry_prunableAt` (the
  capstone assembly). Context is PROVED: `stackPile_worry_sequence`
  itself audits `[propext, Quot.sound]`; only the spread is open.
  Also base-chain: `ground_lifted_win` (the one admitted sorry in
  the base chain, :3919) and `draw1_worry_spread_residue` (:8838).
- **LowSlab's six `[H]` replay witnesses** (`Orig/LowSlab.lean`):
  the top-carry transport (:547), three same-shaped per-kind
  member-replay rows — given an elevated commit, exhibit a slab
  member `u₀` whose one-step `v₀` is class-mate to the landing
  (:715, :786, :1159), the `WasteGuard` member transport (:847),
  and `lowslab_waste_targetclass` (:885, the dashed-witness
  transport). Architecture around them is LANDED: routers shrunk to
  proved dispatchers, the elevation dispatcher proved,
  `lowslab_pull_wf_undo` promoted.
- **ForkFloor/ForkAscent frontier** — `founded_late_seat_exists`
  [H] (the seat-delay residue behind the private
  `p_founded_seat_schedule`) plus the per-kind [M] rows;
  `ascent_exhaustion_forks` [H] in ForkAscent
  (`orientation_assembly_fork` carries the bare-cover corner — NOTE:
  per commit `76389fc` the ascent routing and saturation/climb-delivery
  machinery landed; the exhaustion head remains).  ForkCensus's
  detector LANDED ZERO-SORRY (`classCensusB_true_iff`,
  `pairCandidate_board_witness`, [propext, Quot.sound] — no longer a
  challenge).  Four kind-census rows are PROVED and index-ready the
  moment the routed head lands: `hidden_never_grows`,
  `two_zone_exits_playable`, `founded_returnable_via_seats`,
  `draws_permute_only`.
- **ParentMap's two named residues** (per the `21c047b` landing;
  in-flight — hands off): the `cargo_inr_residue` (head hops into
  its twin pool via `parent_pool` over `canPlace_inr`'s fit;
  `pm_putRun_inr` evaluation rows pre-staged) and the CargoPath
  induction.
- **ConeCrossarm's corridor gate** — the public headline
  `cone_pulls_congr_crossarm` flows a private gate's `sorryAx`;
  only the conditioned sibling
  `cone_pulls_congr_crossarm_of_anchorRungs` is clean.
- **Decompress**: `finalWiggle_reach`.
- **MacroInternal's remaining sorry tiers**: `founded_implies_atRung`,
  `fiber_iff_flat`, `finals_topFibers`, `conjugate_forkState`, the
  `canonFace_*` tier (incl. `canonFace_sameShape` above), and the
  `fork_iff_nonUnionable` tier.

## [M] Mechanical cleanup tasks

**(2026-10-13 status: the [M] ledger below is now mostly RESOLVED — kept
for the record with resolutions noted.)**

- **THE ROOT-LEVEL CanRaiseS TRIPLE-DECLARATION** — OPEN, owner
  decision required (found 2026-10-13, the sweep's fourth hidden
  duplicate family — an INDUCTIVE one):
  `inductive CanRaiseS` is declared in THREE modules —
  `Orig/ForkStateSB.lean:92`, `Orig/CanV3.lean:515` (landing-4's
  selector grade), `Orig/MacroInternal.lean:1162` (the census grade,
  per its own docstring "two predicates, no contradiction").  The
  all-imports ROOT build (`lake build Orig`) fails on this at either
  import order; per-file and per-cone builds are unaffected.  THE FIX
  belongs to the owner chapters: either namespace the three grades
  with bridges, or confirm the root's deliberate exclusion
  permanently (drop the census-tier imports from `Orig.lean`).
- ~~The take-position kit, fourth copy~~ — RESOLVED 2026-10-13
  (`49dbbee`: the pcz kit struck; full kit at `FoundKit`).
- ~~The ZoneAgree placement split~~ — RESOLVED 2026-10-13
  (`71cea33`: the census leaf lives at `Orig/ZoneAgree.lean`).
- ~~PairClass.lean's stale battery comment~~ — RESOLVED 2026-10-13
  (truespeaked to the terminal `[propext, Quot.sound]` grade).
- ~~Dominance waste/draw stronger-grade inversions~~ — RESOLVED
  2026-10-13 (`004ea0d`: promoted `step_wasteToFound_inv_head` /
  `step_wasteToTab_inv_head` public in Irreversible; Reach's
  `step_draw_inv` public; Dominance's three locals struck).
- **FUTURES sweep-up candidates** (grade-promotions, not strikes —
  see the 1348f80 lesson): Classify/ConjugateProof/Dominance
  `lastOf`/`chop` analysis families (locally differentiated grades);
  the deliberately-kept deprecated tactics (belowPull's compound
  `rw` — the `ite_eq_left` desync is priced twice, never "fix"
  blindly).

## HOT — in-flight, hands off while owned

- LowSlab (six [H] above; session active through 08:28+08:40 local).
- ForkFloor/ForkAscent (+498/−14 uncommitted as of 01:40Z).
- HostCensus parked-clean (`interleave_leg_conjugation` closed at
  dc09f87); reclaimable.

## REFUTED — never retry

- weak-grade class-face-uniqueness — REFUTED 2026-10-11 (negation row
  `forkState_unique_refuted`, retired at the 2026-10-17 stale-grade
  strike): `forkState_unique` as then stated (same class + both
  witnesses ⇒ `FaceShape`) is FALSE by the G2 craft — same witness
  pair {5♥, 5♦}, same orientation, spade rungs 5 vs 6, so neither
  `FaceShape` grade connects (cargo legs rung-flat, the conjugate
  composite net-flat).  The statement targets the RETIRED
  `weakForkState` detection (the ca78844 S-grade migration; the
  craft's endpoints are NOT forkStates), so the fence reads: never
  retry class-face-uniqueness at the weak grade, and at any stronger
  grade first price the G2 mechanism — a flat cargo leg un-blocking
  a covered next-up's raise.  Evidence rows stay in-tree
  (`Orig/ForkStateUniqGate.lean` §1: the craft boards +
  `forkGate_strict_head_false`); the S-GRADE class-uniqueness
  question is OPEN.  The per-state honest forms stand PROVED:
  `forkState_pairUnique` (unique, up to twin) and the bare-select
  equality `forkPair_not_twoColors_state`/`_twoRanks_state`.
- The FORK-SPECTRUM completeness family (`forkSpectrum_complete`,
  `_locked`/`_mod_phase`, the 2026-10-11 falsifier card) — REFUTED,
  then RETIRED at the 2026-10-17 cleanup: the unconsumed leaf
  `Orig/ForkSpectrumProof.lean` was DELETED together with the
  in-tree `ForkSpectrum` block (session record: FARM_MEMORY.md).
  The fence stands: never retry as stated — the salvage is the
  statement-family lesson (foundation-flat generator languages
  cannot reach different-rung forkStates; add a raise letter).
- HostCensus's predecessor mirror kit — superseded and FALSE in
  wild generality (a miscounted wild foundation admits reversible
  foundToTab legs whose one-move undo dies); the pullEscape-grade
  precedent from dc09f87. The class-level route walks around it.
- The naive "zonal agreements ⟹ fork" biconditional — unsound per
  the two constructible reasons above; only `canonFace_sameShape`
  is the honest form.
