# Corpus probes — the engine-side half of the pending decision (wave 21)

**Session:** farm-corpus-probes (wave-21 measurement; this file is the only
measurement artifact — no Lean side was touched).

**Engine under measurement:** the issue-15 micro engine —
`fix/issue-15-least-stack-worry-backs` @ `10e62f8` (= `dc41b8e` + the two
issue-15 worry-back fixes), driven through the external repro15 harness
(`C:\Users\hy\AppData\Local\Temp\kilo\lonelybot-repro`), extended with new
modes `frozen2` | `urgency` | `irrev` (the harness's `corner` mode is
untouched and doubled as the comparability control).  Build:
`cargo build --release`; every mode takes `REPRO_SEEDS` (default 300).

**Corpus & trajectory protocol** (identical to the earlier corner probe, so
the numbers are comparable): `default_shuffle(seed)` for the harness's
`2..(2+REPRO_SEEDS)` seed loop — labeled `2..302` at 300 seeds (the
corner-probe corpus; last seed 301), draw 3, per-seed abstract engine
+ concrete `StandardSolitaire` in lockstep (`convert_moves` replay +
`Solitaire::from(&b).equivalent_to(e.state())` asserted after every move),
greedy stepping PS > DS > DP > R > SP, at most 400 steps, stop on
no-moves / win.  Every predicate below is evaluated on the CONCRETE board
(the lockstep makes it equivalent to the engine state at that point).
Extension: the same three probes at seeds `2..1002` (1000 seeds).

**Control:** `corner` reproduces the wave-19B numbers exactly — 5 of 300
seeds, 12 corner states, first example seed 26 ♣K, all 12 states at one
empty pile (at 1000 seeds: 29 seeds, 467 states, histogram
[454, 4, 6, 2, 1] at 1..5 empty piles).

---

## Operationalization vs the Lean side (read first)

- **climb-blocked** (corner-predicate reuse): a suit `s` (foundation height
  `h < 12`) whose next foundation-needed card `Card(h, s)` is buried in the
  concrete stock (`deck_iter`) or the strictly-hidden stratum
  (`get_hidden()`, face-down pile cards).  This is *exactly* the corner
  probe's `blocked` test.  It does **not** count the needed card being
  visible-but-covered or drawn-but-not-waste-top; the true frozen worlds
  are therefore at least as large as the ones measured here.
- **genuinely empty pile** (corner reuse): hidden stratum empty AND visible
  stratum empty (the concrete board auto-flips, so in practice
  visible-empty implies hidden-empty).
- **frozen visible king** (probe 2): the king has been drawn or dealt face-up
  — it is in the waste (drawn) or in a tableau visible stratum — and its
  suit is climb-blocked as above.
- **promotable anchored head** (probe 2): a pile whose *entire visible
  content is one card* (nothing on it) sitting directly on its dealt base,
  whose rank equals its suit's foundation height — removable now.  Two
  readings are reported: **R2** = any single-visible-card head (the
  letter of the ticket), and **R1** = the *pristine* dealt top (the card is
  the pile's original dealt top AND the hidden depth is still the dealt
  `i`, i.e. no flip ever happened on that pile).
- **empty-pile histogram bins** are the count of genuinely empty piles at
  the hit states.
- vs **`twinMid` / `noSeat`** (TwinSwapCompletion.lean:668 / :2504): those
  are *window/mid-level* machinery (the play that fits between a twin's
  firing and its replacement, with per-seat exclusions of the landing
  cells: `deckPile`/`stackPile`/`pilePile` bases, the `pileStack c'` seat
  cells, and the reveal chains' anchors).  These probes are *state-level*:
  single states and the raw candidate card sets the engine offers there.
  Probe 3's candidate card is the concrete counterpart of the
  `.pileStack c'` seat cell of `noSeat`'s match.  The corpus-side landing
  statistics of §8's audit remain a separate (mid-level) ticket; these
  state-shape numbers are the inputs for re-scoping premises to the
  measured worlds.
- vs **`irreversibleAt`** (Theorems.lean:138 — the authority):
  `irreversibleAt st m := ∀ st₁ play, st.apply m = some st₁ →
  st₁.run play ≠ some st` — *no play at all* returns.  Every check below is
  a one-step *proxy*: if a one-step return exists (the engine offers the
  raw worry-back `SP c` at the immediate post-promotion state), the move is
  *not* `irreversibleAt`, hence every fraction below is an **upper bound**
  on the true `irreversibleAt` rate (a later play might still re-seat the
  card, pushing the true rate lower).
- **K+ caveat** (class labels below): the micro engine's abstract state
  tracks each pile's bottom visible card (the *anchor*/*window top*)
  plus the strictly-buried cards in order, but the visible cards *above*
  the anchor as an unordered set.  So a raw `PileStack` candidate need not
  be a concrete pile top: it may be *covered-landed* (mid-stratum), whose
  concrete replay (`convert_moves`) relocates the covering run to another
  pile first.  The probes classify every candidate instead of assuming a
  concrete top.

---

## Probe 1 — frozen-king-at-≥2-anchors (the `c2_two_option_king_frozen` regime's borderline)

**Definition (per state):** some suit's king is still in the stock or the
strictly-hidden stratum AND that suit is climb-blocked (corner predicate,
`h < 12`) AND **≥2** genuinely empty piles exist.  This grades the honest
regime of `same_pin_hole_oneAnchor` / `c2_two_option_king_frozen` (the
theorems hold at ≤1 free anchor): how big is the ≥2 world really?

| metric (states = greedy-trajectory states) | seeds 2..302 | seeds 2..1002 |
|---|---|---|
| seeds touching the ≥2-anchor regime | **29 / 300 (9.7%)** | 96 / 1000 (9.6%) |
| hit states, visited | 3232 | 10070 |
| hit states, **distinct** | **75** | **345** |
| the ≥1-anchor world (context): seeds | 173 / 300 | 611 / 1000 |
| the ≥1-anchor world (context): visited / distinct | 12584 / 1008 | 37997 / 3421 |
| hit states also carrying a buried king that is its own suit's next-needed (h == 12) | 0 | 7 |

**Empty-pile histogram at hit states** (bins = genuinely empty pile count):

seeds 2..302:

| empty piles | visited (≥2-hit) | distinct (≥2-hit) | visited (the ≥1 world) |
|---|---|---|---|
| 1 | 0 | 0 | 9352 |
| 2 | 2853 | 66 | 2853 |
| 3 | 379 | 9 | 379 |
| ≥4 | 0 | 0 | 0 |

seeds 2..1002:

| empty piles | visited (≥2-hit) | distinct (≥2-hit) | visited (the ≥1 world) |
|---|---|---|---|
| 1 | 0 | 0 | 27927 |
| 2 | 8621 | 310 | 8621 |
| 3 | 1110 | 23 | 1110 |
| 4 | 336 | 9 | 336 |
| 5 | 3 | 3 | 3 |
| ≥6 | 0 | 0 | 0 |

**First concrete example** (seed 26; the ♦ and ♥ kings both buried and
climb-blocked — ♦3 and ♥A sit in the hidden strata while p1/p3 stand empty —
the state was reached along the greedy trajectory):

```
seed 26: buried king(s) in ♥,♦ climb-blocked — ♥:needsA  ♦:needs3  ♣:needs2  ♠:needs5 — visible tops [— 4♦ — 5♦ K♣ 8♠ 3♥] — empty piles 2
  Foundations   ♥:needsA  ♦:needs3  ♣:needs2  ♠:needs5
  Pile 1        empty
  Pile 2        [8♦] K♠ Q♥ J♣ 10♦ 9♣ 8♥ 7♠ 6♥ 5♣ 4♦
  Pile 3        empty
  Pile 4        [3♣] [7♣] [2♣] 9♥ 8♣ 7♦ 6♣ 5♦
  Pile 5        [9♦] [A♥] [K♦] K♣
  Pile 6        [K♥] [J♥] [J♠] [3♦] [J♦] 8♠
  Pile 7        [10♥] [Q♦] [2♥] [7♥] 6♠ 5♥ 4♣ 3♥
  Stock (3 cards) 10♣ 9♠ 6♦
  Waste (5 cards) Q♠ 4♥ Q♣ 5♠ 10♠
```

(♥A is face-down in p5, ♦3 face-down in p6, K♥ face-down in p6, K♦
face-down in p5 — both kings buried with their suits' next-needed cards.)

**Reading.**  The ≥2-anchor regime is real but small: ~9.7% of deals pass
through it at least once along the greedy policy, and it accounts for
7.4% (75 of the 1008) of the distinct blocked-buried-king-with-≥1-anchor
states.  The bulk of the frozen-king world sits at exactly 1 free anchor — inside
the regime the ≤1-anchor theorems already cover — and the ≥2 tail
concentrates at exactly 2 empty piles (≈89% of the ≥2 hits).  The
"king-is-its-own-next-needed" reading (h == 12) adds only 7 states at 1000
seeds.  Visited counts run roughly 30–40x the distinct ones (trajectory
revisits); distinct-state counts are the load-bearing column.

---

## Probe 2 — route urgency (the anchored-head unseat route's raw material)

**Definition (per state):** (a) a frozen/climb-blocked **drawn** (waste) or
**tableau** (visible stratum) king AND (b) at least one uncovered
promotable anchored head (visible content = one card on its dealt base,
rank = its suit's foundation height — removable now) AND ≥1 genuinely empty
pile.  Variants: (a) loose = drawn-or-tableau vs strict = waste-top-or-pile-top;
(b) R2 = any single-visible head vs R1 = pristine dealt top.

| combo (seeds / visited / distinct) | seeds 2..302 | seeds 2..1002 |
|---|---|---|
| **[0] loose ∧ R2 — headline** | **37 / 82 / 82** | **122 / 267 / 267** |
| [1] strict ∧ R2 | 11 / 12 / 12 | 41 / 72 / 72 |
| [2] loose ∧ R1 (pristine top) | 11 / 14 / 14 | 46 / 60 / 60 |
| [3] strict ∧ R1 (pristine top) | 4 / 4 / 4 | 20 / 24 / 24 |

**Empty-pile histogram at headline hits** (visited = distinct here; no hit
state was revisited):

| empty piles | seeds 2..302 | seeds 2..1002 |
|---|---|---|
| 1 | 60 | 199 |
| 2 | 14 | 41 |
| 3 | 4 | 17 |
| 4 | 4 | 10 |
| ≥5 | 0 | 0 |

**Head/engine agreement:** every promotable anchored head was also offered
by the engine as a raw `PileStack` (83/83 head evaluations at 300 seeds,
279/279 at 1000) — the concrete "single visible card, rank = height" head
is exactly the engine's own promotion offer, so the model-side `anchorHead`
premise and the engine's generator agree.

**First concrete example** (seed 20 — ♣K drawn into the waste with 13
later cards above it and ♣A face-down in p6, ♥ at height 1 with the 2♥ head
alone on p5, and p2 standing empty):

```
seed 20: frozen king(s) [♣K suit frozen at height 0 (needs A buried; king in the waste)]; promotable anchored head(s) [p5:2♥] — ♥:needs2  ♦:needsA  ♣:needsA  ♠:needsA — visible tops [2♠ — J♥ 2♦ 2♥ 2♣ Q♠] — empty piles 1
  Foundations   ♥:needs2  ♦:needsA  ♣:needsA  ♠:needsA
  Pile 1        3♦ 2♠
  Pile 2        empty
  Pile 3        [9♦] J♥
  Pile 4        [8♦] [9♥] [3♣] 6♥ 5♠ 4♦ 3♠ 2♦
  Pile 5        [6♣] [7♦] 2♥
  Pile 6        [Q♣] [10♣] [J♦] [A♣] [J♠] 8♠ 7♥ 6♠ 5♦ 4♣ 3♥ 2♣
  Pile 7        [A♠] [9♣] [K♥] [5♣] [K♠] [7♣] K♦ Q♠
  Stock (2 cards) 10♥ Q♥
  Waste (14 cards) K♣ 4♠ 9♠ 6♦ A♦ Q♦ 10♦ 10♠ J♣ 5♥ 8♣ 4♥ 7♠ 8♥
```

**Reading.**  The unseat route's raw material shows in ~12% of deals
(loose) / ~4% (immediately-landable strict king) along the greedy
trajectories — the route is not a pristine-countermodel artifact, but its
live form (waste-top king + head + free anchor simultaneously) is rarer:
11/300 seeds.  Note that in this engine only a *waste* king can land on a
free anchor (`DeckPile`; pile→pile king moves do not exist — the
no-pile-to-pile regime), which is what the strict variant isolates.
Histograms: the route co-occurs with exactly one free anchor 3 of 4 times.

---

## Probe 3 — context-irreversibility rate (the window-gate (b) engine cost)

**Method.**  Over every state visited by the greedy trajectories, enumerate
the engine's current raw `PileStack` candidates (`list_moves`, unfiltered);
for each, three reversibility checks — labeled honestly as proxies for the
Lean `irreversibleAt` (Theorems.lean:138 — the authority; see the bound
relation at the end):

1. **NOW check (the ticket's letter):** the reverse seating exists now —
   some pile top is rank+1 of the opposite colour, or (for a king) a
   genuinely empty pile exists.  Implemented with the engine's own seating
   rule, `Card::go_after` over the concrete tops.
2. **ENGINE check (operative):** after applying the promotion (on a cloned
   engine), the raw worry-back `SP c` is *offered* by the engine at the
   immediate post-promotion state — the engine's own notion of a
   one-step-back move existing.
3. **CONCRETE-POST check** (only for the well-defined classes): the same
   seating test at the concrete post-promotion board, counting the seat the
   move itself creates — the flipped anchor card, the freed own anchor (for
   a king), or the exposed underlyer.

**Candidate classes** (K+ set-representation; see the caveat above):
`anchor-alone` (the pile's only visible card — promotion empties or flips),
`anchor-covered` (bottom visible, covered cards on it), `top-landed`
(exposed above the anchor), `covered-landed` (mid-stratum above the
anchor).

| metric | seeds 2..302 | seeds 2..1002 |
|---|---|---|
| candidates sampled (visited / distinct) | 41990 / 1744 | 132634 / 5059 |
| IRREVERSIBLE, NOW check (distinct / visited) | 78.38% / 87.37% | 77.68% / 86.96% |
| **IRREVERSIBLE, ENGINE check (distinct / visited)** | **32.22% / 1.34%** | **35.38% / 1.35%** |
| IRREVERSIBLE, CONCRETE-POST check (classes 0+2) (distinct / visited) | 33.65% / 1.28% | 36.68% / 1.31% |
| king candidates (distinct) NOW-irrev / ENGINE-irrev | 67: 1 / 0 | 143: 2 / 0 |

**Per-class breakdown** (distinct-state weights; "N/L/E" = candidates /
NOW-irrev / ENGINE-irrev):

| class | seeds 2..302 (N/L/E) | seeds 2..1002 (N/L/E) |
|---|---|---|
| anchor-alone | 806 / 565 / 536 | 2595 / 1807 / 1729 |
| anchor-covered | 48 / 27 / 26 | 99 / 62 / 61 |
| top-landed | 787 / 683 / 0 | 2119 / 1834 / 0 |
| covered-landed | 103 / 92 / 0 | 246 / 227 / 0 |

**First concrete examples**

Irreversible both ways (seed 2, step 0 — the A♦ head alone on p3 has no
black-2 receiver anywhere: 2♠ lies face-down in p4, 2♣ in the stock —
promotable, and stuck up):

```
seed 2 step 0: PileStack A♦ [anchor-alone, p3 pos 1/1] — no 2 receiver of the opposite color and no free pile for a king among tops [8♦ J♥ A♦ 6♦ J♣ 7♣ Q♣]; empty piles 0
  Foundations   ♥:needsA  ♦:needsA  ♣:needsA  ♠:needsA
  Pile 1        8♦
  Pile 2        [6♥] J♥
  Pile 3        [Q♦] [9♠] A♦
  Pile 4        [Q♥] [2♠] [6♠] 6♦
  Pile 5        [5♣] [3♥] [10♥] [2♦] J♣
  Pile 6        [8♠] [10♣] [K♠] [A♠] [4♣] 7♣
  Pile 7        [J♠] [8♣] [9♣] [A♥] [4♥] [4♠] Q♣
  Stock (24 cards) 3♣ 10♦ 5♦ 7♠ 5♥ K♥ 7♥ Q♠ 9♥ 5♠ 7♦ 2♣ 8♥ K♦ K♣ J♦ 10♠ 6♣ 2♥ 9♦ 4♦ 3♠ 3♦ A♣
  Waste (0 cards)
```

Reversible now (seed 2, step 17 — a 5·red receiver (5♦) is standing on p4):

```
seed 2 step 17: PileStack 4♣ [anchor-alone, p6 pos 1/1] — a 5 receiver of the opposite color exists among tops [7♠ 9♥ 2♥ 5♦ 10♦ 4♣ J♦]
  Foundations   ♥:needsA  ♦:needs2  ♣:needs4  ♠:needsA
  Pile 1        8♦ 7♠
  Pile 2        [6♥] J♥ 10♠ 9♥
  Pile 3        [Q♦] 9♠ 8♥ 7♣ 6♦ 5♠ 4♦ 3♠ 2♥
  Pile 4        [Q♥] [2♠] 6♠ 5♦
  Pile 5        [5♣] [3♥] [10♥] [2♦] J♣ 10♦
  Pile 6        [8♠] [10♣] [K♠] [A♠] 4♣
  Pile 7        [J♠] [8♣] [9♣] [A♥] [4♥] [4♠] Q♣ J♦
  Stock (10 cards) 5♥ K♥ 7♥ Q♠ 7♦ K♦ K♣ 6♣ 9♦ 3♦
  Waste (0 cards)
```

**Reading.**

- The **ENGINE check is the operative number** for the window-gate option
  (b): 32–35% of distinct-state promotion candidates carry no immediate
  worry-back, so a gate that closes the window on irreversible promotions
  would flag about a third of the candidate seatings in the state space.
- The letter NOW check **overcounts permanence ~2.4x** (78% vs 32%): every
  top-landed / covered-landed candidate (47% of distinct candidates, 98% of
  visited ones) has, by the descending-alternating construction of concrete
  piles, a legal receiver directly beneath it — the promotion's own pile
  hands the seat back (the ENGINE check sees this too: 0 of 129,940 visited
  landed candidates were engine-irreversible).  A gate implemented at the
  lettered NOW-strength would misclassify half the promotions.
- **Where the irreversibility actually lives:** anchor promotions of
  non-king heads — 1729/2595 (67%) of anchor-alone and 61/99 of
  anchor-covered candidates at 1000 seeds.  King promotions are *never*
  engine-irreversible here (0 of 143 distinct): the freed anchor (or another
  empty pile / receiver) always takes the king back immediately.
- The **visit-weighted rate (1.3%) is much lower** because greedy
  trajectories re-visit reversible shuttle states (SP/PS two-cycles) at
  high multiplicity: along-play window churn is dominated by reversible
  promotions, while the distinct-state cost (one gate per state) is the
  32–35% figure.
- **Bound relation to `irreversibleAt`:** engine-reversible (a raw `SP c`
  offer exists) implies *not* `irreversibleAt`, so both IRREVERSIBLE
  fractions are upper bounds on the Lean rate; a returned-later play can
  still re-seat the card, pushing the true rate below 32%.  The class table
  shows where the upper bound is tight (anchor promotions) vs vacuous
  (~all landed promotions are one-step reversible).
- Disagreement counts (visited): NOW-reversible-but-engine-irreversible: 0
  (both probes); NOW-irreversible-but-engine-reversible: 36,125 / 113,552
  — all explained by seats the move itself creates or exposes: the
  underlyer seat of landed candidates, the flipped anchor card, and the
  freed anchor for kings (the flip-class contributes 29+1 of these at 300
  seeds, 78+1 at 1000; the rest are the landed underlyer seats).

---

## Headline numbers (seeds 2..302; 1000-seed extension in parentheses)

1. **Frozen-king-at-≥2-anchors: 29 of 300 seeds (96 of 1000), 75 distinct
   states (345)** — ~9.7% of deals touch the regime the ≤1-anchor theorems
   leave open, but it is only 7.4% of the blocked-king-with-anchor states;
   the rest sit at exactly 1 free anchor, inside the proven regime.
2. **Route urgency: 37 of 300 seeds (122 of 1000), 82 distinct states
   (267)** carry a frozen drawn/tableau king together with an uncovered
   promotable anchored head at ≥1 free anchor (immediately-landable strict
   variant: 11 seeds / 41); every such head was also the engine's own
   `PileStack` offer (279/279).
3. **Context-irreversibility: 32.22% of distinct-state raw `PileStack`
   candidates leave no immediate worry-back (35.38% at 1000 seeds;
   visit-weighted 1.34%)** — an upper bound on the Lean `irreversibleAt`
   rate; the lettered receiver-exists-now check would give 78.4% and
   overstate the gate's cost 2.4x.

**For the pending decision** (route (a) `anchorHead` channel vs (b) the
window gate): the unseat route's raw material is measurable-but-modest
(4–12% of deals depending on strictness), anchor-promotions are where
irreversibility concentrates, and a NOW-strength gate would overfire on
landed promotions — the engine-side numbers support a gate defined at the
engine's reverse-offer strength, if route (b) is taken.
