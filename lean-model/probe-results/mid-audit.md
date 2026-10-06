# §8 landing-site audit — do reached states' between-mids ever land on the twin seats? (wave 22)

**Session:** farm-mid-audit (wave-22 measurement; this file is the only
measurement artifact — no Lean side and no repo `src/` was touched).

**Engine under measurement:** the issue-15 micro engine — exactly the
wave-21 setup (`corpus-results.md`): the external repro15 harness
(`C:\Users\hy\AppData\Local\Temp\kilo\lonelybot-repro`, engine at
`lonelybot-main` = `dc41b8e` + the two issue-15 worry-back fixes), extended
with a new mode `midaudit` (the `corner` control is untouched and reproduces
the wave-19B numbers: 5 seeds / 12 states / seed 26 ♣K).  Build:
`cargo build --release`; `REPRO_SEEDS` (default 300) plus the 1000-seed
extension, same as wave 21.

**Corpus & trajectory protocol** (identical to all prior probes, so the
numbers are comparable): `default_shuffle(seed)` for seeds `2..(2+REPRO_SEEDS)`
— labeled `2..302` at 300 seeds, `2..1002` at 1000 — draw 3, per-seed abstract
engine + concrete `StandardSolitaire` in lockstep
(`convert_moves` replay + `Solitaire::from(&b).equivalent_to(e.state())`
asserted after every move), greedy stepping PS > DS > DP > R > SP, at most
400 steps, stop on no-moves / win.  Every predicate below is evaluated on
per-step CONCRETE snapshots (lockstep-equivalent to the engine at that
point); the engine's raw offer list is recorded per step.

---

## Operationalization vs the Lean side (read first)

The audited window is exactly `State.solvable_swapTwin_mixed`'s
(TwinSwapCompletion.lean:1119): the source play
`[p₁; PileStack t; mid; PileStack t.flipSuit; p₂]`, with the mid gated per
move by `Move.twinMid t` (:668) and `mid_access_of_noSeat`'s per-seat
exclusions (:2504): `b ≠ β ∧ b ≠ Sum.inr t`, where β is the twin's vacated
base cell (`A.board.bottomOf t = some β`, hereafter **the twin's seat**).
Operationalized on the concrete board:

- **twin / mate:** a twin firing is any realized `PileStack t` step; the
  mate is `t' = t.swap_suit()` (Rust `Card::swap_suit` = Lean
  `Card.flipSuit`, Basic.lean:77/150 — the same-rank pair flip within a
  color: ♥↔♦, ♣↔♠).
- **window pools:** the *PileStack-replaced* pool (the first later
  `PileStack t'` step exists and closes it) is the mixed window's exact
  shape — the **headline pool**.  *DeckStack-replaced* (the mate first
  returns via the waste — outside the window shape) and *open* (the mate
  never fires from a pile by trajectory end) are measured separately as
  supplemental pools.  Empty mids (adjacent firings, `mid = []`) are the
  already-proven `paired` family, counted and excluded from mid-move stats.
  Nested windows are intentional and independent: every firing anchors its
  own window and may also sit inside a wider window's mid — incidences are
  attributed per (window, step).
- **the twin's seat β, concretely:** on the pre-firing concrete board of its
  own pile — `Sum.inl` (the pile's bottom-visible slot) iff `t` was the
  pile's bottom face-up card, else `Sum.inr c₀` with `c₀` the face-up card
  directly under `t`.  This is the concrete reading of `bottomOf`.
- **mid moves:** every realized greedy step strictly between the firing and
  the replacement, Rust→Lean kinds: `PileStack→pileStack c`,
  `DeckStack→deckStack c`, `DeckPile→deckPile c b`,
  `StackPile→stackPile c b`, `Reveal→pilePile z b`.  Name clash disclosed:
  the Rust `Reveal` is the anchor-initiated whole-run pile→pile move (the
  Lean `pilePile`), NOT the Lean flip-reveal.
- **twinMid (:668), by the letter:** the three height-reading kinds fail iff
  the moved card is on the twin's own suit or *is* the mate (`c.suit ≠
  t.suit ∧ c ≠ t.flipSuit`); `deckPile`/`pilePile` pass unconditionally.
- **noSeat (:2504), per mid move, by the letter:**
  - the three landing kinds: the landing base `b` — replicating `convert`'s
    `find_free_pile` (first pile by index whose top accepts) — equals the
    anchor cell of an empty target pile (`Sum.inl`) or the target top card
    (`Sum.inr`).  Seat hit iff `b = β`, or `b = Sum.inr t` (a landing ON a
    returned twin).
  - `pileStack c`: seat hit iff `Sum.inr c = β` — i.e. a mid promotion of
    `c₀`, the card the twin sat on (**raising the underlyer**, witness A's
    shape).
  - `reveal a'`: the concrete engine has **no explicit reveal moves** —
    flips are automatic side-effects of the concrete composite move that
    empties a pile.  Approximated by the realized flip-onto-β test: a mid
    move whose concrete replay pops the twin's own pile's hidden top while
    β is that pile's anchor cell (the `b = Sum.inl a'` leg).  The
    `hiddenBase`/hidden-card legs cannot couple with β on this engine: β
    rides a visible cell or an anchor, never a hidden cell, and a hidden
    card cannot serve as a seat for a card above it mid-window — so the
    anchor leg is the reveal clause's whole concrete content.
- **clean vs dirty (the content split):** every seat candidate (an OFFER at
  a mid state) and every seat event (a REALIZED mid move) is split by the
  twinMid letter of its carrying move.  The `b ≠ β` exclusion only has
  content **over and above** twinMid on the passing half; on the excluded
  half (e.g. every `SP t` shuttle back) twinMid already refuses the move,
  so noSeat is redundant there — the **shadow/dirty-only** class.  This
  split is this audit's interpretive addition to the letter, used to answer
  the midaccess card's vacuity question.
- **incidence units:** windows counted per firing; mid states / mid moves
  per (window, step) incidence; *distinct* = first occurrence of the
  concrete state key extended with the seat-β and twin (states) or the move
  (moves) — a concrete state shared by two window contexts counts once per
  (state, seat, twin).  The **delay-state** row counts, per window, the
  pre-replacement state itself (could the play have delayed the mate one
  step by taking a seat move first?).
- **K+ caveat** (inherited from corpus-results.md): the engine's
  `PileStack` candidates can be covered-landed (mid-stratum); β and all
  seat tests read the concrete board, the lockstep guarantees the
  equivalence, and covered firings' covering-run relocations are treated as
  part of the same abstract move (its noSeat clause names only
  `Sum.inr c`).  Draws (`Move.draw`) are embedded sub-steps of DP/DS
  composites, unconditionally mid-safe, counted nowhere; flips likewise
  ride their carrying move.
- **what this cannot approximate, honestly:** (1) the `haccess` premise's
  full replayability is measured only through its no-landing form (noSeat)
  — a mid could in principle fail to replay for reasons no seat cell
  captures; (2) the theorem's `p₁`/`p₂` cleanliness (`cleanTwin` prefix and
  tail) is not audited — the applicability cross-tab below is a mid-gate
  estimate only, not a witness audit; (3) the mid is the corpus greedy
  line, the play the engine actually makes — strong for "the engine's real
  lines" claims, but it under-samples adventurous mids (states where a
  seat lander is offered but not taken are reported separately for exactly
  this reason).  The one structural choice — closing the window at the
  *first* later `PileStack t'` — is the theorem's own bracketing.

---

## Window inventory (per firing; seeds 2..302 | seeds 2..1002)

| metric | 300 seeds | 1000 seeds |
|---|---|---|
| twin firings (all PileStack steps) | 41705 | 131909 |
| **PileStack-replaced windows (the mixed window's shape)** | **288 (0.69%)** | 746 (0.57%) |
| — with empty mid (adjacent = the `paired` family) | 32 | 95 |
| DeckStack-replaced (mate returns via the waste) | 95 | 340 |
| open (mate never fires from a pile) | 41322 | 130823 |
| ambiguous firings (t' also PileStack-ready at the firing state) | 37 | 102 |
| seeds touching a PileStack-replaced window | **85 / 300 (28.3%)** | 261 / 1000 (26.1%) |
| seeds with any window-state seat offer | 179 / 300 | 551 / 1000 |
| seeds with a realized between-mid seat event (clean half) | 249 / 300 (159) | 814 / 1000 (535) |

**Reading.** The mixed-window shape is *rare per firing* (0.6–0.7%): along
the greedy PS-priority policy the ladder prefers pushing the fired twin's
own suit onward long before the mate arrives from a pile — but it is *not
rare per deal* (26–28% of seeds pass through at least one), and the
unreplaced/open bulk is the endgame shuttle world the wave-21 irrev probe
already characterized.

---

## The noSeat content — window states (mission question 2)

Per mid state (the states at which realized mid moves are played):
**bites** = OFFERS a forbidden-seat landing *via a twinMid-passing move*
(the exclusion's live content); **dirty-only** = seat candidates exist but
all are already twinMid-excluded (noSeat redundant there); **vacuous** =
no seat candidate exists at all (the premise is satisfied for free).

| pool | states (visited / distinct) | BITES (v / d) | dirty-only (v / d) | VACUOUS (v / d) |
|---|---|---|---|---|
| PileStack-replaced | 3693 / 3693 | **373 / 373 (10.1%)** | 268 (7.3%) | 3052 (82.6%) |
| DeckStack-replaced | 625 / 625 | 57 / 57 (9.1%) | 15 (2.4%) | 553 (88.5%) |
| open (churn-heavy) | 7,857,305 / 13,197 | 17.5% v / **8.7% d** | 48.9% v / 6.7% d | 33.7% v / **84.6% d** |

1000-seed extension: PS-pool 8760 states, bites 855 (9.8%), dirty-only 669
(7.6%), vacuous 7236 (82.6%); open-pool distinct-weighted 8.4% bites /
84.5% vacuous — stable.

**Clean-bite split (PS pool, 300 / 1000):** anchor-seat land offers 261 / 537
states; underlyer-seat land offers 53 / 174; underlyer-raise offers 63 / 152;
**land-on-twin offers 0 / 0**.  `SP t` (the twin's own worry-back) is offered
at 3.87 M open-window incidences (3117 distinct states); 11,408 distinct
mid states carry some twinMid-excluded foundation offer (the mate's own at
499,062 visited / 738 distinct).
Delay-state clean bites: 33 / 288 PS-pool windows (11.5%) — 87 / 746 at 1000
seeds — could have delayed the mate with a passing seat move.

**Verdict (vacuous or content-bearing?):** the `b ≠ β` half of `noSeat` is
**content-bearing in the engine's real lines**: about one mid state in ten
inside theorem-shaped windows live-offers a seat landing on the twin's seat
(kings re-anchoring the vacated pile dominate, plus receiver landings onto
the exposed underlyer and raise promotions of the underlyer itself), and
82.6% of mid states are vacuous for it.  The `b ≠ Sum.inr t` half (landing
ON the twin card) is **vacuous along real lines**: zero offers and zero
realized events at both 300 and 1000 seeds — structurally, the fired twin
sits on its foundation through the mid; the only way it becomes a landing
target is an `SP t` mid-window return, which `twinMid` itself excludes, and
when the greedy shuttle does it anyway the twin lands *on its own old seat
β*, which the other half of the clause catches.

---

## Realized mid moves — the greedy lines' actual landings (mission question 1)

Incidence units; distinct in italics where tracked.  300 seeds (1000-seed in
parens where it differs materially).

- total realized mid-move incidences: 7,861,623 (*17,515*) — by kind:
  3,921,538 PS, 1,459 DS, 3,754 DP, 3,931,654 SP, 3,218 R.  Of these
  **155,999 (2.0%) pass the twinMid letter** (76,602 PS / 997 DS / 3,754 DP
  / 71,428 SP / 3,218 R); the excluded bulk is the `SP t`⇄`PS t` shuttle in
  open windows.  PS-pool mids: 3,693 incidences across 288 windows.
- realized twinMid violations: **7.71 M t-suit foundation moves (3,428
  distinct)** — the fired twin's suit keeps climbing through most mids —
  plus 3,841,165 realized `SP t` returns and only 37 / 37 moves of the mate
  itself (of any kind).  The **catch-up fingerprint** (mate-SUIT foundation
  moves of other cards, the pure catch-up window's material): 49,953 (152,361
  at 1000 seeds) — the catch-up shape is a real, modest slice of the mids.
- **landing moves** (DP+SP+R realized): 3,938,626 (*7,766*), of which on
  twinMid-passing kinds 78,400 (*7,365*).

**The landing-site histogram (twinMid-passing denotes the letter's domain):**

| landing site (realized mid move, clean/passing kind) | visited | distinct |
|---|---|---|
| **ON the seat cell β — anchor-seat lands** (base `Sum.inl` = vacated pile) | 167 | 167 |
| **ON the seat cell β — underlyer-seat lands** (base `Sum.inr c₀`) | 58 | 58 |
| ON the twin card itself (`Sum.inr t`) | **0** | **0** |
| twin's pile, other cell (post-firing re-seated tops) | 13,752 | 910 |
| OTHER pile (the orthogonal land) | 94,084 | 6,413 |
| — *same counts over ALL kinds incl. twinMid-excluded:* dirty underlyer-seat lands (the `SP t` shuttle) | 3,830,565 | 218 |

plus the two non-landing seat channels, clean half:
**underlyer raises (PS of the card the twin sat on): 1,506 / 255 distinct**
(the witness-A shape realized — the promotion of the card the firing
exposed) and **flips onto the twin's anchor cell: 291 / 291** (embedded
reveal legs; 32 dirty ones besides).  The `PS` pool alone realizes **155
clean seat events** in 124 / 288 windows (43%): by type [anchor-land 33,
under-land 12, on-t 0, **raise 41**, **flip 69**] — 386 events / 311
windows (41.7%), [79, 41, 0, 94, 172] at 1000 seeds.

**Rates:** of passing-kind landing moves, 225 / 78,400 = **0.29% land on the
seat** (vs 99.7% orthogonal) — the *offers* exist at 10% of mid states, but
a passing seat landing needs a drawn/worried-back receiver to match the
seat cell exactly, and greed's picks mostly structure elsewhere.  Of all
passing mid moves, 2,022 / 155,999 = **1.3% are clean seat events** (raises
and flips included).  Of the 373 biting state-incidences in the PS pool,
155 realized their offered seat event — a **41.6% take-rate** of biting
states (45.1% at 1000 seeds): when the engine's line *can* take the seat,
it often does.

---

## Windows: mid shapes, lengths, and applicability (mission question 3)

PS-pool mid-length histogram (bin = number of mid moves, 9 = 9+):

| len | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9+ |
|---|---|---|---|---|---|---|---|---|---|---|
| 300 seeds | 32 | 8 | 5 | 7 | 9 | 7 | 5 | 18 | 13 | 184 |
| 1000 seeds | 95 | 28 | 32 | 21 | 21 | 17 | 23 | 34 | 21 | 454 |

Top mid kind-shapes (PS pool, 300 seeds; `…` = truncated at 8): pure
promotion chains dominate — `PS>PS>PS>PS>PS>PS>PS>PS…` (26), short
`PS>PS` (6), single `DS` (3), `DS>DP>DP>DP>DP>DP>DP>DP…` (3),
`R>R>PS>PS>PS>PS>PS>PS…` (3), … plus at 1000 seeds a 5× `DP>DP>DP>DP>DP…`
shape (waste-dump mids).  The mid is overwhelmingly more-of-the-same
foundation traffic around the waiting mate — the theory's catch-up,
punctuated by reveals and shuttles.

| window gate status (PS pool) | 300 seeds | 1000 seeds |
|---|---|---|
| fully twinMid-clean mid (the suit-hold half) | 97 / 288 (33.7%) | 285 / 746 (38.2%) |
| realized any seat event | 131 / 288 | 337 / 746 |
| realized a CLEAN seat event | 124 / 288 (43.1%) | 311 / 746 (41.7%) |
| **twinMid-clean AND no realized clean seat event** (the mid-gate applicable estimate) | **71 / 288 (24.7%)** | **211 / 746 (28.3%)** |

**Reading.** The binding premise along real greedy lines is `twinMid`'s
suit-hold (only ~34–38% of even the theorem-shaped windows clear it),
*not* the seat exclusion; among mid-gate effects the seat half is real but
second-order — roughly one window in four clears both gates as-is.

---

## First concrete example — seed 2, the A♦ window (PileStack-replaced)

Twin `A♦` fires as the very first move (its pile p3's bottom visible card,
so β = p3's **anchor cell**); the mate `A♥` sits face-down in p7 and fires
much later — a long catch-up-shaped mid.  Two seat events from that one
window:

**(a) a flip onto the seat cell (mid step 19, `R 9♠`)** — the mid so far
(this is the first realized CLEAN seat event in the corpus):

```
  1. DS A♣    2. DS 2♣    3. DP 8♥    4. DP 10♠   5. DP 9♥
  6. DP 5♠    7. DP J♦     8. DP 4♦    9. DP 3♠   10. R 6♦
 11. DP 5♦   12. DP 2♥    13. DP 7♠   14. DP 10♦  15. DS 3♣
 16. R 7♣   17. PS 4♣    18. PS A♠   19. R 9♠
```

```
seed 2 (state before mid move 19):
  Foundations   ♥:needsA  ♦:needs2  ♣:needs5  ♠:needs2
  Pile 1        8♦ 7♠
  Pile 2        [6♥] J♥ 10♠ 9♥
  Pile 3        [Q♦] 9♠ 8♥ 7♣ 6♦ 5♠ 4♦ 3♠ 2♥
  Pile 4        [Q♥] [2♠] 6♠ 5♦
  Pile 5        [5♣] [3♥] [10♥] [2♦] J♣ 10♦
  Pile 6        [8♠] [10♣] K♠
  Pile 7        [J♠] [8♣] [9♣] [A♥] [4♥] [4♠] Q♣ J♦
  Stock (10 cards) 5♥ K♥ 7♥ Q♠ 7♦ K♦ K♣ 6♣ 9♦ 3♦
  Waste (0 cards)
```

`R 9♠` runs the whole `9♠…2♥` column (p3's post-firing visible content,
revealed card `9♠` at its head) onto `10♦` on p5 — emptying p3, whose
auto-flip pops **Q♦ face-up onto β = p3's anchor cell**: the reveal-clause
leg of `noSeat` realized (the mid is passing — `pilePile` is
unconditionally twinMid — but the composite cannot replay at the
pre-firing state, where `A♦` still occupied the anchor and the flip card
`9♠` itself was hidden).

**(b) an anchor-seat land (mid step 24, `DP K♦`)** — the first
bites-state in the corpus; the state offers *two* seat landings and the
greedy **takes one of them**:

```
seed 2 (state before mid move 24):
  Foundations   ♥:needsA  ♦:needs4  ♣:needs5  ♠:needs2
  Pile 1        8♦ 7♠
  Pile 2        [6♥] J♥ 10♠ 9♥
  Pile 3        empty
  Pile 4        [Q♥] [2♠] 6♠ 5♦
  Pile 5        [5♣] [3♥] 10♥
  Pile 6        [8♠] [10♣] K♠ Q♦ J♣ 10♦ 9♠ 8♥ 7♣ 6♦ 5♠ 4♦ 3♠ 2♥
  Pile 7        [J♠] [8♣] [9♣] [A♥] [4♥] [4♠] Q♣ J♦
  Stock (0 cards)
  Waste (9 cards) 5♥ K♥ 7♥ Q♠ 7♦ K♦ K♣ 6♣ 9♦
```

Offered seat landings at this state: `R K♠` and `DP K♦`, both onto p3's
empty anchor cell = β; the greedy picks **`DP K♦` — the king from the
waste lands exactly on the vacated twin seat** (`deckPile`, passing), one
of the 167 clean anchor-seat lands.  These two events also show *why*
the offer histogram's anchor bin dominates: a vacated anchor cell is an
empty pile, and king landings are the engine's only pile landings onto
empty piles.

---

## Headline numbers (seeds 2..302; 1000-seed extension in parentheses)

1. **Window reach:** 85 of 300 deals (261 of 1000) pass through a
   theorem-shaped [PileStack t … PileStack t'] window; but only 288 of
   41,705 firings (746 of 131,909, 0.6–0.7%) close that way — the greedy
   real lines mostly climb onward or shuttle.
2. **noSeat's `b ≠ β` is content-bearing:** 10.1% (9.8%) of mid states in
   theorem-shaped windows offER a passing seat landing (anchor lands 261,
   underlyer lands 53, raises 63 at 300 seeds); 82.6% are vacuous; 7.3%
   dirty-only.  The real lines realize **155 clean seat events / 43% of
   the windows** (386 / 41.7% at 1000), take-rate of biting states 41.6%,
   and only **0.29% of passing landing moves** land on the seat — offers
   are common, takes are rare.
3. **noSeat's `b ≠ Sum.inr t` is vacuous in real lines: 0 offers, 0
   realized at both corpora** — the fired twin is foundationed through
   the mid, the `SP t` shuttle is twinMid-excluded, and it re-lands on its
   own β-seat anyway, where the β-half catches it.
4. **The binding gate is twinMid, not noSeat:** only 33.7% (38.2%) of
   theorem-shaped windows have fully twinMid mids; 24.7% (28.3%) clear
   both mid gates — the suit-hold premise is where real lines lose the
   window, before the seats matter.
5. **The realized seat channels, in order:** underlyer raises 1,506
   (the witness-A shape — promotions of the card the firing exposed),
   anchor-cell lands 167 (kings re-anchoring the vacated pile), anchor
   flips 291, underlyer lands 58 — with the raise+flip pattern confirming
   the Lean side's per-kind noSeat clauses each carry engine content.

**For the midaccess card's ticket 1:** the no-landing premise's two halves
are not alike — the vacated-seat half is a live, measurable constraint
(≈10% of mid states, ≈43% of windows, small absolute counts), the
on-twin half is dead letter along engine lines and could be discharged
cheaply if a formal route exists; any re-scoping of `noSeat` should
also weigh that the twinMid suit-hold, not the seats, is the premise real
greedy lines actually break.
