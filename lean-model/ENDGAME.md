# ENDGAME.md — the reshape endgame route (B4 / §5.1 N-half)

Reading agent deliverable, 2026-09-14. The single remaining root: the
compliant-play normal form that closes the crux `solvable_of_pileStack`'s
park/excursion/endgame residue. No proofs here; every Lean claim cites
file:line, every paper claim cites `main.tex:line` (Temp/opencode/paper,
Blake & Gent, JAIR 85, 2026). UNSURE items are marked **[GAP]**.

## 1. The theorem and its residue

**Proven (the first-move machinery, all citable).** For the crux
`solvable_of_pileStack` (Theorems.lean:1847; guards `hwf`, `hnotlock :
st.isLocked c = false`, `hm`, `hsol`): the R-half (`canReturnBase`,
Theorems.lean:27) is closed by `solvable_of_pileStack_return`
(Theorems.lean:365); nil is vacuous (`not_pileStack_of_win`,
Theorems.lean:1620); the delete case (`…step_delete`, Theorems.lean:1635);
the run-root square `pileStack_pilePile_stackPile` (Theorems.lean:1412);
and the eight commuting steps `solvable_of_pileStack_step_{draw,reveal,
deckStack,deckPile,pileStack,stackPile,pilePile}` (Theorems.lean:1647–1763),
each a landed square `pileStack_comm_*` (Theorems.lean:460–1250) plus the
packaged IH plus prepend.

**Remaining — exactly the blocked shapes** (the plan note,
Theorems.lean:1820–1836): moves seating a card **on `c`** (`deckPile x
(inr c)`, `stackPile x (inr c)`, `pilePile x (inr c)` — the *park*), and
`stackPile` of **`c`'s suit** (the same-suit worry-back at the shifted
rung — the *excursion*). Both reduce to the endgame: when `c`'s base is
non-returnable (deal-adjacent `inr d` with `canSitOn c d = false`, or a
non-king on an anchor), the worry-back lands on a **rank-mate** instead.
Four rows share this root: `safe_pileStack_dominant`'s N-half
(Dominance.lean:237), `deck_dominance_draw1`'s C part (Dominance.lean:522,
the pre-exit worry normal form), `stackPile_safe_prunable`'s tenth case
`deckPile x (inr c)` (Dominance.lean:678, the storage case), and —
downstream — `engine_replay_of_pilePile`'s locked boundary carry
(Restriction.lean:94).

## 2. What the paper actually proves

Numbering confirmed (`thm`/`lemma`/`corollary` share one counter,
main.tex:84–86; `\appendix` at main.tex:1217): App. B = Proofs
(main.tex:1367), B.1/B.2 its halves.

- **App. B.1** = `sec:dominance-proof-safe-moves` (main.tex:1387).
  **Definition 1** (main.tex:1396–1411): *potentially safely buildable* =
  same-suit rank-below already foundationed (or Ace), and recursively
  every card that could move onto `c` is too; + legal now = **safely
  buildable**. **Theorem 1** (main.tex:1417): when a safely-buildable
  card exists, the next move may be forced to be its foundation build.
- **Corollary 2** (main.tex:1453): the worry-back ban — never worry back
  a card that would be immediately safely buildable after ("pointless
  loop"; generalizes Bjarnason et al. 2007).
- **Corollary 3** (main.tex:1460): the thresholds. Red-black **with**
  worry back: "at most two more than the opposite-colour foundations'
  tops, at most three more than the other same-colour suit"
  (main.tex:1466) — bit-for-bit our `safeToStack` (Dominance.lean:92:
  same colour `toIdx ≤ heights + 2`, other colour `+ 1`); their
  8♣/7♦/9♥/8♠ example (main.tex:890) matches. The repo ledger's
  "Thm 1 / App. B.1" citations are correct as they stand.
- **App. B.2** = `sec:dominance-proof-partial-pile` (main.tex:1506).
  **Theorem 4** (main.tex:1521): the *immediate building* dominance — an
  incomplete pile may move only if the card above is then built to
  foundation immediately. The proof shape to steal:
  - General pattern (main.tex:1380–1382): work on the **last
    noncompliant** move; each step yields a winning sequence with either
    fewer noncompliant moves or the same number with the last one
    nearer the end; iterate to zero (the lexicographic termination
    of §4).
  - Case 1 (`c_i` safely buildable, main.tex:1431–1436): **delete**
    `m_i`, reinsert where the compliant tail first safely builds `c_i`.
  - Case 2 (main.tex:1438–1442): `m_i` moved neither *from* any safely
    buildable card (those are uncovered) nor *to* one (Definition 1's
    recursion), so all safely-buildable cards survive and **swapping**
    `m_i` past the compliant `m_{i+1}` is legal.
  - Critical Case 1 (main.tex:1545–1581): the follow-on move onto the
    vacated pile is redirected to the *other* target while an
    **invariant** holds — the piles under the two affected cards stay
    **swapped** — until a convergence subcase (a)/(b)/(c) restores
    identical layouts (main.tex:1558–1581).
- **Theorem 5** (main.tex:1614): Thm 1 × Thm 4 are compatible — the
  published instance of the closure property interaction-doc §2 asks
  for. Proof (main.tex:1619–1632): the Thm-1 transformations preserve
  Thm-4 compliance (deletes remove the only partial-pile move; swaps
  can't pair a partial-pile move with a safe build).
- **The stock caveat** (main.tex:899, 941): the safe dominance must not
  be enforced from the stock, *except* draw size 1 + unlimited redeals
  ("the stock … as if it were a reserve"); Wolter's Canfield bug
  (main.tex:1060–1063) is the cautionary tale. Our landed
  formalization of the exception: `draw1_cursor_solvable`
  (Dominance.lean:370). Their worry-back anecdote (main.tex:1052 — a
  worry-back immediately after stacking can be *necessary*) is why our
  crux has no safety hypothesis. Streamliners (main.tex:953–970) are
  NOT dominances — can produce false negatives; not citable for
  soundness.

**What the paper does NOT contain.** Our endgame. Their game class
(main.tex:1521–1527) has *ungated* pile-to-pile relocations: every
convergence move in Thm 4 Case 1 is a free relocation onto an
interchangeable target (the "indistinguishable build policy",
main.tex:1514). In our model the analogous moves are **gated**:
`stackPile` reads the rung (`toIdx x + 1 = heights x.suit`); the
placement moves read `canPlace` (visible base, free top). The **storage
park** (a drawn card parked on a foundation-passed-but-needed card) and
the **run-carrying re-home** have no counterpart in their proofs —
grepping "storage"/"redundant" finds nothing in their dominance context
(only transposition-table space, main.tex:905). The storage-park/
run-carrying normal form is the repo's generalization; B&G give the
*shape* (last-noncompliant lex induction, delete/swap/redirect with an
invariant, pairwise compatibility = Thm 5's grade) but not the content.

## 3. The normal form

Setting: `r := c.rank.toIdx = st.heights c.suit` (the legality guard of
`hm`), `b₀` with `st.board.bottomOf c = some b₀`, N-case
`canReturnBase c b₀ = false`. Structural facts it rests on:

- **F0 (the rung card is `c`)**: only `pileStack`/`deckStack` raise a
  height, always at the exact rung; the card of `c`'s suit at rung `r` is
  `c` alone; `deckStack c` never fires (c visible at st ⇒
  `vis_off_cycle`, State.lean:135; WF preserved by `apply_wf`,
  Move.lean:1027). So a winning π fires `pileStack c` at some position
  `j` — *the rung pass* — and `heights c.suit ≤ r` on the whole pre-`j`
  prefix.
- **F1 (transience, the catch-22)**: at `j`, `topOf (Sum.inr c) = none`
  (the `pileStack c` guard), so every tenant parked on `c` before `j`
  has left; a tenant leaves only by `pileStack x`, `pilePile x b`
  (re-homing the run rooted at `x`), or a carrying `pilePile` below `c`.
- **F2 (seat locality)**: the cards `x` with `canSitOn x c` are exactly
  rank `r−1`, colour opposite to `c`; the cards such an `x` can sit on
  are exactly the two rank-`r` cards of `c`'s colour — `c` and its twin
  `c.flipSuit` (`Card.only_blocker_is_twin`, Basic.lean:144;
  `Card.receivers`, Basic.lean:177). **A park on `c` has exactly one
  alternative seat: the twin.**
- **F3 (vacated-base special case)**: in the N-case with `b₀ = Sum.inr d`
  where `d` has rank `r` and `c`'s colour (the deal can stack so), the
  twin seat *is* `d` — bare in `s₁`, visible by `vis_base_of_notLocked`
  (Theorems.lean:323).

The compliant play — Lean-shaped sketch (a predicate on plays,
`stepsOK`-style, Pace.lean:780):

```lean
/-- The blocked shapes: seating on c, and same-suit worry-backs. -/
def cBlocked (c : Card) : Move → Bool
  | .deckPile _ b'' | .stackPile _ b'' | .pilePile _ b'' =>
      decide (b'' = Sum.inr c)
  | .stackPile x _ => decide (x.suit = c.suit)   -- the excursion shape
  | _ => false

/-- π is rung-normal for c when the pre-rung-pass segment is unblocked:
    pileStack c bubbles to the front by the landed squares alone. -/
def rungNormal (st : State) (c : Card) (π : List Move) : Prop :=
  ∀ k m rest, π = π.take k ++ m :: rest → k < rungPos st c π →
    cBlocked c m = false   -- rungPos = index of the first pileStack c (F0)
```

Concretely: before the rung passes, nobody parks on `c`, and `c`'s suit
is never worried back — hence no c-suit `pileStack` fires below `r`
either (possible only after an excursion drops the height). The
parked-`x`-leaves-before-the-rung clause of the crux note
(Theorems.lean:1825–1830) is F1, which *holds of every play*; the normal
form strengthens it to "no park at all before the rung", reached by
transforming π (§5). The endgame's content: **every winning π has a
winning rung-normal counterpart** — the B&G-Thm-1-shaped theorem we must
prove ourselves; their Thm 1 is the safety-flavoured instance of exactly
this sentence.

## 4. The induction measure

**Chosen: lexicographic `(B, L)` on the play**, where `B(π)` = the number
of `cBlocked` moves strictly before the rung pass `j`, `L(π)` =
`π.length`. Transformation steps:

1. **Excursion-pair deletion** — `[stackPile x b, …, pileStack x]` nets
   to identity on heights/board; the adjacent version is landed
   (`stackPile_pileStack_cancel`, Dominance.lean:536); the spread version
   carries the intermediate segment (`x`-seat- and height-blind — only
   c-suit moves read `heights c.suit`, and those are exactly the
   excursions and the rung itself). Effect: `B ↓`, `L ↓`.
2. **Twin-park redirect** — park `x` on `c.flipSuit` instead of `c`
   (legal by F2; F3 is the free sub-case). Effect: `B ↓ 1`, `L`
   unchanged; the replacement is not blocked.
3. **Storage elimination** (safety instances only — the Dominance
   rows): the parked chain goes up the foundation instead; each
   substitution stacks a card, so the descent is well-founded on rank
   (the safety bounds descend exactly two ranks — Cor. 3's mechanism,
   main.tex:1486–1488; Dominance.lean:668–673 leans on it). Effect:
   `B ↓`, `L ↓`.

Termination: steps 1–3 strictly decrease `B`; `B = 0` is `rungNormal`;
then bubbling `pileStack c` to the front is `L`-many landed squares and
the delete case finishes. B&G's own bookkeeping (main.tex:1380–1382,
1447–1448) is the same pair, phrased on "last noncompliant move" — the
per-step analysis should also work from the **last** blocked move
(their style), because the redirect (step 2) can interact with earlier
parks targeting the same twin seat (see §6).

**Rejected candidates.** `cascadeMeasure` (Dominance.lean:786) and
`heightDebt` (Dominance.lean:776) are NOT monotone along arbitrary
winning plays — worry-backs drop heights — so they cannot order the
transformation system itself; they stay in their landed jobs (the B2
induction, Restriction.lean:34; the drains inside one transformation).
The storage chain's rank descent is bounded by 13 — no hidden
divergence there.

## 5. The case order + lemma drafts

Work order for the attack agent (each item a named candidate; repair
discipline — every guard named, nothing vacuous; refute-first each
statement before proving):

**W1 — the scaffold (mostly assembly, [E/M]).**
`solvable_of_pileStack_aux`: strong induction on π.length packaging the
existing dispatch — nil / delete / run-root / eight squares — with the
IH-transfer guards explicit per case: `s₂.isLocked c = false`
(`reveal_notLocked` Theorems.lean:1504 for reveal; the other shapes do
not write `depths` or `c`'s seat — the transfers are the
`bottomOf_attach_ne`/`bottomOf_detach_ne` one-liners, **still
unwritten** per FARM_MEMORY), `s₂.board.bottomOf c = some b₀` (same
lemmas), and `apply_wf`. The blocked arms call W2/W3/W4.

**W2 — the rung pass exists [E].**
```lean
theorem rung_pass_of_win {st : State} (hwf : st.WF) {c : Card} {s₁ : State}
    (hm : st.apply (Move.pileStack c) = some s₁) {π : List Move} {w : State}
    (hw : st.run π = some w) (hwin : w.isWin = true) :
    ∃ π₁ π₂, π = π₁ ++ Move.pileStack c :: π₂ ∧
      ∀ u, st.run π₁ = some u → u.heights c.suit = st.heights c.suit
```
The last conjunct: the rung pass is the *first* exceedance of `r`. Kit:
`State.isVis_of_apply_pileStack` (TwinSwap.lean:219), `vis_off_cycle`,
`founds_gone` (State.lean:149 — this WF conjunct also closes the wave-5
"no-passing" alert (ii): the stNP witness predates `founds_gone`),
run-state analysis via `run_take_trace`.

**W3 — the excursion lemma [M].**
```lean
theorem excursion_pair_delete {st : State} (hwf : st.WF) {c x : Card} {b : Base}
    {γ π₂ : List Move} {w : State} (hσ : x.suit = c.suit)
    (hrk : x.rank.toIdx + 1 = st.heights x.suit)
    (hrun : st.run (Move.stackPile x b :: γ ++ Move.pileStack x :: π₂) = some w)
    (hblind : ∀ m ∈ γ, m.seatsOrReads x = false ∧ ¬ cSuitMove c m) :
    ∃ π', st.run (γ ++ π₂) = some w ∧ …
```
Spread version of `stackPile_pileStack_cancel` (Dominance.lean:536).
The `hblind` guard is the honest shape — spelling "the intermediate
segment does not read the dropped height or `x`'s seat" is a def-level
choice, see §7.

**W4 — the park episode [H, the endgame core].**
```lean
theorem park_episode_replay {st : State} (hwf : st.WF) {c x : Card} {b₀ : Base}
    {s₁ s₂ : State} (hnotlock : st.isLocked c = false)
    (hbot : st.board.bottomOf c = some b₀) (hnr : canReturnBase c b₀ = false)
    (hm : st.apply (Move.pileStack c) = some s₁)
    (hmk : st.apply (Move.deckPile x (Sum.inr c)) = some s₂)  -- or stackPile/pilePile
    (hwin : st.run (Move.deckPile x (Sum.inr c) :: rest) = some w ∧ w.isWin = true)
    -- license disjunction: twin seat ∨ tenant-stackable ∨ rank-mate return
    (hlic : (st.isVis c.flipSuit = true ∧ st.board.topOf (Sum.inr c.flipSuit) = none)
          ∨ x.rank.toIdx = st.heights x.suit
          ∨ ∃ d'', canSitOn c d'' = true ∧ st.isVis d'' = true ∧
              st.board.topOf (Sum.inr d'') = none) :
    s₁.solvableFrom
```
Three sub-lemmas, each mapped to landed kit:
- **W4a (twin-park)**: redirect to `deckPile x (inr c.flipSuit)`; the
  license for the seat divergence `x`-on-`c` vs `x`-on-twin is the C6-row
  machinery (`twinPair_placement_equi`, Dominance.lean:492, open) fed by
  `solvable_cargoTwin_transfer` (TwinSwap.lean:246) +
  `State.pilePile_return_legal` (TwinSwap.lean:309, proven). F3 is the
  free sub-case.
- **W4b (foundation channel, safety instances)**: `deckStack x` at the
  ready rung; then the *convergence at `j`*: source and replay boards
  coincide at the rung pass (both have `c` stacked; the redirected seats
  re-bare when the tenants exit, by F1) — the
  B&G-Thm-4-Case-1-invariant analogue, with gated convergence moves
  where theirs were free.
- **W4c (rank-mate return)**: worry `c` back onto a visible free `d''`
  with `canSitOn c d'' = true`, then replay π *verbatim* (the seat
  divergence `d` vs `d''` is twin-blind to every π-move; at `j` the
  worry-back's attach is undone by `pileStack c` and the states
  coincide). Template: `pileStack_stackPile_roundtrip` (Theorems.lean:36)
  minus `canReturnBase` — replaced by the `d''` guard.

**W5 — assembly.** Normal-form existence (`rungNormal_of_solvable`, by
§4's measure) + replay (`rungNormal_delete`: bubble +
`solvable_of_pileStack_step_delete`) ⇒ the crux. Then as Dominance
corollaries: the N-half (channels A/B available under `hsafe`; channel
A's no-passing half is now WF itself via `founds_gone`, State.lean:149 —
closing wave-5 alert (ii)); `deck_dominance_draw1` C = the same normal
form with `c` stocked (A landed: `draw1_cursor_solvable`,
Dominance.lean:370; B = the exchange cases, Dominance.lean:494–508);
`stackPile_safe_prunable` case 10 = W4b at the worry-created seat
(Dominance.lean:662–673).

## 6. Falsifiers (witness discipline, per statement)

- **W2**: refute shape = a WF state + winning play reaching heights 13
  in `c`'s suit without `pileStack c` — requires `deckStack c` with `c`
  visible-and-stocked, killing `vis_off_cycle`. Probe: `#eval`/decide
  grids on small deals. No Rust instrument speaks to this one.
- **W3**: refute shape = an excursion pair whose intermediate segment
  *does* read the dropped height or re-homes through `x`'s seat. Probe:
  `#eval` over short plays on 2-pile deals; test `hblind` non-vacuous
  (a vacuous guard is a statement bug — the `eStep_deckStack_unique`
  precedent).
- **W4a**: refute shape = the twin visible+free at the park, but π
  itself later parks on the twin ("otherwise untouched" violated) — the
  B&G Case-1-invariant failure. If a cyclic witness exists (redirect
  creates a new blocked park), the §4 measure is wrong. Probe:
  small-deal `#eval` grids hunting redirect cycles.
- **W4b**: refute shape = a park whose tenant is **not** stackable, twin
  unavailable, no rank-mate for `c` — the forced park (§7). **Rust
  instrument: the relocation-failure counter** — `convert_move`
  (src/convert.rs:9) does at most one relocation per abstract move
  (`PileStack`'s cover-card relocation, src/convert.rs:62–74;
  `find_free_pile` unwraps at src/convert.rs:138,153). Per
  no_pile_to_pile.md §5 item 2: replace the unwraps with a counted
  error, log every abstract move needing > K relocations. Zero logs
  over the solved corpus = storage depth ≤ K; a hit = the exact
  counterexample shape for Lean. **NOT yet implemented** — the cheapest
  empirical protection for the whole route.
- **W4c**: refute shape = `d''` fitting+free but π parks on `d''`
  before `j`. Probe: analytic — the guard must be checked against π, not
  the state alone (a state-level-only statement is the `toEngine_lifts`
  mistake class, FARM's REFUTED 2).
- **The crux itself**: the decisive empirical backstop is the
  verdict-level 2×2 ablation (`traverse::tests::phase0_verdict_ablation`,
  interaction doc §7 item 1/P1) plus the 1M/50k cross-checks; a mismatch
  falsifies the composed story, and the ablation bisect attributes it.

## 7. Gaps that are genuinely ours (orchestrator decisions)

1. **The forced park [GAP — the critical one].** When the twin seat is
   unavailable (hidden/foundation/occupied), the tenant `x` is not
   stackable (no `hsafe` in the crux), and no rank-mate return exists
   for `c`, the replay from `s₁` has no seat for `x` and no foundation
   channel — and F2 says the twin is the *only* alternative seat, so the
   park on `c` was forced in the source too. Neither B&G nor the repo
   docs settle this: their relocations are ungated (§2); our channel A/B
   assume safety (interaction doc §4), which the crux deliberately
   lacks. Options: (a) it never arises in a *winning* play (needs
   proof — e.g. the forced park's exit is `pileStack x`, rung-gated
   but `c`-suit-independent, and the draw of `x` could be delayed past
   the rung pass — a drawStep-2+ pace argument with no landed lemma);
   (b) the crux needs a repair (`hsafe`, or `initialReachable` scoping
   à la Restriction.lean:64); (c) a witness refutes the crux as stated.
   **Refute-first before W4.**
2. **Def-level choices in W3/W4.** `cBlocked`/`seatsOrReads` and the
   simulation relation (the φ mapping source prefix-states to replay
   states: heights offset +1, seat divergence, convergence at `j`) have
   no formal definitions yet. Statement-repair risk is concentrated
   here — every historical refutation in this cluster (B4Witness
   phantom tenant, B4LockedWitness dead pile, LiftWitness2 Fits-mirror)
   lived at a "the guard forgot this shape" seam. The B&G Case-1
   invariant (swapped piles, main.tex:1552–1553) is the template for the
   episode-invariant, but its convergence moves are free where ours are
   rung-gated — do not assume the port is mechanical.
3. **`rungNormal`'s form**: play-global (`∀ k m rest` decomposition) vs
   episode-list. The global form composes with the length induction
   more directly; the episode form makes the "otherwise untouched"
   guards local. Pick one early; both are falsifiable by the same
   probes (§6).
4. **The unwritten one-liners** (W1): the six non-reveal
   lockedness/bottomOf transfer lemmas — mechanical, but they gate
   everything; do them first, in the same batch as W1.
5. **Wave-5 alert (iii) stands for the Dominance rows**: height
   monotonicity along the *transformed* play (safety thresholds
   surviving worry-backs) is only guaranteed by the normal form itself —
   the N-half proof must carry `hsafe`-preservation as an invariant of
   the transformation: B&G Thm 5's compatibility argument in our setting
   (main.tex:1619–1632 is the port target).
6. **The relocation instrument (§6, W4b)** is unimplemented; it protects
   the published 81.95%/47.58% numbers and is the cheapest falsifier on
   the board — phase-0 material before any W4 proof effort.

*Route reading by the farm's READING agent. Nothing here is proven; every
statement named in §5 must pass the refute-first gate before proof work.*
