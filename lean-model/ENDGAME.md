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
/-- The blocked shapes: seating on c, and same-suit worry-backs.
    (REPAIRED 2026-09-14: the draft's separate `.stackPile x _` arm was
    SHADOWED by the 3-way seat group — fold the excursion test into the
    stackPile arm.) -/
def cBlocked (c : Card) : Move → Bool
  | .deckPile _ b'' | .pilePile _ b'' => decide (b'' = Sum.inr c)
  | .stackPile x b'' =>
      decide (b'' = Sum.inr c) || decide (x.suit = c.suit)
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
      ∀ u, st.run π₁ = some u → u.heights c.suit ≤ st.heights c.suit
```
The last conjunct (REPAIRED 2026-09-14: the draft said `=` — FALSE: an
excursion before the rung pass dips the height; witness
Temp/opencode/w2probe.lean; honest first-exceedance form is `≤`):
the rung pass is the *first* exceedance of `r`. LANDED (Theorems.lean,
`rung_pass_aux`/`rung_prefix_cons`/`rung_pass_of_win`). Kit:
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

**W4 — the park episode [H, the endgame core] — REFORMULATED 2026-09-14
(user decision).** The staged license disjunction below is SUPERSEDED:
the forced-park shape (no license holds) is known FALSE — no refutation
witness owed. The route forward is **twin-swap canonicalization**: the
park/pilePile-shaped reshaping is absorbed by the now-fully-proven
TwinSwap machinery — `State.swapTwin` (the unconditional automorphism,
heights permuted with the cards), `solvable_swapTwin`,
`solvable_cargoTwin_transfer`, `pilePile_return_legal`,
`aboveOf_congr_off` — so the replay never case-splits on the park's
legality: it transfers the cargo to the twin representation and lets
the automorphism carry the verdict. The exact statement shape is the
open design item: candidates include (a) swap-the-successor — `s₁ ∨
swapTwin-pair s₁` solvable; (b) the statement over the twin quotient
(the engine's own representation — verdicts on the quotient, ambiguous
seats unidentified); (c) the play-level form — the winning play rewrites
via swap-steps to one that never parks on `c`, folded into W5's
normal-form existence. What the three sub-lemmas below still buy: their
licenses are the FREE cases of the canonicalization (F3's sub-case
analysis feeds whichever shape is chosen). W4b/W4c remain the
Dominance-row corollaries' channels either way.
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

## 8. W4 — the reformulated statement, three drafts (design pass, 2026-09-14)

Design deliverable; nothing proven; gaps marked [GAP]/[IN-FLIGHT]; Lean claims
cite file:line. Decision context: FARM.md:286-294 — the staged crux is FALSE at
the forced-park shape (known); the repair is twin-swap canonicalization, not a
guard.

### 8.0 Inventory + corner taxonomy

Landed: `State.swapTwin` (TwinSwap.lean:50 — heights FIXED, NOT an
automorphism: TwinSwap.lean:44-49, TwinSwapWitness.lean:12-16),
`solvable_cargoTwin_transfer`/`pilePile_return_legal`/`aboveOf_congr_off`/
`solvable_cargoTwin`/`redundantTwins_heights_eq` (TwinSwap.lean:246/382/361/
504/110); the exchange substrate `exchangeTwin`/`exchangeTwinCargo`
(TwinExchange.lean:86/118, proven) + the sorry rows `…_exchange` [H]
(TwinExchange.lean:173), `…_exchange_bare` [M] (:205); the W1-W3 kit (aux
Theorems.lean:1953, ∃-hyp :1957; `cBlocked` :1893; `rung_pass_of_win` :2258;
`excursion_pair_delete_adjacent` :2293; `seatsOrReads`/`excursionSim`
Frame.lean:1087/1201). **[IN-FLIGHT]** the four §5 names (`apply_swapTwin`,
`solvable_swapTwin`, `solvable_cover_twin_iff`, `swapTwin_wf`) are NOT
greppable at design time (09:10, the user's live edit) — contracts R1-R4,
§8.4. The heights-permutation design must respect TwinSwapWitness.lean:18-24
(suit counts are shared with non-swapped cards) **[GAP]**.

Corner taxonomy (F2: the twin is the only alternative seat, Basic.lean:144 +
`Card.receivers` Basic.lean:177):
- **(i) twin bare+visible** — the redirect works (fit:
  `canSitOn_swapTwin_right`, Basic.lean:243); the FREE cases (the old W4a/W4c
  licenses); hazard: the redirect cycle (§6 W4a).
- **(ii) twin occupied by a FITTING cargo `y`** — the exchange corner:
  `exchangeTwinCargo c` moves `y`'s run onto `c`'s seat board-only
  (TwinExchange.lean:86-91), licensed by [H]. The exchange BLOCKS the stack
  (`y` on `c`): the canonical play stacks `c` after `y` departs (F1) — a
  reorder, not a stack-successor fact.
- **(iii) twin unavailable** (hidden / foundation-passed / deal-inherited
  NON-FITTING occupier — Bridge.lean:466 trap, TwinExchange.lean:54-58) —
  the TRUE corner: no redirect, no exchange license, no delayable draw at
  draw-3 (draw-1: the reserve lemma, Dominance.lean:370, rescues). The staged
  `s₁.solvableFrom` is FALSE here — the user's decision.
- Shared convergence core (all three proofs): within an episode window
  [park, departure] the threads differ only at twin seats; at each tenant's
  own `pileStack` (rung-gated, `c`-suit-independent) they CONVERGE — B&G
  Case-1 (main.tex:1552-1553) at gated moves; TwinExchange.lean:27-50.

### 8.1 (a) swap-the-successor — the disjunctive twin-stack theorem

The literal reading of "`s₁ ∨ swapTwin-pair s₁`" — the swap-image
`s₁.swapTwin c` — is VACUOUS (the R1 conjugation square + R2 equisolve the
disjuncts); the non-vacuous draft is the TWIN-STACK successor:

```lean
theorem solvable_of_pileStack_or_twin {st : State} (hwf : st.WF) {c : Card}
    {s₁ s₁' : State} (hnotlock : st.isLocked c = false)
    (hm  : st.apply (Move.pileStack c) = some s₁)
    (hmt : st.apply (Move.pileStack c.flipSuit) = some s₁')
    (hsol : st.solvableFrom) :
    s₁.solvableFrom ∨ s₁'.solvableFrom := sorry
```
`hwf`/`hnotlock` DERIVED (the crux's own; carried by the `lockedness_*`
transfers, Theorems.lean:2008-2085); `hm` the move; `hsol` given; `hmt`
**ASSUMED, load-bearing** — packs twin-visible + twin-bare + `heights
c.flipSuit.suit = c.rank.toIdx` (from `redundantTwins_heights_eq`,
TwinSwap.lean:110). Cannot drop: at unequal heights disjunct-2 does not
exist (collapse to the FALSE staged crux); underivable from `hsafe`
(LeastRedundantWitness, Dominance.lean:263-284).

Proof: `rung_pass_of_win` (Theorems.lean:2258) + the §4 descent; parks
redirect at (i) (blindness: `aboveOf_congr_off`, TwinSwap.lean:361 — the
W3-φ template, Frame.lean:1201), exchange-canonicalize at (ii)
(`solvable_cargoTwin`, TwinSwap.lean:504 — executable there: `c` bare by
`hm`; or [H]); the redirect-cycle terminal escapes to the mirror world
(R1+R2+equal-heights + the aux, W1) delivering `s₁'`. **[GAP]**
`redirect_or_mirror` (descent terminal; template: B&G Case-2,
main.tex:1438-1442); license shared with the open
`twinPair_placement_equi` (Dominance.lean:749). Forced-park survival:
**SILENT** at (iii) — and (ii)-unequal — `hmt` fails (twin not bare, or
the rung mismatch); speaks only at redirect-cycle shapes — (a) does not
repair the corner. Corollary yield: weak — `hmt` underivable from `hsafe`
(Dominance.lean:92-96 bounds same-colour at `r−2`), so none of the three
rows (Dominance.lean:237/522/678) fall; only §5.5 instances
(`isRedundantStack`, Dominance.lean:246). Refute-first: (a1) both stacks
fire, `st` solvable, BOTH successors dead — kills (a); (a2) `hmt`
non-vacuity (`eStep_deckStack_unique` class); (a3) the redirect-cycle
hunt — no witness ⇒ disjunct-2 is dead weight.

### 8.2 (b) the twin quotient — the verdict-canonical package

```lean
def TwinEq (st st' : State) : Prop :=
  EqvGen (fun u v => ∃ t, v = u.swapTwin t) st st'

theorem solvable_of_pileStack_quot {st : State} (hwf : st.WF) {c : Card}
    {s₁ : State} (hnotlock : st.isLocked c = false)
    (hm : st.apply (Move.pileStack c) = some s₁) (hsol : st.solvableFrom) :
    ∃ s₁', TwinEq s₁ s₁' ∧ s₁'.solvableFrom := sorry
```
**Vacuity trap, plainly**: orbits are swap-images and R2 makes verdicts
orbit-invariant — the ∃ is witnessed by `s₁` itself: the bare form is
EQUIVALENT to the staged (false) crux. Teeth require identifying more
than orbits — exactly TwinExchange's rows (`exchangeTwinCargo` is NOT a
`swapTwin` orbit: cargo values move, heights untouched,
TwinExchange.lean:127-128 vs TwinSwap.lean:50-57):

```lean
/-- (b2) the ambiguous cover — the deck-cover specialization of the
    [M] row: parking x on c vs on the twin. -/
theorem solvable_cover_twin_iff' {st : State} {x c : Card} {p p' : State}
    (hvis : st.isVis c = true) (hvis' : st.isVis c.flipSuit = true)
    (hfree : st.board.topOf (Sum.inr c) = none)
    (hfree' : st.board.topOf (Sum.inr c.flipSuit) = none)
    (hp : st.apply (Move.deckPile x (Sum.inr c)) = some p)
    (hp' : st.apply (Move.deckPile x (Sum.inr c.flipSuit)) = some p') :
    p.solvableFrom ↔ p'.solvableFrom := sorry
```
— the cover-successors differ at exactly the two seat slots (`p' =
`p.exchangeTwinCargo c` **[GAP: the `Board.ext_topOf` identification
one-liner — the same TwinExchange.lean:197-200 names]**); the statement
is `exchange_bare` (TwinExchange.lean:205) at `hzone`'s visible arm; its
redundancy-licensed instance is the open `twinPair_placement_equi`
(Dominance.lean:749); (b3) is [H] itself. `hvis/hvis'/hfree/hfree'`
ASSUMED (the ambiguous-seats shape — the premiseless form is the
refuted-family risk); `hp/hp'` the parks. Proof: the three-link
mirroring (TwinExchange.lean:27-50) — frozen phase (`aboveOf_congr_off` +
`canSitOn_swapTwin_right/_left`, Basic.lean:243/249), bridge
(`solvable_cargoTwin`, TwinSwap.lean:504), tails coincide. **[GAP]** the
walk-passing structural correspondence (TwinExchange.lean:32-38); R2 for
the orbit layer. Forced-park survival: at (ii) the class contains the
twin-bare representative — the descent runs there, the verdict transfers
back; at (iii) `hfit` dies with the deal-inherited cargo — silent IFF the
premiseless exchange is false (TwinExchange.lean:52-64's gate); at
(iii)-hidden/foundationed there is no cargo — silent. Survives as a
CLASS statement; delivers no stack-successor conclusion — the endpoint
is again (c)'s certificate, by the class route. Corollary yield: the
engine-facing verdict lemmas (the TT canonicalization, Macro.lean:76) +
the §5.5 row (Dominance.lean:749 as a (b2) corollary); the three target
rows only via (c)'s assembly. Refute-first: (b1) the premiseless-exchange
witness hunt (TwinExchange.lean:58-64); (b2) the phantom-arm stuck shape
(TwinExchange.lean:62-64); (b3) the class-membership probe: the extended
class of a corner-(ii) state contains a park-free-in-`c` member.

### 8.3 (c) play-level swap-rewrites folded into W5 — the characterized normal form

The pure normal-form existence is FALSE at (iii) (the park is forced), so
W5 carves the corner out with an explicit certificate — an ADDED
CONCLUSION, not a guard (hypotheses unchanged; the falsity quarantined
in a probe-able predicate):

```lean
/-- The forced-park certificate (DRAFT): the corner where no pre-pass
    canonicalization removes the park on c. State-level arms; the
    tenant-unstackability arm is play-level and stays OUT (the
    toEngine_lifts mistake class, §6 W4c's note). -/
def State.forcedPark (st : State) (c : Card) : Prop :=
  ¬(st.isVis c.flipSuit = true ∧ st.board.topOf (Sum.inr c.flipSuit) = none) ∧
  ∀ d, canSitOn c d = true →
    ¬(st.isVis d = true ∧ st.board.topOf (Sum.inr d) = none)

theorem rungNormal_or_forcedPark {st : State} (hwf : st.WF) {c : Card}
    {s₁ : State} (hnotlock : st.isLocked c = false)
    (hm : st.apply (Move.pileStack c) = some s₁) (hsol : st.solvableFrom) :
    (∃ π w, st.run π = some w ∧ w.isWin = true ∧
      ∃ π₁ π₂, π = π₁ ++ Move.pileStack c :: π₂ ∧
        ∀ m ∈ π₁, cBlocked c m = false) ∨ st.forcedPark c := sorry

/-- The repaired crux: the staged conclusion off the certificate. -/
theorem solvable_of_pileStack' {st : State} (hwf : st.WF) {c : Card} {s₁ : State}
    (hnotlock : st.isLocked c = false)
    (hm : st.apply (Move.pileStack c) = some s₁) (hsol : st.solvableFrom) :
    s₁.solvableFrom ∨ st.forcedPark c := sorry
```
(`solvable_of_pileStack'` = disjunct-1's play + the LANDED aux
(Theorems.lean:1953, ∃-hyp :1957 IS disjunct-1) + `…_step_delete`
(Theorems.lean:1744) — the W1 scaffold untouched; all hypotheses DERIVED
from the staged crux, Theorems.lean:2383-2386.)

Proof: the §4 (B, L) descent — 1 excursion-pair deletion (W3 adjacent
:2293 + `stackPile_pileStack_cancel`, Dominance.lean:536; spread on
`excursionSim`, Frame.lean:1201); 2' the exchange-canonicalizing
redirect — (i) plain, (ii) transfer-then-redirect (`solvable_cargoTwin`,
executable: `c` bare by `hm`) with the transfer B-neutral, (iii) the
descent STALLS and emits the certificate; 3 storage elimination (the
safety instances); the episode windows ride the convergence core (§8.0).
**[GAP]** (c-α) the divergence-window one-step replay — the
walk-agreement lemma, `aboveOf_congr_off` the template (the same piece
W3's φ needs); (c-β) the transfer's B-neutrality stalls the §4 measure
(last-noncompliant-first, or a third component); (c-γ) certificate
EXACTNESS — too narrow reintroduces falsity, too wide kills the
corollaries. Forced-park survival: at (iii) the theorem asserts the
certificate — TRUE there by construction (the arms name the
unavailability shapes); at (i)/(ii) the normal form exists and the
conclusion is delivered — the only candidate that both SPEAKS at the
corner and closes the crux off it. Corollary yield: all three rows UNDER
`hsafe` — the bridge: `hsafe` kills the certificate (the opposite-colour
conjunct makes every live rank-`r−1` tenant stackable — channel A; the
same-colour conjunct kills the no-return arm — channel B;
Dominance.lean:92-96). **[GAP: the channel-A/B simulation with
`hsafe`-preservation along the transformed play — §7.5 alert (iii), the
B&G Thm-5 port, main.tex:1619-1632]** — which the rows always owed
(Dominance.lean:230-234); case 10 = the same assembly at the
worry-created seat (Dominance.lean:662-673); `deck_dominance_draw1` C
adds the landed reserve lemma (Dominance.lean:370). Refute-first:
(c1) certificate exactness — (α) a staged-falsity shape where
`forcedPark` is FALSE (too narrow), (β) an `hsafe` state matching it
(too wide); (c2) a repeating redirect-then-transfer cycle (B never
drops); (c3) re-verify the `lockedness_*` transfers per aux arm
(Theorems.lean:2008-2085).

### 8.4 Trade-offs + recommendation (for the user to override)

| | falsity risk | proof cost | corollary yield | W1-W3 fit |
|---|---|---|---|---|
| (a) twin-stack disjunction | low (silent at the corner); `hmt` vacuity risk | low (rides (c)'s descent) | poor (§5.5 only) | aux reused as-is |
| (b) quotient/verdict package | the [H]/[M] rows' own gates (deal-adjacency corner) | medium (mirroring designed; walk lemma missing) | engine verdicts + §5.5; rows only via (c)'s endpoint | orthogonal (state-level) |
| (c) normal form + certificate | certificate exactness (c1) — quarantined, probe-able | high (descent + (c-α)/(c-β) + the bridge) | all three rows (via the [GAP] bridge) | exact (aux's ∃-form IS disjunct-1) |

Recommendation: **(c) as the target, with (b)'s exchange package as its
lemma-0 — the hybrid**. (1) falsity quarantined in a named predicate —
the refute-first discipline's best shape; (2) the landed W1 aux consumes
disjunct-1 verbatim (Theorems.lean:1957), W2/W3 as-is — zero rework;
(3) all three Dominance rows hang off it with ONE shared remaining gap
(the `hsafe`-preservation bridge); (4) (b)'s mirroring
(TwinExchange.lean:27-50) is the designed proof of the descent's hardest
step — buy it as lemmas, don't re-derive. Demote (a) to an `hmt`-shape
corollary (keeps the §5.5 channel warm). Propagation cost, flagged: the
disjunct reaches `solvable_of_accomm_step` (Theorems.lean:2393-2401) —
corner-exclusion mid-accommodation is unproven **[GAP]**; the
alternative is proving the certificate vacuous on accommodation-reachable
states (B2-side, unstarted).

Contracts record (the [IN-FLIGHT] four): R1 `apply_swapTwin` — the
conjugation square, (a)'s mirror case only; R2 `solvable_swapTwin` — the
orbit layer, (b)'s trivial half; R3 `solvable_cover_twin_iff` — (b2) =
`exchange_bare` at the deck-cover; R4 `swapTwin_wf` — WF preservation,
the heights-permutation question (witnesses/TwinSwapWitness.lean:18-24).
(c) needs NONE directly — it rides the landed `solvable_cargoTwin` + the
[H]/[M] rows; the hybrid needs R2/R4 only for the droppable orbit layer.
