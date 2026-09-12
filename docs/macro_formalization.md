# Macro (commitment) formalization — proof notes

Working document for replacing the 5-move engine game with a commitment game of
two moves, together with the theorems needed to prove it exact.

Legend: [x] established / [~] claimed & cross-validated, proof pending / [ ] open

Line references are pinned to commit `5146b98` and *will* drift — prefer
searching by function name.

Build sequencing (recorded): Phase 0 — falsifiers on the *current*
engine; Phase 1 — the architecture-independent spine (the reshape lemma,
T, L1/L2, the safe-stack port); Phase 2 — this game, gated on verdict
equality with the current engine. See the interaction doc's §8 and the
soundness ledger's migration plan.

## 0. Claims

- **C1 (Reduction).** The old game can be replaced by a commitment game with two
  moves — `Draw(d)` and `Reveal(c)` — where all reversible pile↔stack shuffling
  is absorbed into a computed *accommodation* per commitment. Solvability is
  preserved (both directions).
- **C2 (Bound).** Each commitment, applied to a state, yields at most **2**
  distinct post-states (in the engine's state abstraction):
  {target card lands on the tableau, target card lands on the stack}.
  (Sharpened and measured in §6 — the true form is ≤2 *reversible-closure
  classes* per commitment; state-level multiplicity is unbounded — and
  proved in the streamlined poset form in §7.)
- **Verdict status (2026-09):** the macro game on the *direct* transition
  function now matches the shipped solver on 64 games across both draw
  steps (oracle and fast paths equal; `macro_verdict_matches_engine`),
  and a larger 128-game sweep lives `#[ignore]`d as the acceptance harness.

Supporting theorems:

- **T (Twin swap).** Local shuffling of same-color suits within the piles
  preserves solvability.
- **A (Accommodation reduction).** Accommodating a commitment requires only
  stack↔pile shuffling.

## 1. Preliminaries: the engine's state abstraction

A state records (src/state.rs:451-459):

- the stack (foundation) height of each suit (16 bits),
- the size of each pile's *hidden structure* — the dealt cards not yet revealed
  (16 bits, per-pile counts only; identities are *not* encoded),
- the deck order and draw offset (29 bits),
- the set of visible tableau cards — kept in the runtime struct, but not
  part of the encode (re-derived as the complement on decode).

Two things are deliberately **not** recorded:

1. *Where* a visible card sits (which pile, in which run). Moves mutate only the
   visible set: `DeckPile`/`StackPile` just add to `visible_mask`
   (src/state.rs:365-393), `PileStack` removes from it, and `Reveal(c)` pops
   the structure under `c` while `c` stays in the visible set (src/state.rs:395-402).
2. *Which* cards remain in each pile's hidden structure (only the sizes are
   encoded, src/hidden.rs:195-204).

Rules facts used throughout:

- Tableau stacking depends only on (rank, color): a card of rank r, color c̄
  lands on a card of rank r+1, opposite color. Suit-within-color matters only to
  the stack (foundation prefixes are per-suit).
- The stack per suit is always a prefix A..f(s), so "card is stackable" =
  `f(suit(card)) == rank(card)` (src/stack.rs:48-50; ranks are 0-indexed —
  height f means ranks 0..f−1 are stacked, so the next acceptable card has
  rank exactly f).
- There are no tableau↔tableau moves except the surface reveal
  (gen_moves emits none; the reveal mask is `vis & locked & free_slot`,
  src/state.rs:293). Call this inherited fact **A1**; it is cross-validated
  (README: 1M Solvitaire seeds, Klondike-solver seeds 0..50k).

## 2. Lemma A — the accommodation reduction [x]

**Lemma A1 (commitment partition).** Every irreversible move introduces either
a deck card (`DeckPile`, `DeckStack`) or a hidden card (`Reveal`,
`PileStack`-on-locked = reveal-by-stacking). This is exactly the classification
of `reverse_move` (src/state.rs:312-321): only `PileStack` (unlocked) and
`StackPile` are reversible.

**Lemma A2 (reversible fragment).** A move sequence with no commitment in it
consists solely of `PileStack`(unlocked)/`StackPile`. Such shuffles preserve
the deck and the hidden structures, and change only pile tops and stack tops.
Pops are allowed only from pile tops that are stackable; pushes only land on
compatible tops (or king→empty).

**Lemma A3 (accommodation reduction).** Fix a state s and a commitment m:

- `Draw(d)`: the target card is X = d;
- `Reveal(c)`: the target card is X = c — the *departing* surface card. (The
  newly revealed card r inherits c's place and needs no destination of its own.)

Then m is executable from s iff some shuffle σ of the reversible closure of s
gives X a legal destination (compatible tableau top, king→empty, or stackable).
Any old-game play therefore regroups as
shuffle, commit, shuffle, commit, ..., which is precisely the macro game.

*Proof.* (⇐) shuffles are legal moves, and m is legal at σ(s). (⇒) between two
consecutive commitments of any play, every move is reversible (A1), hence is a
shuffle (A2); the commitment's legality is evaluated at the state where it is
made. Completeness of "shuffling is the only accommodation mechanism" rests on
A1. ∎

Consequence: macro search = for each candidate commitment (each drawable d,
each surface c), decide whether an accommodating shuffle exists, and
characterize the post-states.

### Structural facts for reasoning about accommodations

- **(F1) Two twins only.** For target X of rank r, color c̄, the tableau
  destinations are exactly the two cards of rank r+1, opposite color — the
  twins Y, Ȳ. Each is in exactly one of: pile top (ready), buried in a pile,
  on the stack, in the deck, or still hidden.
- **(F2) Segment transfer.** Unstacking a deep card from the stack forces
  unstacking everything above it in that suit first; that foundation segment
  forms a valid run, and landing the whole segment on a single compatible top
  is one composite action. Any *split* of the segment needs at least the same
  destination for its top card, which the whole-segment landing also uses.
  (The claim that whole-segment landing dominates all splits still needs a
  proof — see O5.)
- **(F3) Forced sweep.** When a dominantly-safe stack move exists, the engine
  already treats stacking as forced and returns it as the only move
  (`pile_stack_dom`, src/state.rs:176-183; safety = min over same-color twin
  suit heights, `Stack::dominance_mask`, src/stack.rs:26-32).

## 3. Theorem T — twin swap (local same-color suit shuffling) [~]

**Statement (to be confirmed, see O1/O2).** Let X and X̄ be two cards of the
same rank and same color, different suits (e.g. 8♠ and 8♣). If **both** reside
in the tableau piles (anywhere: visible runs, surfaces, or hidden in
structures), then the two games differing by exchanging the positions of X and
X̄ are solvability-equivalent. Equivalently: local shuffling of same-color
suits within the piles preserves solvability.

**Why the hypothesis has force.** If both twins are in the piles then neither
is on the stack, so both foundation heights of that color are < rank(X) — there
is room to re-interleave the two suits' foundation prefixes. The deck is
untouched by the swap, so the draw order is identical in both games.

**Roles in the engine today.**

1. Exactness of the state abstraction: the encode forgets arrangement and
   hidden identities; same-encode concrete positions are related by local
   suit shuffles, which T says are solvability-equivalent. Without T the
   transposition table (src/traverse.rs:81) could skip a winning state.
2. Dominance pruning of twin choices: the `paired_stack` / `least_stack` /
   `suit_filter` block (src/state.rs:222-286) only searches the canonical
   twin; the post-reveal filter allows stacking {c, twin(c)}
   (src/pruning.rs:90-102).
3. Foundation safety dominance: `Stack::dominance_mask` (src/stack.rs:26-32).

**Proof strategy (to write out).**

Take a winning play P for the game with X at position p, X̄ at position q;
build a winning play P' for the swapped game. Transform P by *position-based
relabeling*: whenever P moves the card at position p (which is X), P' moves the
card at the same position (which is X̄), and vice versa; all other moves are
unchanged. Legality of non-twin moves is unaffected:

- tableau legality is (rank, color)-based, and twins agree on both;
- stackability of a non-twin card depends only on its own suit's foundation
  height, which is untouched by the relabeling while both twins remain
  un-stacked.

The only obstruction is the *stack asymmetry*: when P stacks X (say X♠, needing
f(♠) = r−1 at that moment), P' wants to stack X♣ at the same position, needing
f(♣) = r−1 — which may not hold yet. Bridge it with the interleaving lemma:

- **(L1, interleaving).** The tableau is color-blind, so the order in which the
  two same-color suits climb their foundations can be exchanged arbitrarily,
  subject only to per-card accessibility, and accessibility of a card does not
  depend on the interleaving (its blockers are removed by their own stacking
  or by reveals, in an order that can be carried along).
  ⇒ P' can first raise the ♣ prefix to r−1 (replaying, in its own suit, the
  "unbury" structure P used to raise the ♠ prefix), then stack X♣, and
  continue.

Proof obligations / open items:

- **O1.** Locality: is the swap restricted to *within one pile*, or between any
  two pile positions? (C2 needs the destination-collapse version: placing X on
  twin top Y vs Ȳ — but note both yield the same `Encode`, so this may not
  even need a cross-pile swap; see §4.)
- **O2. Hidden twins — discharged** (no_pile_to_pile.md §1): within a
  game, a pile's hidden structure is always a prefix of the original deal,
  so the per-pile counts pin the hidden identities. The encode's hidden
  amnesia therefore never conflates different hidden arrangements within
  a game, and T is not needed for hidden cards. What remains of O2 is the
  *cross-game* question (two deals differing by a hidden twin swap), which
  is the local-shuffling statement of T itself.
- **O3.** Boundary case: f(♠) = r−1 but f(♣) < r−1 (one twin stackable now,
  the other not) — the interleaving lemma must cover it.
- **O4.** Formalize in Lean (lean-verify/), next to the existing Klondike
  model; brute-check against the ref_graph CSVs.
- **O5.** Segment-split dominance (F2).

## 4. C2 via T — at most 2 outcomes per commitment [~]

Let m be a commitment with target card X (rank r, color c̄). The outcomes:

1. **Tableau outcome.** X lands on a tableau pile. By F1 there are at most two
   destination cards (the twins Y, Ȳ), and:
   - both landings produce the *same engine state* (same visible set, same
     structure sizes, same stack, same deck) — the placement position is not
     part of the state;
   - T guarantees that merging these two concrete landings is exact.
2. **Stack outcome.** X is stackable and is stacked instead (`Reveal(c)` via
   stacking c = the old `PileStackReveal`; `Draw(d)` straight to the stack = the
   old `DeckStack`). This is a genuinely different state (stack height +1,
   X leaves the visible set).

Hence at most 2 outcome *kinds* per commitment. The measured and corrected
form of the bound is in §6.3/§6.7: ≤ 2 reversible-closure classes, with the
second class labeled by the irreversible scar of the accommodation, not by
the destination twin (classical T-collapse covers the twin choice only).
Additional collapsing:

- If X is *dominantly* stackable (F3), the tableau outcome is dominated and the
  commitment has a single outcome.
- Accommodation-side choices (which twin to unbury, where a worried-back
  segment lands) collapse the same way: each accommodation chain targets one
  specific twin card, and by T the twin choice is WLOG.

Open: prove that the accommodation itself contributes no extra state choice
(minimality of the forced stacking set — see O6), and the terminal sweep:

- **O6.** Minimality/uniqueness of the accommodation: two different minimal
  accommodating shuffles must yield the same post-state, or be dominated.
  (Resolved into §6.3–6.5: an operational canonical form + an in-tree
  falsifier.)
- **O7.** Terminal handling: the last commitments do not empty the tableau by
  themselves; specify the `Finish` pseudo-macro (stack sweep until stuck, win
  iff all 52 stacked) and its interaction with `is_sure_win`
  (src/state.rs:444-447).

## 5. Empirical companion (runs alongside the proofs)

- **Differential checker.** For states sampled from real games and solver
  runs: enumerate the old-formalism candidates (the `ListStatesCallback`
  traversal, src/mcts_solver.rs:58-83) and assert every candidate end-state is
  `equivalent_to` one of its commitment's ≤2 outcomes, and every macro script
  is legal in the old game. Any mismatch is a hole in T, A, or the old
  dominance rules.
- **Full-corpus verdict cross-check.** Old solver vs macro solver on the
  Solvitaire 1..1M sample and Klondike-solver 0..50k; verdicts must match
  exactly.

## 6. The closure algebra and the efficient transition
(derived 2026-09, with the first in-tree measurements; probe code
`src/macro_game.rs`, branch `macro-game`)

This section turns the scaffold measurements into the design theory for a
*direct* transition function: the point of the rework is that macro move
generation and state transition must be constant-work-per-commitment, not a
closure exploration. The algebra shows that this is possible.

### 6.1 The closure, algebraically [~; shape measured]

By A2, the reversible closure of `s` consists exactly of the states obtained
from `s` by shuttling *unlocked* cards between tableau and foundation; deck
order+offset and the hidden structures are invariant. Therefore, in a
closure state:

- deck and hidden are fixed;
- per suit, the foundation content ranges over a **height interval** (only
  prefix digs are possible — F2);
- the visible/top changes come only from worried-back cards (a worried-back
  card becomes a top, and covers the top it landed on).

Measurement confirming the shape (probe `macro_scaffold_smoke`): outcome
post-states of one commitment vary only in the *stack* component, forming
per-suit interval lattices (e.g. `[2000, 1000, 0]`, `[320, 220, 120, 210]`
— nibble-lattices over two suits), with hidden and deck parts constant.
State-level multiplicity is **not bounded by 2 or 4** — floating worry-back
coordinates multiply out (an 8-state grid was observed) — which forces the
corrected C2 of §6.3.

### 6.2 Locality lemma [x — formula arithmetic]

For commitment target `X` (rank `r`, color χ): covering a destination twin
`Y` requires a card of type `Y − 4`, which is rank `r`, color χ — i.e. the
type of `X` itself: `{X, twin(X)}`. As `X` is in flight during its own
commitment — off-tableau for a `Draw`, and locked-hence-never-a-coverer
for a `Reveal` (the departing surface sits on *hidden* cards, so it
covers no destination) — **the only pre-existing blocker of `X`'s landing
in the whole deck is `twin(X)`**. This is the "never a third suit"
observation in exact form: a commitment's interference zone is one type.

### 6.3 C2, corrected and measured [~]

- **State-level ≤ 2 is false, and the two-twin-neighborhood "≤ 4" is not
  the right level either** — free floats form products. The true claim:
  *each commitment has at most 2 post-state **closure classes***
  (tableau-kind, stack-kind).
- **Free-float collapse.** A float outside the commitment's type
  neighborhood (type `X`, `X±4`) has its flip-legality masks untouched by
  the commitment's placement, so the shuffle separating two accommodation
  variants remains legal after the commitment: free variants are mutually
  reachable post-commitment, hence one closure class. (Modulo the same
  type-neighborhood mask check as L1/L2 — mechanical; pending.)
- **Measurement.** Quotienting post-states by mutual reversible
  reachability (`closure_classes`, `closure_contains`): across 200 games of
  greedy macro play (default_shuffle seeds 12..111, draw 1 and 3) — 16,791
  enumerated commitments (§6.7's histogram; an earlier first pass counted
  ≈4.5k) — **max distinct closure classes per commitment =
  2 — zero violations**. The probe asserts this in-tree; a value ≥ 3 is the
  falsifier.
- **What is left of C2.** The interacting corner: only `twin(X)` can be
  frozen by the commitment (e.g. on a stack outcome, `f(suit(X))` moves past
  `r`, killing `twin(X)`'s own stackability). The remaining case list —
  `twin(X)` ∈ {stacked, on `Y`, on `Ȳ`, free} — is where the dominance
  eliminations (5.1/5.4: "a dominant card is never available for worrying
  back"; minimality of the accommodation) remove the extra configurations.

### 6.4 The availability algebra [~]

Whether an outcome shape exists for target `X` at the raw state reduces to
a **well-founded recursion over types**, not a search. Cases for the tableau
outcome (need an uncovered top of type `X+4`):

1. **Direct** — `bm[X+4]` holds (type-level, already `X ∈ free_slot`).
2. **Dig** — `Y` is covered; its coverer is `twin(X)` (forced by §6.2),
   which is then a top; vacating it = stacking it (`sm[twin(X)]` — a
   foundation prefix fact) or, if a king, moving to an empty pile.
3. **Borrow** — a `P`-twin sits on its suit's foundation top; worry it back
   (`SP` needs an uncovered top of type `X+8` — the same question one rank
   up, same color).
4. **Deeper dig** — `twin(X)` itself is covered; coverers descend in rank
   and flip color per level; the recursion bottoms out at **aces**, which
   are never coverable.

Borrows ascend toward kings (which terminate at holes); digs descend
toward aces. So availability is a monotone, rank-bounded AND-OR computation
over ≤ 26 types — no closure exploration. The stack outcome is the same
machinery: `X` is stackable now, or becomes so after raising the prefix —
each missing prefix card needs the very same one-card dig, descending to
aces.

**Completeness was the open part**: whether these four cases exhaust the
closure's ways of producing a landing is now *measured-closed* — the §6.6
differential found the crease real (chained borrows/digs of depth > 1) and
confined it: the bounded neighborhood BFS fallback covers it exactly, with
27/5129 firings. So the list of cases is now empirically exhaustive over
the corpus; the remaining honesty item is that "depth-4.." bounds are
empirical, not proven.

### 6.5 The representation fact [x — engine invariant]

The abstract moves are total, arrangement-free functions of the abstract
state; their preconditions are answered at type level by the masks (§3 of
`no_pile_to_pile.md`); and the type level is *per-card exact* exactly where
it matters: while `X` is off-tableau (deck, hidden), `bm[type(X)]` says
whether `twin(X)` specifically is an uncovered top, the parity over a single
visible twin being exact. For the `Reveal` commitment, where the departing
surface is still on-tableau, per-card questions about `twin(X)` ride on
§6.2's lockedness argument instead (a locked surface covers nothing, so
`X` itself never enters any covering count). Hence:

> The transition function needs no new state: the 61-bit encode plus the
> existing runtime arrays suffice. A macro transition is a short
> deterministic program of ordinary abstract moves (the dig/borrow sequence
> from §6.4) followed by the safe-sweep canonicalization (F3 repeatedly —
> already what `canonicalize` does in `src/macro_game.rs`). No closure DFS,
> no closure-class clustering, no per-card arrangement at generation time.
> Per-node expansion cost: `#drawables + #surfaces` times constant-bounded
> rule work.

On whether the stack component could be collapsed further: it splits into
three parts with different statuses. (i) The **safe prefix** per suit — the
only component the sweep canonicalizes; its content is forced and
derivable. (ii) The **scar per suit** — which dig/borrow segments have been
spent irreversibly; this is genuinely semantic information (two scar
classes of one commitment can have different futures; §6.7) and cannot be
dropped. (iii) The **float coordinates** — up/down positions of
worry-back-able unlocked cards inside the closure; pure noise, collapsible
in principle by a stronger canonicalization than the sweep, but the
collapse costs a closure walk per node, and §6.7's measurements show the
residual variety is at most a handful of classes — the bookkeeping win is
not worth the walk. So: within a closure class the stack detail is
collapsible noise; across classes it carries the only irreversible state a
commitment can create, and that part is incompressible.

One trap was missed by the monotone-sweep intuition above, and the probe
caught it (`sweep_is_confluent`): the sweep is confluent **except at
ambiguous-twin types** — both twins visible, one covered (`present=2,
placed=1` in the parity counts). There the type-level masks know the count
but not the identity, and "stack `L`" vs "stack `H`" diverge by a real,
per-suit foundation-height difference. 69 divergent orderings on the
128-game corpus, always confined to the stack component. Consequences:

- `canonicalize`'s deterministic rule (lowest index) is required, not
  incidental: the sweep is a *function*, not an order-free fixpoint. The
  ambiguity is the twin-expansion case of the reshape lemma operating
  inside the sweep — the same wall both architectures hit.
- The *semantic* safety of the choice — "the chosen reading never uniquely
  loses wins" — is a genuine obligation (twin-swap-shaped); it joins T's
  queue. It is bounded empirically at the verdict level by
  `macro_verdict_matches_engine`.
- The same invisible ambiguity exists in the old engine's abstract
  transitions; there it is defused by the cascade's canonical-twin rules
  and by `convert.rs` resolving the concrete card lazily. The macro engine
  needs its own explicit rule — this is it.

### 6.6 The falsifier for the design — MEASURED GREEN (2026-09)

`macro_transitions_direct` (in-tree in `src/macro_game.rs`, branch
`macro-game`) differentially against the closure-oracle
`enumerate_commitments`, per commitment per state over the probe corpus,
with channel forensics wired in. Result at this writing: **5129 commitment
evaluations, 0 fabricated successors, 0 missed availability** — the
`extra_separate == 0` assertion is hard and never fired; the `missing`
metric started at 44 and went to 0 through three rule-list shortenings
caught by the instrument alone: (a) a control-flow ordering bug in the
stack channels, (b) the zero-step degenerate prefix case colliding with
the ambiguous-twin story, (c) the declared §6.4 crease (chained
borrows/digs deeper than one) — closed by a bounded neighborhood BFS
fallback that fires on 27/5129 commitments. Channel load: tableau-direct
87%, stack-direct 18%, shared ~97% of outputs with the constant-work
channels; the BFS fallback is the residual scaffolding and is where
any future divergence will appear.

### 6.7 Why ≤ 2 is structural: the two-type interaction ball

Refined measurement (same probe, 2026-09): cluster *both* outcome kinds of
each commitment's canonical post-states together by mutual reversible
reachability.

- Combined class histogram over the corpus: `[_, 16777, 14, 0, 0]` —
  single-class commitments 16777 (of which **1102 contain both kinds**,
  i.e. `X` remains stackable after landing and the kinds are
  closure-connected via a late `PileStack(X)`); two-class commitments 14;
  never more. **Total closure classes per commitment ≤ 2, empirically
  unviolated** — this is the strongest surviving slogan form of C2.
- Same-kind multi-class splits: **3 on the corpus** (my first pass of the
  probe gated on `> 2` samples and missed them): two tableau variants of
  `Reveal(33)` distinguished only by *which suits' dig segments froze up*,
  a two-tableau split of `Draw(5)`, and a two-*stack* split of
  `Draw(20)`. So "one class per kind" is refuted as the strong form; the
  operative classification of the second class is by **accommodation
  residue**, see the scar model below.

The mechanism is now formula-tight. A commitment changes legality masks
only inside its effect set — `{type(X), type(X+4)}` for a `Draw`, extended
by `{type(r−4), type(r)}` when a `Reveal` flips `r` (the full accounting is
Lemma B, §7.1):

- the placement of `X` onto `Y` changes `xor_vis`/`free` bits in `type(X)`
  and (via `free << 4`) the cover of `type(X+4)` — the destination;
- an `SP(z)` downward flip is destroyed only when the commitment covered
  `z`'s landing — `z`'s landing type is `z+4`, covered type is `X+4`, so
  `z ∈ type(X)`: only the committed card's own class loses downward flips;
- a `PS(z)` upward flip is destroyed only for the covered card itself
  (`type(X+4)`);
- a `Reveal`'s flipped card is *locked* — locked cards never shuttle in a
  closure, so it introduces no float coordinate at all; the deck side of
  a `Draw` is commitment-determined.

Every coordinate outside this two-type ball keeps its flip legality
post-commitment, so free-float variation reconverges. What does *not*
always reconverge is the **scar model**, which is the residual structure of
C2:

> A dig can spend a float **upward irreversibly**: if the accommodation
> stacks `twin(X)` (or a prefix chain containing it) to free the landing,
> then post-commitment its only legal worry-back landings — the parent it
> vacated, and the other twin — are respectively covered by `X` and
> unavailable, so the dig cannot be undone by reversible play. Different
> dig choices (which twin / how deep) leave **mutually unfliappable scars**
> in the stack heights, and those scars are the second closure class.

That explains all 14 anomalies: the 11 mixed-kind pairs differ by
`{X's residence}` plus a frozen scar segment; the 3 same-kind splits are
two different scar geometries of the same kind. The empirical fact that
there is never a third class rests on the locality lemma in its strongest
form: a scar needs the commitment's whole two-type neighborhood, and there
is only one `twin(X)` to spend — no third configuration can be frozen.

**Design consequence (important):** scar classes may have genuinely
different futures, so the macro search must keep *all* closure classes of a
commitment as successors (the ≤ 2 bound is what keeps this cheap).
Canonicalizing to one representative per kind is *unsound*, not just
lossy. Note the parallel with the current engine: the
`paired_stack`/`least_stack` cascade (method.md §5.5–5.6) is exactly
scar-management — the two architectures' hardest machinery is the same
machinery.

**Residual obligations:** (i) prove there is never a third scar — i.e. all
irreversible spends inside one accommodation are linearly ordered, so at
most one binary scar-choice survives; (ii) decide the *canonical* scar
policy the direct transition should implement (of the ≤2 classes, which
the macro game prefers, e.g. deepest-safe-dig) — measurable against the
closure-oracle before any proof is attempted.

The configuration table (measured, same corpus). Computing each
commitment's parent configuration at the canonical root (direct landing
available / dig channel live / borrowable parents / dead or buried
parents) and histogramming against closure-class count:

- Every one of the 14 multi-class commitments lies in the
  "some side channel with irreversible residue is live" region —
  `{borrowable: 2, direct: false}` once, `dig: true` nine times,
  `direct: true` with a concurrent borrow/dead channel four times. All
  other configurations (~25 of them, ~16,700 commitments) are
  single-class.
- Two exclusion facts read off the table: `borrowable: 2` ⟹ `dig: false`
  (structural — a foundation-top parent cannot be covered), and in the
  corpus `dig: true` never co-occurs with `direct: true` (the dig is live
  only when no free landing exists).

So "two mutually exclusive cases × two options" has a concrete form: the
*case* is which color eats the scar (dig ⇒ X's color via `twin(X)`;
borrow ⇒ the parents' color via the foundation top), the *options* are the
suit choices inside the case — and the exclusions above are the reason
they never compose into three.

#### Status bookkeeping

- **C2 remains [~]** with content now converged to: interaction ball
  (formula-tight, essentially [x]) + scar model + the measured
  configuration table above (every multi-class case concentrated in the
  side-channel region; exclusion facts observed). The surviving proof
  obligations: (a) the four-case channel list is complete (§6.4's open
  crease), (b) the exclusions + the interaction ball force ≤ 2.
- The claim in §0/§4 should now be read in the refined form:
  *≤ 2 macro successors per commitment; the successors are labeled by
  outcome kind **and**, when present, by the accommodation's irreversible
  scar — and the macro engine keeps both.*

### 6.8 What §6 implies for the open items

- **O6** has an operational answer already measured: canonical form = safe
  sweep + closure-quotient; uniqueness of the canonical post-state per
  commitment-kind is the confluence of the §6.4 priority order (direct >
  dig > borrow > king-hole) — testable by the §6.6 differential.
- **O5** (can every accommodation be reduced to the sweep?) is replaced by
  the sharper question: is the §6.4 rule list complete? The same §6.6 test
  decides.
- The remaining open items here (O1/O3/O5, and O7's terminal sweep) become
  boundary cases to encode into the §6.4 rule list rather than separate
  hazards; the interaction doc's register keeps the cross-cutting ones.

## 7. C2, streamlined: closures as coordinates, commitments as pinnings [~]

The reframe (post-rewrite, 2026-09): instead of "four channels plus two
residue lemmas plus exclusions", the whole story is one definition plus one
finite lemma. This section supersedes the earlier lemma-based package; the
falsifier probes of §6.6–§6.7 are unchanged and refer to this version.

**Setup.** Regard each unlocked card as a *coordinate* with bounded range
(its residence: a tableau position vs. the foundation). Per-move legality
couples only through the interaction balls of §6.2/§6.7 (the mask
read/write table shows a *move* never touches coordinates outside its own
few types) — with the two refinements a review pass caught and which the
accounting below must include: (i) a borrow's write-set is an *ascending
ray* — worrying back a `P*` places a new card at `type(X+4)`, shifting the
cover counts at `type(X+8)`, and chained borrows continue upward until the
kings' holes terminate them; (ii) `free_slot`'s king gate reads the global
pile-emptiness count, a non-type-localized read. Neither invalidates the
correction's mainline point — that the *commitment* touches only its five
fixed types — because a *direct* commitment performs no borrow at all, so
for direct and for dig (whose write is a removal, staying in-ball) the
tight ball holds exactly; the ray is the residue class's own bookkeeping,
priced in where it lives (§7.2's P2/P3), not waived.

A commitment with target `X` is the irreversible assignment of one
coordinate: "where `X` resides" (tableau or foundation). What makes a
commitment executable is the state of a tiny local coordinate set; what a
macro successor remembers is which coordinates the commitment *pinned*
irreversibly.

**Definition (macro successors).** The minimal enabling pinnings of a
commitment `X` at a canonical state: subsets of the *resource poset*

```
direct(= ∅)  <  dig(twin X),  borrow(Y),  borrow(Ȳ)      (+ king-hole if X=K)
```

ordered by inclusion, subject to the poset axioms (each provable from the
card arithmetic or measured-structural; the two exclusions of §6.7):

- **(P1)** both borrows live ⟹ no dig — a foundation top cannot be covered.
- **(P2)** direct, when present, dominates every pinning (any dig or borrow
  still playable after committing `X` directly — the scar is reproducible
  inside the same closure, so the extra pinning is not a *new* class).
- **(P3)** a used pinning is *un-erasable, though not un-movable* (the F1
  wording, corrected on review): the commitment consumes the coordinate
  that would reverse it *in its own class* — when a compensating channel
  co-exists, the dig residue can still be undone only by first borrowing
  elsewhere, i.e. by *trading* the pinning for another residue inside the
  same color ball, never by erasing it. Hence classes stay separated by
  residue identity, and they merge only when the placement itself is
  erasable — precisely when `X` remains stackable after landing (a late
  `PileStack(X)`), which is the corpus's 1102 mixed-kind single-class
  commitments of §6.7.

**Theorem (C2, streamlined form) [~].** A commitment has at most **2**
macro successors, labeled by the minimal pinnings available. Proof: by P2,
a second class requires `direct` absent; by §6.2's singleton-blocker count,
the pinnings live in a two-color ball whose simultaneously-live minimal
elements are either {dig + one borrow} or {borrow + borrow̄}; P1 covers the
remaining register. The multi-rank crease (dig/borrow chains of depth > 1)
attaches to a single parent side and is absorbed by the shallower pinning
(depth-ordered) — the one line still requiring a line-force proof. State-
level multiplicity is float noise (§6.3 measurement, unbounded), which never
enters the pinnings. ∎ (modulo the crease and the L1/L2 diligence)

**What the old lemmas became** (for anyone cross-referencing the git
history): the jurisdiction/interaction table survives intact as the
statement "coordinates have small read/write sets" (§6.7's bullets); the
channel list (§6.4) is now the *witness mechanism* for availability rather
than a proof device — its completeness question is unchanged and is exactly
the §6.6 differential's job; the residue lemmas F1/F2 demoted to poset
axioms P2/P3 above; the exclusions E1/E2 to P1/P2.

(Namespacing note: the poset axioms P1–P3 here are *not* the falsifier
instruments P1–P3 of the interaction doc's §7 empirical program — the
latter are loggers that would test claims like the ones above; when in
doubt, cross-references name their doc.)

**What remains outside the streamlined proof** (unchanged from earlier
status): the semantic safety of the ambiguous-twin canonicalization rule
(the α-fiber semantic question, in T's queue, verdict-bounded in the
meantime); the L1/L2 count tables (Lean diligence); and the depth-ordered
pinning absorption inside multi-rank chains (the last encounterable
residue case, never observed in 16,791 commitment points).

Snapshot: C2 content is now *one theorem about a five-element poset*, all
of whose per-row claims are individually checkable, and whose total
empirical support is: zero three-class outcomes and zero verdict
mismatches across the curated corpora to date.
