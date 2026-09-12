# The pruner × dominance interaction — the main skeptical issue

Each filter in this engine comes with its own soundness story. The skeptical
question is whether the stories *compose*: can two individually-sound filters
jointly destroy a winning line that neither would destroy alone? This note
maps exactly where that can happen, what saves it (informally), what is still
unproven, and how to test the composition empirically.

Companion docs: [method.md](method.md) for the rules themselves,
[macro_formalization.md](macro_formalization.md) for the ongoing rework.
Line references are pinned to commit `5146b98` and will drift.

## 1. The three layers and what each one claims

The search expands a state `s` reached with path context `ctx` as:

```
expand(s, ctx) = D(s) ∩ P(s, ctx)
```

- **D** — the dominance rules, `gen_moves::<true>` (src/state.rs:160).
  A pure function of the state. Claim: for every winning play using a
  dominated move, there is a winning play using a kept one (canonicalization
  by twin-swap, safe-stack recoverability, commuting arguments).
- **P** — the path pruner, `FullPruner` (src/pruning.rs). A function of the
  *last move* and its side effects. Claim: every removed move can be
  *reordered* — done at a neighboring state instead — without losing the win.
- **TP** — the transposition table (src/traverse.rs:81). Each `Encode` is
  expanded **once**, with whichever move set the first-arriving path's
  context allowed. Claim: the answer does not depend on the arrival context.

## 2. Why isolated soundness does not compose

Rule A removes move `m` at `(s, ctx_A)` with the justification "do `m`
earlier instead". But "earlier" is another position in the search tree, which
is subject to D and P *of that position*. If D canonicalizes `m` away there,
or P blocks it there, the rescue evaporates — and rule B at the original
position may simultaneously block the "later" direction. Filters can deadlock
each other's rescue paths.

What must actually hold is a **closure property**:

> For every concrete winning play π there is a sequence of local
> transformations (reorderings, canonical substitutions, safe stackings)
> leading to a winning play π′ such that *every intermediate play along the
> transformation is itself accepted by the full filter system* (D ∩ P at
> each ply, plus no TP skip of a needed expansion).

Each individual rule's argument establishes one transformation in isolation.
The composition needs the transformation system to be closed under the
filters — this is the part that has never been written down, and is the
right target for a Lean formalization (it is a rewrite-system confluence
statement, not a per-rule statement).

An important principle that keeps this tractable:

> **An empty `D ∩ P` at a state is not a bug by itself.** It is a bug only if
> no reordering escape exists. The engine relies on this constantly — see
> §4 for the flagship example.

## 3. The three concrete hazards

### H1: reordering closure (D × P)

Every P-rule's rescue ("do `m` earlier") must land somewhere that:

(a) `m` is still **legal** there. The interesting cases are exactly where
    legality changed between the two states:
    - a reveal flips the *presence parity* of the revealed card's type
      (`xor_vis[type(r)]`), which can flip `bm[type(r)]` **on** — moves
      involving `r`'s type family may be legal *only after* the reveal;
    - a drawn-and-placed card adds coverage of the type it sits on, which can
      turn `bm` **off** for the buried card — but a destroyed-later move was
      available *before*, so those reorders are safe;
    - placements are monotone: adding placed cards only reduces movability
      of the covered type.
(b) **D still generates `m`** (or an equivalent) at the earlier state. The
    dominance cascade is state-dependent; e.g. the forced-safe-stack rule
    returns *only* a `PileStack` — if the rescue needs a draw or a reveal at
    that ply, it is not available there.
(c) **P at the earlier context** does not block `m` (no other one-ply rule
    in force).
(d) performing `m` earlier does not disable the context move itself (e.g.
    reordering a stack before a reveal must not cover the reveal's target —
    true, because a reveal target is a surface card and a stackable
    rescue-move is a *top* whose removal only uncovers things).

### H2: context-dependence × the transposition table (this is GHI)

The same `Encode` can be reached under different contexts with different
allowed move sets, but is expanded only once. If the winning move from `s`
is allowed only under the second context, and the H1 rescue (reorder before
the paths merged) fails, the solution is lost. This is the classic
graph-history-interaction problem, aggravated by P.

Structural facts that keep it plausible:

- The contexts are **shallow**: the reveal rules key on the immediately
  preceding move; `last_draw` persists only through a streak of
  `DeckPile`/chained-`StackPile` moves and is cleared by any other move.
  So the rescue never needs a deep reorganization — it needs to move at
  most one move (or one streak) earlier.
- P only ever **narrows** foundation moves and reveals; it never creates
  them. `stack_pile`, `deck_pile` and (in most contexts) `deck_stack`
  remain available as escape moves that reset the context.
- The states *around* a context differ in encode (a reveal/draw always
  changes stack/hidden/deck), so the TP does not conflate the context
  positions themselves.

The residual exposure is exactly: a state whose *only* legal moves are
P-narrowed away, reached under context C, while under another context the
state has moves. Then the expansion recorded for that encode (dead end) is
wrong for the other arrival — unless the reorder rescue covers it.

### H3: identity-sensitivity × the arrangement abstraction

P references concrete cards (the drawn `d`, the revealed `r`) while the state
deliberately forgets arrangement. In thoughtful mode this is consistent: the
deck encode preserves order/identities, and the hidden structure is pinned by
the deal + counts, so "the card revealed by the last move" is well-defined
per encode. The load-bearing question is whether D's canonical choices are
arrangement-robust — that is the twin-swap + `bm`-parity story (method.md §4,
§3.2), and it is where this note connects to the macro formalization.

## 4. The flagship example: king-fill vs forced safe stacking

This is the interaction in its purest form — three rules colliding at one
ply.

**Setup.** The pruner, after a reveal that emptied a pile
(`(Reveal(_), RevealEmpty)`, src/pruning.rs:82), removes *everything* except
king placements: the hole must be filled by a king immediately.

**Collision.** The dominance cascade at that same state may fire the forced
safe-stack rule (§5.1 of method.md): if any visible, movable card is below
the safety threshold, `gen_moves` returns *only* that `PileStack`. The
intersection with "kings only" is **empty** — the search dies on this path at
a state where the real game still has moves. Worse, the paired-stack branch
replaces `free_slot` outright (src/state.rs:236), dropping `KING_MASK`, so
even king draws are gone in that branch.

**The rescue** (why this is not a bug): the safe stack can be reordered to
*before* the emptying reveal — its legality is state-relative and the reveal
does not affect it (H1(a): the reveal only flips parity for the revealed
card's type; there is none here). So the winning line is explored as
`..., stack q, Reveal(c), king-fill, ...` from the earlier position. At that
reordered prefix the post-reveal state is different (`q` already stacked), so
the cascade re-evaluates; if it fires again for another card, that card also
reorders before the reveal. The induction terminates because each reordering
strictly grows the foundation.

**The subtlety that makes this genuinely hard**: the corner case where the
card that must fill the hole *is* the safe-stacked card. The tempting rescue
"stack q, then worry q back into the hole" collides with the dominance rule
`stack_pile & !dom_sm` (src/state.rs:218): a card below the safety threshold
is **never worried back** — and since heights only grow, the threshold only
rises, so `StackPile(q)` stays filtered forever. The rescue must instead use
the substitution argument: if `q` is below the threshold, its twin (or
another king) is still in play and can serve as the fill. The safety
threshold formula (same-color min ≥ r−2, opposite ≥ r−1) is exactly what is
supposed to guarantee the substitute exists — but note this makes the pruner
rule 6.2's soundness depend on the *full strength* of the dominance_mask
formula, including the `r−2` relaxation (method.md §5.1, still a
TODO(vuong)). If the relaxation were wrong, this interaction is where it
would first bite.

## 5. A second worked example: why `{r, twin(r)}` is exactly the right exemption

The rule `(Reveal(_), Card(r))` (src/pruning.rs:90) allows only stacking `r`
or its twin after a reveal, and removes `deck_stack`. The exemption is not
arbitrary — it is exactly the set of moves whose legality the reveal
*created*:

- `bm[type(r)]` can flip on due to the reveal (parity of present twins
  changes), so `r`/`twin(r)` may be stackable only now — they cannot be
  reordered before the reveal.
- Every other removed move was legal before (the reveal adds no other
  movability: placements are monotone), so the reorder rescue applies.

Symmetric check for the interaction with the deck dominance (§5.3 of
method.md): if that rule fires after a reveal, it returns *only* a
`deck_stack` — which the pruner just removed. Intersection empty, rescue =
draw-to-foundation before the reveal (drawing is unaffected by the reveal,
and the last card's stackability is foundation-only). Works, but only
because H1(a) holds for deck moves.

## 6. Audit table (per pruner rule)

| Rule | Rescue claim | Needs from D | Needs from other P | Status |
|---|---|---|---|---|
| `CyclePruner` (2-cycle break) | `m` then immediate undo is identity — delete both | nothing | nothing | solid: composition is trivial |
| `(Reveal, RevealEmpty)` → kings only | non-king moves reorder before the emptying reveal | pre-reveal state must generate them (H1(b)); the fill must exist — substitution when the natural king is safe-stacked (§4) | the reordered position must not be inside a `last_draw` streak that blocks it | argued in §4; corner case (safe king) depends on the `r−2` relaxation — TODO(vuong) |
| `(Reveal, Card(r))` → stack `{r, twin(r)}` only, no `deck_stack` | exemption set = reveal-created moves (§5); others reorder before | cascade must not return *only* moves the pruner removed — verified for the two "return-only" branches (safe stack, deck dominance) via reordering; paired branch keeps the pair both bits | same | argued in §5 |
| `last_draw` → only `twin(d)` stackable; reveals restricted to `(mm>>4) ∪ first_layer` | other stacks reorder before the draw streak; buried landing-spot cards were tops before the draw (H1(a)) | same as above; note the streak (not one-ply) means the rescue target is the streak's parent | the streak structure itself | partial: the deck-ordering rationale for the reveal restriction is the in-code comment (the `DP 8♠, R 10♥, DP K♠` line); **the `twin(d)` exemption is unexplained — TODO(vuong)** |

Open observations while auditing (not necessarily problems):

- `stack_pile = ... & !dom_sm` uses the *raw* `dominance_mask()` (not
  `dom_sm ∩ sm`), so it really does forbid worrying back every card below
  the safety threshold. This is the load-bearing "never need it back" claim;
  it is what §4's corner case leans on. TODO(vuong): the writeup of why the
  threshold guarantees a substitute.
- The paired branch's `free_slot` replacement (dropping `KING_MASK`) means
  "king fill" is unreachable while an unnecessary stackable pair exists —
  fine only because of the §4 reordering induction.

## 7. How to test the composition (the empirical program)

None of the above is a proof. The composition is testable end-to-end,
though, and the repo already has all the machinery:

1. **Ground-truth differential.** Run the solver with all discretionary
   filters off — `gen_moves::<false>` + `CyclePruner` (cycle-breaking is
   needed for termination) + TP — versus the full configuration
   (`gen_moves::<true>` + `FullPruner`). Verdicts (Solved/Unsolvable) must
   match exactly on a seed corpus. The unfiltered search is orders of
   magnitude slower; budget accordingly (start with a sample of the
   Klondike-Solver seeds, where published results exist to anchor the
   ground truth itself).
2. **Attribution bisect.** The 2×2 grid (dominance on/off × Full/Cycle
   pruner) attributes any mismatch to a rule family; then bisect rules
   within the family.
3. **H2 instrumentation.** Log every TP skip where the new arrival's context
   class differs from the first expansion's context, and where the filtered
   move sets would differ. Every such state is a potential GHI loss; the
   claim is that each has a reorder rescue. A ctx-aware TP (re-expand on
   context-class change) as a one-off experiment would bound the risk
   directly.
4. **Micro rescue-checker.** For sampled `(state, ctx)` pairs, enumerate
   P-removed moves and verify each has a legality witness at the reorder
   target (one-streak earlier). Automatable with the existing `traverse`
   callback machinery.
5. **The existing cross-checks** (Solvitaire on 1M seeds, Klondike-Solver
   0..50k, self across versions) are end-to-end tests of exactly this
   composition — which is why they are the main evidence today. Their
   limitation: Solvitaire also prunes (different rules), so agreement is
   strong but not ground truth; the no-filter run of (1) is the only
   unfiltered reference.

## 8. Residual risk register

Ordered by how much worry each deserves:

1. **The closure property of §2 has never been checked as a whole.** All
   per-rule arguments implicitly assume their rescue target is explorable;
   nothing verifies that jointly. The 1M/50k cross-validations test it
   empirically; the ground-truth differential (§7.1) would test it much more
   directly.
2. **The no-pile-to-pile move set** (method.md §9 leg 1) is upstream of all
   of this and unproven.
3. **The `r−2` safe-stack relaxation** — §4 shows a concrete pruner rule
   whose soundness reduces to it.
4. **The `twin(d)` exemption in `last_draw`** — the one rule with no
   reconstructed rationale.
5. **The deck-order reveal restriction** — motivated by the in-code example,
   never written out.

None of these is known to be wrong; all of them are on the path from
"validated on millions of games" to "proven". The macro/commitment rework
(macro_formalization.md) is an opportunity to fix the deepest of them by
construction: with accommodations computed from the state alone, P's
path-dependence disappears, H2 vanishes, and what remains of the composition
question collapses to the dominance arguments in D plus the twin-swap
theorem.
