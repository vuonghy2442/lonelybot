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

## 2.5. What the literature already proves — and what it does not

Several rules in this engine have published correctness proofs for the
*standard* game (explicit piles, full pile-to-pile moves). The engine's
novelty is not the rules themselves but running them under the restricted
move set and the arrangement-free state; the published proofs are templates
to port, not citations that close the question. (All references below:
Blake & Gent, *The Winnability of Klondike Solitaire and Many Other
Patience Games*, JAIR 85, Article 21, 2026, doi:10.1613/jair.1.17167 —
§5.4 and its Appendices B.1/B.2; the paper's running header uses the
short title "Winnability of Solitaire and Patience Games".)

- **Safe autostack = Keller's rule, exactly.** With worry-back allowed and
  red-black build-down, a card `q` of rank `r` is unconditionally foundable
  when stackable and `f(opp1), f(opp2) ≥ r−1` and `f(twin suit) ≥ r−2`
  (their phrasing: at most 2 above the opposite-colour foundations' top
  cards, at most 3 above the other same-colour suit's top). That is
  bit-for-bit the engine's `dominance_mask` (src/stack.rs:26) — sanity
  check against their example: foundations 8♣ 7♦ 9♥ 8♠ make 10♥ safe
  (`f_opp = 8 ≥ 9−1`, `f_twin = 7 ≥ 9−2` in 0-indexed ranks) and J♥ unsafe
  (`8 < 10−1`), matching the engine's mask either way. This corrects
  method.md's framing: the `r−2` twin condition is **not an engine
  relaxation**, it *is* the classical condition for games with worry-back.
  (The genuinely stronger classical variant — stackable when `f_opp ≥ r` —
  applies only to games *without* worry-back, which is not this one.) What
  is actually engine-specific and still unproven: evaluating the rule in a
  state that does not track runs, and composing it with P and the TP — i.e.
  precisely the remainder of this document.
- **The worry-back ban is published too** (same paper: never move a card
  from foundation to tableau while it is safe-automovable — "a pointless
  loop"; a generalization of Bjarnason, Tadepalli & Fern 2007). That is
  `stack_pile & !dom_sm` verbatim. (`deck_pile & !(dom_sm & sm)` is the
  stock-side *analogue* — the same recoverability argument applied to a
  same-card choice between two currently-legal moves, so the stock caveat
  does not bite — but it is not itself the published statement.)
  Crucially for us, no separate compatibility proof for the safe-stack +
  ban pair is needed: the ban is a *corollary of their Theorem 1* — in any
  Theorem-1-compliant solution (which always stacks a safely-buildable
  card when one exists), a worry-back of a safely-buildable card is itself
  a non-compliant move, so compliant solutions never make it; both engine
  rules merely select among Theorem-1-compliant solutions. Their actual
  Theorem 5 proves a different pair compatible — the safe-move dominance
  (Thm 1) with the incomplete-pile *immediate-building* dominance (Thm 4) —
  which is a published instance of exactly the closure property §2 asks
  for, and the closest published analogue of this engine's 5.1 ×
  `(Reveal, Card(r))` pairing analyzed in §5 (modulo the move-set port).
- **The incomplete-pile dominance** (Wolter 2014, Birrell 2018; proof in
  their Appendix B.2, plus a stronger form requiring the follow-up build to
  be   *immediate*): a partial pile move is allowed only if the card it
  exposes can be built to foundation at once. Their proof's intuition —
  the exposing move "was not really urgent so we can delay it until
  later, or even not do it at all" — is the ancestor of every P-rule in
  this engine. The `(Reveal, Card(r))` rule is that same scheme transplanted to a
  move set with no partial pile moves; their proof does not carry over
  verbatim, but §5 makes the transplanted claim exact (lemma L2).
- **The stock caveat cuts the other way.** The safe-move dominance must
  *not* be applied to moves from the stock, except when draw size is 1 with
  unlimited redeals (then the stock behaves like a reserve). In this engine
  that licenses exactly the `draw_step == 1` branch of `get_deck_mask`
  (src/state.rs:136-142) — and nothing more. The `is_pure` last-card rule
  for `draw_step ≥ 2` (method.md §5.3) has no published counterpart: it
  stands on its own argument (a pure deck cycles back to the same
  partition, so dealing around to the last card loses no draw-order
  information). That argument is plausible but has never been written out
  beyond two sentences; the register below ranks it accordingly.

Rule-by-rule status, then: the two main foundation dominances are proven
*for the standard game*. What remains open here is (i) porting those proofs
to the restricted move set and the set abstraction, and (ii) the
composition with P and the TP. (i) is a port; (ii) is new territory either
way.

## 3. The three concrete hazards

### The two local lemmas everything reduces to

Nearly every "for" argument below bottoms out in one of two claims about
how a move changes the *generated* move set of its neighbours. Stating them
precisely converts hand-waving into obligations; both are small enough to
be Lean targets independent of the twin-swap theorem.

- **L1 (placement monotonicity, tableau side).** Placing a card `c` onto
  the tableau (`DeckPile`, or the moved card of a `Reveal`) creates no new
  tableau-side move except placements that land on `c` (the type `c−4`
  family), and can only *destroy* movability of the type `c+4` it covers.
  Foundation heights and deck contents are untouched. (Deck-side, a
  `DeckPile` of course shifts the drawable window — that is not monotone,
  and managing exactly that is the whole point of the `last_draw` streak
  machinery, Table 2 in §6.) — Follows from the `bm`/`free_slot` parity formulas
  once those formulas are trusted; that trust is H3.
- **L2 (reveal legality delta).** `Reveal(c)` revealing `r` changes the
  generated move set only by: (i) toggling foundation moves within
  `{r, twin(r)}` — in either direction, per the parity; (ii) adding
  placements onto the fresh top `r`; (iii) removing moves that needed type
  `c+4` movable (`c` now covers it). Nothing else can change: `xor_vis`
  toggles only for `type(r)`, `xor_free << 4` only for `type(c+4)`, deck
  and stack are untouched.

L2 is what makes the `{r, twin(r)}` exemption of §5 *exactly* right rather
than arbitrary: the pruner keeps all of (ii) — placements and reveals are
unfiltered in that context — and exempts (i) from the foundation filter;
everything destroyed by the reveal was legal before it, so it reorders.

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

- The contexts are **shallow** — and, in fact, *disjoint by construction*.
  The reveal rules key on the immediately preceding move being a `Reveal`;
  `last_draw` is set by `DeckPile`, survives a `StackPile` that does **not**
  land on the drawn card, and is cleared by every other move — including
  `Reveal` itself and a `StackPile` chained onto the drawn card (chaining
  "consumes" the fresh top the streak was protecting). Two consequences:
  (1) a state is never simultaneously under a reveal rule and the streak
  rule — P decomposes into two one-ply regimes ({§6.2, §6.3 of method.md}
  after a reveal; the streak rules between draws) plus the cycle rule;
  (2) rescues never need a deep reorganization — at most one move, or one
  bounded streak, earlier.
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

**Why the underlying dominance is no longer the weak point here.** The
forced-safe-stack / never-worry-back pair is exactly Keller's rule plus its
published companion ban, both proven correct for the standard game (§2.5) —
and jointly sound, since both are consequences of the same Theorem 1
(compliant solutions never worry a safe card back, so the two rules never
fight over a solution). Their proof also suggests the right local statement
for this engine, which splits into two channels by which stacking `q`
(rank `r`, colour X) could ever hurt:

- **(A) `q` is needed later as a destination.** Only the two cards of rank
  `r−1`, opposite colour can ever sit on `q` (placements need an uncovered
  run-parent; no other card ever lands on `q`). With `f_opp ≥ r−1`, both
  are permanently foundation-safe: if already stacked, substituting the
  height facts into the threshold shows they are themselves dominant
  (their same-colour condition needs `≥ r−3`, their opposite-colour
  condition needs `f_X ≥ r−2` — the latter is exactly the twin-suit
  conjunct), so rule 5.4 forbids their return forever; if unstacked, they
  are stackable the moment they become tops, and 5.1 forces them home —
  either way they never need `q`. All conditions are on heights only,
  hence monotone: once true, true forever.
- **(B) stacking `q` buries `q`'s own foundation prefix.** `StackPile` can
  only take the current foundation *top*, so stacking `q` freezes the
  suit-`q` prefix beneath it. But every card in that prefix is dominant by
  the same inequalities, so none of them can ever be legally worried back
  anyway; freezing loses nothing that was reachable.

So 5.1 and 5.4 are *one* invariant maintained jointly — "no dominant card
is ever needed on the tableau" — provable by induction on rank, the
induction hypothesis at rank `r` being exactly channels A and B for ranks
`< r`. This is the shape to hand to Lean. What the induction hides: it is
stated on heights and masks, while channel A's "they never need `q`" is a
statement about concrete runs — the induction still rests on the
arrangement abstraction being faithful (H3). What it removes is any doubt
about the *height formula* itself.

One more consequence for the composition question, worth stating as a
named lemma since every P-rule collision recurs to it:

> **Drain-safes-first lemma (unproven, but mechanical).** Let `s` be a
> state and `m*` an irreversible "anchor" move (draw or reveal). If a
> winning play from `s` begins `m*` and the filtered search instead dies
> because rule 5.1 (or 5.2) keeps returning forced `PileStack`s that P
> blocks at the post-`m*` states, then the reordered play — stack the
> pending safe cards first, in the forced order, then `m*` — is
> filter-accepted and still wins. The anchor's legality is unaffected by
> stacking other tops (a `PileStack` only uncovers — L1). The anchor's
> post-state has *at least* the reference play's safe cards (dominance is
> monotone in the heights, which are only higher), so its forced drains
> are well-defined; the chain terminates because each drain strictly grows
> the foundation.

**The subtlety that makes this genuinely hard**: the corner case where the
card that must fill the hole *is* the safe-stacked card. The tempting rescue
"stack q, then worry q back into the hole" collides with the dominance rule
`stack_pile & !dom_sm` (src/state.rs:218): a card below the safety threshold
is **never worried back** — and since heights only grow, the threshold only
rises, so `StackPile(q)` stays filtered forever. The rescue must instead use
the substitution argument: if `q` is below the threshold, its twin (or
another king) is still in play and can serve as the fill.

Sharpening where that leaves the corner case: the published safe-stack
proof (and channels A/B above) covers `q`'s absence *as a destination*; a
hole-fill is a third, cruder need — `q` as bare content, "any king fills an
empty pile" — which no foundation-height condition speaks to. But note
which rescue gives this: the §6.2 reordering moves *every* non-king move
of the reference play's post-emptying interval before the emptying (they
commute with it), so by the time the hole appears, every reveal and draw
the reference play performs before filling has already happened, and any
king the reference play could surface is surfaced. (Drain-safes-first
alone does not give this — it moves only stacks; deferred emptying gives
the same from the other direction.) The only way to lose is therefore: every winning line's filler
is this one safe-stacked king, while all three other kings sit locked
behind structures that provably require a free pile to open — a genuine
deadlock pattern that predicate (P2) in §7 is designed to hunt. Status:
reduced from "depends on the soundness of the `r−2` formula" (that part is
now Keller's theorem, modulo the port) to a self-contained, testable
*fill-existence* question — still open.

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

With L1/L2 (§3) this observation upgrades from "plausible" to a conditional
proof: L2 says the legality delta of the context move is *exactly*
`{r, twin(r)}` on the foundation side plus placements onto the new top, and
the pruner keeps all of them. The rule is the engine's analogue of the
incomplete-pile dominance of Blake & Gent App. B.2 — expose only when the
build is immediate — with two differences in our favour: the "immediate"
set is computable from masks rather than search, and their "delay is safe"
induction is here just the one-ply reordering of H1, one case per surviving
move family. What remains external to the proof: the faithfulness of the
parity model itself (H3), and that the TP accepts the reordered arrival
(H2). One asymmetry to note: reveal-by-stacking (`PileStack` on a locked
card, which also produces `ExtraInfo::Card(r)`) is deliberately *not*
covered by this rule (the in-code TODO at src/pruning.rs:103). That is
under-pruning — conservative, not a soundness risk — but it means the audit
for this rule only needs to cover literal `Reveal` moves.

Symmetric check for the interaction with the deck dominance (§5.3 of
method.md): if that rule fires after a reveal, it returns *only* a
`deck_stack` — which the pruner just removed. Intersection empty, rescue =
draw-to-foundation before the reveal (drawing is unaffected by the reveal,
and the last card's stackability is foundation-only). Works, but only
because H1(a) holds for deck moves. It is also exactly where the published
stock caveat (§2.5) bites: safe-stacking *from the stock* is unsafe in
general because reaching the card changes the draw offset; the `is_pure`
condition is the engine's answer (a pure offset returns to the same
partition, so the reach-around is information-free). The reordered line is
sound irreversible-move accounting; the dominance itself, at draw ≥ 2, is
the part with no published backing.

## 6. Audit tables

### Table 1: the dominance cascade (D-internal)

| Rule (method.md §) | Claimed soundness | Grounding / dependency | Status |
|---|---|---|---|
| Forced safe stack (5.1) | stacking a dominant card never loses wins | Keller's rule — **proven** for the standard game (B&G App. B.1); engine port = channels A/B (§4) | grounded upstream; port pending (H3) |
| Worry-back ban (5.4) | never unstack a dominant card | published companion dominance, a corollary of B&G Theorem 1 (B.1); jointly sound with 5.1 because both hold in every Theorem-1-compliant solution | grounded upstream; port pending |
| Deck dominance, `draw_step == 1` (5.3 partial) | force the dominant drawable stock card | inside the published stock exception (draw 1, unlimited redeals ⇒ stock ≈ reserve) | grounded upstream |
| Deck dominance, `draw_step ≥ 2` (`is_pure` last card) | force `last_card → foundation` when the deck cycles cleanly | **no published counterpart** (B&G warn dominance must not be applied from the stock); rests on the pure-partition/redeal argument | open — writeup owed |
| ≥3 redundant stackables → lowest only (5.2) | canonical representative; the rest stay available | reduces to 5.1+5.4: a prematurely stacked non-dominant card stays worry-back-able, and if it becomes dominant in the meantime its destinations have substitutes; plus stack-stack commutation for the ordering | open, but the dependency chain is now explicit |
| Twin-pair collapse (5.5) | pair = twin-swap equivalence class; `free_slot` restricted to placements onto the pair | twin-swap theorem T + L1 (only placements onto the pair are created); the dropped `KING_MASK` is rescued by drain-safes-first | conditional on T |
| Least-stack cascade (5.6) | rank/color-canonical ordering avoids creating a 3rd unnecessary stackable | stack-stack commutation within same-colour regions + T; intricate | TODO(vuong) stands |
| King / empty-pile rules (5.7) | first-layer-king reveal to an empty pile is a pure shuffle | empty-pile symmetry | solid modulo that symmetry |

### Table 2: the pruner rules (P × D)

| Rule | Rescue claim | Needs from D | Needs from other P | Status |
|---|---|---|---|---|
| `CyclePruner` (2-cycle break) | `m` then immediate undo is identity — delete both | nothing | nothing | solid: composition is trivial; required for termination so it stays in every ablation (§7) |
| `(Reveal, RevealEmpty)` → kings only | non-king moves reorder before the emptying reveal — except those the reveal *created* (placements onto the moved card, per L1), which reorder to *after* the king fill instead — or the emptying is deferred forever; the fill collateral is the §4 corner | pre-reveal state must generate them (H1(b)) — the forced-branch collisions are covered by drain-safes-first | compatible with the streak rule *by construction*: an emptying reveal is always first-layer (`make_reveal` returns `None` iff nothing is beneath), and 6.4's exemption includes first-layer — so deferring the emptying across a draw streak is never blocked | argued in §4; one open corner (king-fill existence) with falsifier (P2) |
| `(Reveal, Card(r))` → stack `{r, twin(r)}` only, no `deck_stack` | exemption set = *exactly* the reveal's legality delta (L2); all other moves reorder before | the return-only collision with 5.1 / 5.3 is covered by reordering + drain-safes-first; paired branch keeps both bits | none: a `Reveal` clears `last_draw`, so this rule never co-fires with the streak rule — the feared `pile_stack ∩` conflict between them is *structurally impossible* | proved modulo L1/L2 (+H3, +TP acceptance per H2) |
| `last_draw` pile_stack → `twin(d)` only | any other stack commutes with the draw ("could have been done before"): the two orders `PS;DP` / `DP;PS` reach the **same encode**, so at least one must survive the filters | the pre-draw order may be canonicalized away by D itself (forced/cascade/least) — the exemption's real purpose is to keep one order alive against exactly those H1(b) collisions; conjectured that `{twin(d)}` is the exact necessary set | the streak structure itself | **open**: mechanism conjectured, not confirmed — TODO(vuong), now with a concrete target (find or refute a state where the pre-draw order is D-suppressed and the post-draw order is D∩P-empty) |
| `last_draw` reveal → `(mm>>4) ∪ first_layer` | allowed = the reveals the draw *created* (landing on `d`/`twin(d)` — the only new landing spots, by L1) plus first-layer reveals (which create a hole, and holes couple to king mechanics, not to the deck cycle) | none beyond L1 | ordered playing of reveals vs. the fixed deck order — the `DP 8♠, R 10♥, DP K♠` comment | open: rationale exists only as the in-code example; write the deck-order argument out |

Open observations while auditing (not necessarily problems):

- `stack_pile = ... & !dom_sm` uses the *raw* `dominance_mask()` (not
  `dom_sm ∩ sm`), so it really does forbid worrying back every card below
  the safety threshold. This is exactly the published worry-back ban (which
  is stated on the same unconditional predicate), and it is what §4's
  corner case leans on: the remaining unproven piece is not the ban but
  fill-existence — why a safe-stacked king always leaves a substitute
  filler. Tracked as predicate (P2) in §7.
- The paired branch's `free_slot` replacement (dropping `KING_MASK`) means
  "king fill" is unreachable while an unnecessary stackable pair exists —
  rescued by the same drain-safes-first reordering as §4's collision (the
  pair's stacks are just two more forced foundation moves to do before the
  emptying reveal).

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
6. **(P1) The decisive cheap check.** Instrument `traverse` to log every
   state where `gen_moves::<false>` is non-empty but the fully filtered set
   (`gen_moves::<true>` after the pruner) is empty, tagged by *which* rule
   pair zeroed each move family (D-branch × P-context). Every composition
   deadlock imaginable — §4's collision, a least-stack-vs-streak
   intersection, anything not yet thought of — passes through this
   predicate, and it is exhaustive over whatever seed corpus it is run on.
   A single logged live state is a concrete counterexample shape; zero logs
   over the reference corpus upgrades all reorder rescues from "argued" to
   "never observed to fail, at the decision point where failure would
   happen".
7. **(P2) King-fill existence.** After every `(Reveal, RevealEmpty)`, log
   states where *no* king placement is generated even by the unfiltered
   generator. Each hit is a candidate witness for the §4 corner case; the
   soundness claim is exactly "no hits on winnable states" (correlate with
   the verdict).
8. **(P3) Streak rescue witnesses.** Extend the micro rescue-checker of (4)
   to the streak machinery: for each move killed by the `last_draw` rules,
   require an explicit witness — either the same move legal/generated at
   the streak's start state, or the convergent-order encode
   (`PS(twin d); DP d` ≡ `DP d; PS(twin d)`) present in the TP. This is the
   direct test of the `twin(d)` conjecture in Table 2.
9. **Draw-step split.** Run the ground-truth differential of (1) separately
   for draw-1 (where the deck dominance is literature-backed) and draw-3
   (where it is not), so a verdict mismatch is attributed to the deck rule
   rather than drowned in aggregate agreement.

## 8. Residual risk register

Ordered by how much worry each deserves:

1. **The closure property of §2 has never been checked as a whole.** All
   per-rule arguments implicitly assume their rescue target is explorable;
   nothing verifies that jointly. The 1M/50k cross-validations test it
   empirically; the ground-truth differential (§7 item 1) and the
   filtered-empties logger (P1) would test it much more directly. Now with
   named sub-lemmas to prove instead of one blob: drain-safes-first (§4),
   stack-stack commutation (5.2/5.5/5.6), L1/L2 (the reveal rules).
2. **The no-pile-to-pile move set** (method.md §9 leg 1) is upstream of all
   of this and unproven. It is also the blocker for quoting Blake & Gent's
   Appendix B proofs verbatim: their games have partial pile moves, so the
   port to this move set must happen *here*, not rule by rule.
3. **The safe-stack pair (5.1 + 5.4)** — downgraded. The height formula is
   Keller's rule, proven for the standard game (App. B.1), and the pair's
   mutual soundness follows from both being consequences of Theorem 1
   (§2.5). Their Theorem 5 is the compatibility of a *different* pair —
   safe moves × incomplete-pile immediate building — which is the published
   analogue of this engine's 5.1 × `(Reveal, Card(r))` pairing (§5).
   What remains is the port to the
   set abstraction (H3) and the §4 king-fill corner, which is now a
   concrete falsifiable predicate (P2) rather than a vague worry.
4. **The deck dominance at draw ≥ 2** — upgraded. This is the one place the
   engine walks past a published *warning* (safe dominance must not be
   applied from the stock; B&G §5.4.1). The `is_pure` escape hatch is the
   engine's own answer and has never been written out beyond two sentences.
5. **The `last_draw` pair of rules** — the pile_stack exemption now has a
   mechanism to confirm or refute (generation-collision coverage of the
   convergent-order encode; Table 2, row 4, plus logger P3); the reveal
   restriction still has only the in-code example as its rationale.
6. **The twin-swap theorem (T)** — unchanged from macro_formalization.md;
   every canonical-substitution rule leans on it, and the arrangement
   faithfulness (H3) is the common substrate of all ports.

None of these is known to be wrong; all of them are on the path from
"validated on millions of games" to "proven". The macro/commitment rework
(macro_formalization.md) is an opportunity to fix the deepest of them by
construction: with accommodations computed from the state alone, P's
path-dependence disappears, H2 vanishes, and what remains of the composition
question collapses to the dominance arguments in D plus the twin-swap
theorem.
