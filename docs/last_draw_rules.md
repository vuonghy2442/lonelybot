# The last_draw streak rules — the general claim, the deck-offset argument, and the residues

Status: the weakest-justified rule family in the engine (both halves of §6.4
of method.md). Until now, its entire written justification was the
three-move comment at src/pruning.rs:116-119. This document states the
general claim for the first time, writes the deck-offset argument for the
clean cases, names the two residues where the argument does not (yet)
reach, and specifies the falsifier that decides them.

Line references are pinned to commit `34c8d04`. Rigor tier of this rule
family: [soundness_ledger.md](soundness_ledger.md) rows D4/D5.

## 0. The rules, precisely

The streak: `last_draw` is set by `DeckPile(d)`, survives `StackPile`s
that land elsewhere, and is cleared by every other move (src/pruning.rs:68-74).
While set (src/pruning.rs:107-120), `prune_moves` removes:

- **6.4a** — every `PileStack` except the twin of the drawn card:
  `filter.pile_stack |= !other` (line 114);
- **6.4b** — every `Reveal(x)` except `x ∈ (mm >> 4) ∪ first_layer`, where
  `mm = {d, twin(d)}` (line 120).

Decoding `mm >> 4`: the shift is rank−1 *with the color flip* (the card
layout's parity), so the allowed reveal targets are the cards of rank `r−1`
opposite in colour to `d` — **exactly the type that sits on a card of the
drawn pair's type**. Revealing such an `x` moves it, and its natural
destination is the freshly drawn `d` itself (or a card of `d`'s type). (The
card exposed beneath `x` is *unconstrained* — a hidden flip of arbitrary
type; that freedom is precisely residue R2, §4.) The kept set is the
run-building level immediately around `d`: the cards that sit on `d`.

`DeckStack` and `StackPile` are unrestricted during the streak; `DeckPile`
continues or restarts it.

## 1. The anecdote, decoded

> `DP 8♠, R 10♥, DP K♠` — "if you reveal 10 first then you forced to get
> K, which might prevent you from getting 8; if you get 8 first, you can't
> reveal 10, because it expects you to reveal it before to get the
> required card to put under 8, but since it doesn't reveal anything, it's
> not doing it" (src/pruning.rs:116-119)

The comment justifies the `first_layer` disjunct, and it parses once the
two couplings are separated:

- **10♥ is a first-layer card** (the bottom of its pile): revealing it
  *empties the pile*, so `(Reveal, RevealEmpty)` fires, the next move
  must be a king placement, and if the only accessible king is the `K♠`
  in the deck then the forced fill is a *draw* — which moves the offset
  and can make a later-needed card (the other 8) unreachable in the
  required pass. **This is the one way a reveal can force a draw**, and it
  belongs exclusively to first-layer targets: only they can empty a pile
  (`make_reveal` returns `RevealEmpty` iff nothing is beneath, i.e.
  `n_hidden` was 1 — the surface *is* the first layer).
- Therefore the emptying reveal's *position inside the streak* is
  load-bearing: it must happen after the 8's draw (so the 8 is secured)
  and before the forced king draw. Reordering it to the streak start is
  **not** offset-neutral — which is why the rule *keeps* first-layer
  reveals instead of pruning them.

Everything else 6.4b removes is claimed to be offset-neutral and
reorderable; that is the content of §2–§3.

## 2. The general claims (stated for the first time)

**Claim A (6.4b).** Every reveal removed by 6.4b has a filter-accepted
witness at or before the streak's start, **unless** its legality was
created inside the streak by a move other than the draws' own placements —
and the exception set is (conjecturally) exactly the two residues of §4.
The reordering is deck-neutral (Lemma D1).

**Claim B (6.4a).** `{twin(d)}` is exactly the set of `PileStack`s that
must remain available mid-streak: stacking `d` itself is redundant with
`DeckStack` (draw straight to the foundation — unrestricted during the
streak); every other stack has a pre-streak witness (by the logic of D3
below); `twin(d)` is the one whose loss is not recoverable by reordering —
via the convergent encode `PS(twin d); DP d ≡ DP d; PS(twin d)` and/or
the burial mechanism of §5.

## 3. The deck-offset argument (the clean half)

**Lemma D1 (offset-neutrality).** `Reveal`, `StackPile` and `PileStack`
do not touch the deck — no offset change, no card consumption
(`make_reveal`, `make_pile::<false>`, `make_stack::<false>`, src/state.rs;
only `DeckPile`/`DeckStack` ever touch it). Hence reordering any sequence
of reveals, unstacks and stacks *across* draws preserves the entire draw
trajectory: the same cards are drawn, at the same offsets, so every
pass-parity property of the play is invariant. The deck's cyclic window —
the feature that makes this the least local rule in the engine — is moved
*only* by draws, and the rescue neither inserts nor removes them. The
closure covers 6.4a's reorderings (`PS;DP` vs `DP;PS`) as well: the
transposed orders agree on every deck component, and the one fine point —
the draw's landing surviving the earlier stack — is the parity count
recorded in the interaction doc's Table 2 (stacking sees strictly fewer
placed coverers, so `PS;DP` is legal whenever `DP;PS` is).

**Lemma D2 (the first-layer split).** The only way a reveal can force a
draw is the `(Reveal, RevealEmpty)` → forced-king → `DeckPile(king)`
chain, and only first-layer targets can empty a pile. So: non-first-layer
reveals are draw-forcing-free and offset-neutral under reordering;
first-layer reveals are exactly the offset-coupled ones — kept by the
rule, never reordered. This is the anecdote, generalized.

**Lemma D3 (legality regression).** For a removed, non-first-layer reveal
`x`: legality at a mid-streak position implies legality at the streak
start, unless the destination was created mid-streak. Placements during
the streak can only *destroy* `x`'s options (a placed card of type `u`
covers one spot of type `u+4`; L1), which is the safe direction for
reordering earlier. What the streak's moves can *create*:

| creator | creates | new destination for |
|---|---|---|
| a draw's placement of `d_i` | a top of the drawn type | the family of `d_i` (kept by 6.4b) |
| a kept family reveal `x′` | the relocated `x′` as a fresh top, plus the exposed card — of an *unconstrained* type (a hidden flip) | `x′`'s children, one level below the family — **R1 without any `StackPile`**; the exposure — **R2** |
| a mid-streak `StackPile(u)` | a top of `u`'s type | cards that sit on `u` — **residue R1** |

The first row doubles as the exemption-tightness argument: the kept family
is exactly the reveal-legality the streak's own *draws* create — the same
pattern as 6.3's `{r, twin(r)}` after a reveal. Rows 2–3 are where kept
streak moves exceed the family: both residues are constructible by kept
moves alone (see §4).

## 4. The residues (where a counterexample would live)

**R1 — the deeper build.** The streak constructs a run *down* from the
drawn card using non-drawn cards: `DP(d)`, then `StackPile(u)` of the
family onto `d` — legal only now, because no rank-`r` top existed before
the streak — then `Reveal(x)` with `x` the *next* level down (rank `r−2`),
whose only destination is `u`: streak-created. (A second constructor needs
no `StackPile` at all: a kept family `Reveal(x′)` onto `d` installs `x′`
itself as a fresh top one level below the family, and the next level down is
removed by the rule exactly as here — the falsifier's R1 tag in §6, being
destination-shape based, covers both constructors.) `x ∉ mm >> 4` (one level
too deep) and not first-layer → removed. The reorderings all fail: before
the streak, `u` had no landing; after the streak, later family draws have
exactly `x`'s type, so they either consume `u`'s spot or land *on* `x`
itself — and a locked card that gets covered can never be revealed
afterwards. The candidate counterexample shape: no pre-streak card of the
drawn type, a forced interleaving by deck positions, and no alternative
winning line. Narrow, but not obviously empty.

**R2 — exposure-created destinations.** A kept family reveal exposes the
hidden card beneath it — of unconstrained type. If that exposed card is a
removed `x`'s only destination, `x`'s reveal is streak-dependent without
being in the family.

Both residues are the "unless"-clause of Claim A, and both are exactly
what the falsifier of §6 must measure.

## 5. Claim B: the twin exemption, and a second candidate mechanism

The convergent-encode argument (interaction doc, Table 2): `PS(twin d);
DP d` and `DP d; PS(twin d)` reach the same encode, so keeping one order
alive covers the other; the exemption guards against D canonicalizing the
pre-draw order away.

A second mechanism, new here: **burial**. The streak's subsequent draws
are (typically) of the family, whose landing type is the drawn pair's
type — `d`'s and `twin(d)`'s piles. A later draw landing on `twin(d)`
covers it, and with no pile-to-pile moves a buried locked card can never
be stacked; stacking `twin(d)` before the streak continues is therefore
time-critical in exactly the streak window. This also explains why `d`
itself needs no exemption (stacking `d` ≡ `DeckStack`, unrestricted) and
why no other stack does (pre-streak witnesses, by D3's logic).

## 6. The falsifier (P3 extension — concrete spec)

Instrument the point where 6.4b removes a reveal (a debug build of
`FullPruner::prune_moves`, around src/pruning.rs:117-120):

1. For each removed `Reveal(x)` at streak state `s`, record the
   streak-start state `s₀` — the parent of the streak's first draw
   (reconstructable from the search stack, or keep a small ring of
   encodes in the pruner).
2. Check witnesses at `s₀`: is `Reveal(x)` generated there
   (`gen_moves::<false>` + cycle filter)? If not, log
   `(deal, streak, x)` — a candidate R1/R2 instance.
3. Tag each hit: destination type one level below the family (R1 shape),
   or a card exposed inside the same streak (R2 shape)?
4. Correlate with the verdict: a hit on a game the unfiltered config
   solves but the full config does not is a live counterexample; hits on
   games both solve are exactly the witnesses the reordering rescue must
   explain.

For Claim B, log streak states where `twin(d)` is movable and stackable,
and check whether a later streak draw buries it in the winning line —
measuring the burial mechanism's frequency.

Zero logs over the reference corpus upgrades Claim A's reordering half to
"never observed to fail"; a hit is the `sorry`-free Lean target.

## 7. Standing

- The deck-offset argument (D1–D3) is written here for the first time;
  the in-code anecdote is decoded and generalized by D2.
- The first-layer exemption is now *derived* (offset-coupled through
  forced kings) rather than anecdotal.
- Open: the R1/R2 discharge, Claim B's necessity, and the P3-extension
  measurements.
- This document feeds the interaction doc's Table 2 (both `last_draw`
  rows) and its residual register item 5.
