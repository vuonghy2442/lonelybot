# Parking: the destination is not a fork — design lemma and audit

(2026-09-12. To be folded into `macro_formalization.md` §4 when the
word-level engine edit settles; kept separate while §6.5b is in flight.
All measurements cited are from the 2026-09-12 session, commit `bf479a6`.)

## P.0 The design principle, stated

The macro game's moves are the two irreversible *parking* decisions:

- **Reveal** — slide a locked surface card off the card it covers, onto
  another tableau spot;
- **Deck-to-tableau** — take an accessible deck card and lay it down.

Everything else a play does is one of:

- **forced stacking** — the safe-sweep canonicalization stacks every
  dominantly-safe, movable, unlocked card (this is `canonicalize`);
- **just-in-time stacking** — stacking a *non*-dominant card is never a
  decision worth branching on: it can be deferred to the moment it is
  forced (Lemma P below);
- **accommodation** — the reversible shuffles (worry-backs, digs) that
  *make a parking spot*, internal to realizing a commitment.

Under this reading the only genuine fork per commitment is the
**scar**: *which card comes back down from a foundation to make room.*
Each worried-back card leaves a different residue — a different card
buried, a different set of things stackable — and that residue is the
branch. This is the same content as C2's measured-and-corrected form
(§6.3/§6.7: "the second class labeled by the irreversible scar of the
accommodation"), read from the design side rather than the measurement
side.

## P.1 Lemma P (parking) [~]

Let `s` be a canonical state, `X` a commitment target whose tableau
placement is legal at `s` (a compatible free slot exists), and suppose
the stack realization is also available (X stackable at `s`). Let
`s_tab` / `s_stk` be the two post-states. Then:

**(a) Same class — measured false as stated.** The forward leg is
unconditional: `PileStack(X)` from X's parked position is always
reversible-legal (parked ⇒ visible, unlocked, uncovered, stackable).
The return leg is not: from `s_stk`, `StackPile(X)` needs a free spot
of X's type, and the corpus shows it is not always there. The probe
(`debug_destination_diamond`, 722 both-kind commitments): 79%
swept-equal (the dominant region — provably so, arithmetic from the
dominance definition), 14% encode-equal after the link, 3%
closure-linked, and **34/722 = 4.7% distinct classes**. The
destination fold is therefore a genuine prune, not a class-quotient;
the property it actually needs is the one-sided containment
**L-CONT** — `solvable(s_stk) ⟹ solvable(s_tab)` — which held 34/34
on the measured misses and 128/128 with the promoted fold. See the
later §P.6 for the ledger.

**(b) Stackability persists; freeness may not.** A suit cannot advance
past an unstacked card — stacking is per-suit sequential, so while X is
parked and *uncovered*, X's suit height sits at `X.rank` and the height
condition of "stack X" remains satisfied at every future state until X
is stacked. The movability condition does not persist: a later park of
a type X−4 card (rank r−1, opposite color) can cover X, and when X's
instance is the only uncovered instance of its type, every realizing
arrangement does. Covering is a fiber fact — the set-level state shows
only the parity flip at X's type (`bm[X-type]` empties) — so the
abstract-state observable of the corner is a `!bm[X-type]` window while
X remains unstacked.

**(c) Parking dominates, up to the covering corner.** Every play from
`s_stk` that never needs X covered-over has a value-equivalent play from
`s_tab`: keep X parked; immediately before the first move of the
`s_stk`-play that requires X up (or X's spot free, or the card under X
exposed), insert "stack X" — legal by (b) while X is uncovered. The
insertion point is therefore "when X is free and stackable", not merely
"when X is needed": if X has been covered, freeing it requires stacking
the coverer, and placed cards have exactly one exit (being stacked —
there are no pile-to-pile moves), so the coverer chain is itself an
accommodation obligation — the machinery Lemma P is trying to dissolve
the fork into. The open corner to name: *all realizations of a later
commitment cover X, and the covering card cannot be stacked in time.*
Plausibly the same dig-shaped-scar phenomenon as the C-SCAR residue.
The reverse simulation needs worry-backs; without them, `s_stk` cannot
recover `s_tab`.

*Proof sketch.* (a)'s forward leg is by inspection; the return leg fails
at the measured 4.7%, and L-CONT replaces the mutual claim — the
dominant region is proven outright, the remainder is `[m]`. (b) follows
from per-suit sequential stacking for the height condition; the freeness
caveat and its fiber-level observable are as stated. For (c), the
"requires X up" dependence is type-local: only moves whose legality or
effect touches X's type ball are affected by X's position, so the
insertion points are well-defined and finite; the inserted move is
exactly the realization difference, available whenever X is uncovered.

*Empirical support.* The F3 canon measurement: when the F3 fold stopped
materializing tableau outcomes of dominantly-stackable X, ~4.9M sweep
steps vanished (6.53M → 1.60M over the 3M-node seed-32 probe) — those
post-states were canonicalizing straight back into the stack outcome.
Dominant X is the forced case of (a), where the two realizations are
not merely same-class but sweep-*equal*.

## P.2 Corollary: the destination is not a fork

For any commitment, branching on the destination (tableau vs stack) is
never *semantically* necessary:

- the one-sided containment L-CONT holds on everything measured —
  `solvable(s_stk) ⟹ solvable(s_tab)`, 34/34 on the probe's boundary
  cases, 128/128 with the promoted fold (P.a's mutual form fails at
  4.7%, but the fold only needs this direction);
- without worry-backs, tableau-first dominates (P.c);
- when only one realization is legal, there is no choice at all.

One successor per commitment — the tableau realization — is therefore
sound *modulo two named drops*, with the stack realization kept only for
the forced case (no compatible slot):

- **stack-side scar classes.** §6.7 measured a same-kind *stack* split
  (the two-class `Draw(20)` case): the second class realized only on the
  stack side. The current fold already declines to hunt it — the
  `!stack_produced && !stack_now` gate on the shared BFS — so a
  per-commitment tableau collapse widens that known under-emission from
  a measured residue into a designed-in one. C-SCAR (the canonical-scar
  conjecture) must discharge it first; this is part of the `missing`
  residue the differential measures.
- **the covering corner of P(b)/(c)** — the one case where parking first
  is not freely recoverable.

The experiment is F3-shaped: flip the fold to per-commitment
tableau-first emission and watch the class-coverage metric in
`macro_direct_matches_oracle` plus the 128-game verdict sweep — the
instruments already exist.

The two-branch fold as currently implemented is a deliberate
over-approximation: it never loses a verdict (the gate is green), it
only re-explores class-equivalent territory under different encodes —
measured at +3.5–14% branches and ~7% node drift between the oracle
(class clustering) and direct (per-kind) paths.

## P.3 Audit: does the implementation follow the principle?

As of `bf479a6`:

**Follows**
- Commitment set is exactly Reveal / Draw (`Commitment`, src/macro_game.rs).
- The sweep does the forced stacking (`canonicalize`).
- The accommodation channels (dig / borrow / shared BFS) make parking
  spots; prefix-raise and the stack channels are the stack-side
  fallback.
- F3 in the search fold is precisely the forced case of P: when the
  sweep would immediately undo a park, the park branch is not emitted.

**Deviates**
1. *Channel priority is inverted.* Within a commitment's emission
   group, `macro_transitions_core` fires stack-direct, tableau-direct,
   prefix-raise, dig, borrow, then the shared-BFS results (stack-bfs,
   tableau-bfs): the stack side outranks the parking side at the fixed
   channels, and the first-wins fold keeps its representative. The
   oracle's clustering considers tableau samples first (`canon_tableau`
   before `canon_stack` in `enumerate_transitions`; within each sample
   set, the DFS order is enumeration order). Both branches are explored
   (the sanctioned two), so this is an *order* deviation — but order is
   what moved seed 18 draw-1 from 96,326 nodes (draw-first) to 84
   (reveal-first).
2. *The branching budget is on the wrong axis.* The per-kind fold
   branches on the destination (a non-fork by P.2) and collapses the
   scar (the fork) via first-channel-wins: of the two borrow parents
   P₁/P₂ only the first survives the fold. The scar choice it keeps is
   the hand-written channel priority, not a canonical scar (C-SCAR's
   deepest-safe-dig-first).

## P.6 Why either scar works — the convergence argument [~]

The C-SCAR result (either single-scar policy preserves verdicts) is not a
coincidence; it has a mechanism. The two surviving scar classes (after T
collapses the P₁/P₂ twin choice — those covers are type-identical: same
rank, same color) are the *cross-kind* pair, dig vs borrow: the dig's
post-state has twin(X) up (+1 on the twin's suit, X parked on the twin's
vacated spot); the borrow's has parent P down (−1 on P's suit, X parked
on P).

1. **Convergence point.** A win is all-foundations-complete, so every
   winning play from either scar contains X's own stacking, at some
   moment t₁.
2. **Post-convergence repair.** After t₁, the dig's residue (twin up)
   is progress, and the borrow's residue (P re-exposed) is repairable:
   P was stackable at worry-time by construction — its suit height sat
   at P.rank exactly — so re-stacking is a legal reversible move, and
   repairs are accommodation-internal (invisible to the macro move
   structure). The futures merge up to one reversible repair.
3. **Pre-convergence window.** Before t₁, the states differ only in
   type-invisible ways (X's covers are type-identical; height deltas
   repair inside future accommodations) — except one hole: the
   borrow's P is *buried under X*, so its repair is deferred until X
   stacks. A winning line needing P's foundation-top before t₁, with no
   same-type substitute, would make the classes genuinely diverge.

Steps 1–2 are essentially rigorous (the win condition forces the
convergence point; post-convergence is closure algebra). Step 3's hole
is *the same obstruction* as the parking lemma's covering corner
(P.1(b)): **P2 absorption, the parking dominance half, and C-SCAR's
verdict-equivalence stand or fall on the same buried-scar window — one
proof obligation, three theorems.** Falsifier prediction: any
counterexample has the shape "X commits, X cannot stack in one scar
class (prefix blocked by the scar's burial chain), the other class
wins" — hunt with the `!bm[scar-type]`-while-X-unstacked instrument.

## P.7 Four new proof surfaces (2026-09-12, closing the arc)

- **Scar monogenicity [finite check].** If two displacement moves
  (dig-twin / borrow-P₁ / borrow-P₂) each survive the other, their
  composition's class collapses to the second displacement alone —
  accommodation chains are indexed by one card's displacement, so
  ≤2 classes per commitment becomes structural (Newman local
  confluence; the proof is a 3×3 pair analysis in the words algebra;
  the non-confluent pairs = the delimited crease). Falsifier: group
  the corpus's multi-step witnesses by last-displacement vs
  displacement-multiset.
- **Height-walk decomposition [M-4's proof].** Winning plays are
  lattice walks in ℤ⁴ (stack = +eᵢ, worry = −eᵢ) whose excursions are
  *funded* by the static unlock DAG — so accommodation depth is
  bounded by the DAG's longest chain, a priori. Falsifier: per-seed
  longest-chain vs deepest observed witness.
- **The exchange lemma [the unlock greedoid].** Feasible commitment
  sets (playable in some order) may form a greedoid; exchange would
  subsume scar equivalence, parking dominance, streak rules, and
  C-IND independence (stubborn sets become a corollary). Predicted
  exception region: the covering corner. Falsifier: corpus enumeration
  of small feasible pairs.
- **One simulation [proof economy].** R = "differ by one repairable
  displacement" is a one-directional simulation; F3, L-CONT, and
  C-SCAR are each the conservative side of R, so one induction (repair
  insertion + type-ball locality) proves all three, and the covering
  corner is exactly the non-R region — the only place any fold can
  fail.

The unifying picture: height space ℤ⁴, the game a lattice walk with
funded excursions, the dominance cone governing the sweep, scars as
debts repaid before the top element, and the covering corner as the
sole obstruction to exchange-greediness. Parking, scars, streaks, and
certificates are one object from four sides.

*Complexity caveat.* Generalized Klondike is NP-complete, and none of
the P-series claims conflict with that — they are fixed-52 statements
(the game is a finite O(1) object). But hardness *predicts the
failure modes under scaling*: M-2's residual (alive-under-the-bound-
but-dead) is complexity-theoretically required to be non-empty in the
generalized game (an exact fixpoint would make solvability poly);
M-4's bound is Θ(n) (the DAG chain grows with rank count — the crease
is linear, not constant); the exchange lemma, if true, can only be a
pruning tool (no poly augmentation oracle, or the exception set
carries the hardness); and C-IND stays a constant-factor reduction,
not a complexity collapse — hardness lives in the composition of n
commitments, not the O(1)-width type locality. Note also: this
engine's variant (no pile-to-pile moves, K+ full-information deck)
breaks the standard hardness gadgets, so its generalized complexity
is technically open — the cautious prior remains "hard."

## P.5 Experiment log

**C-SCAR verified on the acceptance corpus (2026-09-12, same setup).**
`macro_verdict_matches_engine` extended to run the single-scar policies:
both `SuccSelect::TallestOnly` and `SuccSelect::ShortestOnly` match the
old engine's verdict on all 32 games × both draws — zero mismatches,
with per-seed timings differing from `All` (the policies filter for
real) but always agreeing on verdict. This is *stronger* than the
conjecture's "deepest-safe-dig-first never loses a win": either scar
choice preserves the verdict, i.e. the second class's futures are
verdict-equivalent on this corpus — the empirical face of P2
absorption. The canonical-scar choice is a free parameter; pick by
cost. Remaining obligations: the 128-game policy sweep (not runnable
pre-words — the oracle walk makes it minutes-to-hours), the absorption
proof for multi-rank chains, and M-4's a priori depth bound.

**P.2 caveat 1 discharged — the under-emission is a depth artifact
(2026-09-12, pre-words tree at `bf479a6`, throwaway worktree).** With
the accommodation caps raised 12/10 → 40 (and `StepTransition`'s
`ArrayVec<Move, _>` capacity scaled to match — a hard requirement, the
shallow capacity panics on deep witnesses):

- `macro_direct_matches_oracle`: **missing 12 → 0** (extra 0, separate 0
  unchanged; merged 10315 → 10327; oracle classes uncovered 21 → 11),
  runtime unchanged (0.06s — the level-order kills make most goals
  terminate far below any cap);
- `macro_verdict_matches_engine`: green, perf-neutral (0.96s);
- seed 32 (3M-node capped probe): +1–5% BFS states, +1% wall.

Conclusion: the per-kind fold's residual was measuring the depth
bound, not a rule-list gap — at depth ≤ 40 the direct rule list covers
every oracle class on the corpus. P.2's first named drop downgrades
from designed-in under-emission to depth artifact; C-SCAR's remaining
obligation is the a priori bound (M-4, DAG-derived; deepest observed
witness ≈ 26 steps, so 30 suffices empirically). Actionable on the
words tree: raise the caps and scale the capacity — expected
`missing=0` there at smaller marginal cost.

**P.3 deviation 1 measured — parking-first order is safe but
perf-neutral.** Reordering tableau-direct before stack-direct within
each commitment's emission group: verdicts green, differential
identical (the per-kind fold keeps the same representatives, so the
metrics are order-invariant), timing ±3–9% mixed sign. Unlike
reveal-first at the commitment level (96k → 84 nodes on seed 18), the
kind order within a commitment barely matters — both branches are
explored and the tp table absorbs the consequences. The design
alignment argument stands; the speed argument does not.

## P.6 The collapse, promoted — and its remaining proof surface

(2026-09-12, words tree. The fold is now the shipped macro search
semantics: `collapse_pick` in `macro_solvable_direct`.)

**The reduction.** Branch on the destination is sound iff the two
post-states carry the same value. Two roads to that:

- *The class route (strong).* `post_tab ≡ post_stk` as closure classes.
  The link is unconditionally legal: from `post_tab`, `PileStack(X)` — X
  is parked ⇒ visible, unlocked, uncovered, stackable — and the move is
  reversible (X unlocked). Class then reduces to the sweep/stack diamond
  R-DIA: `canonicalize(post_tab + PileStack(X)) ≡class post_stk`.
- *The containment route (the one the fold actually needs).* One-sided:
  `solvable(post_stk) ⟹ solvable(post_tab)`. Proven for the F3-dominant
  region — X is dominantly safe ⇒ the `post_tab` sweep stacks X
  (movable/uncovered/dominant at park time; parking only covers its
  parent, which was canonical, so no extra sweep fires) ⇒ sweep-*equal*.
  Note the covering corner (P.1b) does **not** bear on the class route —
  closure reachability never simulates future play.

**The measurement** (`debug_destination_diamond`): 722 both-kind
commitments on the differential corpus. Tableau→stack link lands:

- in P.1a's class: **79%** — the tableau outcome already swept X (the
  generalized F3 signature; sweep-equal);
- encode-equal after the link: 99;
- closure-linked: 22;
- **distinct classes: 34 (4.7%)** — R-DIA fails at measurable rate; the
  class route is *not* the theorem.

All 34 misses then held **win-region containment** against ground-truth
`solve`: solvable(stack side) ⟹ solvable(tableau side), held=34,
violated=0. The misses' recurring shape (10♥/Q♣ pairs across turns of
seed 12; K♣ runs on seed 40) is the covering corner's fingerprint —
candidate witnesses for the P.1c gap, and in every one the parked branch
recovered the win anyway.

**Status of the collapse.** Promoted after the 128-game corpus gate
(0 mismatches; the single cap was seed 32, undecidable-in-budget in both
folds). Proven pieces: class-value invariance; the link lemma; the F3
region's sweep-equality (arithmetic, ~93% of duals land same-class).
Evidence pieces `[m]`: L-CONT on all 34 measured misses; C-SCAR's
scar-side equivalence (§P.5, both policies verdict-equal). Open `[~]`:
L-CONT proven at scale (or a constructed counterexample) — the corner
that remains is exactly "forced cover of X with the coverer unstackable
in time"; C-SCAR's multi-rank absorption proof; M-4's depth bound.

Also this tree: accommodation caps 12/10 → 40 (P.5's depth-artifact fix,
ported to the words engine; `StepTransition` capacity 42), differential
now `missing=0 extra=0`, merged=10327 — matching the pre-words cap-40
measurement exactly.

## P.4 Parked experiments

- **Channel reorder** (cheap): parking channels before stack channels
  in `macro_transitions_core` + the fold's DFS order; gate on
  `macro_verdict_matches_engine`, measure with `macro_verdict_perf_probe`.
- **Per-scar fold** (C-SCAR): branch on the scar set instead of the
  kind; requires the canonical-scar conjecture's verdict sweep.
- **M-1 coincidence mining**: nearly free as an instrument — the
  differential already holds (commitment, kind, channel, canonical
  encode) per state; logging cross-channel encode coincidences
  (stack-direct vs tableau-direct landing on the same swept encode is
  the generalized F3 signature) turns the corpus into the miner, and
  every hit is a sound dominance rule with a P.a-style proof.
- **M-2 loss certificates**: the achievable-height min-plus fixpoint
  over the static unlock DAG (O2) — the only listed item that attacks
  losing-game exhaustion (seed 32: ≥3M canonical nodes vs the old
  engine's complete 2.9M-state refutation). Composes with the
  commutation/stubborn-set reduction (C-IND): certificates prune
  branches, stubborn sets prune orderings, and both orders' swept
  encodes compare directly off the words engine's `post_words` /
  `set_board`.
