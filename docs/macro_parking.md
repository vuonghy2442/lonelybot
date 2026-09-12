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

**(a) Same class.** `s_stk` is reachable from `s_tab` by one reversible
move (`PileStack(X)` from X's parked position), and `s_tab` from `s_stk`
by `StackPile(X)` (the spot X would take is still free — committing X
to the stack consumes nothing on the tableau). The two post-states are
one reversible pair apart, hence in the same closure class, hence carry
the same game value.

**(b) Stackability is preserved while parked.** A suit cannot advance
past an unstacked card — stacking is per-suit sequential, so while X is
parked, X's suit height sits at `X.rank` and "stack X" remains legal at
every future state until X is stacked.

**(c) Parking dominates.** Every play from `s_stk` has a value-equivalent
play from `s_tab`: keep X parked; immediately before the first move of
the `s_stk`-play that requires X up (or X's spot free, or the card under
X exposed), insert "stack X" — legal by (b). The reverse simulation
needs worry-backs; without them, `s_stk` cannot recover `s_tab`.

*Proof sketch.* (a) is by inspection of the two post-states (they differ
only in X's position). (b) follows from per-suit sequential stacking.
For (c), the "requires X up" dependence is type-local: only moves whose
legality or effect touches X's type ball are affected by X's position,
so the insertion points are well-defined and finite; the inserted move
is exactly the realization difference.

*Empirical support.* The F3 canon measurement: when the F3 fold stopped
materializing tableau outcomes of dominantly-stackable X, ~4.9M sweep
steps vanished (6.53M → 1.60M over the 3M-node seed-32 probe) — those
post-states were canonicalizing straight back into the stack outcome.
Dominant X is the forced case of (a), where the two realizations are
not merely same-class but sweep-*equal*.

## P.2 Corollary: the destination is not a fork

For any commitment, branching on the destination (tableau vs stack) is
never *semantically* necessary:

- with worry-backs available, the two branches are the same class (P.a);
- without them, tableau-first dominates (P.c);
- when only one realization is legal, there is no choice at all.

One successor per commitment — the tableau realization — is therefore
sound, with the stack realization kept only for the forced case (no
compatible slot). The residual obligation is the scar caveat: if a
commitment's *second closure class* (§6.7) is realized only on the
stack side, per-commitment tableau-collapse drops it — this is part of
the `missing` residue the differential measures and part of what C-SCAR
(the canonical-scar conjecture) must discharge before the collapse is
proven rather than merely measured.

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
1. *Channel priority is inverted.* `macro_transitions_core` fires
   stack-direct → tableau-direct → prefix-raise → stack-BFS → dig →
   borrow → tableau-BFS: the stack side outranks the parking side. The
   oracle does the opposite (`canon_tableau` is clustered before
   `canon_stack`). Both branches are explored (the sanctioned two), so
   this is an *order* deviation — but order is what moved seed 18
   draw-1 from 96,326 nodes (draw-first) to 84 (reveal-first).
2. *The branching budget is on the wrong axis.* The per-kind fold
   branches on the destination (a non-fork by P.2) and collapses the
   scar (the fork) via first-channel-wins: of the two borrow parents
   P₁/P₂ only the first survives the fold. The scar choice it keeps is
   the hand-written channel priority, not a canonical scar (C-SCAR's
   deepest-safe-dig-first).

## P.4 Parked experiments

- **Channel reorder** (cheap): parking channels before stack channels
  in `macro_transitions_core` + the fold's DFS order; gate on
  `macro_verdict_matches_engine`, measure with `macro_verdict_perf_probe`.
- **Per-scar fold** (C-SCAR): branch on the scar set instead of the
  kind; requires the canonical-scar conjecture's verdict sweep.
- **M-1 coincidence mining**: enumerate (commitment, kind, channel)
  pairs over the differential corpus whose canonical post-encodes
  coincide; every hit is a sound dominance rule with a P.a-style proof.
- **M-2 loss certificates**: the achievable-height min-plus fixpoint
  over the static unlock DAG (O2) — the only listed item that attacks
  losing-game exhaustion (seed 32: ≥3M canonical nodes vs the old
  engine's complete 2.9M-state refutation).
