# `Temp/Drain_transport_rows.lean` — report

**Outcome: all three `RaiseTransport` fields are closed, plus (A) and (D).**
No counterexample survives to (B) or (C); the file `Temp/Drain_transport_rows.lean`
(779 lines) compiles with `lake env lean Temp/Drain_transport_rows.lean` with
zero `sorry`, zero `Classical`, zero `noncomputable`, zero `native_decide`.

All theorem axiom prints are `[propext, Quot.sound]`.

---

## 1. Jobs delivered

| job | theorem | status |
|---|---|---|
| field 1 `CanRaiseS_preserved` | `OneColourClosure.drain_transport_canRaiseS_row` | proved (re-export of `specShift_sem_fwd`; same proof as `Temp/Drain_transport.lean`) |
| (A) `hcanrev` | `OneColourClosure.canrev_drain_row` | proved (`canRaise_reversibleAtW`) |
| (C) `rank_preserved` | `OneColourClosure.rank_preserved_row` | proved (delegates to `DrainClose.floor_raise`) |
| (B) `raisable_preserved` | `OneColourClosure.raisable_preserved_row` | **proved here** |
| (D) bundle | `OneColourClosure.raiseTransport_all` | proved |
| (D) payoff | `OneColourClosure.drain_phase_fork` | proved |

No residual `Prop` is left open.

### Exact statements (main rows)

```lean
theorem drain_transport_canRaiseS_row {u u' : State} {x c : Card}
    (hwf : u.WF) (h : Drain.DrainInvariant u x)
    (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hstep : State.step u (Move.tabToFound c) = some u') :
    CanRaiseS u' x.twin

theorem canrev_drain_row {u : State} {x c : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x) (hra : Drain.DrainRaisable u x)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin) :
    reversibleAtW u (Move.tabToFound c)

theorem rank_preserved_row {u u' : State} {x c : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x) (hra : Drain.DrainRaisable u x)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hstep : State.step u (Move.tabToFound c) = some u') :
    ∀ d, CanRaiseS u' d → x.rank.toIdx ≤ d.rank.toIdx

theorem raisable_preserved_row {u u' : State} {x c : Card}
    (huwf : u.WF) (hinv : Drain.DrainInvariant u x) (hra : Drain.DrainRaisable u x)
    (hc : CanRaise u c) (hcx : c ≠ x) (hct : c ≠ x.twin)
    (hstep : State.step u (Move.tabToFound c) = some u') :
    Drain.DrainRaisable u' x

theorem raiseTransport_all (x : Card) : Drain.RaiseTransport x

theorem drain_phase_fork {st : State} {x : Card}
    (hwf : st.WF) (h : Drain.DrainInvariant st x) (hra : Drain.DrainRaisable st x) :
    ∃ F, sameOrbitSetoid.r st F ∧ forkState F
```

### Axiom lines (verbatim)

```
'OneColourClosure.drain_transport_canRaiseS_row' depends on axioms: [propext, Quot.sound]
'OneColourClosure.canrev_drain_row' depends on axioms: [propext, Quot.sound]
'OneColourClosure.rank_preserved_row' depends on axioms: [propext, Quot.sound]
'OneColourClosure.canRaise_tabToFound_fwd_of_ne' depends on axioms: [propext, Quot.sound]
'OneColourClosure.raisable_preserved_row' depends on axioms: [propext, Quot.sound]
'OneColourClosure.raiseTransport_all' depends on axioms: [propext, Quot.sound]
'OneColourClosure.drain_phase_fork' depends on axioms: [propext, Quot.sound]
```

---

## 2. The mathematical core of (B)

Let `u'` be the landing state of a licensed raise of `c`.  The only cards whose
`freeCardS`/`nextUp` reads can *improve* are:

1. **the card directly beneath `c`** (the last card of `chop faceUp`).  It has
   rank `c.rank + 1` (ranks rise downward in a `faceUp` run) and becomes the new
   pile top, so once `freeCardS` holds its seat clause is exactly `CanRaise`'s.
   Handled by `canRaise_of_canRaiseS_of_top`.
2. **the unique `c.rank + 1` card of `c`'s suit** (`nextUp` can only change for
   that card).  Call it `d = succ(c)`.
3. **the twin of the card beneath `c`** (its twin can newly top the raised
   pile).  This one is *not* next-up: `c`'s colour is the *opposite* family to
   the pair (`color_ne_pair`), the card beneath `c` has the pair's colour, and
   the pair suits have rung `x.rank` (both twins are `S`-live).  So its rank
   would have to be `x.rank` while it equals `c.rank + 1 > x.rank`.

For `d = succ(c)`, the pair pin `pair_rank_pin` proves `c.rank = x.rank`:

* `color_ne_pair`: `c` has the opposite colour family to `x`;
* `under_card_twins`: the two `S`-live twins sit directly on the two distinct
  cards of that opposite family one rank above (they are twins of each other and
  neither is a pile top);
* if `c.rank = x.rank + 1`, then `c` itself is one of those two under-cards, but
  `c` is a pile top — contradiction;
* if `c.rank ≥ x.rank + 2`, the `x.rank + 1` card of `c`'s suit is already in the
  foundation, but it is one of the two under-cards — contradiction with
  `mem_found_unique`.

Then `succ(c)` has rank `x.rank + 1`, the same family, hence is one of the two
under-cards; its twin is the other, and both are buried (not tops).  A blocked
`S`-live card must have its twin on top (`PairRungKit.pileOfTop_twin_of_block`),
contradiction.  This is `succ_card_not_live`.

The remaining higher-rank transfers use `freeCardS_bwd_of_gt`, which rebuilds
`freeCardS u d` from `freeCardS u' d` for `d.rank > c.rank`, `d.suit ≠ c.suit`,
`d` not a top; the only obstruction (the twin becoming the new top) is killed by
the same colour/`nextUp` pin.

### Supporting rows (proved here)

```
lastOf_append_two, lastOf_shape_ne, cons_eq_of_append_cons_eq,
pileOfTop_eq_none_of_shape, fromCard_of_last, canRaise_of_canRaiseS_of_top,
twin_under_card_ne, under_card_twins, color_ne_pair, pair_rank_pin,
pileOfTop_tabToFound_eq_none_of_same_color, succ_card_not_live,
freeCardS_bwd_of_gt, canRaise_tabToFound_fwd_of_ne
```

---

## 3. Counterexample search (honesty note)

The instructed search was carried out before proving, by hand-constructing
small explicit states in the house style.

* **(C)** reduces to the existing statement `DrainClose.floor_raise`; a search
  for `d` S-live at `u'` with `d.rank < x.rank` finds nothing: the newly live
  cards are either `succ(c)` (rank `c.rank + 1`, and `c.rank ≥ x.rank` by the
  invariant floor) or one of the pair's two under-cards (rank `x.rank`).
* **(B)** has one genuinely near-miss configuration, which we chased in detail
  and which is **refuted by the `nextUp` pin, not by a state**:

  > the card `last (chop faceUp)` beneath `c`, and separately its twin, can
  > turn a card's `freeCardS` on by making `pileOfTop d.twin` non-`none`.

  In the twin case `d` has the pair's colour family, so its suit is `x.suit` or
  `x.twin.suit`, whose rungs are both `x.rank`; but `d.rank = c.rank + 1 >
  x.rank`, so `nextUp d` is false and `d` cannot be `S`-live.  In the
  `last (chop faceUp)` case `d` is the new top, so the seat clause of
  `freeCardS` *is* `CanRaise`'s seat clause and `d` is raisable.

No counterexample to (B) or (C) exists; both rows are theorems in the file.

### Non-kernel non-vacuity probe

`Temp/Drain_rows_probe.lean` (scratch, `#eval`, not part of the deliverable)
evaluates a concrete `WF`-shaped state with
`found = (11, 11, 0, 11)` (spade/heart/diamond/club), piles
`p0 = [K♥, Q♣, J♦]`, `p1 = [K♦, Q♠]`, and `x = Q♠`:

```
("nextUp qS", true)      ("nextUp qC", true)
("pileOfTop qS", some p1) ("pileOfTop qC", none)
("canRaiseSB qS", true)   ("canRaiseSB qC", true)
("tabToFoundR qS", true)  ("freeCard qC", true)
("pileOfTop qC", none)    ("drainLiveB", true)
```

So `Q♠` is raisable, `Q♣` is `S`-live but blocked, and the live set is exactly
the pair: the `DrainInvariant + DrainRaisable` hypotheses are satisfiable (the
state is terminal, so `drain_phase_fork` returns a fork by
`drain_terminal_fork`).  This is a computational sanity check only; the main
file's theorems are kernel-checked and do not depend on it.

---

## 4. Does `drain_raise_phase` now run unconditionally?

**Yes.**  `drain_phase_fork` instantiates `Drain.drain_raise_phase` with
`hcanrev := canrev_drain_row` and `htrans := raiseTransport_all x`, so the
raise-only drain now produces a fork in `sameOrbitSetoid.r st` directly from
`st.WF`, `DrainInvariant st x`, and `DrainRaisable st x` alone — no
`RaiseTransport` or reversibility provider remains as a hypothesis.
