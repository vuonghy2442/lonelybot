# Temp/FrozenSuit — report

## The theorem (exact statement)

`Temp/FrozenSuit.lean`, imports `Orig2.Fiber.LockRung` and
`Orig2.Fork.Class.ForkRaiseReorderProof`.

```lean
theorem commitLocked_rung_le {s z : State} {w : Card} {a : Anchor}
    (hs : s.WF) (horb : sameOrbitSetoid.r s z)
    (hnext : s.nextUp w = true)
    (htop : s.pileOfTop w = some a)
    (hbel : below w (s.piles a).faceUp = [])
    (hhid : (s.piles a).hidden ≠ []) :
    rungAt z w.suit ≤ rungAt s w.suit
```

This is verbatim the requested statement: same binders, same hypothesis list,
and the conclusion is exactly `≤ rungAt s w.suit`.  **No hypothesis had to be
weakened, strengthened or added**, and none of them is a hidden "only face-up
card / whole run" side condition (see the sharpening below).

## Axioms

`lake env lean Temp/FrozenSuit.lean` exits 0.  `#print axioms` on every theorem
in the file:

```
'FrozenSuit.below_cons_of_ne'               does not depend on any axioms
'FrozenSuit.faceUp_singleton_of_head_top'   depends on axioms: [propext]
'FrozenSuit.chop_cons_of_ne_nil'            depends on axioms: [propext]
'FrozenSuit.not_mem_fromCard_of_not_mem'    depends on axioms: [propext]
'FrozenSuit.putCard_piles_inl_apply'        does not depend on any axioms
'FrozenSuit.putCard_piles_inr_apply'        depends on axioms: [Quot.sound]
'FrozenSuit.putRun_piles_inl_apply'         does not depend on any axioms
'FrozenSuit.putRun_piles_inr_apply'         depends on axioms: [Quot.sound]
'FrozenSuit.not_canRaise_of_head_hidden'    depends on axioms: [propext, Quot.sound]
'FrozenSuit.not_inl_of_lock'                depends on axioms: [propext]
'FrozenSuit.head_afterRunRemoved_chop'      depends on axioms: [propext]
'FrozenSuit.putCard_faceUp_head'            depends on axioms: [propext, Quot.sound]
'FrozenSuit.putRun_lock'                    depends on axioms: [propext, Quot.sound]
'FrozenSuit.setPile_afterRunRemoved_lock'   depends on axioms: [propext]
'FrozenSuit.lock_step'                      depends on axioms: [propext, Quot.sound]
'FrozenSuit.lock_play'                      depends on axioms: [propext, Quot.sound]
'FrozenSuit.commitLocked_rung_le'           depends on axioms: [propext, Quot.sound]
'FrozenSuit.commitLocked_rung_le_of_not_king' depends on axioms: [propext, Quot.sound]
```

The last entry is a companion theorem (proved, not assumed) showing that for a
non-king `w` the `hidden ≠ []` hypothesis can be dropped:

```lean
theorem commitLocked_rung_le_of_not_king {s z : State} {w : Card} {a : Anchor}
    (hs : s.WF) (horb : sameOrbitSetoid.r s z)
    (hnext : s.nextUp w = true)
    (htop : s.pileOfTop w = some a)
    (hbel : below w (s.piles a).faceUp = [])
    (hk : w.rank ≠ Rank.king) :
    rungAt z w.suit ≤ rungAt s w.suit
```

It is proved entirely from the pre-existing `LockInv` / `lockInv_play` rows.

`[propext, Quot.sound]` only.  No `sorryAx`, no `Classical.choice`, no
`noncomputable`, no new `Prop` wrapper definition (the invariant is a
conjunction inside theorem statements), and `Orig2/` is untouched.

## The invariance lemma actually needed

The whole theorem is `lock_step` + `lock_play` plus two library rung bridges.
The step lemma, verbatim:

```lean
theorem lock_step {U V : State} {w : Card} {a : Anchor} {m : Move}
    (hwf : U.WF) (hstep : U.step m = some V) (hrev : reversibleAtW U m)
    (hhead : ∃ t, (U.piles a).faceUp = w :: t)
    (hhid : (U.piles a).hidden ≠ [])
    (hnf : w ∉ U.found w.suit) :
    (∃ t, (V.piles a).faceUp = w :: t) ∧ (V.piles a).hidden ≠ [] ∧
      w ∉ V.found w.suit
```

i.e. **the three-part lock invariant**

```text
  (i)  w is the HEAD of its pile's face-up run,
  (ii) that pile's hidden deck is non-empty,
  (iii) w is not on its foundation row,
```

is closed under every reversible letter; `lock_play` carries it along an
arbitrary `ShufflePlayW` (and derives `Z.WF`).  The final step uses the
existing `le_rung_of_not_found` (`w ∉ found ⇒ rung ≤ w.rank.toIdx`) and
`nextUp` to identify `rungAt s w.suit = w.rank.toIdx`.

Per-letter reasons (all in `lock_step`):

* `draw`: `piles`/`found` untouched (`stepDraw_piles`, `stepDraw_found`);
* `wasteToFound` / `wasteToTab`: not reversible at all
  (`wasteToFound_not_reversibleAtW`, `wasteToTab_not_reversibleAtW`);
* `tabToFound c`: `c = w` would be a `CanRaise` of the locked card
  (`canRaise_of_reversibleAtW`), killed by `not_canRaise_of_head_hidden`;
  otherwise the chop of the run still starts with `w` and the hidden deck is
  untouched (`afterRunRemoved_ne` at a non-empty prefix);
* `foundToTab c b`: `putCard` appends at the landing pile, `putCard_found` /
  `putCard_hidden_eq`, and `w ∉ found` survives because the run is only
  `chop`ped;
* `tabToTab c b`: `c = w` is impossible because `tabToTabR U w b = true`
  would need `below w faceUp ≠ []` (false) or `hidden = [] ∧ w king`
  (false by (ii)); otherwise `setPile` of the removal keeps `w` at the head
  (with the hidden deck unchanged), and `putRun` appends at its landing pile.
  Empty-seat landings (`Sum.inl`) can never hit `w`'s pile because that pile
  is non-empty (`not_inl_of_lock`).

Three small helpers (`putCard_faceUp_head`, `putRun_lock`,
`setPile_afterRunRemoved_lock`) carry the two pile edits of the move
algebra.

## Sharpenings found while formalising (the "interesting outcome")

1. **"`w` is the pile's only face-up card" is not an extra hypothesis — it is
   already forced.**  At a `WF` state, `pileOfTop s w = some a` says `w` is the
   *last* element of `s.piles a`'s face-up run, and `below w faceUp = []` says
   nothing stands before the *first* `w`; uniqueness of cards then gives
   `faceUp = [w]`.  So no "whole run" / "sole face-up card" rider is needed.
   (This is the lemma `faceUp_singleton_of_head_top`.)

2. **`hidden ≠ []` is load-bearing, but only in the king case.**  If the caller
   knows `w.rank ≠ Rank.king`, the hypothesis `hhid` is not needed at all: the
   repository's existing `LockInv` / `not_canRaise_of_lock`
   (`Orig2/Fiber/LockRung.lean:144,151`) already gives the same conclusion via
   `lockInv_play` — that is the proved companion
   `commitLocked_rung_le_of_not_king` in the file.  For a king,
   `below w faceUp = []` gives `chop faceUp = []` and the only surviving
   `CanRaise` disjunct is `hidden = [] ∧ w king`, so exactly `hidden ≠ []` is
   what kills it.  Conversely with `hidden = []` and `w` a non-king the lock
   genuinely fails (`w` is then a bare non-king top, which is raisable and
   reversible), so `hhid` cannot simply be dropped in the stated generality.

3. **Cards may be stacked on top of `w` at any point.**  Landings (`putRun`
   and `foundToTab`) append *after* `w`, so `w` stops being the pile top but
   stays at the head of the run; when those cards leave, `w` becomes the top
   again with `chop = []`.  So the lock is not "`w` always tops its pile": the
   right invariant is head-of-run (plus hidden and unfounded), which is what
   `lock_step` tracks.

4. **No hypothesis on `z` is needed.**  `hs : s.WF` plus the reversibility of
   each letter re-derives `z.WF` (`step_wf` inside `lock_play`).

## Blunt answer

**Yes — a commit lock really is frozen across the orbit.**

`w` (next-up, alone face-up on its pile, hidden deck non-empty beneath) is
never `CanRaise` at any orbit-mate, hence is never founded at any orbit-mate,
hence the suit's rung never passes `w`'s rank; the conclusion
`rungAt z w.suit ≤ rungAt s w.suit` holds for *every* `z` with
`sameOrbitSetoid.r s z`.  There is no counterexample.

The lock is not an equality: pulls can lower the rung, so the strict
`<`/`=` refinements are false, and the `≤` is exactly the right strength.
