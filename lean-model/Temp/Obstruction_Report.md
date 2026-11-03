# `Temp/Obstruction.lean` — report

Status: `lake env lean Temp/Obstruction.lean` exits **0**, no `sorry`, no
`Classical`, no `noncomputable`, no new `Prop`/`def` — only three theorems.
`Orig2/` and every other `Temp/*.lean` untouched.

## Exact statements

```lean
/-- The converse of the split — literally `canRaiseS_split.mpr`. -/
theorem canRaiseS_of_nextUp_of_freeCardS {z : State} (hz : z.WF) {x : Card}
    (hn : z.nextUp x = true) (hf : freeCardS z x = true) : CanRaiseS z x

/-- The obstruction classification. -/
theorem not_canRaiseS_cases {z : State} (hz : z.WF) {x : Card}
    (h : ¬ CanRaiseS z x) :
    z.nextUp x = false ∨ z.pileHolding x = none
      ∨ (∃ a bs run, z.pileHolding x = some a ∧
          (z.piles a).faceUp = bs ++ x :: run ∧ run ≠ [] ∧ z.pileOfTop x.twin = none)
      ∨ (∃ a, z.pileHolding x = some a ∧ below x (z.piles a).faceUp = [] ∧
          ((z.piles a).hidden ≠ [] ∨ x.rank ≠ Rank.king))

/-- Case (2) is a cover: `CoveredAt z x`, i.e. `∃ d, seatOf z d = some (.inr x)`. -/
theorem covered_of_not_canRaiseS {z : State} (hz : z.WF) {x : Card} {a : Anchor}
    {bs run : List Card}
    (hhold : z.pileHolding x = some a)
    (hface : (z.piles a).faceUp = bs ++ x :: run)
    (hrun : run ≠ []) :
    CoveredAt z x
```

These are root-namespace theorems (as are `freeCardS`, `CanRaiseS`,
`CoveredAt`), so they are usable unqualified after importing the file.

Consumption pattern for the main proof:

```lean
rcases not_canRaiseS_cases hz h with
  hnext | hnone | ⟨a, bs, run, hh, hface, hrun, htwin⟩ | ⟨a, hh, hbelow, hhk⟩
-- case (2):  exact covered_of_not_canRaiseS hz hh hface hrun
```

## Axiom lines

```text
'canRaiseS_of_nextUp_of_freeCardS' depends on axioms: [propext, Quot.sound]
'not_canRaiseS_cases' depends on axioms: [propext, Quot.sound]
'covered_of_not_canRaiseS' depends on axioms: [propext, Quot.sound]
```

## Where the disjunction had to be adjusted (exact deviations)

Everything is a `Bool` case split on `canRaiseS_split` + `freeCardS`; every
clause is forced by an arm of the `freeCardS` match.  Three fixes were needed
relative to the proposed statement:

1. **(1) had to gain `∨ z.pileHolding x = none`.**
   `nextUp x = false` alone is *not* exhaustive for `¬ CanRaiseS`: `freeCardS`
   has a first arm `| none => false`, and a card that is next-up but face-up in
   no pile is not raisable.  Cheapest witness: a standard deal with `A♠` in the
   stock — at the initial state `nextUp A♠ = true` (`foundHeight ♠ = 0 =
   A♠.rank.toIdx`), `pileHolding A♠ = none`, and no cargo slide ever puts a
   stock card into a pile.  `freeCardS` reads `false` there, `CanRaiseS` fails,
   and none of (2)/(3) applies (they both require `pileHolding = some a`).
   (The same arm also covers waste / founded / still-face-down cards, hence the
   wording "face-up in no pile".)

2. **(2)'s list equation was reversed.**  `faceUp` is bottom-first
   (`Orig/State.lean:256`), so the proposed `(z.piles a).faceUp = run ++ [x]`
   says `x` is the **top** with `run` *below* it — the opposite of "buried",
   and it contradicts `run ≠ []` being the obstruction (a card with cards
   below it is exactly the `below ≠ []` seat success).  The provable and
   semantically intended form is
   `(z.piles a).faceUp = bs ++ x :: run ∧ run ≠ []`, where `run` is the
   nonempty stack **above** `x`; this is exactly `fromCard x faceUp = x :: run`
   with `run ≠ []` (the `decide (run = [])` conjunct of `freeCardS` failing).
   The twin clause `z.pileOfTop x.twin = none` is unchanged and is exactly
   `(z.pileOfTop x.twin).isSome = false`.

3. **(3) could not keep `z.pileOfTop x = some a`, and needed the non-king
   escape.**  The third obstruction is the failure of the *seat* clause
   `decide (below x faceUp ≠ []) || (decide (hidden = []) && decide (x.rank = king))`,
   which gives `below x faceUp = [] ∧ (hidden ≠ [] ∨ x.rank ≠ king)`.
   `below x faceUp = []` only says `x` **bottoms** the face-up run; `x` is a
   pile top only in the special subcase `faceUp = [x]`, so
   `z.pileOfTop x = some a` is not derivable (and is false when there is a
   nonempty run above `x`).  The `x.rank ≠ king` disjunct is genuinely
   reachable at `WF`: a lone non-king in an otherwise empty pile
   (`hidden = []`, `faceUp = [x]`) fails `freeCardS` because the bare-king
   cell does not open to it.  The clause keeps `below x faceUp = []` verbatim
   as requested, and `∃ a` with `pileHolding x = some a` pins the pile (note
   `pileHolding`, not `pileOfTop`).

No other condition was needed: the disjunction is exactly the image of the
`freeCardS` arms (`none`, `fromCard = []` — vacuous at a holding pile —,
`S1 = false`, `S2 = false`), so it is complete; it is not claimed to be
minimal (case (3) and case (2) can overlap when `x` bottoms a run that is
nonempty above it).

## How the cover projection works

`covered_of_not_canRaiseS` needs case (2) *without* its twin clause (the twin
clause plays no role in the cover).  Writing `run = d :: rest`,
`d` is the card directly above `x`; `runOK_nodup` makes `d ∉ bs` and `x ≠ d`,
so `below d faceUp = bs ++ [x]`, whose `lastOf` is `x`; then
`tfc_seatOf_inr_intro` gives `seatOf z d = some (.inr x)`, i.e. `CoveredAt z x`.
`hz` enters only through `runOK_nodup` and `pileHolding_eq_some_iff`.
