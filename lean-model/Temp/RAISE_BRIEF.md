# BRIEF — prove the raiseS reordering lemmas

## Ground rules
- Repo: `B:\code\lonelybot\lean-model`. Toolchain `leanprover/lean4:v4.34.1`, built with `lake`.
- **Do not edit anything under `Orig2/`, `Orig/`, `Archive/`, `Klondike/`.** Write only new files under `Temp/`.
- **No `sorry`.** No `Classical.choice`, no `Classical.em`, no `noncomputable`. Axiom battery must be `[propext]` / `[propext, Quot.sound]`.
- Verify every attempt with:
  `cd B:\code\lonelybot\lean-model; lake env lean Temp\<yourfile>.lean`
  and finish the file with `#print axioms <name>` for each theorem you prove.
- Report: the file path, whether it compiles, the axiom lines, and the exact statement of what you proved.

## The existing card (imports give you all definitions)

`Orig2/Fork/Class/ForkRaiseReorder.lean` — currently compiles, contains:

```lean
namespace OneColourClosure

def RaiseStepS (z z' : State) (c : Card) : Prop :=
  ∃ z₀, CargoPath z z₀ ∧ State.step z₀ (Move.tabToFound c) = some z'

inductive RaiseSSeq : State → List Card → State → Prop
  | nil (s : State) : RaiseSSeq s [] s
  | cons {s z z₀ z' : State} {c : Card} {ws : List Card} :
      RaiseSSeq s ws z → CargoPath z z₀ →
      State.step z₀ (Move.tabToFound c) = some z' → RaiseSSeq s (c :: ws) z'

-- PROVED already:
theorem suit_eq_or_twin_of_color {s t : Suit} (h : s.color = t.color) : s = t ∨ s = t.twin
theorem cover_seats {x c y : Card}
    (hx : canSitOn x c.twin = true) (hy : canSitOn x y = true) : y = c ∨ y = c.twin
theorem nextUp_raise_ne {z z' : State} {c d : Card}
    (h : State.step z (Move.tabToFound c) = some z') (hd : d.suit ≠ c.suit) :
    z'.nextUp d = z.nextUp d

-- TO PROVE (currently `def … : Prop`):
def RaiseAbove : Prop := ∀ {st w : State} {c d : Card},
  st.WF → State.step st (Move.tabToFound c) = some w →
  c.rank.toIdx < d.rank.toIdx → (CanRaise st d ↔ CanRaise w d)

def SpecShift : Prop := ∀ {u z z' : State} {c d : Card},
  z.WF → RaiseStepS z z' c → d ≠ c → d ≠ c.twin →
  (CanRaiseS z d ↔ CanRaiseS z' d)

def RaiseSReorder : Prop := ∀ {s : State} {c : Card},
  CanRaiseS s c → ∀ {ws : List Card} {z : State},
    RaiseSSeq s ws z → c ∈ ws → ∃ z', RaiseSSeq s (c :: ws.erase c) z'

end OneColourClosure
```

Start your file with `import Orig2.Fork.Class.ForkRaiseReorder` (so the definitions and the
three proved lemmas are in scope), then state/prove your target inside `namespace OneColourClosure`.

## Key facts already located (use them; do not reprove)

| lemma | file:line | content |
|---|---|---|
| `canSitOn_eq` | `Orig/Basic.lean:111` | `canSitOn c b = true ↔ c.rank.toIdx + 1 = b.rank.toIdx ∧ c.suit.color ≠ b.suit.color` |
| `Suit.color_twin` | `Orig/Basic.lean:42` | `s.twin.color = s.color` |
| `Rank.toIdx_inj` | `Orig/Basic.lean:65` | `r.toIdx = r'.toIdx → r = r'` |
| `State.nextUp` | `Orig/State.lean:385` | `decide (c.rank.toIdx = st.foundHeight c.suit)` |
| `rungAt_tabToFound` | `Orig2/Substrate/Position.lean:166` | `rungAt v σ = if σ = c.suit then rungAt u σ + 1 else rungAt u σ` |
| `rungAt_cargoPath` | `Orig2/Fork/Local/ForkCriticalPair.lean:97` | `CargoPath a b → rungAt a σ = rungAt b σ` |
| `step_tabToFound_inv` | `Orig2/Substrate/Kit.lean:671` | `st.nextUp c = true ∧ ∃ a, st.pileOfTop c = some a ∧ (… ∧ s' = …)` |
| `canRaise_of_raise_other` | `Orig2/Fork/Split/ForkDrainInduction.lean:165` | **backward**: `CanRaise w d → CanRaise st d`, given `d.suit ≠ c.suit`, `st.pileHolding d = some b`, `w.piles b = st.piles b` |
| `canRaise_of_raise_high` | `:216` | **backward**: same, with `st.pileHolding d = some b` and `d.rank ≤ c.rank` |
| `canRaise_of_raise_high_fwd` | `:258` | **forward**: `CanRaise st d → CanRaise w d`, `d ≠ c`, `d.rank ≤ c.rank` |
| `canRaise_of_pull_of_ne` | `Orig2/Fork/Split/ForkTailCover.lean:153` | pull dual |
| `canRaiseS_split` | `Orig2/Substrate/CargoRaise.lean:858` | `CanRaiseS st c ↔ st.nextUp c = true ∧ freeCardS st c = true` (needs `st.WF`) |
| `freeCardS_sem` | `Orig2/Fiber/FreeOrbit.lean:1305` | semantic form: held, parented-non-king or bare-king, plus a hatch clause over `e` with `canSitOn e c` |
| `freeCardS_orbit_rung` | `Orig2/Fiber/FreeOrbit.lean:1376` | `freeCardS s c = true ↔ freeCardS s' c = true` for **same orbit + same rung vector** |
| `raiseSt_commute` | `Orig2/Fork/Local/ForkCriticalPair.lean:224` | two raises of different suits commute (functional equality) |
| `twin_raise_square` | `:241` | two vanilla raises of different suits fire in **both** orders, same landing state |
| `step_wf` | `Orig2/Substrate/StepWF.lean` | `st.WF → step st m = some s' → s'.WF` |

## Structural facts that took a long time to establish — assume and use

1. **Runs descend upward in rank.** `canSitOn x y` is `x.rank + 1 = y.rank`, so the pile *top*
   has the **lowest** rank; cards below a card have **higher** rank. Hence a card `d` with
   `c.rank < d.rank` **can** sit below `c` in `c`'s pile. Do not assume "higher rank ⇒ other pile".
2. **A cover's only seats are the twin pair.** `cover_seats` (already proved): the card directly
   above `c.twin` can only be placed on `c` or `c.twin`.
3. **`CanRaiseS` is a function of `(orbit, rung vector)`.** Slides preserve rungs
   (`rungAt_cargoPath`) and `freeCardS_orbit_rung` gives representative independence. So when a
   state-level side condition is inconvenient, *choose a different representative* at the same rung.
4. **`SpecShift` is unconditional only at the `CanRaiseS` level.** The state-level lemmas carry
   `pileHolding d = some b` and `d.rank ≤ c.rank`; those are witness content, absorbed by (3).

## Targets, one per agent

### T1 — `RaiseAbove`
```lean
theorem canRaise_of_raise_above {st w : State} {c d : Card} {b : Anchor}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit) (hrank : c.rank.toIdx < d.rank.toIdx)
    (hd : st.pileHolding d = some b) (h : CanRaise st d) : CanRaise w d
```
Plan: `obtain ⟨-, a₀, hpa₀, hs⟩ := step_tabToFound_inv hstep`. Case `b ≠ a₀`: reuse the
`hpiles` computation at `ForkDrainInduction.lean:245-250` and call `canRaise_of_raise_other`.
Case `b = a₀` (`d` below `c`): the raise removes the **top** `c`, so `d`'s top-ness, its
`below`/`chop` reads and its `pileOfTop d.twin` read are unchanged (use `pileOfTop_eq_some_iff`,
`Pile.mem_of_top`, `mem_faceUp_unique`, `lastOf_chop`). Then prove the `↔` (the backward
direction is the mirror; `CanRaise w d → CanRaise st d` may reuse `canRaise_of_raise_other`
in case `b ≠ a₀` and the same read analysis in case `b = a₀`).

### T2 — `SpecShift`, assembly route
```lean
theorem specShift {u z z' : State} {c d : Card}
    (hz : z.WF) (hstep : RaiseStepS z z' c) (hd : d ≠ c) (hdt : d ≠ c.twin) :
    CanRaiseS z d ↔ CanRaiseS z' d
```
Plan: eliminate `RaiseStepS` to `⟨z₀, hpath, hstep₀⟩`; slides preserve `CanRaiseS` (fibre-level)
and rungs; then `canRaiseS_split` on both sides; `nextUp` half by `nextUp_raise_ne` (proved);
`CanRaise` half by rank split `d.rank ≤ c.rank` → `canRaise_of_raise_high_fwd` /
`canRaise_of_raise_high`, else `canRaise_of_raise_above` (T1). You may take T1 as a hypothesis
if it is not yet proved: state `(habove : ∀ …, …) →` in front.

### T3 — `SpecShift`, independent route (hedge)
Same statement, proved **without** T1: via `freeCardS_sem` (`FreeOrbit.lean:1305`) — rebuild the
semantic triple for `d` at the landing state. The four reads are: holding (unchanged for `d ≠ c`),
`Parented`/`Bare` (unchanged, a raise removes a *top*), the hatch clause (`pileOfTop d.twin`,
changed only if `d.twin = c`, excluded), and "no hidden reveal" (guaranteed by the raise's own
guard `chop faceUp ≠ [] ∨ (hidden = [] ∧ rank = king)`).

### T4 — `RaiseSReorder`
```lean
theorem raiseS_reorder {s : State} {c : Card} (hc : CanRaiseS s c)
    {ws : List Card} {z : State} (h : RaiseSSeq s ws z) (hmem : c ∈ ws) :
    ∃ z', RaiseSSeq s (c :: ws.erase c) z'
```
Plan: three-phase canonical form.
* the steps that raise `c`'s cover commute forward — use `specShift` as a hypothesis
  `(hshift : ∀ …, CanRaiseS z d ↔ CanRaiseS z' d)` and `cover_seats` (proved);
* once the covers are gone, `c` and `c.twin` are plain tops, so their order is free —
  `twin_raise_square` (`ForkCriticalPair.lean:241`);
* the remainder replays because the rung vector and orbit agree — `freeCardS_orbit_rung`.
Induct on the word; `List.erase`/`List.Perm` bookkeeping at the end.

## What a good answer looks like
A `Temp/*.lean` file that `lake env lean` accepts with no `sorry`, ending in
`#print axioms <your theorem>` whose output is `[propext]` or `[propext, Quot.sound]`,
plus the exact statement you proved and a note on any hypothesis you had to carry.
