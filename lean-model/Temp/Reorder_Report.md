# T4 report — `RaiseSReorder` (and `SpecShift`) are **FALSE**

File: `Temp/Reorder_proof.lean` (import `Orig2.Fork.Class.ForkRaiseReorder`).
Compiles: **yes**, `lake env lean Temp/Reorder_proof.lean`, no `sorry`, no
`Classical`, no `noncomputable`.

## Headline

Two of the brief's named obligations are refuted, machine-checked, on one
concrete **well-formed** state:

| theorem | statement |
|---|---|
| `specShift_false` | `¬ SpecShift` |
| `shiftHyp_false` | `¬ ShiftHyp` (the shift bundle used by the plan) |
| `raiseSReorder_false` | `¬ RaiseSReorder` |

Axioms: `[propext]` for all three.

## The reason (structural, not an artifact of the encoding)

A raise removes the pile top and **exposes the card beneath it**.  Therefore

* a raise can *enable* another card's `CanRaiseS` — the backward half of
  `SpecShift` is false (the forward half may well be true);
* a card can be raisableS *only after* another card has been raised — hence
  the card that does the exposing cannot be postponed past it, and
  `RaiseSReorder` is false.

Note `RaiseSReorder`'s word convention: the **head is the last raise**, so
`c :: ws.erase c` asks for `c` to be raised **last**.  The refutation uses
c = "the card that must be raised first" and the word `[d, c]` where `d` is
buried under `c`.

## The probe state (`probeState`, proved `WF`)

Pile `p0` holds, bottom-first,

    10♦   9♠   8♥        (8♥ is the pile top)

foundations `♠ ↦ A..8`, `♥ ↦ A..7`, `♦ ↦ []`, `♣ ↦ []`, the other 34 cards in
the stock, `drawStep = 1`.  `probeState_WF` is proved (`[propext]`) — all 52
cards counted exactly once, runs legal, foundations prefixes.

Key facts (all machine-checked):

* `probe_no_tabToTab : ∀ x b, State.step probeState (tabToTab x b) = none`
  — `8♥` needs a black-9 pile top (`9♠` is buried, `9♣` is in the stock);
  `9♠` needs a red-10 top (only `10♦`, which is buried); `10♦` needs a black-J
  top (none).  Since only those three cards are held, **no cargo slide fires**.
* `cargoPath_eq_of_noLeg` ⟹ every `CargoPath probeState z` is trivial.
* `probe_not_canRaiseS_c9S : ¬ CanRaiseS probeState 9♠` (buried, no slide).
* `probe_canRaiseS_c8H : CanRaiseS probeState 8♥`.
* `probe_raiseSeq : RaiseSSeq probeState [9♠, 8♥] afterD`
  (chronologically: raise `8♥`, then `9♠`).
* `probe_canRaiseS_afterC_c9S : CanRaiseS afterC 9♠` — after `8♥` is raised,
  `9♠` is on top with `10♦` beneath, so it is legally raisable.
* `probe_not_raiseSeq_swapped : ¬ ∃ z', RaiseSSeq probeState [8♥, 9♠] z'`
  (the reordered word would have to raise `9♠` first, impossible).

Then
* `specShift_false`: `SpecShift` at `(z, z', c, d) = (probeState, afterC, 8♥,
  9♠)` has all side conditions (`z.WF`, `RaiseStepS`, `9♠ ≠ 8♥`,
  `9♠ ≠ 8♥.twin = 8♦`) but `CanRaiseS · 9♠` goes false → true.
* `raiseSReorder_false`: `hc = probe_canRaiseS_c8H`, `ws = [9♠, 8♥]`,
  `8♥ ∈ ws`, and `c8H :: [9♠, 8♥].erase 8♥ = [8♥, 9♠]`, whose word is illegal.

## What *is* proved (the sound local mechanisms)

All with the shift hypothesis carried explicitly, as the brief asked.
`ShiftHyp` is `SpecShift` without its unused `u` binder
(`shiftHyp_iff_specShift : ShiftHyp ↔ SpecShift`).

```
raiseStepS_of_canRaiseS : CanRaiseS z c → ∃ z', RaiseStepS z z' c
raiseSSeq_snoc         : RaiseSSeq s ws z → (∃ z', RaiseStepS z z' c) →
                         ∃ z', RaiseSSeq s (c :: ws) z'
raiseSSeq_append       : RaiseSSeq s w₁ u → RaiseSSeq u w₂ v →
                         RaiseSSeq s (w₂ ++ w₁) v
raiseSSeq_wf           : RaiseSSeq s ws z → s.WF → z.WF
canRaiseS_persist      : ShiftHyp → RaiseSSeq s ws z → s.WF → c ∉ ws →
                         c.twin ∉ ws → CanRaiseS s c → CanRaiseS z c
raiseSSeq_defer        : (as above) → ∃ z', RaiseSSeq s (c :: ws) z'
swap_of_ne_twin        : ShiftHyp → s.WF → CanRaiseS s c → CanRaiseS s d →
                         d ≠ c.twin → d.suit ≠ c.suit →
                         ∃ s₂, RaiseStepS s s₂ c ∧ ∃ s₃, RaiseStepS s₂ s₃ d
swap_of_ne_twin'       : mirror (d first), with c ≠ d.twin
```

Axioms: `[propext]`, except `raiseSSeq_wf` / `canRaiseS_persist` /
`raiseSSeq_defer` which are `[propext, Quot.sound]` (they go through
`step_wf`/`cargoPath_wf`).

## Notes / corrections to the brief

1. **`RaiseStepS` is strictly weaker than `CanRaiseS`.**  `State.step
   (tabToFound c)` only requires `nextUp c` and `pileOfTop c = some a`; the
   `CanRaise` license additionally requires `chop faceUp ≠ [] ∨ (hidden = [] ∧
   rank = king)`.  So a raise that flips a hidden card is a legal
   `RaiseStepS` but not a `CanRaiseS`.  Hence `RaiseSSeq` words allow
   "commit" raises that `CanRaiseS` does not license, and the plan's step
   `RaiseStepS ↔ CanRaiseS` does not go through.  (`raiseStepS_of_canRaiseS`
   is the true direction; the converse is false in general.)
2. `SpecShift` needs `z.WF` (it has it), but `raiseS_reorder` as stated carries
   no `s.WF`; a proof via `hshift` must add one — moot, since the statement is
   false.
3. The correct fragment of reordering that *is* available:
   `raiseSSeq_defer` — a card absent from the word (together with its twin)
   can always be appended at the end.  The twin exception is real: raising
   `c.twin` founds the only alternative seat of `c`'s cover, which is exactly
   the obstruction in the probe state (with `8♥` playing the cover role and
   `9♣` the twin-style seat).
