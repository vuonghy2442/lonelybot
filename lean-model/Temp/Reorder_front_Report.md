# T4 (corrected) report — `raiseS_reorder_front` is **also false**

File: `Temp/Reorder_front_proof.lean`.  Compiles: **yes**
(`lake env lean Temp\Reorder_front_proof.lean`), no `sorry`, no `Classical`,
no `noncomputable`.

Build dependency (needed once):
`lake env lean -o .lake/build/lib/lean/Temp/SpecShift_sem.olean Temp/SpecShift_sem.lean`
(the file `import Temp.SpecShift_sem`).

## Headline

```lean
def RaiseSReorderFront : Prop :=
  ∀ {s : State} {c : Card}, s.WF → CanRaiseS s c →
    ∀ {ws : List Card} {z : State}, RaiseSSeq s ws z → c ∈ ws →
      ∃ z', RaiseSSeq s (ws.erase c ++ [c]) z'

theorem raiseSReorderFront_false : ¬ RaiseSReorderFront     -- [propext, Quot.sound]
```

So the word-convention fix is right, but the corrected statement still fails —
now in the *mirror* direction: raising `c` **first** founds the only remaining
seat of `c.twin`'s cover, so `c` may be forced to be raised **last**.

## The second probe state (`probeState`, proved `WF`)

    pile p0:  K♥            <- c, a bare king, raisableS now
    pile p1:  K♦  Q♠        <- c.twin = K♦, covered by Q♠
    found:    ♠↦A..J, ♥↦A..Q, ♦↦A..Q, ♣↦[]
    stock:    remaining 14 cards

Legal play (chronologically `K♦`, `Q♠`, `K♥`; word `[K♥, Q♠, K♦]`):

1. cargo: slide `Q♠` off `K♦` onto `K♥` (reversible slide, `CargoLeg` proved
   via `tabToTabR_iff_reversibleAtW`), then raise `K♦`;
2. raise `Q♠`;
3. raise `K♥`.

The front-reordered word is `[Q♠, K♦, K♥]` (chronologically `K♥` first).  After
`K♥` is founded:
* `Q♠` has **no seat at all** (`Q♠` can only sit on a red king: `K♥` is founded,
  `K♦` is beneath it), so `Q♠` stays on `K♦` in every cargo mate;
* hence `K♦` is never a pile top (`no_top_of_seat`), so the second raise can
  never fire.

Machine-checked pieces:
`probe_canRaiseS_KH`, `probe_raiseSeq` (the legal word),
`no_step_KD_after_KH` (the cover-seat invariant, using `Parented` orbit
invariance + `cover_seats` + `no_top_of_seat`),
`probe_not_raiseSeq_front` (the reordered word is illegal), and
`raiseSReorderFront_false`.

## What *is* closed (all unconditional — no `SpecShift` hypothesis)

`specShift_sem_fwd` is enough for the usable direction, so the earlier
false-`ShiftHyp` dependency is gone:

| theorem | statement |
|---|---|
| `raiseStepS_of_canRaiseS` | `CanRaiseS z c → ∃ z', RaiseStepS z z' c` |
| `raiseSSeq_snoc` | `RaiseSSeq s ws z → (∃ z', RaiseStepS z z' c) → ∃ z', RaiseSSeq s (c :: ws) z'` |
| `raiseSSeq_append` | `RaiseSSeq s w₁ u → RaiseSSeq u w₂ v → RaiseSSeq s (w₂ ++ w₁) v` |
| `raiseSSeq_wf` | `RaiseSSeq s ws z → s.WF → z.WF` |
| `canRaiseS_persist_fwd` | `RaiseSSeq s ws z → s.WF → x ∉ ws → x.twin ∉ ws → CanRaiseS s x → CanRaiseS z x` |
| `raiseSSeq_defer` | same hypotheses → `∃ z', RaiseSSeq s (x :: ws) z'` (x last) |
| `swap_c_first` | `s.WF → CanRaiseS s c → CanRaiseS s d → d ≠ c → d ≠ c.twin → ∃ s₂, RaiseStepS s s₂ c ∧ ∃ s₃, RaiseStepS s₂ s₃ d` |
| `swap_d_first` | mirror: `c ≠ d`, `c ≠ d.twin` ⟹ fire `d` then `c` |
| `raiseSSeq_front_two` | `s.WF → CanRaiseS s c → CanRaiseS s d → d ≠ c → d ≠ c.twin → ∃ z', RaiseSSeq s [d, c] z'` — the corrected-direction reordering for the two-card word |

Axioms: `[propext]`, except `raiseSSeq_wf`, `canRaiseS_persist_fwd`,
`raiseSSeq_defer`, `swap_c_first`, `swap_d_first`, `raiseSSeq_front_two`
which are `[propext, Quot.sound]` (they ride `step_wf` / `cargoPath_wf` /
`freeCardS_orbit_rung`).

## The exact remaining hypothesis (twin-free case)

§9 proves the reduction

```lean
theorem raiseS_reorder_front_of_block
    (hs : s.WF) (hc : CanRaiseS s c) (h : RaiseSSeq s ws z)
    (hmem : c ∈ ws) (ht : c.twin ∉ ws)
    (hblock : ∀ (A B : List Card) (u : State), ws = A ++ c :: B → c ∉ A →
      RaiseStepS s u c → ∃ v, RaiseSSeq u (A ++ B) v) :
    ∃ z', RaiseSSeq s (ws.erase c ++ [c]) z'
```

with the `List.erase` / split bookkeeping proved
(`exists_append_cons_of_mem`, `erase_append_cons_of_not_mem`).  So the whole
corrected theorem, *with `c.twin ∉ ws`*, is exactly the **block-replay**
obligation `hblock`: after `c` is raised, the block that followed it can still
be played.  This is where the difficulty sits: the block's state differs from
the original state because `c`'s own raise moved from the middle to the front,
and `RaiseSSeq` steps only supply the *weak* `nextUp ∧ pileOfTop` (not the
`CanRaise` shape), so `specShift_sem_fwd` cannot be applied to them step by
step as the planned route assumed.

## Notes for the parent

1. **Two refutations now**: `Temp/Reorder_proof.lean` (`¬ RaiseSReorder` — the
   head/“last” form, probe state `9♠` under `8♥`) and this file
   (`¬ RaiseSReorderFront` — the tail/“first” form, probe state `K♦` covered by
   `Q♠`).  Both obstructions are the same fact: the twin's cover has only the
   twin pair as seats, so the two twins cannot be freely ordered.
2. `specShift_sem_fwd` (forward only) is the right currency; the `↔` of
   `SpecShift` is false (same-suit successor, and my probe states).
3. `RaiseSSeq` steps are **weaker** than `CanRaiseS`: `State.step (tabToFound c)`
   needs only `nextUp c ∧ pileOfTop c = some a`, while `CanRaise` also needs
   `chop faceUp ≠ [] ∨ (hidden = [] ∧ rank = king)`.  A theorem about
   `RaiseSSeq` therefore cannot get `CanRaiseS` facts out of its steps; e.g.
   `raiseSSeq_front_two` needs `hd : CanRaiseS s d` explicitly.  If the
   intended game notion is "licensed raises only", redefine `RaiseStepS` with
   `CanRaise z₀ c` (or add it to the `RaiseSSeq.cons` premise) — then the
   state-transfer arguments have a chance.
