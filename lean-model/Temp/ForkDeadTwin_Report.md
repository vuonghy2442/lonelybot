# Temp/ForkDeadTwin — the dead-twin fork statement is FALSE

## Verdict (one line)

`hfork` is **not provable**: the both-vanilla arm of
`SpectrumCollapse.spectrum_pair_fork_or_both` is **realised** inside a
fork-free orbit, and the counterexample is closed in Lean
(`OneColourClosure.ForkDeadTwinBoard.fork_of_dead_twin_false`).

`Temp/ForkDeadTwin.lean`:

```lean
theorem fork_of_dead_twin_false :
    ¬ (∀ (s u v : State) (c : Card) (b : Base) (ws : List Card),
        s.WF → State.step s (Move.foundToTab c b) = some u →
        RaiseSSeqLicensed u ws v → (∀ d ∈ ws, d.suit ≠ c.suit) →
        c.twin ∈ ws → ¬ CanRaiseS v c → Fork s)
```

`lake env lean Temp/ForkDeadTwin.lean` → **EXIT=0**, no `sorry`, no
`Classical`, no `noncomputable`, no new `Prop` wrapper.  Every `#print
axioms` line is `[propext]` or `[propext, Quot.sound]` (full list in §7).

---

## 1. What *is* proved: the exact reduction

The intended `z`-state argument was completed (`dead_twin_z`), then fed to
`spectrum_pair_fork_or_both`.  The result is the honest dichotomy:

```lean
theorem dead_twin_z {s u v : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (htw : c.twin ∈ ws) :
    ∃ (pre post : List Card) (z : State),
      ws = pre ++ c.twin :: post ∧ c.twin ∉ post ∧
      RaiseSSeqLicensed u post z ∧ CanRaiseS z c ∧ CanRaiseS z c.twin
```

(Split at the **last** occurrence of `c.twin` in the word — the word is
reverse-chronological, so this is the first twin letter played.  `post` is
then the chronological prefix; `c`'s licence is carried over it by
`canRaiseS_step_of_rank_ne` / `SatDifferConfig.licence_lost_only_by_twin`,
which are exactly the freight-inert rows.  Both lemmas absorb the cargo
prefix, which is why the covering slide inside a letter cannot kill `c`
unless the letter is `c` or `c.twin`.)

```lean
theorem fork_of_dead_twin_or_both_vanilla {s u v : State} {c : Card} {b : Base}
    {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (htw : c.twin ∈ ws) (hdead : ¬ CanRaiseS v c) :
    Fork s ∨
      ∃ z', sameOrbitSetoid.r s z' ∧
        (∀ d, CanRaiseS z' d → d = c ∨ d = c.twin) ∧
        CanRaise z' c ∧ CanRaise z' c.twin
```

`hdead` is **unused in the second arm** — that is the obstruction.  Note the
both-vanilla arm is reached at a *drained* class-mate `z'`, not at `z`, so
there is no `twin_raise_square_both` at `z` to compare with the original
play: the original play raises `c.twin` after a cargo leg that *covers* `c`,
while the square compares two two-letter vanilla prefixes.  No square
argument connects the two.

---

## 2. The counterexample board

Every state below has the same stock (all remaining cards, in the fixed
`Card.universe` order), `waste = []`, `drawStep = 1`, and `p2 … p6` empty.

### Source `o0` (the pull source)

```
♥ = A..5   ♦ = A,2,3   ♠ = A..5   ♣ = A..4
p0 = [6♥]            p1 = [6♦, 5♣, 4♦]
```

### The play

| # | move | state | rungs (H,D,S,C) | P0 | P1 |
|---|------|-------|-----------------|----|----|
| 0 | — | `o0` | (5,3,5,4) | `[6♥]` | `[6♦,5♣,4♦]` |
| 1 | `foundToTab 5♠ (inr 6♥)` | `o2` | (5,3,4,4) | `[6♥,5♠]` | `[6♦,5♣,4♦]` |
| 2 | `tabToTab 4♦ (inr 5♠)` | `o7` | (5,3,4,4) | `[6♥,5♠,4♦]` | `[6♦,5♣]` |
| 3 | `tabToFound 5♣` | `o12` (endpoint `v`) | (5,3,4,5) | `[6♥,5♠,4♦]` | `[6♦]` |

* `o0.WF` is proved (`wfB`); the pull is `pull`, the cargo leg is
  `slide`/`slide_back` (`CargoLeg`, hence `CargoPath`), the raise is
  `raise5C`, and the licensed word is `play : RaiseSSeqLicensed o2 [5♣] o12`.
  `hno : ∀ d ∈ [5♣], d.suit ≠ 5♠.suit` and `twin_mem : (5♠).twin ∈ [5♣]`
  are proved (`(5♠).twin = 5♣`).
* At `o12`, `5♠` is covered by `4♦`; `4♦`'s only legal base is a black `5`,
  and `5♣` is on the foundation (`5♠` is directly below `4♦`), so `4♦`
  cannot move and `5♠` can never be exposed.  Hence

```lean
theorem o12_dead_cS5 : ¬ CanRaiseS o12 cS5
```

  (`canRaiseSB` decided on the concrete state; the cargo fibre of `o12` is
  `{o12, o14}` and both have spectrum `{4♦}`, so `5♠` is dead in the whole
  fibre).

So `s = o0`, `u = o2`, `v = o12`, `c = 5♠`, `b = inr 6♥`, `ws = [5♣]`
satisfy every hypothesis of `fork_of_dead_twin` — while `¬ Fork o0`.

### The orbit is fork-free

The reversible orbit of `o0` has exactly **15 states** (compact projection
*and* the full `valley_probe` model agree: 15 states, 0 fork witnesses).  In
Lean the list is `ORB = [o0, …, o14]`; `orbit_closed : ORB.all checkStep =
true` (a kernel `decide` over every candidate move of every state) and
`orbitForkFree : ORB.all noForkB = true`, turned into

```lean
theorem not_fork_o0 : ¬ Fork o0
```

via `InOrb_of_shuffle` (every reversible orbit-mate's state test lands in
`ORB`) and `noForkB_sound`.

Full orbit (spectrum = `CanRaiseS` spectrum of the cargo fibre):

| state | rungs | P0 | P1 | spectrum |
|-------|-------|----|----|----------|
| o0  | (5,3,5,4) | `[6♥]` | `[6♦,5♣,4♦]` | {4♦} |
| o1  | (5,4,5,4) | `[6♥]` | `[6♦,5♣]` | {5♣} |
| o2  | (5,3,4,4) | `[6♥,5♠]` | `[6♦,5♣,4♦]` | {4♦,5♠,5♣} |
| o3  | (5,3,5,4) | `[6♥,5♣,4♦]` | `[6♦]` | {4♦} |
| o4  | (5,4,5,5) | `[6♥]` | `[6♦]` | ∅ |
| **o5** | (5,4,4,4) | `[6♥,5♠]` | `[6♦,5♣]` | **{5♠,5♣}** |
| o6  | (5,4,5,4) | `[6♥,5♣]` | `[6♦]` | {5♣} |
| o7  | (5,3,4,4) | `[6♥,5♠,4♦]` | `[6♦,5♣]` | {4♦,5♠,5♣} |
| o8  | (5,3,4,4) | `[6♥,5♣,4♦]` | `[6♦,5♠]` | {4♦,5♠,5♣} |
| o9  | (5,4,4,5) | `[6♥,5♠]` | `[6♦]` | {5♠} |
| o10 | (5,4,4,5) | `[6♥]` | `[6♦,5♠]` | {5♠} |
| **o11** | (5,4,4,4) | `[6♥,5♣]` | `[6♦,5♠]` | **{5♠,5♣}** |
| o12 | (5,3,4,5) | `[6♥,5♠,4♦]` | `[6♦]` | {4♦} |
| o13 | (5,3,4,4) | `[6♥,5♣]` | `[6♦,5♠,4♦]` | {4♦,5♠,5♣} |
| o14 | (5,3,4,5) | `[6♥]` | `[6♦,5♠,4♦]` | {4♦} |

The only pair-shaped spectra are `{5♠,5♣}` at `o5` and `o11` — and at both
states **both** twins are vanilla-raisable, so the fork's block clause fails.

### The both-vanilla arm, realised

At `o5`:

```lean
theorem o5_canRaise_cS5 : CanRaise o5 cS5     -- 5♠ on 6♥, spade rung 4
theorem o5_canRaise_cC5 : CanRaise o5 cC5     -- 5♣ on 6♦, club rung 4
theorem o5_spectrum : ∀ d : Card, CanRaiseS o5 d → d = cS5 ∨ d = cC5
```

So `o5` is a class-mate of the pull source with the spectrum collapsed onto
`{c, c.twin}` and both twins vanilla — precisely the second arm of
`fork_of_dead_twin_or_both_vanilla`, and `¬ Fork o0`.  The dichotomy is
sharp, and the gap is not an artefact of the drain: it is where the theorem
dies.

---

## 3. Probe numbers for the both-vanilla arm

Model: the compact projection (`Temp/Search_lib.py`), validated against
`Temp/valley_probe.py` on the counterexample
(`Temp/ForkDeadTwin_fullcheck.py`: compact 15 states / 0 forks, full model
15 states / 0 forks).  A "dead-twin instance" is a pull edge
`s --foundToTab c b--> u` plus a licensed word from `u` whose letters all
avoid `c.suit`, raising `c.twin`, and killing `c` at the endpoint.  "Arm" =
the component contains a state whose cargo-fibre spectrum is exactly
`{c, c.twin}` and where both twins are directly vanilla-raisable.

Script: `Temp/ForkDeadTwin_sweep.py` (random: 5 seeds × 300 components,
`walk_hi` generator; exhaustive: `Search_enum.enum_boards`).

| family | components | states | forkless comps | pull edges | dead-twin instances | in forkless comps (= counterexamples) | realise the both-vanilla arm |
|---|---|---|---|---|---|---|---|
| random (full deck) | 1008 | 135,131 | 1001 | 211,616 | 584 | **542** | **542 / 542** |
| K3/tab4 (exhaustive, 40 s) | 258,090 | — | 258,090 | 289,409 | 0 | 0 | 0 |
| K4/tab4 + K3/tab5 (exhaustive) | 436,491 | — | 436,491 | (not counted) | 0 | 0 | 0 |

Reading:

* The both-vanilla arm is **not** a corner case: every one of the 542
  forkless dead-twin instances found realises it (542/542).  Option (i) of
  the brief is dead.
* The remaining 42 random instances sit in components that *do* carry a
  fork — those are the cases where `hfork` happens to hold, through an
  unrelated fork elsewhere in the class.
* The obstruction needs a rank with a legal "cover" slide and a foundation
  tall enough to pull from, which is why the exhaustive small-rank boards
  (`K ≤ 4`, `tab ≤ 5`) show none: they do have pulls (136,562 of 258,090
  K3/tab4 components), just no dead-twin instance.  The minimal witness
  above uses ranks 4–5 (fives and sixes) and 4 tableau cards.

---

## 4. Why each step of the intended proof fails / succeeds

| intended step | status |
|---|---|
| split `ws = pre ++ c.twin :: post`, `z` before the first twin letter | **proved** (`dead_twin_z`) |
| `CanRaiseS z c.twin` | **proved** (`canRaiseS_of_raiseSSeqLicensed_head`) |
| `CanRaiseS z c` (carry over the suit-avoiding, twin-free prefix) | **proved** (`canRaiseS_of_word_notMem`) |
| `spectrum_pair_fork_or_both` at `z` | **applied** |
| fork arm ⇒ `Fork s` | **proved** (`sameOrbitSetoid` transitivity) |
| both-vanilla arm ⇒ contradiction with `hdead` | **false** (`o5`), counterexample |
| `twin_raise_square_both` at `z` to compare plays | not applicable: the arm is at the drained `z'`, and the original play's `c.twin` letter is preceded by a cargo leg that covers `c` (a *non-vanilla* slide), which the square cannot reorder |

The precise obstruction: `CanRaiseS` is *cargo-span* liveness.  `c` is
alive at `u` (pulled), and a letter `d` with `d.suit ≠ c.suit`, `d ≠ c`,
`d ≠ c.twin` cannot kill it — but the letter `c.twin` can: its **cargo
prefix** may slide a cover onto `c` before the raise.  At the same time the
drain argument only guarantees that the *drained* spectrum collapses with
both twins vanilla; it says nothing about the cargo leg of the original
word, and the endpoint `v` is reached by that word, not by a drained play.

---

## 5. What survives (and why the pull case is not lost)

`pull_case_or_twin_dead` (`Temp/PullTwin.lean`) is still exhaustive; only
its third disjunct is no longer routed through a fork.  In the
counterexample, the pull case still holds by the *join* route: the
chronological play "raise `4♦`, then raise `5♣`" (word `[5♣, 4♦]`) is legal
from `o0` — both are vanilla at the states where they fire — and reaches
`o4` with rungs `(5,4,5,5)`, which dominates `v = o12`'s `(5,3,4,5)`.  Probe: `raiseS` rungs from `o0` are
`{(5,3,5,4), (5,4,5,4), (5,4,5,5)}`, and `v`'s rung vector is dominated.
This is the same pattern the earlier global probes saw (`dom_ok` = all
pairs, 2.7M pairs, 0 failures), i.e. `hfork` is not only false but
unnecessary.

---

## 6. Verification

Prerequisites (oleans in `.lake/build/lib/lean/Temp`):

```
lake env lean Temp/PullReplay.lean
lake env lean Temp/SpectrumCollapse.lean
lake env lean Temp/RaisesOrFork.lean
lake env lean Temp/SatDiffer_config.lean
lake env lean Temp/PullTwin.lean
```

Card:

```
lake env lean Temp/ForkDeadTwin.lean                    # EXIT=0
lake env lean -o .lake/build/lib/lean/Temp/ForkDeadTwin.olean Temp/ForkDeadTwin.lean
```

No `sorry`, no `Classical`, no `noncomputable`, no `native_decide`; the only
`decide`s are kernel reductions on concrete boards and on the finite
candidate-move lists of §3.5 of the card.

---

## 7. Exact axiom lines

`Temp/ForkDeadTwin_out.txt`, verbatim:

```
'OneColourClosure.exists_split_last' depends on axioms: [propext]
'OneColourClosure.dead_twin_z' depends on axioms: [propext, Quot.sound]
'OneColourClosure.orbit_source_landing' depends on axioms: [propext, Quot.sound]
'OneColourClosure.fork_of_dead_twin_or_both_vanilla' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.wfB_sound' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.orb_wfB' depends on axioms: [propext]
'OneColourClosure.ForkDeadTwinBoard.orb_wf' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.o0_wf' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.o2_wf' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.o5_wf' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.o7_wf' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.o12_wf' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.pull' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.slide' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.slide_back' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.leg' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.path' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.o2_live_cC5' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.raise5C' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.play' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.hno' depends on axioms: [propext]
'OneColourClosure.ForkDeadTwinBoard.twin_mem' depends on axioms: [propext]
'OneColourClosure.ForkDeadTwinBoard.o12_dead_cS5' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.o5_canRaise_cS5' depends on axioms: [propext]
'OneColourClosure.ForkDeadTwinBoard.o5_canRaise_cC5' depends on axioms: [propext]
'OneColourClosure.ForkDeadTwinBoard.o5_spectrum' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.pile_eq_of' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.stateEqB_refl' depends on axioms: [propext]
'OneColourClosure.ForkDeadTwinBoard.stateEqB_sound' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.InOrb_sound' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.InOrb_self' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.mem_allBases' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.mem_allMoves' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.checkStep_sound' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.orbit_closed' depends on axioms: [propext]
'OneColourClosure.ForkDeadTwinBoard.InOrb_of_shuffle' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.twinPairSpecB_complete' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.noForkB_sound' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.orbitForkFree' depends on axioms: [propext]
'OneColourClosure.ForkDeadTwinBoard.not_fork_o0' depends on axioms: [propext, Quot.sound]
'OneColourClosure.ForkDeadTwinBoard.fork_of_dead_twin_false' depends on axioms: [propext, Quot.sound]
```

---

## 8. What remains for `raises_or_fork` (blunt)

The fork-based pull route is dead: `hfork` is refuted in Lean, and the
both-vanilla arm is the norm rather than the exception (542/542 of the
forkless dead-twin instances), so `pull_case` must close through the
**rung-join** route (`pull_case_of_live` / `pull_case_noTwin` /
`RaiseSSeqLicensed` replay) — the one that actually works on this board —
and the campaign's `raises_or_fork` needs a pull-case join lemma, not a
fork lemma.
