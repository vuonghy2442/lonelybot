# `Temp/PullTwin` — the pull case, twin included

Date: 2026-11-03.  Root `B:\code\lonelybot\lean-model`.
New files only: `Temp/PullTwin.lean`, `Temp/PullTwin_out.txt`,
`Temp/PullTwin_Report.md`.  Nothing under `Orig2/` and no existing
`Temp/*.lean` was modified.

**Target used (the `hPull` shape of `Temp/RaisesOrForkMain.lean`):**

```lean
theorem pull_case {s u t v : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) :
    (∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v')
      ∨ Fork s
```

The older brief's `hle : RungLe v u` is **not** used: it is the opposite
inequality (a licensed play only climbs), and the target above has no such
hypothesis.  The theorem below matches the sibling's interface exactly.

---

## 0. Verdict

**`pull_case` does not close unconditionally in this card.**  The endpoint-live
branch and the non-twin branch close; the remaining shape is isolated exactly:

```lean
c.twin ∈ ws  ∧  ¬ CanRaiseS v c
```

(the twin is raised and the pulled card dies).  The file proves the exhaustive
dichotomy `pull_case_or_twin_dead` and the target **from that one missing
input** (`pull_case_of_dead_twin_fork`).  The acceptance board is an instance
of that residual in which the `Fork s` arm *does* hold; it is checked twice,
with both consistent readings of the board.

`lake env lean Temp/PullTwin.lean` → `EXIT=0`.  No `sorry`, no `Classical`,
no `noncomputable`, no new `Prop` wrapper.  Every axiom line is `[propext]` or
`[propext, Quot.sound]`.

---

## 1. What closed

### 1.1 Case A — the endpoint still licenses `c`

```lean
theorem OneColourClosure.pull_case_of_live {s u t v : State} {c : Card}
    {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) (hcz : CanRaiseS v c) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v'
```

The play is `pull_case_of_end_live`; the rung comparisons are the pull's
ledger (`pull_rung_succ`: `rungAt s c.suit = rungAt u c.suit + 1`, equal
elsewhere) and monotonicity.  `RungLe s v'` is **unconditional** for any
licensed play, as expected.

### 1.2 Case B0 — a dead endpoint forces the twin into the word

```lean
theorem OneColourClosure.twin_mem_of_dead {u v : State} {ws : List Card}
    {c : Card} (hu : u.WF) (hρ : RaiseSSeqLicensed u ws v)
    (hc : CanRaiseS u c) (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (hdead : ¬ CanRaiseS v c) : c.twin ∈ ws
```

This is `canRaiseS_of_word_notMem` plus the pull's
`SatDifferConfig.canRaiseS_after_pull`.

### 1.3 The lock sub-case

```lean
theorem OneColourClosure.orbit_source_block {s u bnd : State} {c : Card}
    {b : Base} {low : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hlow : RaiseSSeqLicensed u (playWord low) bnd) :
    sameOrbitSetoid.r bnd s

theorem OneColourClosure.lock_contradiction {s u bnd : State} {c : Card}
    {b : Base} {low : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hlow : RaiseSSeqLicensed u (playWord low) bnd)
    (hnoLow : ∀ d ∈ playWord low, d.suit ≠ c.suit)
    (hnext : bnd.nextUp c = true) {a : Anchor}
    (htop : bnd.pileOfTop c = some a)
    (hbel : below c (bnd.piles a).faceUp = [])
    (hlk : (bnd.piles a).hidden ≠ [] ∨ c.rank ≠ Rank.king) : False
```

`FrozenSuit.commitLocked_rung_le` gives
`rungAt s c.suit ≤ rungAt bnd c.suit = c.rank`, while the pull gives
`rungAt s c.suit = c.rank + 1`.  **Caveat, stated precisely:** this is the
lock row only when `c` is still a pile top at the block end
(`htop : bnd.pileOfTop c = some a`).  `block_end_dead_dichotomy`'s third
disjunct only gives `below c = []`, not `htop`; if `c` is buried under a
nonempty run while `below c = []`, the frozen-suit bound does not apply
directly.  That refinement is part of the residual below.

### 1.4 Route 1, unconditional

```lean
theorem OneColourClosure.pull_case_noTwin {s u t v : State} {c : Card}
    {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) (htwin : c.twin ∉ ws) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v'
```

This is `Temp/PullReplay.lean`'s `pull_case_sorted_rungLe` in the `hPull`
shape.

### 1.5 The exhaustive dichotomy

```lean
theorem OneColourClosure.pull_case_or_twin_dead {s u t v : State} {c : Card}
    {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) :
    (∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v')
      ∨ Fork s ∨ (c.twin ∈ ws ∧ ¬ CanRaiseS v c)
```

and the target from the one missing input:

```lean
theorem OneColourClosure.pull_case_of_dead_twin_fork {s u t v : State}
    {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (hfork : c.twin ∈ ws → ¬ CanRaiseS v c → Fork s) :
    (∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v')
      ∨ Fork s
```

### 1.6 Deliverable order from the brief

| item | status |
|---|---|
| 1. `pull_case_of_live` (Case A) | **closed**, unconditional |
| 2. B0 (`c.twin ∈ ws` when `¬ CanRaiseS v c`) | **closed** (`twin_mem_of_dead`) |
| 3. B1 lock ⇒ contradiction | **closed only with `htop : bnd.pileOfTop c = some a`** (`lock_contradiction`); the buried form of the third disjunct is not covered |
| 3. B1 `CoveredAt ⇒ insert the cover ⇒ Case A` | **not done** — and it cannot close the stated target directly: inserting `raise y` changes the endpoint word to `playWord (sortByRank (ws ++ [y]))`, while the target fixes `playWord (sortByRank ws)`.  It would need a subsequent cancellation of `y` or a separate fork argument |
| 4. B2/B3 cascade and replay | **not closed in general**; the exhaustive dichotomy `pull_case_or_twin_dead` isolates it, and the acceptance board is handled explicitly (reading B via `Fork s`, reading C via Case A) |

---

## 2. The residual (exact Lean statement)

The missing input of `pull_case_of_dead_twin_fork` is

```lean
hfork : c.twin ∈ ws → ¬ CanRaiseS v c → Fork s
```

Equivalently, the single open sub-case of `pull_case` is

```lean
theorem pull_case_dead_twin_residual {s u t v : State} {c : Card}
    {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v) (ht : RungLe t v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit)
    (htw : c.twin ∈ ws) (hdead : ¬ CanRaiseS v c) :
    Fork s
```

Why the present library does not close it: take the state `z` at which the
`c.twin` letter fires.  `c` is still alive there (the kill happens inside that
letter's cargo path) and `c.twin` is S-live, so
`SpectrumCollapse.spectrum_pair_fork_or_both z c` splits into

* `Fork z` — which lifts to `Fork s` along the prefix play and the pull; or
* the **both-vanilla collapsed-spectrum** arm: a class-mate `z'` with
  `(∀ d, CanRaiseS z' d → d = c ∨ d = c.twin)` and both `c`, `c.twin`
  vanilla-raisable.

The second arm has no blocked twin, so `ForkWitness z' c` and
`ForkWitness z' c.twin` both fail.  Turning it into a fork needs a further
argument (or a different class-mate); the replay at `s` is not available there
either, because `¬ CanRaiseS s c.twin` is exactly the assumption of the
residual and the twin cannot be exposed at `s`: the only reversible slides
that can remove its cover need a same-rank/same-colour company below the
cover, which is `c` (on the foundation at `s`) or `c.twin` (the buried card
itself).

The other residual refinement is the buried form of the lock row noted in
§1.3 (`htop` absent).

---

## 3. The acceptance board

`Temp/PullReplay_Counter.lean`'s board is

```
♥ = A..4, ♦ = A..4, p0 = [6♣, 5♥, 4♠], p1 = [6♠, 5♦], c = 5♥, ws = [5♦]
```

Two consistent readings are kernel-checked.

### 3.1 Reading A — the literal board as a pull landing (`counter_board_literal`)

The pulled card is the cover `4♠`; the source has `♠ = A..4` and
`p0 = [6♣, 5♥]`.  Pulling `4♠` onto `5♥` produces **exactly the counter
board** (with `♠ = A..3`), and `ws = [5♦]` then raises `5♦`.  At the endpoint
the counter's `5♥` is dead (`vA_dead_H5`) — its twin `5♦` has left the tableau
and `4♠` cannot be cargo-moved.  Since `4♠.twin = 4♣ ∉ ws`, the non-twin route
applies:

```lean
theorem PullTwinBoard.counter_board_literal :
    ∃ v', RaiseSSeqLicensed sA (playWord (sortByRank [D5])) v' ∧
      RungLe sA v' ∧ RungLe uA v'
```

### 3.2 Reading B — the pulled card is `5♥`, the twin kills it (`counter_board_twin_kill`)

Source `sB`: `♥ = A..5`, `p0 = [6♣]`, `p1 = [6♠,5♦,4♠]`.  Pull `5♥` onto
`6♣`; the `5♦` letter's cargo path slides `4♠` onto `5♥` (the counter's
mechanism), then raises `5♦`.  At the endpoint `vB`:

```lean
theorem PullTwinBoard.vB_dead_H5   : ¬ CanRaiseS vB H5
theorem PullTwinBoard.sB_dead_D5   : ¬ CanRaiseS sB D5     -- replay fails
theorem PullTwinBoard.uB_not_vanilla_D5 : ¬ CanRaise uB D5 -- 4♠ not raisable
theorem PullTwinBoard.uB_spectrum :
    ∀ c : Card, (c = H5 ∨ c = D5) ↔ CanRaiseS uB c      -- spectrum = {5♥,5♦}
theorem PullTwinBoard.fork_sB      : Fork sB
theorem PullTwinBoard.counter_board_twin_kill :
    (∃ v', RaiseSSeqLicensed sB (playWord (sortByRank [D5])) v' ∧
      RungLe sB v' ∧ RungLe uB v') ∨ Fork sB
```

So on this reading the pull case still **succeeds**, but through the `Fork s`
arm, not through the replay: `5♦` is *not* a pile top at `sB` (it is buried
under `4♠`, with `5♥` founded), so `CanRaiseS sB 5♦` is kernel-false.  The
landing `uB` is the fork witness: its S-spectrum is exactly `{5♥, 5♦}` and
`5♦` is vanilla-blocked, because `c = 5♥` tops a pile there (the twin-top
disjunct) — exactly the configuration the counter records.

### 3.3 Reading C — the twin present and revivable (`counter_board_twin_replay`)

With `p1 = [6♠,5♦]` (no `4♠` above it) the twin is a pile top at the source:

```lean
theorem PullTwinBoard.sC_live_D5 : CanRaiseS sC D5
theorem PullTwinBoard.counter_board_twin_replay :
    ∃ v', RaiseSSeqLicensed sC (playWord (sortByRank [D5])) v' ∧
      RungLe sC v' ∧ RungLe uC v'
```

Here `c = 5♥` survives the endpoint, so Case A (`pull_case_of_live`) supplies
the play; this is the revivable-twin twin-present test.

**Status.**  All three readings compile, have `#print axioms` lines below,
and Reading B is the literal dead-`c` counter mechanism.  The replay route of
the brief (replay `ws` at `s` with `CanRaiseS s c.twin`) is not needed on
Reading C (Case A is stronger) and is *unavailable* on Reading B (the twin is
buried at `s`), which is why Reading B lands in the isolated residual and is
closed there by the fork arm.

**A correction to the brief's picture.**  The two requirements

* `5♦` is a pile top at the pull source `s`, and
* `c = 5♥` is dead at the endpoint `v`,

are incompatible for this card.  At `s`, `5♦` being a pile top means it is
*not* the company under a cover (a cover needs the same-rank same-colour card
directly below it, i.e. `5♥` or `5♦`).  At `u`, `c = 5♥` is a pile top, so it
cannot be the company either.  Hence no reversible cargo slide can place a
`4` on `5♥`, and `c` stays exposed; consequently `CanRaiseS v c` would still
hold, contradicting the second requirement.  Kernel-side, the literal dead
reading (`sB`) has `sB_dead_D5 : ¬ CanRaiseS sB 5♦`, while the revivable
reading (`sC`, `sC_live_D5`) has `c` still alive at `vC`.  This is why the
acceptance board cannot be closed by the replay in the dead case: the replay
premise is false exactly there, and the only remaining route is the `Fork s`
arm (which does hold).

---

## 4. Axiom lines (verbatim from `Temp/PullTwin_out.txt`)

```
'OneColourClosure.pull_rung_succ' depends on axioms: [propext, Quot.sound]
'OneColourClosure.pull_case_of_live' depends on axioms: [propext, Quot.sound]
'OneColourClosure.twin_mem_of_dead' depends on axioms: [propext, Quot.sound]
'OneColourClosure.orbit_source_block' depends on axioms: [propext, Quot.sound]
'OneColourClosure.lock_contradiction' depends on axioms: [propext, Quot.sound]
'OneColourClosure.pull_case_noTwin' depends on axioms: [propext, Quot.sound]
'OneColourClosure.pull_case_or_twin_dead' depends on axioms: [propext, Quot.sound]
'OneColourClosure.pull_case_of_dead_twin_fork' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.sA_wf' depends on axioms: [propext]
'PullTwinBoard.counter_board_literal' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.vA_dead_H5' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.sB_wf' depends on axioms: [propext]
'PullTwinBoard.pullB' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.slideB' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.playB' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.vB_dead_H5' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.sB_dead_D5' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.uB_not_vanilla_D5' depends on axioms: [propext]
'PullTwinBoard.uB_spectrum' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.fork_uB' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.fork_sB' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.counter_board_twin_kill' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.counter_board_twin_replay' depends on axioms: [propext, Quot.sound]
'PullTwinBoard.sC_live_D5' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, no `Classical.choice`, no `native_decide`.

---

## 5. Reproduce

```
cd B:\code\lonelybot\lean-model
lake env lean Temp/PullReplay.lean        # prerequisite olean
lake env lean Temp/SpectrumCollapse.lean  # (not imported by this card)
lake env lean Temp/PullTwin.lean          # EXIT=0
```

The card imports only `Temp.PullReplay`, `Temp.RungMono`, `Temp.FrozenSuit`
and `Orig2.Fork.Class.ForkRaiseReorderProof` (all oleans present).
