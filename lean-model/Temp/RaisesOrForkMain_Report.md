# `Temp/RaisesOrForkMain` — the path induction, assembled

Date: 2026-11-03.  Repo root `B:\code\lonelybot\lean-model`.
New file only: `Temp/RaisesOrForkMain.lean`.  Nothing under `Orig2/` and no
existing `Temp/*.lean` was modified.

---

## 0. Verdict

**The path induction is complete, conditional on one pull-case hypothesis.**
There is **no `sorry`**, no `Classical`, no `noncomputable`, and no new `Prop`
wrapper.  `lake env lean Temp/RaisesOrForkMain.lean` exits `0`; every axiom
line is `[propext]` / `[propext, Quot.sound]`.

Two corrections to the brief, both forced by the kernel:

1. **`hblockEnd` is not used and not assumed** (you confirmed it is false;
   the refutation board in `Temp/PullReplay_Counter.lean` matches the failure
   mode I had found: a buried `c` whose only seat is its twin dies when the
   twin is raised).  I deleted the conditional persistence lemma that depended
   on it.
2. **`hPull`'s `RungLe v u` cannot be right**: a licensed `raiseS` play only
   climbs rungs (`RungMono.rungAt_le`), so `RungLe v u` says the play is empty.
   The induction does **not need any `u`/`v` domination hypothesis at all**
   (the pull's landing is recovered from the play), so the `hPull` below has
   none — it is the sibling `pull_case_sorted_rungLe` shape plus the `∨ Fork s`
   arm, which is what the twin agent should prove.

`hspectrum` is carried to match the interface but is **not consumed** by the
induction: every case either lands in the play arm, or lifts an IH `Fork` along
the orbit.  The collapsed-spectrum producers are therefore not needed for the
assembly (they remain needed by other routes).

---

## 1. Verification

```
cd B:\code\lonelybot\lean-model
lake env lean Temp/RaisesOrForkMain.lean        # EXIT=0
```

Axiom output (verbatim):

```
'OneColourClosure.sameOrbit_of_revStep'   depends on axioms: [propext]
'OneColourClosure.sameOrbit_of_revStep''  depends on axioms: [propext]
'OneColourClosure.fork_of_sameOrbit'      depends on axioms: [propext]
'OneColourClosure.rungLe_of_rung_eq'      does not depend on any axioms
'OneColourClosure.replay_of_orbit_rung'   depends on axioms: [propext, Quot.sound]
'OneColourClosure.countP_erase_add'       depends on axioms: [propext, Quot.sound]
'OneColourClosure.pull_case_of_end_live'  depends on axioms: [propext, Quot.sound]
'OneColourClosure.pull_case_mem'          depends on axioms: [propext, Quot.sound]
'OneColourClosure.pull_case_noTwin'       depends on axioms: [propext, Quot.sound]
'OneColourClosure.raises_or_fork_play'    depends on axioms: [propext, Quot.sound]
'OneColourClosure.raises_or_fork_of'      depends on axioms: [propext, Quot.sound]
'OneColourClosure.fullJoinAtLeastOrFork_of_hPull' depends on axioms: [propext, Quot.sound]
```

Prerequisite oleans used (all fresh): `Temp/RungMono`, `Temp/PullRaiseId`,
`Temp/Obstruction`, `Temp/FrozenSuit`, `Temp/RaisesOrFork`, `Temp/BlockHousing`.

---

## 2. What is closed unconditionally

| piece | statement |
|---|---|
| base of the induction (`play = []`) | empty word at `s`; both `RungLe`s are reflexivity |
| **first letter a raise** (`tabToFound c`) | `CanRaise st c` from `reversibleAtW`; one-letter play `[c]` appended *behind* the IH word (`RaiseSSeqLicensed.append`); `RungLe st v` is free |
| **first letter a slide** (`tabToTab`) | slides keep every rung (`rungAt_tabToTab`), so the IH word is replayed from `st` by `replay_of_orbit_rung` |
| **first letter a draw** | draws keep every rung (`rungAt_draw`), so the same replay applies; no `nextUp`/`freeCardS` analysis is needed |
| `wasteToFound` / `wasteToTab` | impossible: `wasteToFound_not_reversibleAtW`, `wasteToTab_not_reversibleAtW` |
| **fork lift** | `Fork s1 → Fork st` along `sameOrbit_of_revStep'` |
| **pull, non-twin** | `pull_case_noTwin` (see below): fully unconditional |
| **pull, `c ∈ ws`** | `pull_case_mem`: hoist the existing `raise c`, cancel, endpoint rungs unchanged |
| **pull, given endpoint licence** | `pull_case_of_end_live`: append `→` hoist `→` cancel; endpoint is `v + e_c` |

The reusable engine is

```lean
theorem replay_of_orbit_rung {a b v : State} {ws : List Card}
    (ha : a.WF) (horb : sameOrbitSetoid.r a b)
    (hrung : ∀ σ, rungAt a σ = rungAt b σ) (h : RaiseSSeqLicensed b ws v) :
    ∃ v', RaiseSSeqLicensed a ws v' ∧
      (∀ σ, rungAt v σ = rungAt v' σ) ∧ sameOrbitSetoid.r v v'
```

— "a raiseS word replays at any orbit mate with the same rung vector".  At each
letter the licence is transported by `canRaiseS_orbit_rung`; the endpoints stay
in one orbit-rung class because the rung vector is fixed by the word
(`RaiseSSeqLicensed.rungAt_eq`).  This replaces both the slide/CargoPath
composition and the "draws are raise-irrelevant" special case.

The pull fragment that needs no in-flight input:

```lean
theorem pull_case_noTwin {s u v t : State} {c : Card} {b : Base} {ws : List Card}
    (hs : s.WF) (hpull : State.step s (Move.foundToTab c b) = some u)
    (hρ : RaiseSSeqLicensed u ws v)
    (hno : ∀ d ∈ ws, d.suit ≠ c.suit) (htwin : c.twin ∉ ws) (ht : RungLe t v) :
    ∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧
      RungLe s v' ∧ RungLe t v'
```

This is exactly `Temp/PullReplay.lean`'s `pull_case_sorted_rungLe`, re-derived
here from `pull_case_of_end_live` + `canRaiseS_of_word_notMem` (no new input).

---

## 3. The exact shapes I need

### 3.1 `hPull` — the single pull-case hypothesis

```lean
hPull : ∀ {s u t v : State} {c : Card} {b : Base} {ws : List Card},
  s.WF → State.step s (Move.foundToTab c b) = some u →
  RaiseSSeqLicensed u ws v → RungLe t v →
  (∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧ RungLe s v' ∧
    RungLe t v')
  ∨ Fork s
```

Notes for the twin agent:

* **No `RungLe` hypothesis connecting `u` and `v`.**  It is derivable from the
  play (`RungMono.rungAt_le hρ`), so a theorem proved with it instantiates by
  `fun ... _ ht => ...`.  The brief's `RungLe v u` is the opposite inequality
  and is false for a nonempty play.
* **The `∨ Fork s` arm is not optional** and is preserved.  It is the only
  surviving pull sub-case: `c.twin ∈ ws` while `c ∉ ws` (the case where the
  twin's raise kills `c`; see the counterexample board).
* The conclusion word is `playWord (sortByRank ws)`, matching
  `pull_case_sorted_rungLe`.  `RungLe s v'` is actually automatic from that
  play (`rungLe_of_raiseSSeqLicensed`) and is kept only so the successor
  theorem has the exact target shape.

### 3.2 `hspectrum` — carried, not consumed

```lean
hspectrum : ∀ {z : State} {x : Card}, z.WF → CanRaiseS z x → CanRaiseS z x.twin →
  Fork z ∨
    ∃ z', sameOrbitSetoid.r z z' ∧
      (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
      CanRaise z' x ∧ CanRaise z' x.twin
```

This is verbatim `SpectrumCollapse.spectrum_pair_fork_or_both`'s conclusion
(the corrected dichotomy: the blocked arm is already packaged as `Fork z`, and
the both-vanilla arm carries the collapsed spectrum).  The induction below does
not use it — if the interface is preferred without it, delete the argument.

---

## 4. The final conditional statement

```lean
theorem raises_or_fork_of
    (hPull : ∀ {s u t v : State} {c : Card} {b : Base} {ws : List Card},
      s.WF → State.step s (Move.foundToTab c b) = some u →
      RaiseSSeqLicensed u ws v → RungLe t v →
      (∃ v', RaiseSSeqLicensed s (playWord (sortByRank ws)) v' ∧ RungLe s v' ∧
        RungLe t v')
      ∨ Fork s)
    (hspectrum : ∀ {z : State} {x : Card}, z.WF → CanRaiseS z x → CanRaiseS z x.twin →
      Fork z ∨
        ∃ z', sameOrbitSetoid.r z z' ∧
          (∀ c, CanRaiseS z' c → c = x ∨ c = x.twin) ∧
          CanRaise z' x ∧ CanRaise z' x.twin)
    {s t : State} (hs : s.WF) (h : sameOrbitSetoid.r s t) :
    (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s
```

The unconditional path induction it rests on is

```lean
theorem raises_or_fork_play
    (hPull : …) {s t : State} {play : List Move}
    (hplay : ShufflePlayW s play t) (hs : s.WF) :
    (∃ ws v, RaiseSSeqLicensed s ws v ∧ RungLe s v ∧ RungLe t v) ∨ Fork s
```

and `raises_or_fork_of` is one line from it: `h : sameOrbitSetoid.r s t` is
`RevEqW t s`, whose second component is the witness shuffle `s ⇝ t`.

**Payoff (no residue):**

```lean
theorem fullJoinAtLeastOrFork_of_hPull (hPull : …) (hspectrum : …) :
    FullJoinAtLeastOrFork
```

— `w := v`, orbit by `RevEqW_symm (RaiseSSeqLicensed.revEqW …)`, rungs by
`Nat.max_le` (`fullJoinAtLeastOrFork_of_raises_or_fork`).

---

## 5. What is left once the two land

**One theorem:** `hPull` for the twin sub-case (`c.twin ∈ ws`, `c ∉ ws`), with
the `∨ Fork s` arm — then `raises_or_fork_of hPull hspectrum` is the
unconditional target, `fullJoinAtLeastOrFork_of_hPull` is
`FullJoinAtLeastOrFork`, and nothing else is missing.
