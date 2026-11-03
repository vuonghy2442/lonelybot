# `Temp/SatDiffer_config.lean` — report

**Outcome: steps 1 and 2 are closed; step 3 is reduced to one precisely
stated conjunct, and the carry-on conjunct is shown to be unnecessary.**

`lake env lean Temp/SatDiffer_config.lean` exits 0 with zero `sorry`,
zero `Classical`, zero `noncomputable`, zero `native_decide`.  Every
theorem's axiom print is `[propext]` or `[propext, Quot.sound]`.

Nothing under `Orig2/` and no existing `Temp/` file was modified.  The
only new files are `Temp/SatDiffer_config.lean` and this report.  The
prerequisite olean for the imported `Temp.Drain_transport_rows` was
rebuilt with
`lake env lean -o .lake/build/lib/lean/Temp/Drain_transport_rows.olean Temp/Drain_transport_rows.lean`.

---

## 1. Job status

| step | theorem | status |
|---|---|---|
| 1 `licence_lost_only_by_twin` | `SatDifferConfig.licence_lost_only_by_twin` (+ contrapositive `licence_lost_only_by_twin'`) | **PROVED** |
| 1 leaf | `SatDifferConfig.freeCardS_fwd_of_rank_eq`, `canRaiseS_tabToFound_fwd_of_rank_eq`, `not_mem_pileOfTop_of_rank_eq` | **PROVED** |
| 2 `pulled_card_refounded` | `SatDifferConfig.pulled_card_refounded` | **PROVED** (strong form: `rungAt st σ ≤ rungAt W σ`) |
| 2 support | `exists_split_at_mem`, `FirstRise.mem_raise` | **PROVED** |
| 2b pull liveness | `nextUp_after_pull`, `canRaise_after_pull`, `canRaiseS_after_pull` | **PROVED** |
| 3 floor analysis | `canRaise_of_raise_low_fwd` | **PROVED** |
| 3 configuration | `satDifferForkWF_of_asymmetry` (from the 4-conjunct config) | **PROVED (assembly)** |
| 3 with carry-on | `satDifferForkWF_of_drainConfig` (from `DrainInvariant ∧ DrainRaisable`) | **PROVED (assembly)** |
| 3 existence of the config | — | **NOT CLOSED**; exact residual below |

---

## 2. Exact statements

### Step 1

```lean
theorem freeCardS_fwd_of_rank_eq {z z' : State} {e d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
    (hde : d ≠ e) (hdt : d.twin ≠ e) (hr : d.rank = e.rank) :
    freeCardS z d = true → freeCardS z' d = true

theorem canRaiseS_tabToFound_fwd_of_rank_eq {z z' : State} {e d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
    (hde : d ≠ e) (hdt : d.twin ≠ e) (hr : d.rank = e.rank) :
    CanRaiseS z d → CanRaiseS z' d

theorem licence_lost_only_by_twin {u u' : State} {d c : Card}
    (hu : u.WF) (hstep : OneColourClosure.RaiseStepS u u' d)
    (hr : d.rank = c.rank) (hdc : d ≠ c) (hdt : d ≠ c.twin) :
    CanRaiseS u c → CanRaiseS u' c

theorem licence_lost_only_by_twin' {u u' : State} {d c : Card}
    (hu : u.WF) (hstep : OneColourClosure.RaiseStepS u u' d)
    (hr : d.rank = c.rank) (hS : CanRaiseS u c) (hlost : ¬ CanRaiseS u' c) :
    d = c ∨ d = c.twin
```

### Step 2

```lean
theorem pulled_card_refounded {st W : State} {play : List Move} {c : Card} {b : Base}
    (hwf : st.WF) (hplay : ShufflePlayW st play W)
    (hmem : Move.foundToTab c b ∈ play)
    (hrung : rungAt st c.suit ≤ rungAt W c.suit) :
    Move.tabToFound c ∈ play
```

This is the brief's "net rung of `c.suit` is `≥`" read literally: the
end rung is compared with the rung at the play's **start**
(`rungAt st c.suit ≤ rungAt W c.suit`).  The proof splits on whether the
start already reads above `c.rank.toIdx`:

* if `rungAt st c.suit ≤ c.rank.toIdx`, the pull's pre-state reads
  `c.rank.toIdx + 1`, so the first rise already happens in the prefix —
  a `tabToFound c`;
* otherwise the start is above the pull's landing (`c.rank.toIdx`) and
  the end reading at least the start forces a later first rise — again
  a `tabToFound c`.

Both cases use `SatDifferCensus.firstRise_exists` /
`firstRise_of_rung_lt` and `FirstRise.mem_raise` (the crossing letter is
the unique `c.suit`-card of rank index `c.rank.toIdx`, i.e. `c`).

### Step 2b — the pull's landing is already a live configuration

```lean
theorem nextUp_after_pull {F A : State} {c : Card} {b : Base}
    (hF : F.WF) (hstep : State.step F (Move.foundToTab c b) = some A) :
    A.nextUp c = true

theorem canRaise_after_pull {...} : CanRaise A c
theorem canRaiseS_after_pull {...} : CanRaiseS A c
```

This pins the orientation of the plan's pair: the *pulled* card is
raisable at the landing, so at the later blocking state the raisable
member is the **twin** of the pulled card, not the pulled card itself.

### Step 3 — the floor-analysis row

```lean
theorem canRaise_of_raise_low_fwd {st w : State} {c d : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hcd : c ≠ d) (hrank : c.rank.toIdx < d.rank.toIdx)
    (h : CanRaise st d) : CanRaise w d
```

The mirror of `Drain.canRaise_of_raise_high_fwd` for a **lower**-rank
raised card: the raised pile cannot be `d`'s pile (two tops of one pile
would be the same card), and the foundation of `d`'s suit is untouched.
It kernel-checks the first half of the claim that a live card below the
pair can be raised without disturbing the pair's raisable member.

### Step 3 — the two assemblies

```lean
theorem satDifferForkWF_of_asymmetry
    (h : ∀ u v : State, u.WF → SSaturated u → SSaturated v →
      sameOrbitSetoid.r u v →
      (∃ σ : Suit, rungAt u σ ≠ rungAt v σ) →
      ∃ (w : State) (x : Card), sameOrbitSetoid.r u w ∧
        CanRaise w x ∧ CanRaiseS w x.twin ∧ ¬ CanRaise w x.twin ∧
        (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx)) :
    SatDifferForkWF

theorem satDifferForkWF_of_drainConfig
    (h : ∀ u v : State, ... →
      ∃ (w : State) (x : Card), sameOrbitSetoid.r u w ∧ w.WF ∧
        Drain.DrainInvariant w x ∧ Drain.DrainRaisable w x) :
    SatDifferForkWF
```

The first uses `DrainClose.fork_exists_of_asymmetry` (Orig2, already
unconditional); the second uses the brief's
`OneColourClosure.drain_phase_fork` from `Temp/Drain_transport_rows.lean`.

---

## 3. Axiom lines (verbatim)

```
'SatDifferConfig.not_mem_pileOfTop_of_rank_eq' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.freeCardS_fwd_of_rank_eq' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.canRaiseS_tabToFound_fwd_of_rank_eq' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.licence_lost_only_by_twin' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.licence_lost_only_by_twin'' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.exists_split_at_mem' depends on axioms: [propext]
'SatDifferConfig.FirstRise.mem_raise' depends on axioms: [propext]
'SatDifferConfig.pulled_card_refounded' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.canRaise_of_raise_low_fwd' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.nextUp_after_pull' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.canRaise_after_pull' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.canRaiseS_after_pull' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.satDifferForkWF_of_asymmetry' depends on axioms: [propext, Quot.sound]
'SatDifferConfig.satDifferForkWF_of_drainConfig' depends on axioms: [propext, Quot.sound]
```

---

## 4. How step 1 works (and what it does not say)

`CanRaiseS` splits as `nextUp ∧ freeCardS` (`canRaiseS_split`).  For a
same-rank raised card `e ≠ d ≠ d.twin` with `d.rank = e.rank`:

* `d.suit ≠ e.suit` (equal rank plus inequality of cards), so the
  foundation gate `nextUp d` is untouched;
* `freeCardS d` reads only `d`'s holding pile and `pileOfTop d.twin`.
  `d ∉ faceUp(pile of e)` and `d.twin ∉ faceUp(pile of e)` because a
  same-rank card cannot lie strictly below the pile top (a legal run's
  later card has strictly smaller rank).  Hence `d`'s holding pile is
  another pile and is literally unchanged, and if `pileOfTop d.twin`
  was `some q` then `q` is not the raised pile and stays `some q`.

The forward direction is all the licence transport needs.  Equality of
`freeCardS` can fail: a raise whose pile empties may *reveal* `d.twin`
from the hidden deck, turning `none` into `some` for
`pileOfTop d.twin`; that is monotone in the only position the Bool
reads, so it is harmless.

## 5. What step 3 still needs — the precise residual

Let `u v` be `WF`, `SSaturated`, same orbit, with differing rungs.  The
missing conjunct is exactly:

```lean
∃ (w : State) (x : Card),
  sameOrbitSetoid.r u w ∧
  CanRaise w x ∧ CanRaiseS w x.twin ∧ ¬ CanRaise w x.twin ∧
  (∀ c, CanRaiseS w c → x.rank.toIdx ≤ c.rank.toIdx)
```

This is the same statement `Orig2/Fork/Split/ForkBridge.lean:516` names
`Bridge.BottomAsymmetry`; `Bridge.satDifferForkWF_of_bottom_asymmetry`
already reduces `SatDifferForkWF` to it.  Steps 1 and 2 do not
manufacture it: step 2 says the pulled card is *re-founded* whenever the
suit's rung returns, but the plan needs the complementary case — the
suit's rung does **not** return — and then the twin-asymmetry and the
rank floor at the resulting blocking state.

Two clarifications the plan's wording needs:

* **`DrainRaisable` is not the residual.**  `DrainClose`
  (`Orig2/Fork/Split/ForkDrainClose.lean:766`) proves the drain phase
  unconditionally from `DrainInvariant` alone: a blocked live card is
  drained by sliding its cover onto the twin's pile, then raising it.
  `satDifferForkWF_of_asymmetry` therefore needs no carry-on conjunct.
  `satDifferForkWF_of_drainConfig` is included only to show the
  `Drain_transport_rows` route also closes *given* `DrainRaisable`.
* **The rank floor is the fragile conjunct.**  If it fails, the
  violating card is a live `d` with `d.rank.toIdx < x.rank.toIdx`.  Such
  a `d` is in a different suit from `x` (both are next-up), and it
  cannot be in `x`'s pile (`x` is a top), so raising `d` preserves
  `CanRaise x` (`canRaise_of_raise_low_fwd`, kernel-checked) and
  `CanRaiseS x.twin` (the same pile/run analysis, not separately
  formalized).  The one way it can break
  `¬ CanRaise x.twin` is if `d` is the card directly above `x.twin`
  (then `d.rank < x.twin.rank = x.rank`, consistent with the floor
  failure) and the raise exposes `x.twin` as a new top with a nonempty
  seat — at which point `x.twin` becomes raisable, the asymmetry at the
  pair is *destroyed* rather than turned into a fork in the same
  orientation.  So the floor cannot be recovered by a naive one-card
  drain; it needs a re-orientation argument (the exposed twin pair is
  then both-raisable, and the fork must be sought elsewhere in the
  class), which is exactly the open content of `BottomAsymmetry`.

## 6. Blunt summary

**`SatDifferForkWF` is now exactly one conjunct away: the class-mate
carrying `CanRaise w x ∧ CanRaiseS w x.twin ∧ ¬ CanRaise w x.twin` plus
the rank floor (`Bridge.BottomAsymmetry`); steps 1 and 2 are closed, and
the drain/carry-on half is already unconditional, so there is no
`DrainRaisable` residual.**
