# ForklessHasTop — the rung top of a forkless class

Scratch lane. **READ-ONLY on `Orig2/`**; nothing promoted, nothing
committed. Zero `sorry`, zero `Classical.choice`, zero `native_decide`,
zero `axiom`.

Card: `Temp/ForklessTop_Main.lean` (compiled green).
Checks: `Temp/ForklessTop_Checks.lean` / `Temp/ForklessTop_Checks.log`
(main card and the Orig2 raise-only leaves; the `PinLocal`/`PinFork`
types are quoted from those independently compiled scratch cards).
Axiom battery: `Temp/ForklessTop_Main.log`.
Flat-fiber probe: `Temp/ForklessTop_flatprobe.py`.

---

## 0. Verdict

| item | status |
|---|---|
| `HasTopRung` / `ForklessHasTop` formalised exactly as in the brief | **compiled** |
| raise-only climb to a saturated same-orbit upper bound | **compiled, unconditional** |
| `ForklessHasTop` from `ForklessSatRungsAgree` (saturated class-mates have equal rungs) | **compiled** |
| `ForklessFlatNormalWF ⇒ ForklessHasTop` | **compiled** |
| `SatFlatFiberFork ⇒ ForklessHasTop` | **compiled** |
| `SatDifferForkWF ⇒ ForklessHasTop` | **compiled** |
| `ArmDichotomySW ⇒ ForklessHasTop` | **compiled** |
| unconditional `ForklessHasTop` | **not proved** |
| exact remaining input | **`SatFlatFiberFork` / `SatDifferForkWF` for forkless classes** |

The top construction itself is no longer the obstruction.  The
raise-only algorithm reaches a saturated state from any `WF` start, and
a saturated state is the top as soon as all saturated class-mates in a
forkless class agree on their rungs.  That agreement is the live
campaign residue `SatDifferForkWF`; the stronger flat-fiber invariant
`SatFlatFiberFork` / `ForklessFlatNormalWF` implies it
(`satDifferForkWF_of_satFlatFiberFork`).  The measured
fork census (`Temp/AS_top2.log`: random8 197/197, random10 96/96,
twinswap 69/69, greedy 94/94, core/t1 4/4) is exactly the statement
that this residue holds on the sampled forkless components.

No `Orig2/` file was touched.

---

## 1. The compiled definitions

```lean
namespace ForklessTop

def Forkless (u : State) : Prop :=
  ∀ F, sameOrbitSetoid.r u F → ¬ forkState F

def HasTopRung (u w : State) : Prop :=
  sameOrbitSetoid.r u w ∧
    ∀ x, sameOrbitSetoid.r u x → ∀ σ : Suit, rungAt x σ ≤ rungAt w σ

def ForklessHasTop : Prop :=
  ∀ u, u.WF → Forkless u → ∃ w, HasTopRung u w

def ForklessSatRungsAgree : Prop :=
  ∀ u v : State, u.WF → v.WF → Forkless u → sameOrbitSetoid.r u v →
    SSaturated u → SSaturated v → RungEq u v
```

`HasTopRung` and `ForklessHasTop` unfold definitionally to the brief's
statements:

```lean
HasTopRung u w =
  sameOrbitSetoid.r u w ∧
    ∀ x, sameOrbitSetoid.r u x → ∀ σ : Suit, rungAt x σ ≤ rungAt w σ

ForklessHasTop =
  ∀ u, u.WF →
    (∀ F, sameOrbitSetoid.r u F → ¬ forkState F) →
    ∃ w, sameOrbitSetoid.r u w ∧
      ∀ x, sameOrbitSetoid.r u x → ∀ σ, rungAt x σ ≤ rungAt w σ
```

---

## 2. Exact compiled types

From `Temp/ForklessTop_Checks.log` (the `Setoid.r` in the output is
`sameOrbitSetoid.r`):

```lean
ForklessTop.exists_armRaise_sameOrbit {F : State} {c : Card} (hF : F.WF)
    (hc : CanRaiseS F c) :
  ∃ A, ArmRaise F c A ∧ sameOrbitSetoid.r F A ∧ A.WF ∧
    ∀ σ : Suit, rungAt A σ =
      if σ = c.suit then rungAt F σ + 1 else rungAt F σ

ForklessTop.exists_live_of_not_ssaturated {st : State} (hwf : st.WF)
    (h : ¬ SSaturated st) : ∃ c, CanRaiseS st c

ForklessTop.exists_saturated_above (u : State) (hu : u.WF) :
  ∃ w, sameOrbitSetoid.r u w ∧ w.WF ∧ SSaturated w ∧
    ∀ σ : Suit, rungAt u σ ≤ rungAt w σ

ForklessTop.forkless_saturated_rungs_eq
    (h : ∀ u, u.WF → Forkless u →
      ∀ v, sameOrbitSetoid.r u v → SSaturated v → RungEq u v) :
  ForklessSatRungsAgree

ForklessTop.forkless_saturated_rungs_eq_explicit
    (h : ∀ u, u.WF →
      (∀ F, sameOrbitSetoid.r u F → ¬ forkState F) →
      ∀ v, sameOrbitSetoid.r u v → SSaturated v → RungEq u v) :
  ∀ u v, u.WF → v.WF →
    (∀ F, sameOrbitSetoid.r u F → ¬ forkState F) →
    sameOrbitSetoid.r u v → SSaturated u → SSaturated v → RungEq u v

ForklessTop.forklessHasTop_of_forklessSatRungsAgree
    (h : ForklessSatRungsAgree) : ForklessHasTop

ForklessTop.forklessHasTop_of_forkless_saturated_rungs_eq
    (h : ∀ u, u.WF → Forkless u →
      ∀ v, sameOrbitSetoid.r u v → SSaturated v → RungEq u v) :
  ForklessHasTop

ForklessTop.forklessHasTop_of_forkless_saturated_rungs_eq_explicit
    (h : ∀ u, u.WF →
      (∀ F, sameOrbitSetoid.r u F → ¬ forkState F) →
      ∀ v, sameOrbitSetoid.r u v → SSaturated v → RungEq u v) :
  ForklessHasTop

ForklessTop.forklessHasTop_of_forklessFlatNormal
    (h : ForklessFlatNormalWF) : ForklessHasTop

ForklessTop.forklessHasTop_of_forklessFlatNormal_expanded
    (h : ForklessFlatNormalWF) (u : State) :
  u.WF →
    (∀ F, sameOrbitSetoid.r u F → ¬ forkState F) →
      ∃ w, sameOrbitSetoid.r u w ∧
        ∀ x, sameOrbitSetoid.r u x → ∀ σ : Suit,
          rungAt x σ ≤ rungAt w σ

ForklessTop.forklessHasTop_of_satFlatFiberFork
    (h : SatFlatFiberFork) : ForklessHasTop

ForklessTop.forklessHasTop_of_satDifferForkWF
    (h : SatDifferForkWF) : ForklessHasTop

ForklessTop.forklessHasTop_of_armDichotomySW
    (h : ArmDichotomySW) : ForklessHasTop

ForklessTop.hasTopRung_ssaturated {w : State} (hw : w.WF)
    (htop : HasTopRung w w) : SSaturated w

ForklessTop.not_hasTopRung_self_of_not_ssaturated {w : State}
    (hw : w.WF) (h : ¬ SSaturated w) : ¬ HasTopRung w w

ForklessTop.balanced_stall_escapable {z : State} (hz : z.WF) {t : Suit}
    (_hbal : rungAt z t = rungAt z t.twin) (hstall : ¬ SSaturated z) :
  ∃ c, CanRaiseS z c

ForklessTop.balanced_stall_live_split {z : State} {x : Card} (hz : z.WF)
    (hlive : TwinLivePair z x) (hstall : ¬ SSaturated z) :
  (∃ c, CanRaiseS z c ∧ c ≠ x ∧ c ≠ x.twin) ∨
    (CanRaiseS z x ∧ CanRaiseS z x.twin)

ForklessTop.not_forklessFlatNormalWF_of_fiberSplit
    (h : ∃ u v : State, u.WF ∧ Forkless u ∧ sameOrbitSetoid.r u v ∧
      SSaturated u ∧ SSaturated v ∧ ¬ BareFlatEquiv u v ∧
      ∃ w, HasTopRung u w) :
  ¬ ForklessFlatNormalWF
```

The conditional balanced-lane leaves, compiled in `Orig2/Fork/Class/ForkRaiseOnly.lean`
and `Temp/PinLocal_Core.lean` / `Temp/PinFork_Core.lean`, are:

```lean
TwinJoin.RaiseOnlyData (s : State) (t : Suit) (c : Card) : Prop
TwinJoin.ArgminStepGameWF : Prop

TwinJoin.argminStepGameWF_of_raiseOnly
    (h : ∀ (s s' : State) (t : Suit) (c : Card),
      s.WF → s'.WF → sameOrbitSetoid.r s s' →
      rungAt s t.twin ≤ rungAt s t →
      rungAt s t ≤ rungAt s' t →
      rungAt s t.twin < rungAt s' t.twin →
      c.suit = t.twin → c.rank.toIdx = rungAt s t.twin →
      TwinJoin.RaiseOnlyData s t c) :
  TwinJoin.ArgminStepGameWF

TwinJoin.argmin_step_of_raiseOnly {s : State} {t : Suit} {c : Card}
    (hs : s.WF) (hdata : TwinJoin.RaiseOnlyData s t c)
    (hcsu : c.suit = t.twin) :
  ∃ s'', sameOrbitSetoid.r s s'' ∧
    rungAt s'' t = rungAt s t ∧
    rungAt s'' t.twin = rungAt s t.twin + 1

TwinJoin.PinLocal.balanced_push_to_low_target
    (st : State) (t : Suit) (r a : Nat) (hstwf : st.WF)
    (hbal : rungAt st t = rungAt st t.twin)
    (hr : rungAt st t = r)
    (hrle : r ≤ a + 1)
    (hpush : ∀ (z : State) (n : Nat),
      sameOrbitSetoid.r st z → z.WF →
      rungAt z t = rungAt z t.twin → rungAt z t = n → n < a + 1 →
      (∃ z', sameOrbitSetoid.r z z' ∧ z'.WF ∧
          rungAt z' t = rungAt z' t.twin ∧ rungAt z' t = n + 1) ∨
      (∃ F x, sameOrbitSetoid.r z F ∧ ForkWitness F x)) :
  (∃ z, sameOrbitSetoid.r st z ∧
      rungAt z t = rungAt z t.twin ∧ rungAt z t = a + 1) ∨
  (∃ F x, sameOrbitSetoid.r st F ∧ ForkWitness F x)

TwinJoin.PinLocal.lower_push_to_common_point
    (s z : State) (t : Suit) (B a r : Nat) (hs : s.WF)
    (hcls : sameOrbitSetoid.r s z)
    (hB : rungAt s t = B) (ha : rungAt s t.twin = a)
    (hbal : rungAt z t = rungAt z t.twin)
    (hr : rungAt z t = r)
    (har : a ≤ r)
    (hpush : ∀ (y : State) (m : Nat),
      sameOrbitSetoid.r s y → y.WF →
      rungAt y t = B → rungAt y t.twin = m → m < r →
      CanRaise y (Card.mk t.twin (FoundKit.Rk m)) ∨
      (∃ F x, sameOrbitSetoid.r y F ∧ ForkWitness F x)) :
  (∃ y, sameOrbitSetoid.r s y ∧
      rungAt y t = B ∧ rungAt y t.twin = r) ∨
  (∃ F x, sameOrbitSetoid.r s F ∧ ForkWitness F x)

TwinJoin.PinLocal.twin_pair_stack_or_fork
    {st : State} {t : Suit} {h : Nat} (hwf : st.WF) (hh13 : h < 13)
    (hH : rungAt st t = h) (hL : rungAt st t.twin = h)
    (hSH : CanRaiseS st (Card.mk t (FoundKit.Rk h)))
    (hSL : CanRaiseS st (Card.mk t.twin (FoundKit.Rk h)))
    (hlive : TwinLivePair st (Card.mk t (FoundKit.Rk h))) :
  (∃ v, sameOrbitSetoid.r st v ∧
      rungAt v t = h + 1 ∧ rungAt v t.twin = h + 1) ∨
  (∃ F x, sameOrbitSetoid.r st F ∧ ForkWitness F x)
```

`Temp/ArgminEq_Flash.lean` adds the push arm and the blocker pivot:

```lean
TwinJoin.twin_push_exists {F : State} {x : Card} (hwf : F.WF)
    (hx : CanRaise F x) (hy : CanRaise F x.twin) :
  ∃ G, sameOrbitSetoid.r F G ∧
    rungAt G x.suit = rungAt F x.suit + 1 ∧
    rungAt G x.twin.suit = rungAt F x.twin.suit + 1

TwinJoin.balanced_pivot_of_canRaiseS {s : State} {t : Suit} {c : Card}
    (hs : s.WF) (hc : c.suit = t.twin)
    (hcr : c.rank.toIdx = rungAt s t.twin) (hS : CanRaiseS s c) :
  TwinJoin.BalancedExpose s t c

TwinJoin.argmin_step_of_live_at_high {s mid : State} {t : Suit}
    {c : Card} {b : Nat} (hcls : sameOrbitSetoid.r s mid)
    (hwm : mid.WF) (hS : CanRaiseS mid c) (hc : c.suit = t.twin)
    (hH : rungAt mid t = b) :
  ∃ s'', sameOrbitSetoid.r s s'' ∧
    rungAt s'' t = b ∧ rungAt s'' t.twin = rungAt mid t.twin + 1
```

---

## 3. Proof architecture

### 3.1 A raise is a class move

`exists_armRaise_sameOrbit` restates the certified route:

* `CanRaiseS F c` is a cargo span `F → z` plus a vanilla raise at `z`
  (`Vocab.lean` §4, `canRaiseS = ∃ z, CargoPath F z ∧ CanRaise z c`);
* the cargo span is a flat path (`cargoPath_flatPath`), and
  `flatPath_shuffle` realizes it as a witness shuffle;
* `CanRaise z c` makes the raise letter reversible at `WF`
  (`DrainClose.reversibleAtW_tabToFound_of_canRaise`), hence
  `Drain.sameOrbit_of_step` gives `z ~ A`;
* `armRaise_rung` gives the one-coordinate increment.

The result is a same-orbit class-mate whose rung vector is the old one
plus one on `c.suit`, all other coordinates fixed.

### 3.2 The saturation frontier is decidable

`rankSatB k st` is the certified Bool probe for `RankSat k`
(`rankSatB_iff`, `Orig2/Substrate/CargoRaise.lean:880`).  At `k = 13` every card
has `rank.toIdx ≤ 13`, so

```lean
SSaturated st  ↔  rankSatB 13 st = true        (at WF)
```

(`ssaturated_of_rankSatB_true`).  In the other direction
`Drain.exists_of_all_false` extracts a live card from a `List.all`
failure without `Classical.choice`; `canRaiseSB_iff` converts the Bool
probe to `CanRaiseS`.  Hence:

```lean
ForklessTop.exists_live_of_not_ssaturated :
  st.WF → ¬ SSaturated st → ∃ c, CanRaiseS st c
```

This is the constructive discharge of the only place where one might
otherwise reach for classical logic.

### 3.3 The raise-only climb terminates

`exists_saturated_above` recurses on `52 - rungSum`:

* if `rankSatB 13 u = true`, `u` is already saturated;
* otherwise extract a live `c`, raise it to `A`, and
  `rungSum A = rungSum u + 1` (`rungSum_eq_of_rung_eq` + 
  `DrainClose.rungSum_raise`);
* `rungSum ≤ 52` at `WF` (`Drain.rungSum_le_52`) bounds the recursion.

The conclusion is exactly a saturated same-orbit upper bound of the
start.

### 3.4 From rung agreement to the top

`forklessHasTop_of_forklessSatRungsAgree`:

1. Saturate `u` to `w` (`exists_saturated_above`).
2. For any class-mate `x`, saturate `x` to `y`.
3. `w` and `y` are saturated class-mates of the same forkless class, so
   `ForklessSatRungsAgree` gives `RungEq w y`.
4. `x ≤ y` componentwise and `y = w` on every rung, hence `x ≤ w`.

No maximal-element search, no componentwise maximal vector, and no
flat-fiber input is needed beyond step 3.

### 3.5 The global invariants

Each compiled implication is a direct instance of step 3.4:

```lean
ForklessFlatNormalWF ⇒ ForklessSatRungsAgree
  -- saturated class-mates lie in one flat fiber; bareFlat_rung.

SatFlatFiberFork ⇒ ForklessSatRungsAgree
  -- split on the decidable Nat equality rungAt u σ = rungAt v σ;
  -- a mismatch is ¬ BareFlatEquiv, so SatFlatFiberFork yields a fork,
  -- contradicting forklessness.

SatDifferForkWF ⇒ ForklessSatRungsAgree
  -- forkless_rungs_agree_wf (Orig2/Fork/Class/CeilingBridge.lean).

ArmDichotomySW ⇒ ForklessHasTop
  -- via satDifferForkWF_of_armDichotomySW (Orig2/Fiber/SWDichotomy.lean).
```

---

## 4. The raise-only / balanced lane (the user's three ideas)

The brief's suggestion was to build the top by a raise-only or balanced
algorithm.  The implemented route keeps the **raise-only** half and
makes the balanced half optional:

### 4.1 RaiseOnlyData → ArgminStepGameWF

`Orig2/Fork/Class/ForkRaiseOnly.lean` proves the compiled bridge

```lean
TwinJoin.argminStepGameWF_of_raiseOnly :
  (∀ s s' t c, … → TwinJoin.RaiseOnlyData s t c) →
  TwinJoin.ArgminStepGameWF
```

and the local elim

```lean
TwinJoin.argmin_step_of_raiseOnly :
  s.WF → RaiseOnlyData s t c → c.suit = t.twin →
  ∃ s'', s ~ s'' ∧ rungAt s'' t = rungAt s t ∧
    rungAt s'' t.twin = rungAt s t.twin + 1
```

The local card `balanced_raiseOnly_escape` in the main file is exactly
this elim under the name used by the top lane.  It says: if you have a
prepared class-mate with the LOW card raisable and a HIGH-raise-only
ladder, the LOW coordinate climbs one while HIGH stays frozen.

### 4.2 Balanced crossing and the common point

`Temp/PinLocal_Core.lean` compiles:

* `balanced_prefix_of_le_ge` (`Temp/PinMetric_Dist.lean`) — the
  balanced crossing: a witness play whose endpoints straddle a level
  has a common-point prefix at that level;
* `lower_push_to_common_point` — from `(HIGH,LOW) = (B,a)` and a
  balanced class-mate at level `r ≥ a`, each level below `r` either
  supplies the LOW license at fixed HIGH or a fork; hence `(B,r)` or a
  fork;
* `balanced_push_to_low_target` — from a balanced level `r ≤ a+1`,
  each level either pushes the pair to `n+1` or a fork; hence the
  balanced level `a+1` or a fork;
* `twin_pair_stack_or_fork` — at an exact twin live pair with both
  twins S-live, either both rungs push by one, or a `ForkWitness`
  exists.

These are **conditional** leaves: their `hpush` / `hclimb` hypotheses
are exactly the per-level stall case.  They are not used in the top
construction below.

### 4.3 Where the construction can stall — exactly

There are two different "stalls", and only one is mathematical:

* **Raise-only stall.**  The raise-only climb cannot move iff
  `SSaturated st`.  This is a real terminal state, not a dead end for
  the top: it is the state we are trying to reach.  At `WF` it is
  decidable (`rankSatB 13`), and
  `exists_live_of_not_ssaturated` turns every non-stall into an actual
  live card.  There is no "stall with no raise" other than saturation.

* **Balanced stall.**  At a balanced state with both twins buried,
  neither twin is vanilla- or S-raisable.  This is *not* a fork:
  measured `bothblocked_noS` is 176/984 core and 1506/13923 random,
  with no fork site (`Temp/ArgminEq_Report.md` §6).  It is escaped by
  an other-colour raise (the measured first mover is always an
  other-colour `tabToFound`) or by a different balanced level.  In the
  forkless/top setting, the balanced state is either saturated (then it
  is already a candidate top) or `¬ SSaturated`, and
  `balanced_stall_escapable` produces *some* S-live card, which may be
  off the chosen twin pair.  The compiled split
  `balanced_stall_live_split` makes the dichotomy exact: under an exact
  `TwinLivePair`, a non-saturated state either has a live card outside
  the pair (the other-colour escape) or both twins are S-live (the
  `twin_pair_stack_or_fork` push/fork case).  There is no third stall.

The top proof deliberately does not insist on keeping a chosen pair
balanced: it raises whatever card is S-live.  This is why the balanced
dead stall does not block `ForklessHasTop`; it only blocks a
*synchronized* climb that refuses off-pair raises.  If one wants the
synchronized climb, the exact missing input is the per-level
`RaiseOnlyData` / `hpush` datum, and the compiled conditional lemmas
above reduce it to `ArgminStepGameWF`.

---

## 5. Strength and dependencies

| hypothesis | `⇒ ForklessHasTop` | converse compiled? | note |
|---|---|---|---|
| `ForklessSatRungsAgree` | **yes** (`forklessHasTop_of_forklessSatRungsAgree`) | no | exact consumed input |
| `SatDifferForkWF` | **yes** (`forklessHasTop_of_satDifferForkWF`) | no | via `forkless_rungs_agree_wf` |
| `SatFlatFiberFork` | **yes** (`forklessHasTop_of_satFlatFiberFork`) | no | via decidable rung split |
| `ForklessFlatNormalWF` | **yes** (`forklessHasTop_of_forklessFlatNormal`) | no | via `bareFlat_rung` |
| `ArmDichotomySW` | **yes** (`forklessHasTop_of_armDichotomySW`) | no | via `satDifferForkWF_of_armDichotomySW` |

### `SatFlatFiberFork` vs `ForklessFlatNormalWF`

They are the fork/forkless contrapositive pair:

```lean
SatFlatFiberFork :
  ∀ u v, u.WF → SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    ¬ BareFlatEquiv u v →
      ∃ F x, sameOrbitSetoid.r u F ∧ ForkWitness F x

ForklessFlatNormalWF :
  ∀ u v, u.WF → SSaturated u → SSaturated v → sameOrbitSetoid.r u v →
    (∀ F, sameOrbitSetoid.r u F → ¬ forkState F) → BareFlatEquiv u v
```

The two-way equivalence is classical in the direction that has to
decide `BareFlatEquiv`; the compiled consumers only use the constructive
forkless projections above.  No `Classical.choice` is spent on it.

### Are they equivalent to `ForklessHasTop`, or strictly stronger?

As formal statements they are **strictly stronger** as inputs, in the
following precise sense:

* both imply `ForklessHasTop` (compiled above);
* neither is implied by `ForklessHasTop` in the compiled development.
  `ForklessHasTop` is a statement about the four rung coordinates; the
  flat-normal statement additionally asserts `BareFlatEquiv` of
  saturated class-mates, i.e. flat-fiber connectivity.

This is a statement about the compiled dependency graph, not a
meta-theoretic non-implication: no formal countermodel is constructed
here.  The gap is exactly the fiber-connectivity content.

The conditional witness

```lean
ForklessTop.not_forklessFlatNormalWF_of_fiberSplit :
  (∃ u v, u.WF ∧ Forkless u ∧ u ~ v ∧ SSaturated u ∧ SSaturated v ∧
      ¬ BareFlatEquiv u v ∧ ∃ w, HasTopRung u w) →
  ¬ ForklessFlatNormalWF
```

shows exactly what the extra strength is: a forkless class with a rung
top whose saturated class-mates sit in different flat fibers refutes
`ForklessFlatNormalWF` while `ForklessHasTop` can still hold.  Whether
the card model contains such a split is the open flat-fiber rigidity
question (`SatFlatFiberFork`).  A 200-board full-model probe with draws
(`Temp/ForklessTop_flatprobe.py`, cap 1200) found no such forkless
component, so on the measured model the two may coincide; the formal
one-way implication is all that is compiled.

`SatDifferForkWF` is likewise strictly stronger than `ForklessHasTop`:
it asserts rung equality of *all* saturated class-mates, while the top
statement only asks for one dominating rung vector.

---

## 6. Axiom checks

All rows from `Temp/ForklessTop_Main.log`.  The strongest head is
`[propext, Quot.sound]`; several pure-logic rows are `[propext]`.
There is no `sorryAx` and no `Classical.choice`.

```text
'ForklessTop.wf_of_sameOrbit' depends on axioms: [propext, Quot.sound]
'ForklessTop.exists_armRaise_sameOrbit' depends on axioms: [propext, Quot.sound]
'ForklessTop.rungSum_eq_of_rung_eq' depends on axioms: [propext, Quot.sound]
'ForklessTop.ssaturated_of_rankSatB_true' depends on axioms: [propext, Quot.sound]
'ForklessTop.exists_live_of_rankSatB_false' depends on axioms: [propext, Quot.sound]
'ForklessTop.exists_live_of_not_ssaturated' depends on axioms: [propext, Quot.sound]
'ForklessTop.exists_saturated_above' depends on axioms: [propext, Quot.sound]
'ForklessTop.forkless_saturated_rungs_eq' depends on axioms: [propext]
'ForklessTop.forkless_saturated_rungs_eq_explicit' depends on axioms: [propext]
'ForklessTop.forklessSatRungsAgree_of_satDifferForkWF' depends on axioms: [propext]
'ForklessTop.forklessSatRungsAgree_of_satFlatFiberFork' depends on axioms: [propext, Quot.sound]
'ForklessTop.forklessSatRungsAgree_of_forklessFlatNormal' depends on axioms: [propext, Quot.sound]
'ForklessTop.forklessHasTop_of_forklessSatRungsAgree' depends on axioms: [propext, Quot.sound]
'ForklessTop.forklessHasTop_of_forkless_saturated_rungs_eq' depends on axioms: [propext, Quot.sound]
'ForklessTop.forklessHasTop_of_forkless_saturated_rungs_eq_explicit' depends on axioms: [propext, Quot.sound]
'ForklessTop.forklessHasTop_of_forklessFlatNormal' depends on axioms: [propext, Quot.sound]
'ForklessTop.forklessHasTop_of_forklessFlatNormal_expanded' depends on axioms: [propext, Quot.sound]
'ForklessTop.forklessHasTop_of_satFlatFiberFork' depends on axioms: [propext, Quot.sound]
'ForklessTop.forklessHasTop_of_satDifferForkWF' depends on axioms: [propext, Quot.sound]
'ForklessTop.forklessHasTop_of_armDichotomySW' depends on axioms: [propext, Quot.sound]
'ForklessTop.hasTopRung_ssaturated' depends on axioms: [propext, Quot.sound]
'ForklessTop.not_hasTopRung_self_of_not_ssaturated' depends on axioms: [propext, Quot.sound]
'ForklessTop.balanced_stall_escapable' depends on axioms: [propext, Quot.sound]
'ForklessTop.balanced_stall_live_split' depends on axioms: [propext, Quot.sound]
'ForklessTop.not_forklessFlatNormalWF_of_fiberSplit' depends on axioms: [propext]
'ForklessTop.balanced_raiseOnly_escape' depends on axioms: [propext, Quot.sound]
'ForklessTop.argminStepGameWF_of_raiseOnly' depends on axioms: [propext, Quot.sound]
```

The external conditional leaves are also clean:

```text
TwinJoin.PinLocal.balanced_push_to_low_target        [propext, Quot.sound]
TwinJoin.PinLocal.lower_push_to_common_point         [propext, Quot.sound]
TwinJoin.PinLocal.twin_pair_stack_or_fork            [propext, Quot.sound]
TwinJoin.argminStepGameWF_of_raiseOnly               [propext, Quot.sound]
TwinJoin.twin_push_exists                            [propext, Quot.sound]
TwinJoin.balanced_pivot_of_canRaiseS                 [propext, Quot.sound]
```

---

## 7. The precise remaining input

Everything in `ForklessTop_Main.lean` is unconditional except the one
named residue:

> **`SatFlatFiberFork`** (or its forkless form
> `ForklessFlatNormalWF`; either implies the `WF`-gated rung residue
> `SatDifferForkWF`): in a forkless class, two saturated class-mates
> have equal rungs; at the flat vertex, two saturated class-mates in
> different flat fibers force a fork.

Equivalently, prove

```lean
ForklessSatRungsAgree :
  ∀ u v, u.WF → v.WF → Forkless u → sameOrbitSetoid.r u v →
    SSaturated u → SSaturated v → RungEq u v
```

The top construction then closes with
`forklessHasTop_of_forklessSatRungsAgree`, with no further input.

The on-record routes to discharge the residue are the non-comparability
lane (`Orig2/Fork/Class/ForkNonComp.lean`: `NonComparability`, `FrontierPrice`,
`nc_of_frontierPrice`) and the twin-cap / frontier-price refinements;
`Orig2/Fiber/SWDichotomy.lean` already reduces `SatDifferForkWF` to the flat
invariant `SatFlatFiberFork`.  None of those lanes is used in the
compiled top proof: they are the next attack surface, not an input the
top construction can avoid.

The measured fork census is the positive side: every sampled forkless
component has exactly the top vector the theorem predicts.  The
raise-only climb reproduces the top once the residue supplies the
uniqueness of its rung vector.

---

## 8. Files and reproduction

```powershell
cd B:\code\lonelybot\lean-model
lake env lean Temp\ForklessTop_Main.lean          # green, battery at tail
lake env lean Temp\ForklessTop_Checks.lean        # exact types of main + conditional leaves
python Temp\ForklessTop_flatprobe.py              # flat-fiber strictness probe (200 boards)
```

| file | role |
|---|---|
| `Temp/ForklessTop_Main.lean` | the compiled card (definitions, raise-only climb, top reduction, conditional corollaries) |
| `Temp/ForklessTop_Main.log` | axiom battery for the main card |
| `Temp/ForklessTop_Checks.lean` | exact `#check` types of the main card and the balanced/raise-only leaves |
| `Temp/ForklessTop_Checks.log` | the type log |
| `Temp/ForklessTop_flatprobe.py` | full-model flat-fiber search (draws included) |
| `Temp/ForklessTop_Report.md` | this report |

No `Orig2/` file was touched; no commit was made.  Nothing is promoted.
