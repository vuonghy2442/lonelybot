import Orig2.Fork.Class.ForkRaiseReorder

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Temp/SpecShift_proof — T2 (`SpecShift`), assembly route

## Headline finding

`SpecShift` as stated in the card (`d ≠ c`, `d ≠ c.twin` only) is **FALSE**:
a raise `tabToFound c` can *create* a raisableS card.  Two mechanisms,
both produced by the plain `State.step` (which does not require the raise
to be reversible, unlike `reversibleAtW`):

1. **reveal**: `c` is the only face-up card of its pile (so the raise is a
   commit) — the hidden head `d` is flipped onto `faceUp`, so `d` becomes
   held and `freeCardS d` flips `false → true`;
2. **uncovering**: `d` sits directly below `c` in the same pile — the raise
   deletes `c`, so `d` becomes the pile top, and the `run = []` disjunct of
   `freeCardS`'s hatch clause frees it.

Mechanism 1 is machine-checked below (`not_SpecShift`, and again with
`d.suit ≠ c.suit` added in `not_specShift_with_suit`); mechanism 2 is
machine-checked in §6 (`not_SpecShift_reversible`, where the raise is
undoable).  Mechanism 2 also refutes the card's `RaiseAbove`
(`CanRaise st d ↔ CanRaise w d` at `c.rank < d.rank`): there the forward
direction `CanRaise st d → CanRaise w d` fails, because the raise uncovers
`d`.  The *one-way* rows `canRaise_of_raise_high_fwd` /
`canRaise_of_raise_high` survive because they carry
`pileHolding d = some b`.

## What is proved here

* `specShift_nextUp` — the `nextUp` half, unconditional at the `CanRaiseS`
  level (needs `d.suit ≠ c.suit`, which `d ≠ c` does **not** imply).
* `specShift` — the repaired shift theorem: same statement, with the exact
  extra hypothesis that `d` and `d.twin` are **not in `c`'s pile** (the
  hypothesis that fails in both counterexamples, and the only content the
  `CanRaiseS`-level statement needs beyond `d.suit ≠ c.suit`).  No rank
  split and no `RaiseAbove` hypothesis is used.
* `not_SpecShift` / `not_specShift_with_suit` — kernel-checked refutations of
  the card's literal obligation; `not_RaiseAbove` refutes obligation 2a.
-/

namespace OneColourClosure

/-! ## §0. The retired `↔` forms (declared HERE, not in the card)

These are the *false* statements that the card used to carry as obligations.
They live in this refutation file so that `Orig2` keeps only the true forward
forms; the theorems below are the kernel-checked refutations of these exact
statements. -/

/-- The retired `RaiseAbove` `↔` form.  **FALSE** (`not_RaiseAbove`). -/
def RaiseAbove : Prop :=
  ∀ {st w : State} {c d : Card},
    st.WF → State.step st (Move.tabToFound c) = some w →
    c.rank.toIdx < d.rank.toIdx → (CanRaise st d ↔ CanRaise w d)

/-- The retired `SpecShift` `↔` form.  **FALSE** (`not_SpecShift`,
`not_SpecShift_reversible`). -/
def SpecShift : Prop :=
  ∀ {u z z' : State} {c d : Card},
    z.WF →
    RaiseStepS z z' c →
    d ≠ c →
    d ≠ c.twin →
    (CanRaiseS z d ↔ CanRaiseS z' d)

/-! ## §1. Congruence kit for `freeCardS`

`freeCardS` reads exactly three things: the pile holding `c`, that pile's
contents, and `pileOfTop c.twin`.  The three lemmas below let a pile-local
argument be replayed on the probe. -/

/-- `freeCardS` is determined by the holding pile, the contents of that pile,
and the top-status of the twin. -/
theorem freeCardS_congr {st w : State} {c : Card}
    (hhold : w.pileHolding c = st.pileHolding c)
    (hpile : ∀ b, st.pileHolding c = some b → w.piles b = st.piles b)
    (htwin : w.pileOfTop c.twin = st.pileOfTop c.twin) :
    freeCardS w c = freeCardS st c := by
  cases h : st.pileHolding c with
  | none =>
      have hw : w.pileHolding c = none := by rw [hhold, h]
      simp only [freeCardS, h, hw]
  | some b =>
      have hw : w.pileHolding c = some b := by rw [hhold, h]
      simp only [freeCardS, h, hw, hpile b h, htwin]

/-- Run removal cannot expose a card that was neither hidden nor face up. -/
theorem notMem_afterRunRemoved_faceUp {p : Pile} {x : Card}
    (hH : x ∉ p.hidden) (hF : x ∉ p.faceUp) :
    x ∉ (Pile.afterRunRemoved p (chop p.faceUp)).faceUp := by
  intro hm
  rcases mem_afterRunRemoved_faceUp_zone (p := p) (pre := chop p.faceUp) hm with h | h
  · exact hF (chop_mem h)
  · exact hH h

/-- The `pileHolding` search is unchanged when two states agree off one pile
and the queried card is not face up in that pile on either side. -/
theorem pileHolding_eq_of_piles {st w : State} {a₀ : Anchor} {d : Card}
    (hpiles : ∀ a, a ≠ a₀ → w.piles a = st.piles a)
    (hst : d ∉ (st.piles a₀).faceUp) (hw : d ∉ (w.piles a₀).faceUp) :
    w.pileHolding d = st.pileHolding d := by
  unfold State.pileHolding
  refine firstWhere_congr (α := Anchor) ?_ Anchor.all
  intro a
  by_cases ha : a = a₀
  · rw [ha]
    rw [decide_eq_false_iff_not.mpr hw, decide_eq_false_iff_not.mpr hst]
  · rw [hpiles a ha]

/-- The `pileOfTop` search is unchanged when two states agree off one pile and
the queried card is not face up in that pile on either side. -/
theorem pileOfTop_eq_of_piles {st w : State} {a₀ : Anchor} {z : Card}
    (hpiles : ∀ a, a ≠ a₀ → w.piles a = st.piles a)
    (hst : z ∉ (st.piles a₀).faceUp) (hw : z ∉ (w.piles a₀).faceUp) :
    w.pileOfTop z = st.pileOfTop z := by
  unfold State.pileOfTop
  refine firstWhere_congr (α := Anchor) ?_ Anchor.all
  intro a
  by_cases ha : a = a₀
  · rw [ha]
    show decide ((w.piles a₀).top = some z) = decide ((st.piles a₀).top = some z)
    have h1 : ¬ ((w.piles a₀).top = some z) := fun hc => hw (Pile.mem_of_top hc)
    have h2 : ¬ ((st.piles a₀).top = some z) := fun hc => hst (Pile.mem_of_top hc)
    rw [decide_eq_false_iff_not.mpr h1, decide_eq_false_iff_not.mpr h2]
  · show decide ((w.piles a).top = some z) = decide ((st.piles a).top = some z)
    rw [hpiles a ha]

/-! ## §2. The state-level shift of `freeCardS`

If `d` and `d.twin` are entirely outside the raised card's pile, the probe
cannot tell the two states apart: the raised pile keeps the same name for
`d`'s holding (no reveal can touch `d`), and `d.twin` stays a non-top. -/

theorem freeCardS_tabToFound_offPile {st : State} {c d : Card} {a₀ : Anchor}
    (hoff : d ∉ (st.piles a₀).hidden ++ (st.piles a₀).faceUp)
    (hoft : d.twin ∉ (st.piles a₀).hidden ++ (st.piles a₀).faceUp) :
    freeCardS { st.setFound c.suit (st.found c.suit ++ [c]) with
        piles := fun a' => if a' = a₀ then
          Pile.afterRunRemoved (st.piles a₀) (chop (st.piles a₀).faceUp)
        else st.piles a' } d = freeCardS st d := by
  have hoffH : d ∉ (st.piles a₀).hidden := by
    intro h1; exact hoff (List.mem_append.mpr (Or.inl h1))
  have hoffF : d ∉ (st.piles a₀).faceUp := by
    intro h1; exact hoff (List.mem_append.mpr (Or.inr h1))
  have hoftH : d.twin ∉ (st.piles a₀).hidden := by
    intro h1; exact hoft (List.mem_append.mpr (Or.inl h1))
  have hoftF : d.twin ∉ (st.piles a₀).faceUp := by
    intro h1; exact hoft (List.mem_append.mpr (Or.inr h1))
  have hQF : d ∉ (Pile.afterRunRemoved (st.piles a₀) (chop (st.piles a₀).faceUp)).faceUp :=
    notMem_afterRunRemoved_faceUp hoffH hoffF
  have hQtF : d.twin ∉ (Pile.afterRunRemoved (st.piles a₀) (chop (st.piles a₀).faceUp)).faceUp :=
    notMem_afterRunRemoved_faceUp hoftH hoftF
  have hpiles : ∀ a : Anchor, a ≠ a₀ →
      ({ st.setFound c.suit (st.found c.suit ++ [c]) with
          piles := fun a' => if a' = a₀ then
            Pile.afterRunRemoved (st.piles a₀) (chop (st.piles a₀).faceUp)
          else st.piles a' } : State).piles a = st.piles a := by
    intro a ha
    show (if a = a₀ then
        Pile.afterRunRemoved (st.piles a₀) (chop (st.piles a₀).faceUp)
      else st.piles a) = st.piles a
    rw [ite_eq_right ha]
  refine freeCardS_congr ?_ ?_ ?_
  · refine pileHolding_eq_of_piles hpiles hoffF ?_
    show d ∉ (if a₀ = a₀ then
        Pile.afterRunRemoved (st.piles a₀) (chop (st.piles a₀).faceUp)
      else st.piles a₀).faceUp
    rw [ite_eq_left rfl]
    exact hQF
  · intro b hb
    exact hpiles b (fun hba => hoffF (hba ▸ pileHolding_mem hb))
  · refine pileOfTop_eq_of_piles hpiles hoftF ?_
    show d.twin ∉ (if a₀ = a₀ then
        Pile.afterRunRemoved (st.piles a₀) (chop (st.piles a₀).faceUp)
      else st.piles a₀).faceUp
    rw [ite_eq_left rfl]
    exact hQtF

/-! ## §3. The one-step shift of `CanRaiseS` -/

theorem canRaiseS_tabToFound_offPile {st w : State} {c d : Card}
    (hwf : st.WF) (hstep : State.step st (Move.tabToFound c) = some w)
    (hsu : d.suit ≠ c.suit)
    (hoff : ∀ a, st.pileOfTop c = some a →
      d ∉ (st.piles a).hidden ++ (st.piles a).faceUp ∧
      d.twin ∉ (st.piles a).hidden ++ (st.piles a).faceUp) :
    CanRaiseS st d ↔ CanRaiseS w d := by
  obtain ⟨-, a₀, hp₀, hweq⟩ := step_tabToFound_inv hstep
  have hwfw : w.WF := step_wf hwf hstep
  have hfree : freeCardS w d = freeCardS st d := by
    rw [hweq]
    exact freeCardS_tabToFound_offPile (hoff a₀ hp₀).1 (hoff a₀ hp₀).2
  rw [canRaiseS_split hwf, canRaiseS_split hwfw, nextUp_raise_ne hstep hsu, hfree]

/-! ## §4. Sliding inside the fibre

`CanRaiseS` is a cargo-fibre invariant (`canRaiseS_bareCargo_iff'`) and the
rung vector is fixed on a cargo path (`rungAt_cargoPath`), so the `raiseS`
step's slide leg is free. -/

theorem wf_of_cargoLeg {a b : State} (hwf : a.WF) (h : CargoLeg a b) : b.WF := by
  obtain ⟨c, bd, hstep, -⟩ := h
  exact step_wf hwf hstep

theorem wf_of_cargoPath {a b : State} (hwf : a.WF) (h : CargoPath a b) : b.WF := by
  revert hwf
  induction h with
  | refl _ => exact fun hwf => hwf
  | @cons w z u hleg t ih =>
      intro hwf
      exact ih (wf_of_cargoLeg hwf hleg)

/-- **The `nextUp` half, unconditional.**  A raiseS step of `c` never moves
another suit's foundation, so `d`'s next-up bit is fixed (slides fix all
rungs).  The hypothesis `d.suit ≠ c.suit` is *not* implied by `d ≠ c`. -/
theorem specShift_nextUp {z z' : State} {c d : Card}
    (hstep : RaiseStepS z z' c) (hsu : d.suit ≠ c.suit) :
    z'.nextUp d = z.nextUp d := by
  obtain ⟨z₀, hpath, hstep₀⟩ := hstep
  have hlen : (z.found d.suit).length = (z₀.found d.suit).length :=
    rungAt_cargoPath hpath d.suit
  have h1 : z.nextUp d = z₀.nextUp d := by
    unfold State.nextUp State.foundHeight
    rw [hlen]
  have h2 : z'.nextUp d = z₀.nextUp d := nextUp_raise_ne hstep₀ hsu
  rw [h2, h1]

/-- **THE REPAIRED SHIFT THEOREM.**  A `raiseS` step of `c` preserves the
readiness of `d`, provided `d` and `d.twin` are not in the pile of `c` and
`d`'s suit differs from `c`'s.

Both extra hypotheses are necessary: `d`'s presence in `c`'s pile is the
counterexample mechanism (`not_SpecShift`), and same-suit `d` has its
`nextUp` bit crossed by the raise.  No rank split is needed — the pile
condition is rank-free.

Remark for the T4 consumer: for an actual **cover** `d` (rank `c.rank - 1`,
sitting on `c.twin`), both hypotheses are free — a card of rank `< c.rank`
cannot lie in `c`'s pile (`runOK` puts strictly higher ranks below `c`), the
same holds for `d.twin` (same rank), and a cover of `c.twin` has the opposite
colour to `c`, hence a different suit.  What the card's "vacuous by rank"
remark should have excluded is not only `d = c.twin` but the whole pile. -/
theorem specShift {z z' : State} {c d : Card}
    (hz : z.WF) (hstep : RaiseStepS z z' c)
    (hsu : d.suit ≠ c.suit)
    (hoff : ∀ (z₀ : State) (a : Anchor), CargoPath z z₀ →
      State.step z₀ (Move.tabToFound c) = some z' →
      z₀.pileOfTop c = some a →
      d ∉ (z₀.piles a).hidden ++ (z₀.piles a).faceUp ∧
      d.twin ∉ (z₀.piles a).hidden ++ (z₀.piles a).faceUp) :
    CanRaiseS z d ↔ CanRaiseS z' d := by
  obtain ⟨z₀, hpath, hstep₀⟩ := hstep
  have hz₀ : z₀.WF := wf_of_cargoPath hz hpath
  have h1 : CanRaiseS z d ↔ CanRaiseS z₀ d :=
    canRaiseS_bareCargo_iff' (cargoPath_bareCargo hz hpath) d
  have h2 : CanRaiseS z₀ d ↔ CanRaiseS z' d :=
    canRaiseS_tabToFound_offPile hz₀ hstep₀ hsu (hoff z₀ · hpath hstep₀)
  exact h1.trans h2

/-! ## §5. The counterexample — the card's `SpecShift` is false

Witness state: `♠K` is the only face-up card of pile `p0` (its hidden head is
`♦K`); the spade, club and diamond foundations stand at height 12, so

* `zce.nextUp ♦K = true`, but `zce.pileHolding ♦K = none` (it is hidden), so
  `freeCardS zce ♦K = false` and hence `¬ CanRaiseS zce ♦K`;
* the unguarded raise `tabToFound ♠K` fires (the `State.step` guard is only
  `nextUp` + `pileOfTop`), flips `♦K` onto the face-up run and founds `♠K`;
* at the landing state `♦K` is a bare king: `freeCardS zceStep ♦K = true`, and
  its `nextUp` bit is untouched (different suit), so
  `CanRaiseS zceStep ♦K` holds.

The hypotheses of the card's `SpecShift` all hold (`d ≠ c`, `d ≠ c.twin`, and
even `d.suit ≠ c.suit`), so the obligation is unprovable as stated. -/

namespace Counterexample

/-- The raised card: `♠K`. -/
def cK : Card := ⟨Suit.spade, Rank.king⟩

/-- The tracked card: `♦K`; its twin is `♥K`, and `cK.twin = ♣K`. -/
def dK : Card := ⟨Suit.diamond, Rank.king⟩

/-- The witness state. -/
def zce : State where
  found := fun s => if s = Suit.heart then [] else s.upCards.take 12
  piles := fun a =>
    match a with
    | Anchor.p0 => ⟨[dK], [cK]⟩
    | _ => ⟨[], []⟩
  stock := Suit.upCards Suit.heart ++ [⟨Suit.club, Rank.king⟩]
  waste := []
  drawStep := 1

/-- The landing state of the raise at `zce`. -/
def zceStep : State :=
  { zce.setFound cK.suit (zce.found cK.suit ++ [cK]) with
    piles := fun a' => if a' = Anchor.p0 then
      Pile.afterRunRemoved (zce.piles Anchor.p0) (chop (zce.piles Anchor.p0).faceUp)
    else zce.piles a' }

theorem zce_step : zce.step (Move.tabToFound cK) = some zceStep := by
  have hn : zce.nextUp cK = true := by decide
  have hp : zce.pileOfTop cK = some Anchor.p0 := by decide
  simp only [State.step, hn, hp]
  rfl

theorem zce_wf : zce.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s
    · exact ⟨12, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨12, by decide⟩
    · exact ⟨12, by decide⟩
  · intro a
    cases a <;> decide
  · intro c hc
    have h : Card.universe.all (fun c => decide (zce.cardCount c = 1)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp h c hc)
  · decide

theorem zceStep_wf : zceStep.WF := step_wf zce_wf zce_step

theorem zce_free : freeCardS zce dK = false := by decide

theorem zceStep_free : freeCardS zceStep dK = true := by decide

theorem zceStep_next : zceStep.nextUp dK = true := by decide

theorem zce_not_canRaiseS : ¬ CanRaiseS zce dK := by
  intro h
  have h2 := (canRaiseS_split zce_wf).mp h
  rw [zce_free] at h2
  exact absurd h2.2 (by decide)

theorem zceStep_canRaiseS : CanRaiseS zceStep dK :=
  (canRaiseS_split zceStep_wf).mpr ⟨zceStep_next, zceStep_free⟩

/-- **REFUTATION of the card's obligation.** -/
theorem not_SpecShift : ¬ SpecShift := by
  intro h
  have hiff : CanRaiseS zce dK ↔ CanRaiseS zceStep dK :=
    h (u := zce) zce_wf ⟨zce, Steps.refl zce, zce_step⟩ (by decide) (by decide)
  exact zce_not_canRaiseS (hiff.mpr zceStep_canRaiseS)

/-- The same refutation **with `d.suit ≠ c.suit` added**: suit-disjointness
alone does not repair the obligation, the pile condition is what matters. -/
theorem not_specShift_with_suit :
    ¬ (∀ {u z z' : State} {c d : Card}, z.WF → RaiseStepS z z' c →
        d ≠ c → d ≠ c.twin → d.suit ≠ c.suit →
        (CanRaiseS z d ↔ CanRaiseS z' d)) := by
  intro h
  have hiff : CanRaiseS zce dK ↔ CanRaiseS zceStep dK :=
    h (u := zce) zce_wf ⟨zce, Steps.refl zce, zce_step⟩ (by decide) (by decide) (by decide)
  exact zce_not_canRaiseS (hiff.mpr zceStep_canRaiseS)

end Counterexample

/-! ## §6. Second witness — a *reversible* raise, and `RaiseAbove` refuted

The first witness raises with a hidden reveal (a commit).  The second one
raises a card that has company beneath it, so the raise is undoable
(`chop faceUp ≠ []`); the tracked card `d = ♥8` sits **directly below**
`c = ♠7` in the same pile.  Removing `c` makes `d` the pile top, so its
`run` becomes `[]` and the hatch clause of `freeCardS` turns true — the
raise *creates* `d`'s readiness (`CanRaise` itself, not only
`CanRaiseS`).

This is exactly the card's `RaiseAbove` regime (`c.rank.toIdx = 6 <
7 = d.rank.toIdx`) and shows the `↔` form of `RaiseAbove` is false: only
the one-way `canRaise_of_raise_high_fwd` (which carries
`pileHolding d = some b`) survives.  Rank arithmetic does **not** remove
the case: cards below a card have *higher* rank. -/

namespace CounterexampleB

/-- The raised card: `♠7`. -/
def cB : Card := ⟨Suit.spade, Rank.seven⟩

/-- The tracked card: `♥8`, directly below `cB` in pile `p0`. -/
def dB : Card := ⟨Suit.heart, Rank.eight⟩

/-- `♣9`, below `dB`. -/
def xB : Card := ⟨Suit.club, Rank.nine⟩

/-- `♣7`, the card covering `dB.twin = ♦8`. -/
def yB : Card := ⟨Suit.club, Rank.seven⟩

/-- `dB.twin`. -/
def tB : Card := ⟨Suit.diamond, Rank.eight⟩

/-- The cards used outside the stock. -/
def zceBUsed : List Card :=
  (Suit.upCards Suit.spade).take 6 ++ (Suit.upCards Suit.heart).take 7 ++
    [xB, dB, cB, tB, yB]

/-- The witness state: `p0.faceUp = [♣9, ♥8, ♠7]`, `♦8` buried under `♣7` in
`p1`. -/
def zceB : State where
  found := fun s =>
    if s = Suit.spade then s.upCards.take 6
    else if s = Suit.heart then s.upCards.take 7
    else []
  piles := fun a =>
    match a with
    | Anchor.p0 => ⟨[], [xB, dB, cB]⟩
    | Anchor.p1 => ⟨[tB], [yB]⟩
    | _ => ⟨[], []⟩
  stock := Card.universe.filter (fun c => decide (c ∉ zceBUsed))
  waste := []
  drawStep := 1

/-- The landing state. -/
def zceBStep : State :=
  { zceB.setFound cB.suit (zceB.found cB.suit ++ [cB]) with
    piles := fun a' => if a' = Anchor.p0 then
      Pile.afterRunRemoved (zceB.piles Anchor.p0) (chop (zceB.piles Anchor.p0).faceUp)
    else zceB.piles a' }

theorem zceB_step : zceB.step (Move.tabToFound cB) = some zceBStep := by
  have hn : zceB.nextUp cB = true := by decide
  have hp : zceB.pileOfTop cB = some Anchor.p0 := by decide
  simp only [State.step, hn, hp]
  rfl

theorem zceB_wf : zceB.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s
    · exact ⟨6, by decide⟩
    · exact ⟨7, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  · intro a
    cases a <;> decide
  · intro c hc
    have h : Card.universe.all (fun c => decide (zceB.cardCount c = 1)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp h c hc)
  · decide

theorem zceBStep_wf : zceBStep.WF := step_wf zceB_wf zceB_step

theorem zceB_free : freeCardS zceB dB = false := by decide

theorem zceBStep_free : freeCardS zceBStep dB = true := by decide

theorem zceBStep_next : zceBStep.nextUp dB = true := by decide

theorem zceB_not_canRaiseS : ¬ CanRaiseS zceB dB := by
  intro h
  have h2 := (canRaiseS_split zceB_wf).mp h
  rw [zceB_free] at h2
  exact absurd h2.2 (by decide)

theorem zceBStep_canRaiseS : CanRaiseS zceBStep dB :=
  (canRaiseS_split zceBStep_wf).mpr ⟨zceBStep_next, zceBStep_free⟩

/-- The raise of `cB` is live at the *vanilla* license as well. -/
theorem zceBStep_canRaise : CanRaise zceBStep dB :=
  ⟨by decide, Anchor.p0, by decide, Or.inl (by decide)⟩

/-- `d` is not raisable at the origin: it is not a pile top. -/
theorem zceB_not_canRaise : ¬ CanRaise zceB dB := by
  intro h
  obtain ⟨-, a, ha, -⟩ := h
  have hnone : zceB.pileOfTop dB = none := by decide
  rw [hnone] at ha
  cases ha

/-- **`RaiseAbove` (the `↔` form) is false** — the raise *creates* readiness
strictly above `c`'s rank. -/
theorem not_RaiseAbove : ¬ RaiseAbove := by
  intro h
  have hiff : CanRaise zceB dB ↔ CanRaise zceBStep dB :=
    h (st := zceB) (w := zceBStep) (c := cB) (d := dB) zceB_wf zceB_step (by decide)
  exact zceB_not_canRaise (hiff.mpr zceBStep_canRaise)

/-- `SpecShift` fails at a **reversible** raise too (no hidden reveal). -/
theorem not_SpecShift_reversible : ¬ SpecShift := by
  intro h
  have hiff : CanRaiseS zceB dB ↔ CanRaiseS zceBStep dB :=
    h (u := zceB) zceB_wf ⟨zceB, Steps.refl zceB, zceB_step⟩ (by decide) (by decide)
  exact zceB_not_canRaiseS (hiff.mpr zceBStep_canRaiseS)

/-- The same-suit card whose next-up bit the raise of `cB` crosses: `♠8`. -/
def s8 : Card := ⟨Suit.spade, Rank.eight⟩

/-- **`d ≠ c` does not give `d.suit ≠ c.suit`.**  Raising `♠7` moves the spade
foundation to height 7, so `♠8` becomes next-up: the plain `nextUp` shift is
false without suit-disjointness (this is why `specShift_nextUp` carries it). -/
theorem not_nextUp_shift_of_ne :
    ¬ (∀ {z z' : State} {c d : Card}, RaiseStepS z z' c → d ≠ c → d ≠ c.twin →
        z'.nextUp d = z.nextUp d) := by
  intro h
  have hstep : RaiseStepS zceB zceBStep cB := ⟨zceB, Steps.refl zceB, zceB_step⟩
  have hbad := h (z := zceB) (z' := zceBStep) (c := cB) (d := s8) hstep
    (by decide) (by decide)
  exact absurd hbad (by decide)

end CounterexampleB

end OneColourClosure

#print axioms OneColourClosure.specShift_nextUp
#print axioms OneColourClosure.specShift
#print axioms OneColourClosure.Counterexample.not_SpecShift
#print axioms OneColourClosure.Counterexample.not_specShift_with_suit
#print axioms OneColourClosure.CounterexampleB.not_RaiseAbove
#print axioms OneColourClosure.CounterexampleB.not_nextUp_shift_of_ne
#print axioms OneColourClosure.CounterexampleB.not_SpecShift_reversible
