import Temp.RankFront_final

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# RankFront_licensed — the licensed play relation, the un-raise transfer, and R3

This file continues the `raiseS` rank-front lane.  It does **not** modify the
earlier `Temp/RankFront_*` files.

## What is here

1. **`RaiseSSeqL`** — the *licensed* raiseS play relation: every step carries the
   full licence `CanRaise z c` at the state where the raise fires (plus the
   cargo slide, exactly as `RaiseStepS` does).  Accessors, `toSeq`, `wf`,
   `append`, and the adequacy triple:
   * every `RaiseSSeqL` play is a `RaiseSSeq` play;
   * every `RaiseSSeqL` step's raised card is `CanRaiseS` at its origin;
   * every `CanRaiseS` licence is realisable as a `RaiseSSeqL` step.
   Hence `RaiseSSeqL` is exactly the sub-relation of `RaiseSSeq` whose raises are
   reversible (non-commit) raises; it is **strictly smaller** than `RaiseSSeq`
   (`t4a_fires` / `t4a_not_canRaise`), and it is the natural play relation for
   the orbit/reordering algebra.

2. **R1 at the licensed level** — a raise of strictly different rank preserves a
   card's licence, so licences propagate through lower-rank steps.

3. **`swap_of_licensed`** — the sharp adjacent swap: if both cards are licensed
   at the prefix-end state, the lower-ranked one can go first.

4. **The un-raise transfer `(P)`.**  The parent's proposed statement with
   `RaiseStepS` (a *weak* step) is **FALSE**; the kernel-checked counterexample
   `unraise_probe_refutes` is below: a commit raise reveals a hidden card, whose
   twin thereby gains a licence (`CanRaiseS` flips false → true) even though the
   raised card has strictly larger rank.  The corrected statement, with the
   raise *licensed* (`CanRaise`), is true and is proved as
   `canRaiseS_unraise_of_canRaise_step`.

5. **`CanRaiseS` of the least-rank prefix** — from (P), a card whose word-prefix
   consists only of strictly higher ranks is licensed at the start.  This is the
   first step of any rank-sorted replay.

6. **R3 (`CoverMustBeRaised`)** — proved at the `RaiseSSeq` level (hence for
   `RaiseSSeqL`): if the cover `x` of `t` is seated on `t` and `t.twin` is
   founded, then every play that raises `t` also raises `x`.

7. **The residual** of the general rank-front theorem, as a Lean `Prop`
   (`SortedPrefixLicence`), with its proof obligations listed.

House rules: constructive only, no `sorry`, no `Classical`, no `noncomputable`.
-/

namespace OneColourClosure

/-! ## §1. The licensed raiseS relation -/

/-- **`RaiseSSeqL`** — a `raiseS` play in which every raise is *licensed* at the
state where it fires: a reversible cargo slide `CargoPath z z₀`, then
`CanRaise z₀ c`, then the raise.  The head of the word is the **last** raise
(same convention as `RaiseSSeq`). -/
inductive RaiseSSeqL : State → List Card → State → Prop
  | nil (s : State) : RaiseSSeqL s [] s
  | cons {s z z₀ z' : State} {c : Card} {ws : List Card} :
      RaiseSSeqL s ws z →
      CargoPath z z₀ →
      CanRaise z₀ c →
      State.step z₀ (Move.tabToFound c) = some z' →
      RaiseSSeqL s (c :: ws) z'

namespace RaiseSSeqL

/-- Every licensed play is a play. -/
theorem toSeq {s z : State} {ws : List Card} (h : RaiseSSeqL s ws z) :
    RaiseSSeq s ws z := by
  induction h with
  | nil => exact RaiseSSeq.nil s
  | cons _ hp _ hs ih => exact RaiseSSeq.cons ih hp hs

/-- **`step_s`** — the last step of a nonempty licensed play, with all its data. -/
theorem step_s {s z' : State} {c : Card} {ws : List Card}
    (h : RaiseSSeqL s (c :: ws) z') :
    ∃ z z₀, RaiseSSeqL s ws z ∧ CargoPath z z₀ ∧ CanRaise z₀ c ∧
      State.step z₀ (Move.tabToFound c) = some z' := by
  cases h with
  | cons htail hp hcr hs => exact ⟨_, _, htail, hp, hcr, hs⟩

/-- **`cargoPath`** — the slide of the last step. -/
theorem cargoPath {s z' : State} {c : Card} {ws : List Card}
    (h : RaiseSSeqL s (c :: ws) z') :
    ∃ z z₀, RaiseSSeqL s ws z ∧ CargoPath z z₀ := by
  obtain ⟨z, z₀, htail, hp, -, -⟩ := step_s h
  exact ⟨z, z₀, htail, hp⟩

/-- The origin of the last step is licensed for its card. -/
theorem canRaiseS_head {s z' : State} {c : Card} {ws : List Card}
    (h : RaiseSSeqL s (c :: ws) z') :
    ∃ z, RaiseSSeqL s ws z ∧ CanRaiseS z c := by
  obtain ⟨z, z₀, htail, hp, hcr, -⟩ := step_s h
  exact ⟨z, htail, ⟨z₀, hp, hcr⟩⟩

/-- Well-formedness transports forward. -/
theorem wf {s z : State} {ws : List Card} (h : RaiseSSeqL s ws z) :
    s.WF → z.WF := by
  induction h with
  | nil => exact id
  | cons _ hp _ hs ih => exact fun hwf => step_wf (cargoPath_wf (ih hwf) hp) hs

/-- Licensed plays concatenate (`w₁` first, then `w₂`, gives the word `w₂ ++ w₁`). -/
theorem append {s u v : State} {w₁ w₂ : List Card}
    (h₁ : RaiseSSeqL s w₁ u) (h₂ : RaiseSSeqL u w₂ v) :
    RaiseSSeqL s (w₂ ++ w₁) v := by
  induction h₂ generalizing s with
  | nil => exact h₁
  | cons _ hp hcr hs ih =>
      rw [List.cons_append]
      exact RaiseSSeqL.cons (ih h₁) hp hcr hs

end RaiseSSeqL

/-- **Adequacy, forward.**  The head card of a licensed play is `CanRaiseS` at the
state just before it is raised.  Together with `toSeq` this says every
`RaiseSSeqL` step is a genuine licence-bearing raise. -/
theorem canRaiseS_of_raiseSSeqL_head {z z' : State} {c : Card}
    (h : RaiseSSeqL z [c] z') : CanRaiseS z c := by
  have hh := RaiseSSeqL.canRaiseS_head h
  obtain ⟨u, hnil, hc⟩ := hh
  cases hnil
  exact hc

/-- **Adequacy, backward.**  Every `CanRaiseS` licence is realisable as one
licensed step.  Hence `RaiseSSeqL` is not missing any reversible raise. -/
theorem raiseSSeqL_step_of_canRaiseS {z : State} {c : Card} (h : CanRaiseS z c) :
    ∃ z', RaiseSSeqL z [c] z' := by
  obtain ⟨z₀, hp, hcr⟩ := h
  obtain ⟨z', hs⟩ := step_tabToFound_of_canRaise hcr
  exact ⟨z', RaiseSSeqL.cons (RaiseSSeqL.nil z) hp hcr hs⟩

/-! ## §2. R1 at the licensed level -/

/-- **R1, one licensed step.**  Raising a strictly different rank preserves a
card's licence (the forward direction of `specShift_sem_fwd`). -/
theorem canRaiseS_step_of_rank_ne_L {z z' : State} {d c : Card}
    (hz : z.WF) (hstep : RaiseStepS z z' d) (hr : d.rank ≠ c.rank) :
    CanRaiseS z c → CanRaiseS z' c :=
  canRaiseS_step_of_rank_ne hz hstep hr

/-- **R1, a licensed word.**  If every raised card has rank different from `c`'s,
`c`'s licence survives the whole play. -/
theorem RaiseSSeqL.canRaiseS_persist_of_rank_ne {s z : State} {ws : List Card}
    {c : Card} (h : RaiseSSeqL s ws z) (hwf : s.WF)
    (hr : ∀ d ∈ ws, d.rank ≠ c.rank) (hc : CanRaiseS s c) :
    CanRaiseS z c := by
  revert hwf hr hc
  induction h with
  | nil => intro _ _ hc; exact hc
  | cons htail hp hcr hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hr hc
      have hr' : ∀ d ∈ wws, d.rank ≠ c.rank :=
        fun d hd => hr d (List.mem_cons_of_mem _ hd)
      have hcc : cc.rank ≠ c.rank := hr cc (List.mem_cons_self ..)
      have hzwf : zz.WF := RaiseSSeqL.wf htail hwf
      have hz : CanRaiseS zz c := ih hwf hr' hc
      exact canRaiseS_step_of_rank_ne hzwf ⟨zz0, hp, hs⟩ hcc hz

/-- **`swap_of_licensed`** (the sharp adjacent swap).  If the prefix `A` has been
played from `s` to `u`, and **both** `d` and `e` are licensed at `u` with
`d.rank < e.rank`, then the two-step play `A · d · e` is realisable.  This is the
parent's corrected `swap_up` form: the hypothesis is a licence, not a cover
condition (`t5_bare_swap_false` shows covers are insufficient). -/
theorem swap_of_licensed {s u : State} {A : List Card} {d e : Card}
    (hpre : RaiseSSeqL s A.reverse u) (hu : u.WF)
    (hd : CanRaiseS u d) (he : CanRaiseS u e)
    (hr : d.rank.toIdx < e.rank.toIdx) :
    ∃ z', RaiseSSeqL s (e :: d :: A.reverse) z' := by
  obtain ⟨z₀, hp_d, hcr_d⟩ := hd
  obtain ⟨z₂, hs_d⟩ := step_tabToFound_of_canRaise hcr_d
  have hstep_d : RaiseStepS u z₂ d := ⟨z₀, hp_d, hs_d⟩
  have hde : d.rank ≠ e.rank := by intro h; rw [h] at hr; omega
  have he₂ : CanRaiseS z₂ e := canRaiseS_step_of_rank_ne hu hstep_d hde he
  obtain ⟨z₁, hp_e, hcr_e⟩ := he₂
  obtain ⟨z₃, hs_e⟩ := step_tabToFound_of_canRaise hcr_e
  refine ⟨z₃, ?_⟩
  exact RaiseSSeqL.cons
    (RaiseSSeqL.cons hpre hp_d hcr_d hs_d) hp_e hcr_e hs_e

/-! ## §3. The un-raise transfer: `(P)` with a *weak* step is FALSE -/

/-- **Card arithmetic helper.**  If `e` is the top (last face-up card) of a legal
run and `d` is another face-up card of that run, then `e` is above `d`, so
`e.rank < d.rank`. -/
theorem rank_lt_of_mem_of_lastOf {l : List Card} (h : runOK l = true) {e d : Card}
    (hlast : lastOf l = some e) (hd : d ∈ l) (hde : d ≠ e) :
    e.rank.toIdx < d.rank.toIdx := by
  induction l with
  | nil => exact absurd hd List.not_mem_nil
  | cons x t ih =>
      cases t with
      | nil =>
          have hx : x = e := by simpa [lastOf] using hlast
          have hdx : d = x := by simpa using hd
          exact absurd (hdx.trans hx) hde
      | cons y t =>
          have hlast' : lastOf (y :: t) = some e := by simpa [lastOf] using hlast
          rcases List.mem_cons.mp hd with hdx | hdt
          · have he : e ∈ y :: t := lastOf_mem hlast'
            have hlt := above_rank_lt h (y :: t) [] x e rfl he
            rw [← hdx] at hlt
            exact hlt
          · have hrun : runOK (y :: t) = true := (tfc_runOK_two_true h).2
            exact ih hrun hlast' hdt

/-- A card strictly lower-ranked than a pile top cannot occur in that pile. -/
theorem not_mem_pileOfTop_of_rank_lt {z : State} (hz : z.WF) {e d : Card}
    {a : Anchor} (hpa : z.pileOfTop e = some a)
    (hr : d.rank.toIdx < e.rank.toIdx) :
    d ∉ (z.piles a).faceUp := by
  intro hmem
  have hlast : lastOf (z.piles a).faceUp = some e := (pileOfTop_top hpa).2
  have hde : d ≠ e := by intro h; rw [h] at hr; omega
  have hlt := rank_lt_of_mem_of_lastOf (hz.2.1 a) hlast hmem hde
  omega

/-- The twin of a strictly lower-ranked card is also absent from the pile of the
top. -/
theorem not_mem_pileOfTop_twin_of_rank_lt {z : State} (hz : z.WF) {e d : Card}
    {a : Anchor} (hpa : z.pileOfTop e = some a)
    (hr : d.rank.toIdx < e.rank.toIdx) :
    d.twin ∉ (z.piles a).faceUp := by
  have hrt : d.twin.rank.toIdx = d.rank.toIdx := rfl
  intro hmem
  have hlast : lastOf (z.piles a).faceUp = some e := (pileOfTop_top hpa).2
  have hde : d.twin ≠ e := by
    intro h
    have h1 : d.twin.rank.toIdx = e.rank.toIdx := by rw [h]
    omega
  have hlt := rank_lt_of_mem_of_lastOf (hz.2.1 a) hlast hmem hde
  omega

/-! ### §3.1 `pileHolding` / `pileOfTop` are insensitive to a higher-rank raise -/

/-- The holding pile of a card is unchanged by a raise that does not touch its
pile. -/
theorem pileHolding_eq_of_agree {z z' : State} {a0 : Anchor} {x : Card}
    (hwz' : z'.WF)
    (hagree : ∀ a, a ≠ a0 → z'.piles a = z.piles a)
    (hx0 : x ∉ (z.piles a0).faceUp) (hx0' : x ∉ (z'.piles a0).faceUp) :
    z'.pileHolding x = z.pileHolding x := by
  cases hh : z.pileHolding x with
  | none =>
      have hno : ∀ a, x ∉ (z'.piles a).faceUp := by
        intro a
        by_cases ha : a = a0
        · subst ha; exact hx0'
        · rw [hagree a ha]; exact tfc_not_mem_faceUp_of_holdNone hh a
      rw [tfc_pileHolding_none hno]
  | some a =>
      have ha0 : a ≠ a0 := by
        intro h; subst h; exact hx0 (pileHolding_mem hh)
      have hmem : x ∈ (z'.piles a).faceUp := by
        rw [hagree a ha0]; exact pileHolding_mem hh
      rw [(pileHolding_eq_some_iff hwz').mpr hmem]

/-- The top-search for a card absent from the changed pile is unchanged. -/
theorem pileOfTop_eq_of_agree {z z' : State} {a0 : Anchor} {x : Card}
    (hagree : ∀ a, a ≠ a0 → z'.piles a = z.piles a)
    (hx0 : x ∉ (z.piles a0).faceUp) (hx0' : x ∉ (z'.piles a0).faceUp) :
    z'.pileOfTop x = z.pileOfTop x := by
  unfold State.pileOfTop
  apply firstWhere_congr
  intro a
  by_cases ha : a = a0
  · subst ha
    have h1 : ¬ ((z'.piles a).top = some x) := fun h => hx0' (Pile.mem_of_top h)
    have h2 : ¬ ((z.piles a).top = some x) := fun h => hx0 (Pile.mem_of_top h)
    simp [State.topOf, h1, h2]
  · have hp := hagree a ha
    show decide (z'.topOf a = some x) = decide (z.topOf a = some x)
    rw [State.topOf, State.topOf, hp]

/-- `nextUp` of a lower-ranked card is unchanged by a raise of a higher rank. -/
theorem nextUp_tabToFound_eq_of_low_rank {z z' : State} {e d : Card}
    (hstep : State.step z (Move.tabToFound e) = some z')
    (hr : d.rank.toIdx < e.rank.toIdx) :
    z'.nextUp d = z.nextUp d := by
  have hnext : z.nextUp e = true := (step_tabToFound_inv hstep).1
  have heq : e.rank.toIdx = z.foundHeight e.suit := by
    simpa [State.nextUp] using of_decide_eq_true hnext
  unfold State.nextUp
  by_cases hsu : d.suit = e.suit
  · have hlen0 : z.foundHeight d.suit = e.rank.toIdx := by rw [hsu]; exact heq.symm
    have hlen1 : z'.foundHeight d.suit = z.foundHeight d.suit + 1 := by
      unfold State.foundHeight
      rw [found_tabToFound hstep d.suit, ite_eq_left hsu, List.length_append,
        List.length_singleton]
    rw [hlen1, hlen0]
    have h1 : ¬ (d.rank.toIdx = e.rank.toIdx) := by omega
    have h2 : ¬ (d.rank.toIdx = e.rank.toIdx + 1) := by omega
    simp [h1, h2]
  · have hlen : z'.foundHeight d.suit = z.foundHeight d.suit := by
      unfold State.foundHeight
      rw [found_tabToFound hstep d.suit, ite_eq_right hsu]
    rw [hlen]

/-- **`freeCardS` inertness.**  A *licensed* raise of a strictly higher rank leaves
the tableau-readiness of `d` untouched: the raised card's pile neither holds `d`
nor `d.twin` (rank), and a licensed raise never reveals a hidden card. -/
theorem freeCardS_tabToFound_eq_of_low_rank {z z' : State} {e d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
    (hcr : CanRaise z e) (hr : d.rank.toIdx < e.rank.toIdx) :
    freeCardS z' d = freeCardS z d := by
  obtain ⟨-, a1, hpa1, hseat⟩ := hcr
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have ha10 : a1 = a0 := Option.some.inj (hpa1.symm.trans hpa0)
  rw [ha10] at hseat
  have hwz' : z'.WF := step_wf hz hstep
  have hd0 : d ∉ (z.piles a0).faceUp := not_mem_pileOfTop_of_rank_lt hz hpa0 hr
  have hdt0 : d.twin ∉ (z.piles a0).faceUp :=
    not_mem_pileOfTop_twin_of_rank_lt hz hpa0 hr
  have hd0' : d ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_ne hne]
      intro h; exact hd0 (mem_chop_of_mem_chop h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, Pile.afterRunRemoved_bare hhid]; simp
      · rw [afterRunRemoved_ne hch]
        intro h; exact hd0 (mem_chop_of_mem_chop h)
  have hdt0' : d.twin ∉ (z'.piles a0).faceUp := by
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    rw [hp0]
    rcases hseat with hne | ⟨hhid, -⟩
    · rw [afterRunRemoved_ne hne]
      intro h; exact hdt0 (mem_chop_of_mem_chop h)
    · by_cases hch : chop (z.piles a0).faceUp = []
      · rw [hch, Pile.afterRunRemoved_bare hhid]; simp
      · rw [afterRunRemoved_ne hch]
        intro h; exact hdt0 (mem_chop_of_mem_chop h)
  have hagree : ∀ a, a ≠ a0 → z'.piles a = z.piles a := by
    intro a ha
    rw [hpiles a, ite_eq_right ha]
  have hph_d : z'.pileHolding d = z.pileHolding d :=
    pileHolding_eq_of_agree hwz' hagree hd0 hd0'
  have hpt : z'.pileOfTop d.twin = z.pileOfTop d.twin :=
    pileOfTop_eq_of_agree hagree hdt0 hdt0'
  unfold freeCardS
  rw [hph_d]
  cases hhh : z.pileHolding d with
  | none => rfl
  | some a =>
      have ha0 : a ≠ a0 := by
        intro h; subst h; exact hd0 (pileHolding_mem hhh)
      simp only [hagree a ha0, hpt]

/-- **`(P)`, corrected (licensed) form.**  A licensed raise of a strictly higher
rank is **licence-inert** for a lower-ranked card: `CanRaiseS d` holds before iff
it holds after.  This is the un-raise transfer the sorting induction needs. -/
theorem canRaiseS_inert_tabToFound_of_low_rank {z z' : State} {e d : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound e) = some z')
    (hcr : CanRaise z e) (hr : d.rank.toIdx < e.rank.toIdx) :
    CanRaiseS z' d ↔ CanRaiseS z d := by
  have hwz' : z'.WF := step_wf hz hstep
  have hnext := nextUp_tabToFound_eq_of_low_rank hstep hr
  have hfree := freeCardS_tabToFound_eq_of_low_rank hz hstep hcr hr
  rw [canRaiseS_split hwz', canRaiseS_split hz, hnext, hfree]

/-- **`(P)` at the step level.**  A licensed step (a cargo slide followed by a
licensed raise) of a strictly higher rank preserves a lower-ranked card's
licence, both ways. -/
theorem canRaiseS_inert_of_canRaiseStep {z z₀ z' : State} {e d : Card}
    (hz : z.WF) (hpath : CargoPath z z₀) (hcr : CanRaise z₀ e)
    (hstep : State.step z₀ (Move.tabToFound e) = some z')
    (hr : d.rank.toIdx < e.rank.toIdx) :
    CanRaiseS z' d ↔ CanRaiseS z d := by
  have hz₀ : z₀.WF := cargoPath_wf hz hpath
  have h1 : CanRaiseS z' d ↔ CanRaiseS z₀ d :=
    canRaiseS_inert_tabToFound_of_low_rank hz₀ hstep hcr hr
  -- cargo invariance in both directions
  have hround : CanRaiseS z d ↔ CanRaiseS z₀ d := by
    constructor
    · intro h
      exact (canRaiseS_orbit_rung hz (sameOrbit_of_cargoPath hpath)
        (rungAt_cargoPath hpath)).mp h
    · intro h
      exact (canRaiseS_orbit_rung hz₀
        (sameOrbitSetoid.iseqv.symm (sameOrbit_of_cargoPath hpath))
        (fun σ => (rungAt_cargoPath hpath σ).symm)).mp h
  exact h1.trans hround.symm

/-! ### §3.2 The counterexample: `(P)` with `RaiseStepS` is FALSE -/

/-- The raised card: `8♥` (sole face-up card of pile `p0`). -/
def urE : Card := ⟨Suit.heart, Rank.eight⟩
/-- The hidden card beneath it: `7♠`. -/
def urR : Card := ⟨Suit.spade, Rank.seven⟩
/-- `urR.twin = 7♣`, the card that gains a licence. -/
def urD : Card := ⟨Suit.club, Rank.seven⟩
/-- The card above `urD` in its pile. -/
def urU : Card := ⟨Suit.diamond, Rank.six⟩
/-- The card below `urD` in its pile. -/
def urW : Card := ⟨Suit.diamond, Rank.eight⟩

theorem urR_twin : urR.twin = urD := by decide

/-- The probe state:
* `p0.hidden = [7♠]`, `p0.faceUp = [8♥]` (sole face-up card);
* `p1.faceUp = [8♦, 7♣, 6♦]` (`7♣` seated on `8♦`, `6♦` above it).
Foundations: `♠` A..6, `♥` A..7, `♦` none, `♣` A..6. -/
def urState : State where
  found := fun su =>
    match su with
    | .spade => (Suit.upCards .spade).take 6
    | .heart => (Suit.upCards .heart).take 7
    | .diamond => []
    | .club => (Suit.upCards .club).take 6
  piles := fun a =>
    match a with
    | .p0 => ⟨[urR], [urE]⟩
    | .p1 => ⟨[], [urW, urD, urU]⟩
    | _ => ⟨[], []⟩
  stock := stockOf (fun su =>
    match su with
    | .spade => 6
    | .heart => 7
    | .diamond => 0
    | .club => 6) [urR, urE, urW, urD, urU]
  waste := []
  drawStep := 1

theorem urState_WF : urState.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro su
    match su with
    | .spade => exact ⟨6, by decide⟩
    | .heart => exact ⟨7, by decide⟩
    | .diamond => exact ⟨0, by decide⟩
    | .club => exact ⟨6, by decide⟩
  · intro a
    match a with
    | .p0 => decide
    | .p1 => decide
    | .p2 => decide
    | .p3 => decide
    | .p4 => decide
    | .p5 => decide
    | .p6 => decide
  · intro c _
    rcases c with ⟨su, r⟩
    cases su <;> cases r <;> decide
  · decide

/-- `8♥` is `nextUp` and is the sole face-up card of `p0`, so the *weak* step
fires. -/
theorem ur_pileOfTop : urState.pileOfTop urE = some Anchor.p0 := by decide

theorem ur_nextUp : urState.nextUp urE = true := by decide

/-- The weak raise landing. -/
def urAfter : State :=
  { urState.setFound urE.suit (urState.found urE.suit ++ [urE]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (urState.piles Anchor.p0)
          (chop (urState.piles Anchor.p0).faceUp)
      else urState.piles a' }

theorem ur_step : State.step urState (Move.tabToFound urE) = some urAfter :=
  step_tabToFound_splice ur_nextUp ur_pileOfTop

/-- The raise is **not** licensed: `chop` is empty and the hidden deck is not. -/
theorem ur_not_canRaise : ¬ CanRaise urState urE := by
  intro h
  obtain ⟨-, a, hpa, hseat⟩ := h
  rw [ur_pileOfTop] at hpa
  have ha : a = Anchor.p0 := (Option.some.inj hpa).symm
  subst ha
  rcases hseat with hne | ⟨hhid, -⟩
  · exact absurd hne (by decide)
  · exact absurd hhid (by decide)

/-- The landing of sliding `6♦` off `7♣` onto the revealed `7♠`. -/
def urSlide : State :=
  (urAfter.setPile Anchor.p1
      (Pile.afterRunRemoved (urAfter.piles Anchor.p1)
        (below urU (urAfter.piles Anchor.p1).faceUp))).putRun
    (fromCard urU (urAfter.piles Anchor.p1).faceUp) (Sum.inr urR)

theorem ur_step_slide :
    State.step urAfter (Move.tabToTab urU (Sum.inr urR)) = some urSlide := by
  rw [step_tabToTab_eq]
  have hhold : urAfter.pileHolding urU = some Anchor.p1 := by decide
  have hcp : urAfter.canPlace urU (Sum.inr urR) = true := by decide
  rw [hhold]
  simp only [hcp, ite_true]
  rfl

theorem ur_slide_cargoLeg : CargoLeg urAfter urSlide := by
  refine ⟨urU, Sum.inr urR, ur_step_slide, ?_⟩
  exact (tabToTabR_iff_reversibleAtW (step_wf urState_WF ur_step) urU
    (Sum.inr urR)).mp (by decide)

theorem ur_slide_canRaise : CanRaise urSlide urD := by
  refine ⟨?_, Anchor.p1, ?_, Or.inl ?_⟩
  · decide
  · decide
  · decide

/-- **`7♣` gains the licence after the commit raise.** -/
theorem ur_canRaiseS_after : CanRaiseS urAfter urD :=
  ⟨urSlide, Steps.cons ur_slide_cargoLeg (Steps.refl urSlide), ur_slide_canRaise⟩

/-- **`7♣` is not licensed before it.** -/
theorem ur_not_canRaiseS : ¬ CanRaiseS urState urD := by
  intro h
  have hsplit := (canRaiseS_split urState_WF).mp h
  have hf : freeCardS urState urD = true := hsplit.2
  have hfalse : freeCardS urState urD = false := by decide
  rw [hfalse] at hf
  exact Bool.false_ne_true hf

/-- **`(P)` IS FALSE FOR `RaiseStepS`.**  There is a WF state, a weak
`tabToFound` step of `8♥` (rank 7) and a card `7♣` (rank 6) that is *not*
`CanRaiseS` before the step but *is* `CanRaiseS` after it.  The raised `8♥` is not
licensed: it is a commit raise that reveals the hidden `7♠ = 7♣.twin`, and that
revealed twin becomes the landing site that licenses `7♣`.  So the un-raise
transfer cannot be stated with the weak `RaiseStepS`; the *licence* is
load-bearing. -/
theorem unraise_probe_refutes :
    ¬ (∀ {z z' : State} {e d : Card}, z.WF → RaiseStepS z z' e →
        d.rank.toIdx < e.rank.toIdx → CanRaiseS z' d → CanRaiseS z d) := by
  intro H
  have hlt : urD.rank.toIdx < urE.rank.toIdx := by decide
  have hstepS : RaiseStepS urState urAfter urE := ⟨urState, Steps.refl urState, ur_step⟩
  exact ur_not_canRaiseS (H urState_WF hstepS hlt ur_canRaiseS_after)

/-- **The un-raise transfer along a licensed word.**  If every card of the word
`B` has strictly higher rank than `x`, then `x`'s licence is *transferred
backwards* across the whole word. -/
theorem canRaiseS_unraise_word {s z : State} {B : List Card} {x : Card}
    (h : RaiseSSeqL s B z) (hwf : s.WF)
    (hr : ∀ b ∈ B, x.rank.toIdx < b.rank.toIdx) :
    CanRaiseS z x → CanRaiseS s x := by
  revert hwf hr
  induction h with
  | nil => intro _ _ hc; exact hc
  | cons htail hp hcr hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hr hc
      have hr' : ∀ b ∈ wws, x.rank.toIdx < b.rank.toIdx :=
        fun b hb => hr b (List.mem_cons_of_mem _ hb)
      have hcc : x.rank.toIdx < cc.rank.toIdx := hr cc (List.mem_cons_self ..)
      have hzwf : zz.WF := RaiseSSeqL.wf htail hwf
      have hz : CanRaiseS zz x :=
        (canRaiseS_inert_of_canRaiseStep hzwf hp hcr hs hcc).mp hc
      exact ih hwf hr' hz

/-- **The least-rank suffix is licensed at the start.**  If `x` is the last raise
of a licensed word and every other raised card has strictly higher rank, then `x`
is licensed at the starting state.  This is the base step of any rank-sorted
replay: the globally least-rank card can be raised first. -/
theorem canRaiseS_of_prefix_rank_gt {s z : State} {B : List Card} {x : Card}
    (h : RaiseSSeqL s (x :: B) z) (hwf : s.WF)
    (hr : ∀ b ∈ B, x.rank.toIdx < b.rank.toIdx) :
    CanRaiseS s x := by
  obtain ⟨u, htail, hcan⟩ := RaiseSSeqL.canRaiseS_head h
  exact canRaiseS_unraise_word htail hwf hr hcan

/-- Dropping a suffix of a licensed word leaves a licensed word. -/
theorem RaiseSSeqL.drop_suffix {s z : State} {A B : List Card}
    (h : RaiseSSeqL s (A ++ B) z) : ∃ u, RaiseSSeqL s B u := by
  induction A generalizing z with
  | nil => exact ⟨z, by simpa using h⟩
  | cons a A ih =>
      rw [List.cons_append] at h
      obtain ⟨z₁, -, htail, -, -, -⟩ := RaiseSSeqL.step_s h
      exact ih htail

/-- **The globally least-rank card of a licensed word is licensed at the start.**
(Stated on the first occurrence split of the word; `x ∉ B` is the "appears once"
condition, automatic for real plays.) -/
theorem canRaiseS_of_min_rank {s z : State} {A B : List Card} {x : Card}
    (h : RaiseSSeqL s (A ++ x :: B) z) (hwf : s.WF)
    (hB : x ∉ B)
    (hmin : ∀ y ∈ A ++ x :: B, y ≠ x → x.rank.toIdx < y.rank.toIdx) :
    CanRaiseS s x := by
  obtain ⟨u, hu⟩ := RaiseSSeqL.drop_suffix (A := A) (B := x :: B) h
  refine canRaiseS_of_prefix_rank_gt hu hwf ?_
  intro b hb
  exact hmin b (by
    rw [List.mem_append]
    exact Or.inr (List.mem_cons_of_mem _ hb)) (fun h => hB (h ▸ hb))

/-! ## §4. R3 — the cover must be raised (`CoverMustBeRaised`)

The state-level lock (`twin_covered_persists`, `step_none_of_twin_covered`) says
that while `x` is seated on `t` and `t.twin` is founded, `t` is never a pile top
in the cargo class, so `t` cannot be raised.  The play-level statement follows by
carrying the invariant "`x` is still seated on `t`" through every raise of a
*different* card. -/

/-- A raise of a card different from a seated card preserves its seat. -/
theorem seatOf_tabToFound_of_seated_ne {z z' : State} {c x t : Card}
    (hz : z.WF) (hstep : State.step z (Move.tabToFound c) = some z')
    (hseat : seatOf z x = some (Sum.inr t)) (hxc : x ≠ c) :
    seatOf z' x = some (Sum.inr t) := by
  obtain ⟨a, hhold, hbel, hlast⟩ := tfc_seatOf_of_inr hseat
  obtain ⟨a0, hpa0, hpiles⟩ := piles_tabToFound hstep
  have hwz' : z'.WF := step_wf hz hstep
  have hlastf : lastOf (z.piles a0).faceUp = some c := (pileOfTop_top hpa0).2
  have hmem : x ∈ (z.piles a).faceUp := pileHolding_mem hhold
  by_cases ha : a = a0
  · rw [ha] at hhold hbel hlast hmem
    have hchopmem : x ∈ chop (z.piles a0).faceUp :=
      mem_chop_of_mem_of_ne_last hmem hlastf hxc
    have hne : chop (z.piles a0).faceUp ≠ [] := fun h => by
      rw [h] at hchopmem
      exact absurd hchopmem List.not_mem_nil
    have hp0 : z'.piles a0 =
        Pile.afterRunRemoved (z.piles a0) (chop (z.piles a0).faceUp) := by
      rw [hpiles a0, ite_eq_left rfl]
    refine tfc_seatOf_inr_intro (a := a0) ?_ ?_
    · exact (pileHolding_eq_some_iff hwz').mpr (by
        rw [hp0, afterRunRemoved_ne hne]
        exact hchopmem)
    · rw [hp0, afterRunRemoved_ne hne,
        below_chop_of_mem_of_ne_last hmem hlastf hxc]
      exact hlast
  · have hmem' : x ∈ (z'.piles a).faceUp := by
      rw [hpiles a, ite_eq_right ha]
      exact hmem
    refine tfc_seatOf_inr_intro (a := a) ?_ ?_
    · exact (pileHolding_eq_some_iff hwz').mpr hmem'
    · rw [hpiles a, ite_eq_right ha]
      exact hlast

/-- A cargo leg preserves the seat of every card except its mover; a *seated*
card (non-king, sitting on a card) can never be the mover while its twin-mate's
cover is founded. -/
theorem seatOf_cargoLeg_of_seated {w v : State} {x t : Card}
    (hwf : w.WF) (hleg : CargoLeg w v)
    (hseat : seatOf w x = some (Sum.inr t))
    (hfound : t.twin ∈ w.found t.twin.suit) :
    seatOf v x = some (Sum.inr t) := by
  obtain ⟨c, b, hstep, hrev⟩ := hleg
  have hxnotking : x.rank ≠ Rank.king := tfc_seatOf_inr_rank_ne_king hwf hseat
  have hxc : x ≠ c := by
    intro hxc
    have hseat_c : seatOf w c = some (Sum.inr t) := by rw [← hxc]; exact hseat
    have hnk : c.rank ≠ Rank.king := by rw [← hxc]; exact hxnotking
    have hR : tabToTabR w c b = true :=
      (tabToTabR_iff_reversibleAtW hwf c b).mpr hrev
    obtain ⟨a, hhold, hcp, -⟩ := tfc_tabToTabR_inv hR
    cases b with
    | inl a' => exact hnk (canPlace_inl hcp).2
    | inr y =>
        obtain ⟨k, hk, hfit⟩ := canPlace_inr hcp
        obtain ⟨a2, hhold2, -, hlast2⟩ := tfc_seatOf_of_inr hseat_c
        have hfitt : canSitOn c t = true := (tfc_seat_parent hwf hhold2 hlast2).1
        rcases seat_possibilities hfitt hfit with h | h
        · rw [h] at hk
          exact absurd hk (by rw [no_top_of_seat hwf hseat_c]; simp)
        · rw [h] at hk
          exact absurd hk (by rw [pileOfTop_eq_none_of_found hwf hfound]; simp)
  have hpoint := tfc_seat_point_edit hwf hstep hrev x
  rw [hpoint, ite_eq_right hxc]
  exact hseat

/-- A cargo path preserves a seated card's seat. -/
theorem seatOf_cargoPath_of_seated {w v : State} {x t : Card}
    (hwf : w.WF) (hpath : CargoPath w v)
    (hseat : seatOf w x = some (Sum.inr t))
    (hfound : t.twin ∈ w.found t.twin.suit) :
    seatOf v x = some (Sum.inr t) := by
  revert hwf hseat hfound
  induction hpath with
  | refl => intro _ hs _; exact hs
  | @cons w zmid v hleg hrest ih =>
      intro hwf hs hf
      have hw' : zmid.WF := cargoPath_wf hwf (Steps.cons hleg (Steps.refl zmid))
      have hs' : seatOf zmid x = some (Sum.inr t) :=
        seatOf_cargoLeg_of_seated hwf hleg hs hf
      have hf' : t.twin ∈ zmid.found t.twin.suit := by
        rw [found_cargoLeg hleg]; exact hf
      exact ih hw' hs' hf'

/-- **The seat invariant.**  If `x` sits on `t` and `t.twin` is founded at the
start, then along any licensed play that does not raise `x`, `x` still sits on
`t` and `t.twin` is still founded. -/
theorem seat_invariant_of_not_mem {s z : State} {ws : List Card} {x t : Card}
    (h : RaiseSSeq s ws z) (hwf : s.WF)
    (hseat : seatOf s x = some (Sum.inr t))
    (hfound : t.twin ∈ s.found t.twin.suit)
    (hx : x ∉ ws) :
    seatOf z x = some (Sum.inr t) ∧ t.twin ∈ z.found t.twin.suit := by
  revert hwf hseat hfound hx
  induction h with
  | nil => intro _ hs hf _; exact ⟨hs, hf⟩
  | cons htail hp hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hseat hfound hx
      have hx' : x ∉ wws := fun hmem => hx (List.mem_cons_of_mem _ hmem)
      have hxc : x ≠ cc := fun hcon => hx (by rw [hcon]; exact List.mem_cons_self ..)
      have hzwf : zz.WF := raiseSSeq_wf htail hwf
      obtain ⟨hseat_zz, hfound_zz⟩ := ih hwf hseat hfound hx'
      by_cases htc : t = cc
      · -- the cover's card is being raised: impossible, `t` is never a top
        exfalso
        have hnotop : zz0.pileOfTop cc = none := by
          rw [← htc]
          exact twin_covered_persists hzwf hseat_zz hfound_zz hp
        obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hs
        rw [hnotop] at hpa
        exact absurd hpa (by simp)
      · -- raising a different card preserves the seat and the foundation
        have hseat_zz0 : seatOf zz0 x = some (Sum.inr t) :=
          seatOf_cargoPath_of_seated hzwf hp hseat_zz hfound_zz
        have hfound_zz0 : t.twin ∈ zz0.found t.twin.suit := by
          rw [found_cargoPath hp]; exact hfound_zz
        have hseat' : seatOf zz' x = some (Sum.inr t) :=
          seatOf_tabToFound_of_seated_ne (cargoPath_wf hzwf hp) hs hseat_zz0 hxc
        have hfound' : t.twin ∈ zz'.found t.twin.suit := by
          rw [found_tabToFound hs t.twin.suit]
          by_cases hsu : t.twin.suit = cc.suit
          · rw [ite_eq_left hsu]
            exact List.mem_append.mpr (Or.inl hfound_zz0)
          · rw [ite_eq_right hsu]
            exact hfound_zz0
        exact ⟨hseat', hfound'⟩

/-- **R3 (`CoverMustBeRaised`), proved at the `RaiseSSeq` level.**  If `x` sits on
`t` and `t.twin` is founded at a WF start, every play that raises `t` also raises
`x`.  This closes the play-level obligation left open in `RankFront_final`. -/
theorem cover_must_be_raised : CoverMustBeRaised := by
  intro s z ws x t h
  induction h with
  | nil =>
      intro hwf hseat hfound ht
      exact absurd ht List.not_mem_nil
  | cons htail hp hs ih =>
      rename_i zz zz0 zz' cc wws
      intro hwf hseat hfound ht
      rcases List.mem_cons.mp ht with htc | htws
      · -- `t = cc` is raised now; `x` cannot have been left behind
        by_cases hxw : x ∈ wws
        · exact List.mem_cons_of_mem _ hxw
        · exfalso
          obtain ⟨hseat_zz, hfound_zz⟩ :=
            seat_invariant_of_not_mem htail hwf hseat hfound hxw
          have hnotop : zz0.pileOfTop cc = none := by
            rw [← htc]
            exact twin_covered_persists (raiseSSeq_wf htail hwf)
              hseat_zz hfound_zz hp
          obtain ⟨-, a, hpa, -⟩ := step_tabToFound_inv hs
          rw [hnotop] at hpa
          exact absurd hpa (by simp)
      · exact List.mem_cons_of_mem _ (ih hwf hseat hfound htws)

/-- **R3 for the licensed relation** (immediate from `cover_must_be_raised`). -/
theorem cover_must_be_raised_L {s z : State} {ws : List Card} {x t : Card}
    (h : RaiseSSeqL s ws z) (hwf : s.WF)
    (hseat : seatOf s x = some (Sum.inr t))
    (hfound : t.twin ∈ s.found t.twin.suit)
    (ht : t ∈ ws) : x ∈ ws :=
  cover_must_be_raised h.toSeq hwf hseat hfound ht

/-! ## §5. The exact residual

`(P)` (corrected) transfers licences across **higher-rank** raises, and R1
transfers them across **lower-rank** raises.  What neither supplies is the
*sorted-prefix bridge*: the sorted prefix is built at states that also differ from
the original play's prefix by the *slides*.  The residual below is the sharp
statement of that bridge.  Its proof obligations are:

* `canRaiseS_inert_of_canRaiseStep` — undo the missing higher-rank raises
  (**proved**);
* `RaiseSSeqL.canRaiseS_persist_of_rank_ne` — add the extra lower-rank raises
  (**proved**);
* `twin_raise_square` (`Orig2/Fork/Local/ForkCriticalPair.lean:241`) — the tie
  block, once both same-rank cards are tops (**available**);
* the **open** part: the cargo/slide identification between the sorted-prefix
  endpoint and the original prefix state after the two transfers above.  This is
  stated as the hypothesis of `SortedPrefixLicence`, and is *not* proved. -/
def SortedPrefixLicence : Prop :=
  ∀ {s z u : State} {R P : List Card} {x : Card},
    s.WF →
    R.Pairwise (fun a b => a.rank.toIdx ≤ b.rank.toIdx) →
    (∀ r ∈ R, r ∈ P) →
    (∀ p ∈ P, p.rank.toIdx < x.rank.toIdx → p ∈ R) →
    RaiseSSeqL s R.reverse u →
    RaiseSSeqL s P.reverse z →
    x ∈ P →
    CanRaiseS u x

/-! ## §6. Kernel-checked licensed census witnesses

The full census is in `Temp/RankFront_licensed_census.py` (see the report).  Here
are concrete `RaiseSSeqL` witnesses for the probe states, so the licensed level is
not merely model-checked.  Note which words are *not* licensed: `t3`'s and `t5`'s
long three-step plays are commit plays (a bare non-king top with an empty hidden
deck), hence they live in `RaiseSSeq` but not in `RaiseSSeqL`. -/

/-- A concrete licence certificate: `c` is next-up and is a pile top with company
beneath it. -/
theorem canRaise_lic {z : State} {c : Card} {a : Anchor}
    (hn : z.nextUp c = true) (hp : z.pileOfTop c = some a)
    (hs : chop (z.piles a).faceUp ≠ []) : CanRaise z c :=
  ⟨hn, a, hp, Or.inl hs⟩

/-- **T2, licensed rank-front**: `[8♦, 8♥, 9♠]` (chronological), word
`[9♠, 8♥, 8♦]`. -/
theorem t2_rankfront_L : ∃ z, RaiseSSeqL t2 [e9S, e8H, e8D] z := by
  have h1 : CanRaise t2 e8D :=
    canRaise_lic (a := Anchor.p1) (by decide) (by decide) (by decide)
  have h2 : CanRaise t2a e8H :=
    canRaise_lic (a := Anchor.p0) (by decide) (by decide) (by decide)
  have h3 : CanRaise t2b e9S :=
    canRaise_lic (a := Anchor.p0) (by decide) (by decide) (by decide)
  exact ⟨t2c, RaiseSSeqL.cons
    (RaiseSSeqL.cons
      (RaiseSSeqL.cons (RaiseSSeqL.nil t2) (Steps.refl t2) h1 t2_step_8D)
      (Steps.refl t2a) h2 t2a_step_8H)
    (Steps.refl t2b) h3 t2b_step_9S⟩

/-- **T3, licensed two-card play** `[8♥, 9♠]` (the third card `10♦` would be a
commit raise). -/
theorem t3_two_L : ∃ z, RaiseSSeqL t3 [e9S, e8H] z := by
  have h1 : CanRaise t3 e8H :=
    canRaise_lic (a := Anchor.p0) (by decide) (by decide) (by decide)
  have h2 : CanRaise t3a e9S :=
    canRaise_lic (a := Anchor.p0) (by decide) (by decide) (by decide)
  exact ⟨t3b, RaiseSSeqL.cons
    (RaiseSSeqL.cons (RaiseSSeqL.nil t3) (Steps.refl t3) h1 t3_step_8H)
    (Steps.refl t3a) h2 t3a_step_9S⟩

/-- **T5, licensed two-card play** `[10♦, 8♥]` (word `[8♥, 10♦]`). -/
theorem t5_two_L : ∃ z, RaiseSSeqL t5 [e8H, eTD] z := by
  have h1 : CanRaise t5 eTD :=
    canRaise_lic (a := Anchor.p1) (by decide) (by decide) (by decide)
  have h2 : CanRaise t5a e8H :=
    canRaise_lic (a := Anchor.p0) (by decide) (by decide) (by decide)
  exact ⟨t5b, RaiseSSeqL.cons
    (RaiseSSeqL.cons (RaiseSSeqL.nil t5) (Steps.refl t5) h1 t5_step_TD)
    (Steps.refl t5a) h2 t5a_step_8H⟩

/-- **T5, the other licensed two-card play** `[8♥, 10♦]` (word `[10♦, 8♥]`). -/
theorem t5_two_L' : ∃ z, RaiseSSeqL t5 [eTD, e8H] z := by
  have h1 : CanRaise t5 e8H :=
    canRaise_lic (a := Anchor.p0) (by decide) (by decide) (by decide)
  have h2 : CanRaise t5A eTD :=
    canRaise_lic (a := Anchor.p1) (by decide) (by decide) (by decide)
  exact ⟨t5AT, RaiseSSeqL.cons
    (RaiseSSeqL.cons (RaiseSSeqL.nil t5) (Steps.refl t5) h1 t5_step_8H)
    (Steps.refl t5A) h2 t5A_step_TD⟩

/-- **T6, licensed rank-front**: three bare kings, `[K♦, K♠, K♥]` (word
`[K♥, K♠, K♦]`). -/
theorem t6_rankfront_L : ∃ z, RaiseSSeqL t6 [cKH, eKS, cKD] z := by
  have h1 : CanRaise t6 cKD :=
    ⟨by decide, Anchor.p2, by decide, Or.inr ⟨by decide, by decide⟩⟩
  have h2 : CanRaise t6a eKS :=
    ⟨by decide, Anchor.p0, by decide, Or.inr ⟨by decide, by decide⟩⟩
  have h3 : CanRaise t6b cKH :=
    ⟨by decide, Anchor.p1, by decide, Or.inr ⟨by decide, by decide⟩⟩
  exact ⟨t6c, RaiseSSeqL.cons
    (RaiseSSeqL.cons
      (RaiseSSeqL.cons (RaiseSSeqL.nil t6) (Steps.refl t6) h1 t6_step_KD)
      (Steps.refl t6a) h2 t6a_step_KS)
    (Steps.refl t6b) h3 t6b_step_KH⟩

end OneColourClosure

#print axioms OneColourClosure.RaiseSSeqL.toSeq
#print axioms OneColourClosure.RaiseSSeqL.step_s
#print axioms OneColourClosure.RaiseSSeqL.cargoPath
#print axioms OneColourClosure.RaiseSSeqL.canRaiseS_head
#print axioms OneColourClosure.RaiseSSeqL.wf
#print axioms OneColourClosure.RaiseSSeqL.append
#print axioms OneColourClosure.canRaiseS_of_raiseSSeqL_head
#print axioms OneColourClosure.raiseSSeqL_step_of_canRaiseS
#print axioms OneColourClosure.canRaiseS_step_of_rank_ne_L
#print axioms OneColourClosure.RaiseSSeqL.canRaiseS_persist_of_rank_ne
#print axioms OneColourClosure.swap_of_licensed

#print axioms OneColourClosure.rank_lt_of_mem_of_lastOf
#print axioms OneColourClosure.not_mem_pileOfTop_of_rank_lt
#print axioms OneColourClosure.not_mem_pileOfTop_twin_of_rank_lt
#print axioms OneColourClosure.pileHolding_eq_of_agree
#print axioms OneColourClosure.pileOfTop_eq_of_agree
#print axioms OneColourClosure.nextUp_tabToFound_eq_of_low_rank
#print axioms OneColourClosure.freeCardS_tabToFound_eq_of_low_rank
#print axioms OneColourClosure.canRaiseS_inert_tabToFound_of_low_rank
#print axioms OneColourClosure.canRaiseS_inert_of_canRaiseStep
#print axioms OneColourClosure.urState_WF
#print axioms OneColourClosure.ur_step
#print axioms OneColourClosure.ur_not_canRaise
#print axioms OneColourClosure.ur_slide_canRaise
#print axioms OneColourClosure.ur_canRaiseS_after
#print axioms OneColourClosure.ur_not_canRaiseS
#print axioms OneColourClosure.unraise_probe_refutes
#print axioms OneColourClosure.canRaiseS_unraise_word
#print axioms OneColourClosure.canRaiseS_of_prefix_rank_gt
#print axioms OneColourClosure.RaiseSSeqL.drop_suffix
#print axioms OneColourClosure.canRaiseS_of_min_rank
#print axioms OneColourClosure.seatOf_tabToFound_of_seated_ne
#print axioms OneColourClosure.seatOf_cargoLeg_of_seated
#print axioms OneColourClosure.seatOf_cargoPath_of_seated
#print axioms OneColourClosure.seat_invariant_of_not_mem
#print axioms OneColourClosure.cover_must_be_raised
#print axioms OneColourClosure.cover_must_be_raised_L
#print axioms OneColourClosure.SortedPrefixLicence
#print axioms OneColourClosure.canRaise_lic
#print axioms OneColourClosure.t2_rankfront_L
#print axioms OneColourClosure.t3_two_L
#print axioms OneColourClosure.t5_two_L
#print axioms OneColourClosure.t5_two_L'
#print axioms OneColourClosure.t6_rankfront_L

#print axioms OneColourClosure.urR_twin
#print axioms OneColourClosure.ur_pileOfTop
#print axioms OneColourClosure.ur_nextUp
#print axioms OneColourClosure.ur_step_slide
#print axioms OneColourClosure.ur_slide_cargoLeg
