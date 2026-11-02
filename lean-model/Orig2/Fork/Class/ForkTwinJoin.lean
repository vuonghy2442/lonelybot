import Orig2.Fork.Class.ForkMeetCover
import Orig2.Fork.Class.ForkReadBracket
import Orig2.Fork.Split.ForkDrainClose

/-! ## Merged from `ForkRaiseOnly.lean` (2026-11-02) -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Orig2.ForkRaiseOnly — from a HIGH-raise-only path to the argmin step

This card isolates the raise-only reduction: if some prepared class-mate
`y` already has the LOW card `c` as a pile top and there is a HIGH-suit
raise-only play from `y` to a state with HIGH rung `B = rungAt s t`, then
the argmin step follows.  The remaining obligation is only to construct
that `y` and that raise-only play (the shortest-path parent is the current
candidate selector; see `FARM_MEMORY.md`).

Proved here:

* `HighRaiseOnly.rung_ne` — a HIGH-raise-only play changes no other rung.
* `HighRaiseOnly.canRaise` — it preserves `CanRaise · c` for `c` of the
  other twin suit (raising the same-colour twin never touches `c`).
* `argmin_step_of_raiseOnly` — the local step.
* `ArgminStepGameWF` / `argminStepGameWF_of_raiseOnly` — the WF-gated
  global form.  The source `ArgminStepGame` omits the `WF` hypotheses even
  though every application carries them; this card states the honest
  WF form and reduces it to the raise-only datum.

No `sorry`, no `Classical.choice`; the battery is at the tail.
-/

namespace TwinJoin

/-- A play all of whose letters are raises of suit `t`. -/
def HighRaiseOnly (t : Suit) (y y' : State) : Prop :=
  ∃ ρ, ShufflePlayW y ρ y' ∧
    ∀ m ∈ ρ, ∃ c : Card, m = Move.tabToFound c ∧ c.suit = t

/-- The raise-only datum sufficient for the Argmin step.

`y` is a class-mate of `s` where the LOW card `c` is already raisable and
the LOW rung is unchanged; a HIGH-raise-only play carries `HIGH` from
`rungAt y t` up to `rungAt s t`, and `c` stays raisable on the way. -/
def RaiseOnlyData (s : State) (t : Suit) (c : Card) : Prop :=
  ∃ y y', sameOrbitSetoid.r s y ∧
    rungAt y t.twin = rungAt s t.twin ∧
    rungAt y t ≤ rungAt s t ∧
    CanRaise y c ∧
    HighRaiseOnly t y y' ∧
    rungAt y' t = rungAt s t

/-- A HIGH-raise-only play leaves every other rung unchanged. -/
theorem HighRaiseOnly.rung_ne {t : Suit} {y y' : State}
    (h : HighRaiseOnly t y y') {σ : Suit} (hσ : σ ≠ t) :
    rungAt y' σ = rungAt y σ := by
  obtain ⟨ρ, hwalk, hletters⟩ := h
  revert hletters
  induction hwalk with
  | nil st => intro _; rfl
  | @cons st s1 W m ρ hrev hstep hrest ih =>
      intro hletters
      obtain ⟨d, hmd, hds⟩ := hletters m (by simp)
      subst hmd
      have hsu : d.suit ≠ σ := by
        intro hEq
        exact hσ (hEq.symm.trans hds)
      have hstep' : State.step st (Move.tabToFound d) = some s1 := hstep
      have hr : rungAt s1 σ = rungAt st σ := by
        rw [rungAt_tabToFound hstep' σ]
        exact ite_eq_right (fun hEq => hsu hEq.symm)
      rw [ih (fun m hm => hletters m (List.mem_cons_of_mem _ hm)), hr]

/-- A HIGH-raise-only play preserves `CanRaise · c` for a card `c` of the
other suit: the raised cards are same-coloured twins of `c`, so they cannot
be `c`, cannot top `c`'s pile, and the LOW foundation is untouched. -/
theorem HighRaiseOnly.canRaise {t : Suit} {y y' : State} {c : Card}
    (h : HighRaiseOnly t y y') (hywf : y.WF) (hct : c.suit ≠ t)
    (hc : CanRaise y c) : CanRaise y' c := by
  obtain ⟨ρ, hwalk, hletters⟩ := h
  revert hywf hc hletters
  induction hwalk with
  | nil st =>
      intro _ hc _
      exact hc
  | @cons st s1 W m ρ hrev hstep hrest ih =>
      intro hwf hcan hletters
      obtain ⟨d, hmd, hds⟩ := hletters m (by simp)
      subst hmd
      have hcd : d ≠ c := by
        intro hEq
        exact hct (by rw [← hEq]; exact hds)
      have hsu : d.suit ≠ c.suit := by
        intro hEq
        exact hct (hEq.symm.trans hds)
      have hcan1 : CanRaise s1 c :=
        R12.canRaise_survives_raise (z := c) (w := d) (st := st)
          hwf hstep hsu hcd hcan
      exact ih (step_wf hwf hstep) hcan1
        (fun m hm => hletters m (List.mem_cons_of_mem _ hm))

/-- **THE LOCAL REDUCTION.**  Raise-only data plus the LOW-card facts give
the `ArgminStepGame` conclusion. -/
theorem argmin_step_of_raiseOnly {s : State} {t : Suit} {c : Card}
    (hs : s.WF) (hdata : RaiseOnlyData s t c)
    (hcsu : c.suit = t.twin) :
    ∃ s'', sameOrbitSetoid.r s s'' ∧
      rungAt s'' t = rungAt s t ∧
      rungAt s'' t.twin = rungAt s t.twin + 1 := by
  obtain ⟨y, y', hcls_sy, hlowy, hhighle, hcan_y, hplay, hhighy'⟩ := hdata
  -- `y` is WF because it is reached from the WF state `s`
  have hywf : y.WF := by
    obtain ⟨σ, hσ, τ, hτ⟩ := hcls_sy
    exact SatDifferCensus.Walk_wf_end hτ hs
  -- HIGH and LOW are different suits
  have hne : c.suit ≠ t := by
    rw [hcsu]
    exact Suit.twin_ne t
  have hne' : t ≠ t.twin := fun h => Suit.twin_ne t h.symm
  -- the raise-only play preserves the LOW rung and the license at `c`
  have hreal : rungAt y' t.twin = rungAt y t.twin :=
    HighRaiseOnly.rung_ne hplay (σ := t.twin) (fun h => hne' h.symm)
  have hcan_y' : CanRaise y' c :=
    HighRaiseOnly.canRaise hplay hywf hne hcan_y
  -- `y'` is WF
  have hy'wf : y'.WF := by
    obtain ⟨ρ, hwalk, -⟩ := hplay
    exact SatDifferCensus.Walk_wf_end hwalk hywf
  -- fire the LOW raise at `y'`
  obtain ⟨s'', hstep⟩ := step_tabToFound_of_canRaise hcan_y'
  have hrev : reversibleAtW y' (Move.tabToFound c) :=
    DrainClose.reversibleAtW_tabToFound_of_canRaise hy'wf hcan_y'
  have hsingle : ShufflePlayW y' [Move.tabToFound c] s'' :=
    Walk.cons hrev hstep (Walk.nil s'')
  have hcls_y'y'' : sameOrbitSetoid.r y' s'' := by
    show RevEqW s'' y'
    exact RevEqW_symm (shufflePlayW_revEqW hsingle)
  have hcls_sy' : sameOrbitSetoid.r s y' := sameOrbitSetoid.trans hcls_sy
    (by
      show RevEqW y' y
      obtain ⟨ρ, hwalk, -⟩ := hplay
      exact RevEqW_symm (shufflePlayW_revEqW hwalk))
  refine ⟨s'', sameOrbitSetoid.trans hcls_sy' hcls_y'y'', ?_, ?_⟩
  · rw [rungAt_tabToFound hstep t]
    rw [ite_eq_right (fun hEq => hne hEq.symm), hhighy']
  · rw [rungAt_tabToFound hstep t.twin]
    rw [ite_eq_left hcsu.symm, hreal, hlowy]

/-- The WF-gated form of `ArgminStepGame`, exactly what the join reduction
uses (the source `ArgminStepGame` omits WF; all applications have it). -/
def ArgminStepGameWF : Prop :=
  ∀ (s s' : State) (t : Suit),
    s.WF → s'.WF → sameOrbitSetoid.r s s' →
    rungAt s t.twin ≤ rungAt s t →
    rungAt s t ≤ rungAt s' t →
    rungAt s t.twin < rungAt s' t.twin →
    ∃ s'', sameOrbitSetoid.r s s'' ∧
      rungAt s'' t = rungAt s t ∧
      rungAt s'' t.twin = rungAt s t.twin + 1

/-- **THE GLOBAL REDUCTION.**  If every eligible pair has a prepared
class-mate with a HIGH-raise-only path, then `ArgminStepGameWF` holds. -/
theorem argminStepGameWF_of_raiseOnly
    (h : ∀ (s s' : State) (t : Suit) (c : Card),
      s.WF → s'.WF → sameOrbitSetoid.r s s' →
      rungAt s t.twin ≤ rungAt s t →
      rungAt s t ≤ rungAt s' t →
      rungAt s t.twin < rungAt s' t.twin →
      c.suit = t.twin → c.rank.toIdx = rungAt s t.twin →
      RaiseOnlyData s t c) :
    ArgminStepGameWF := by
  intro s s' t hswf hs'wf hcls hlow hhigh hstrict
  have hk13 : rungAt s t.twin < 13 :=
    Nat.lt_of_lt_of_le hstrict (rungAt_le13 hs'wf t.twin)
  let c : Card :=
    { suit := t.twin, rank := FoundKit.Rk (rungAt s t.twin) }
  have hcsu : c.suit = t.twin := rfl
  have hcrank : c.rank.toIdx = rungAt s t.twin := by
    show (FoundKit.Rk (rungAt s t.twin)).toIdx = rungAt s t.twin
    exact FoundKit.Rk_toIdx _ hk13
  exact argmin_step_of_raiseOnly hswf
    (h s s' t c hswf hs'wf hcls hlow hhigh hstrict hcsu hcrank) hcsu

end TwinJoin

#print axioms TwinJoin.HighRaiseOnly.rung_ne
#print axioms TwinJoin.HighRaiseOnly.canRaise
#print axioms TwinJoin.argmin_step_of_raiseOnly
#print axioms TwinJoin.argminStepGameWF_of_raiseOnly



set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# TwinJoin - the sign-swap / dip / join formulation of T

This file states the theorem the campaign's T half is aiming at, without
claiming it.  The two pieces are:

* `DipExists` - the IVT: a twin-pair order flip on a play gives a dual dip.
  This is PROVABLE from the unit-step rung lemmas; it is stated here as a
  `def` so the open part is not confused with it.

* `TwinJoinOrForkTarget` - T: at the componentwise maximum of the twin-pair
  columns, either a class-mate joins both columns, or the class carries a
  `ForkWitness`.  This is OPEN.  The `3c` case (both covered) is inside the
  join disjunct: the join must be constructed there.

The `SignSwap` hypothesis is the *pairwise* order flip, NOT the crossed
endpoint values (`rungAt s t > rungAt s' t`, `rungAt s t.twin < rungAt s' t.twin`).
The crossed values are the trade-off (V); the sign swap is what the IVT needs.
-/

namespace TwinJoin

/-- The pairwise order flip on the twin pair `{t, t.twin}`: at one endpoint
`t` is at least its twin, at the other the reverse.  This is the IVT's
hypothesis, not the crossed/trade-off hypothesis. -/
def SignSwap (s s' : State) (t : Suit) : Prop :=
  (rungAt s t.twin ≤ rungAt s t ∧ rungAt s' t ≤ rungAt s' t.twin) ∨
  (rungAt s' t.twin ≤ rungAt s' t ∧ rungAt s t ≤ rungAt s t.twin)

/-- The join: a class-mate of `s` carrying both twin-pair columns at their
componentwise maximum. -/
def JoinAt (s s' s''' : State) (t : Suit) : Prop :=
  sameOrbitSetoid.r s s''' ∧
    rungAt s''' t = Nat.max (rungAt s t) (rungAt s' t) ∧
    rungAt s''' t.twin = Nat.max (rungAt s t.twin) (rungAt s' t.twin)

/-- `Dominates s s'`: `s` is at least `s'` on every rung coordinate.  In this
case the join is trivial: `s` itself is the componentwise maximum. -/
def Dominates (s s' : State) : Prop := ∀ σ : Suit, rungAt s' σ ≤ rungAt s σ

/-- If `s` dominates `s'`, `s` is the join. -/
theorem joinAt_self_of_dominates {s s' : State} {t : Suit}
    (h : Dominates s s') : JoinAt s s' s t := by
  refine ⟨RevEqW_refl s, ?_, ?_⟩
  · exact (Nat.max_eq_left (h t)).symm
  · exact (Nat.max_eq_left (h t.twin)).symm

/-- If `s'` dominates `s`, `s'` is the join (given the class relation). -/
theorem joinAt_other_of_dominates {s s' : State} {t : Suit}
    (hcls : sameOrbitSetoid.r s s') (h : Dominates s' s) :
    JoinAt s s' s' t := by
  refine ⟨hcls, ?_, ?_⟩
  · exact (Nat.max_eq_right (h t)).symm
  · exact (Nat.max_eq_right (h t.twin)).symm

/-- **THE DOMINATION CASE IS TRIVIAL.**  If one endpoint dominates the other
on every coordinate, the join is that endpoint. -/
theorem join_or_fork_of_dominates {s s' : State} {t : Suit}
    (hcls : sameOrbitSetoid.r s s') (h : Dominates s s' ∨ Dominates s' s) :
    (∃ s''', JoinAt s s' s''' t) ∨
    (∃ F x, sameOrbitSetoid.r s F ∧ ForkWitness F x) := by
  rcases h with h | h
  · exact Or.inl ⟨s, joinAt_self_of_dominates h⟩
  · exact Or.inl ⟨s', joinAt_other_of_dominates hcls h⟩

/-- The IVT conclusion on a fixed play: some prefix state has equal twin-pair
rungs.  `s.run (ρ.take i) = some x` names the prefix state. -/
def DipExists (s s' : State) (t : Suit) (ρ : List Move) : Prop :=
  ∃ (i : Nat) (x : State),
    s.run (ρ.take i) = some x ∧ rungAt x t = rungAt x t.twin

/-- **THE IVT STEP (provable).**  A sign swap on a play gives a dip.  The
proof is the unit-step integer walk on `d = rungAt · t - rungAt · t.twin`:
every letter changes one rung by at most 1, so `d` steps by `-1`, `0`, or `+1`
and cannot jump over zero.  Stated as a `def` so it is not mistaken for the
open content. -/
def DipLemma : Prop :=
  ∀ (s s' : State) (t : Suit) (ρ : List Move),
    s.WF →
    ShufflePlayW s ρ s' → SignSwap s s' t → DipExists s s' t ρ

/-- **THE TARGET (SATURATION-FREE).**  Two WF class-mates with a twin-pair
sign swap: either the componentwise maximum is joined by a class-mate, or the
class carries a fork witness.  NO `SSaturated` at either endpoint.  OPEN: the
`3c` case (both twins covered at the dip) lives inside the join disjunct. -/
def TwinJoinOrForkTarget : Prop :=
  ∀ (s s' : State) (t : Suit),
    s.WF → s'.WF → sameOrbitSetoid.r s s' →
    SignSwap s s' t →
    (∃ s''', JoinAt s s' s''' t) ∨
    (∃ F x, sameOrbitSetoid.r s F ∧ ForkWitness F x)

/-- The **overshoot join**: a class-mate whose twin-pair columns are at least
the componentwise maximum (not exactly equal to it).  This is the relaxation
that makes the overshoot case trivial. -/
def JoinAtLeast (s s' s''' : State) (t : Suit) : Prop :=
  sameOrbitSetoid.r s s''' ∧
    Nat.max (rungAt s t) (rungAt s' t) ≤ rungAt s''' t ∧
    Nat.max (rungAt s t.twin) (rungAt s' t.twin) ≤ rungAt s''' t.twin

/-- The exact join is an overshoot join. -/
theorem joinAt_imp_joinAtLeast {s s' s''' : State} {t : Suit}
    (h : JoinAt s s' s''' t) : JoinAtLeast s s' s''' t := by
  obtain ⟨horb, h1, h2⟩ := h
  refine ⟨horb, ?_, ?_⟩
  · rw [h1]; exact Nat.le_refl _
  · rw [h2]; exact Nat.le_refl _

/-- **THE OVERSHOOT CASE IS IMMEDIATE.**  If the dip level is already at least
both endpoint colour maxima, the dip itself is the overshoot join.  So the
bounded-dip lemma is not needed on this side. -/
theorem joinAtLeast_of_dip_above {s s' x : State} {t : Suit} {r : Nat}
    (hclass : sameOrbitSetoid.r s x)
    (hdip : rungAt x t = r ∧ rungAt x t.twin = r)
    (habove : Nat.max (rungAt s t) (rungAt s' t) ≤ r ∧
      Nat.max (rungAt s t.twin) (rungAt s' t.twin) ≤ r) :
    JoinAtLeast s s' x t := by
  refine ⟨hclass, ?_, ?_⟩
  · rw [hdip.1]; exact habove.1
  · rw [hdip.2]; exact habove.2

/-- **THE RELAXED TARGET.**  Sign swap ⇒ an overshoot join or a fork.  This is
weaker than `TwinJoinOrForkTarget` (the exact join), and it is what to prove
first: the dip-above-goal case is already a theorem, and the remaining case is
the dip below the goal. -/
def TwinJoinOrForkOvershoot : Prop :=
  ∀ (s s' : State) (t : Suit),
    s.WF → s'.WF → sameOrbitSetoid.r s s' →
    SignSwap s s' t →
    (∃ s''', JoinAtLeast s s' s''' t) ∨
    (∃ F x, sameOrbitSetoid.r s F ∧ ForkWitness F x)

/-- The exact target implies the relaxed one. -/
theorem overshoot_of_exact (h : TwinJoinOrForkTarget) : TwinJoinOrForkOvershoot := by
  intro s s' t hs hs' hcls hswap
  rcases h s s' t hs hs' hcls hswap with hjoin | hfork
  · obtain ⟨z, hz⟩ := hjoin
    exact Or.inl ⟨z, joinAt_imp_joinAtLeast hz⟩
  · exact Or.inr hfork

/-- **THE ARGMIN STEP (game level, strengthened).**  If the twin rung is the
lower (≤ the t rung), the target `s'` is at least the t rung and strictly above
the twin rung, then some class-mate raises the LOWER twin rung by one, keeping
the t rung unchanged.  This is the target-compatible step: it stays ≤ `s'` on
the colour.  The intended proof is `prepare_neutral` (prepare the twin's next
card with rung-neutral moves, then raise it).

OPEN — the AS probe is testing it. -/
def ArgminStepGame : Prop :=
  ∀ (s s' : State) (t : Suit),
    sameOrbitSetoid.r s s' →
    rungAt s t.twin ≤ rungAt s t →
    rungAt s t ≤ rungAt s' t →
    rungAt s t.twin < rungAt s' t.twin →
    ∃ s'', sameOrbitSetoid.r s s'' ∧
      rungAt s'' t = rungAt s t ∧
      rungAt s'' t.twin = rungAt s t.twin + 1

/-- **The join is symmetric under swapping the endpoints** (given the class
relation). -/
theorem joinAt_swap {s s' s''' : State} {t : Suit}
    (hcls : sameOrbitSetoid.r s s') (h : JoinAt s s' s''' t) :
    JoinAt s' s s''' t := by
  obtain ⟨horbit, h1, h2⟩ := h
  refine ⟨RevEqW_trans horbit (RevEqW_symm hcls), ?_, ?_⟩
  · calc
      rungAt s''' t = Nat.max (rungAt s t) (rungAt s' t) := h1
      _ = Nat.max (rungAt s' t) (rungAt s t) := by
        simpa using Nat.max_comm (rungAt s t) (rungAt s' t)
  · calc
      rungAt s''' t.twin = Nat.max (rungAt s t.twin) (rungAt s' t.twin) := h2
      _ = Nat.max (rungAt s' t.twin) (rungAt s t.twin) := by
        simpa using Nat.max_comm (rungAt s t.twin) (rungAt s' t.twin)

/-- The local engine at a dip, with the three cases explicit.  `CoveredStall`
is the `3c` residual, named here as a `Prop` over the dip state.  The target
above is the iterate-to-the-max of this step; the join branch of `3c` is what
must be built. -/
def CoveredStall (x : State) (c : Card) : Prop :=
  rungAt x c.suit = c.rank.toIdx ∧ rungAt x c.twin.suit = c.rank.toIdx ∧
    ¬ CanRaise x c ∧ ¬ CanRaise x c.twin

/-- The local step: at a dip where both twin suits sit at the rank of the
card `c`, either one level of join (raise `c` and `c.twin`), or a fork, or the
covered/covered stall.  OPEN only at the stall; 3a/3b are assembly of
`fork_exists_of_asymmetry` / the raise-both step. -/
def DipStepOrFork : Prop :=
  ∀ (x : State) (c : Card),
    x.WF →
    rungAt x c.suit = c.rank.toIdx ∧ rungAt x c.twin.suit = c.rank.toIdx →
    (∃ y, sameOrbitSetoid.r x y ∧
        rungAt y c.suit = c.rank.toIdx + 1 ∧
        rungAt y c.twin.suit = c.rank.toIdx + 1)
    ∨ (∃ F w, sameOrbitSetoid.r x F ∧ ForkWitness F w)
    ∨ CoveredStall x c

/-- The reduction: the local step plus termination of the climb gives the
target.  Termination is `rungAt ≤ 13` (the deck); the proof is an induction
on the remaining distance to the maximum.  This is the assembly, not the
open case. -/
def TargetOfStep : Prop :=
  DipStepOrFork → TwinJoinOrForkTarget

/-- Iterate the argmin step until `b`'s twin reaches `R`, keeping `b`'s high
suit at `H`.  `b` is the base (it already carries the high coordinate `H`), the
raised coordinate is `hs.twin` with target `R ≤ H`, and `z` is the upper
class-mate supplying the room. -/
theorem argmin_iterate
    (h : ArgminStepGame)
    {b z : State} {hs : Suit} {H R : Nat}
    (hcls : sameOrbitSetoid.r b z)
    (hH : rungAt b hs = H)
    (hle : rungAt b hs.twin ≤ R)
    (hRH : R ≤ H)
    (hroomH : H ≤ rungAt z hs)
    (hroomR : R ≤ rungAt z hs.twin) :
    ∃ c, sameOrbitSetoid.r b c ∧ rungAt c hs = H ∧
      rungAt c hs.twin = R := by
  have hmain : ∀ k, k ≤ R - rungAt b hs.twin →
      ∃ c, sameOrbitSetoid.r b c ∧ sameOrbitSetoid.r c z ∧
        rungAt c hs = H ∧
        rungAt c hs.twin = rungAt b hs.twin + k := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨b, RevEqW_refl b, hcls, hH, rfl⟩
    | succ k ih =>
        intro hk
        obtain ⟨c, hbc, hcz, hHc, htc⟩ := ih (Nat.le_of_succ_le hk)
        have hlt : rungAt c hs.twin < R := by
          rw [htc]; omega
        have h1 : rungAt c hs.twin ≤ rungAt c hs := by
          rw [hHc]; omega
        have h2 : rungAt c hs ≤ rungAt z hs := by
          rw [hHc]; exact hroomH
        have h3 : rungAt c hs.twin < rungAt z hs.twin := by omega
        obtain ⟨c', hcc', hHc', htc'⟩ := h c z hs hcz h1 h2 h3
        refine ⟨c', sameOrbitSetoid.trans hbc hcc', ?_, ?_, ?_⟩
        · exact sameOrbitSetoid.trans (sameOrbitSetoid.symm hcc') hcz
        · rw [hHc', hHc]
        · rw [htc', htc]; omega
  obtain ⟨c, hbc, -, hHc, htc⟩ := hmain (R - rungAt b hs.twin) (Nat.le_refl _)
  refine ⟨c, hbc, hHc, ?_⟩
  rw [htc]; omega

/-- **THE REDUCTION.**  Overshoot + argmin ⇒ exact join.  The base is the
endpoint carrying the LARGER of the two componentwise maxima; the argmin step
raises its other pair coordinate to its max, which is at most the base's fixed
high coordinate.  The overshoot class-mate `z` is used only as the room. -/
theorem target_of_overshoot_and_argmin
    (hover : TwinJoinOrForkOvershoot) (harg : ArgminStepGame) :
    TwinJoinOrForkTarget := by
  intro s s' t hs hs' hcls hswap
  rcases hover s s' t hs hs' hcls hswap with hz | hfork
  · obtain ⟨z, hcls_z, hz_t, hz_w⟩ := hz
    let Mt : Nat := Nat.max (rungAt s t) (rungAt s' t)
    let Mw : Nat := Nat.max (rungAt s t.twin) (rungAt s' t.twin)
    have hMt : Mt = Nat.max (rungAt s t) (rungAt s' t) := rfl
    have hMw : Mw = Nat.max (rungAt s t.twin) (rungAt s' t.twin) := rfl
    by_cases hcase : Mt ≤ Mw
    · -- the TWIN max is the larger; the high suit is t.twin, raised suit t
      by_cases hb : rungAt s' t.twin ≤ rungAt s t.twin
      · -- base s
        have hH : rungAt s (t.twin) = Mw := by
          rw [hMw]; exact (Nat.max_eq_left hb).symm
        have hle : rungAt s (t.twin).twin ≤ Mt := by
          rw [Suit.twin_twin]; exact Nat.le_max_left _ _
        have hroomH : Mw ≤ rungAt z (t.twin) := hz_w
        have hroomR : Mt ≤ rungAt z t := hz_t
        obtain ⟨c, hsc, hHc, hRc⟩ :=
          argmin_iterate (b := s) (z := z) (hs := t.twin) (H := Mw) (R := Mt)
            harg hcls_z hH hle hcase hroomH
            (by simpa [Suit.twin_twin] using hroomR)
        refine Or.inl ⟨c, hsc, ?_, ?_⟩
        · rw [show rungAt c t = Mt by simpa [Suit.twin_twin] using hRc, hMt]
        · rw [hHc, hMw]
      · -- base s'
        have hb' : rungAt s t.twin ≤ rungAt s' t.twin := Nat.le_of_not_ge hb
        have hH : rungAt s' (t.twin) = Mw := by
          rw [hMw]; exact (Nat.max_eq_right hb').symm
        have hle : rungAt s' (t.twin).twin ≤ Mt := by
          rw [Suit.twin_twin]; exact Nat.le_max_right _ _
        have hcls' : sameOrbitSetoid.r s' z :=
          sameOrbitSetoid.trans (sameOrbitSetoid.symm hcls) hcls_z
        have hroomH : Mw ≤ rungAt z (t.twin) := hz_w
        have hroomR : Mt ≤ rungAt z t := hz_t
        obtain ⟨c, hsc, hHc, hRc⟩ :=
          argmin_iterate (b := s') (z := z) (hs := t.twin) (H := Mw) (R := Mt)
            harg hcls' hH hle hcase hroomH
            (by simpa [Suit.twin_twin] using hroomR)
        refine Or.inl ⟨c, ?_, ?_, ?_⟩
        · exact sameOrbitSetoid.trans hcls hsc
        · rw [show rungAt c t = Mt by simpa [Suit.twin_twin] using hRc, hMt]
        · rw [hHc, hMw]
    · -- the T max is the larger; the high suit is t, the raised suit is t.twin
      have hMwlt : Mw < Mt := Nat.lt_of_not_ge hcase
      by_cases hb : rungAt s' t ≤ rungAt s t
      · -- base s
        have hH : rungAt s t = Mt := by
          rw [hMt]; exact (Nat.max_eq_left hb).symm
        have hle : rungAt s t.twin ≤ Mw := Nat.le_max_left _ _
        have hroomH : Mt ≤ rungAt z t := hz_t
        have hroomR : Mw ≤ rungAt z t.twin := hz_w
        obtain ⟨c, hsc, hHc, hRc⟩ :=
          argmin_iterate harg hcls_z hH hle (Nat.le_of_lt hMwlt) hroomH hroomR
        refine Or.inl ⟨c, hsc, ?_, ?_⟩
        · rw [hHc, hMt]
        · rw [hRc, hMw]
      · -- base s'
        have hb' : rungAt s t ≤ rungAt s' t := Nat.le_of_not_ge hb
        have hH : rungAt s' t = Mt := by
          rw [hMt]; exact (Nat.max_eq_right hb').symm
        have hle : rungAt s' t.twin ≤ Mw := Nat.le_max_right _ _
        have hcls' : sameOrbitSetoid.r s' z :=
          sameOrbitSetoid.trans (sameOrbitSetoid.symm hcls) hcls_z
        have hroomH : Mt ≤ rungAt z t := hz_t
        have hroomR : Mw ≤ rungAt z t.twin := hz_w
        obtain ⟨c, hsc, hHc, hRc⟩ :=
          argmin_iterate harg hcls' hH hle (Nat.le_of_lt hMwlt) hroomH hroomR
        refine Or.inl ⟨c, ?_, ?_, ?_⟩
        · exact sameOrbitSetoid.trans hcls hsc
        · rw [hHc, hMt]
        · rw [hRc, hMw]
  · exact Or.inr hfork

end TwinJoin
