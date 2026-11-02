import Orig2.Fork.ForkTwinJoin
import Orig2.Fork.ForkReadBracket
import Orig2.Fork.ForkDrainClose

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

