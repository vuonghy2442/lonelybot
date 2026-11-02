import Orig2.Fork.CrossSuit.ForkCrossSuit
import Orig2.Fork.Local.ForkDirect
import Orig2.Fork.Split.FirstPassage
import Orig2.Fork.CrossSuit.ForkCrossSuitPure

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkFibreCorridor — the fibre graph of the cross-suit corridor

Scratch card.  READ-ONLY on `Orig2/`; no source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; axiom battery at the tail.

## The lens

A free letter (`draw` or `tabToTab`) does not touch the foundation, so the
interior `γ` of a free corridor

```text
raise c ; (free letters) ; pull d
```

lies inside ONE cargo fibre (`BareCargoEquiv` class) — the states with a fixed
foundation vector, connected by reversible `tabToTab` moves.  A cross-suit
corridor is therefore the two-edge pattern

```text
F₀ --raise c--> F --(free path inside F)--> --pull d--> F₁
```

in the fibre graph.  `Temp/Fibre_Report.md` builds that graph for the 13 census
boards and measures it; this card proves the structural rows the measurement
turns on.

## What this card proves (all kernel-checked)

* **§1 A PULL NEVER LANDS AT A SATURATED STATE.**  The pull's own card is
  raisable at the landing (`ValleyStep.pull_card_canRaise`), so the landing is
  `¬ SSaturated`.  Consequence for the fibre graph: **no pull edge enters a
  `SAT` fibre** (`no_sat_member_of_pull_landing`).  With `SSaturated` being a
  `BareCargoEquiv` invariant (`ssaturated_bareCargo_iff`), `SAT` fibres are
  pull-sinks-free / raise-source-free corners of the fibre graph.

* **§2 A SATURATED STATE HAS NO (REVERSIBLE) RAISE.**  `ssaturated_no_raise`:
  a reversible `raise c` at a saturated `WF` state is impossible — hence **no
  raise edge leaves a `SAT` fibre**.  Play-level corollaries: a witness play
  out of a saturated state cannot *start* with a raise
  (`saturated_play_head_ne_raise`) and one into a saturated state cannot *end*
  with a pull (`saturated_play_last_ne_pull`).

  Together §1–§2 are the exact SAT-anchoring the fibre graph has: the literal
  pattern `SAT --raise--> F --pull--> SAT` of the brief is impossible, but
  *degenerately* — each of its two half-edges is already impossible at `SAT`,
  so this says nothing about the corridor, whose raise and pull sit at a
  middle fibre.

* **§3 THE FREE CORRIDOR'S SUIT IS THE CARD.**  In a free corridor, if the
  pull's suit is the raise's suit then the pull is exactly the raised card
  (`free_corridor_same_suit_eq`).  Hence for a free interior

  ```text
  c.suit ≠ d.suit  ↔  d ≠ c,
  ```

  i.e. **every free corridor that does not cancel is cross-suit**, and the
  same-suit free corridors are exactly the same-card relocations.  At the
  fibre level this is the measured invariant `Cin(F) = Cout(F)`: a fibre's
  boundary has at most one card per suit (the foundation has one top per
  suit), so "cross-suit" is *not* extra content on a free corridor.

  §4 packages this as an equivalence of residuals:
  `CrossSuitFreeCorridorResidual ↔ FreeCorridorCancels`, where
  `FreeCorridorCancels` says a minimal `SSaturated`→`SSaturated` play never has
  a free `raise c ; … ; pull d` with `d ≠ c`.

* **§5 FLAG (measurement, `Temp/Fibre_Report.md`).**  The fibre graph has *no*
  cross-suit restriction: every raise edge of the witness graph has an inverse
  pull edge on the same card (`Cin(F) = Cout(F)` was exact on 6155/6155 edges
  of the 13-board census), so cross-suit 2-edge patterns are exactly the
  distinct boundary-card pairs, and they are abundant (1658 in the census,
  including through `SAT` fibres).  So the fibre lens does **not** close the
  saturation discriminator; this card records the fibre-level facts that
  survive, not a route to `crossSuitVacuity`.
-/

namespace Fibre

open ValleyElim

/-!
## §1. A pull never lands saturated
-/

/-- **THE PULL'S CARD IS RAISABLE AT THE LANDING, so the landing is not
saturated.**  (`ValleyStep.pull_card_canRaise` is the licence.) -/
theorem pull_landing_not_saturated {A B : State} {c : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab c b) = some B) :
    ¬ SSaturated B := by
  intro hsat
  exact hsat c (CanRaiseS.now c (ValleyStep.pull_card_canRaise hA hstep))

/-- **NO `SAT` FIBRE AT A PULL'S LANDING.**  The landing's whole
`BareCargoEquiv` class is unsaturated: no pull edge of the fibre graph enters a
`SAT` fibre. -/
theorem no_sat_member_of_pull_landing {A B B' : State} {c : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab c b) = some B)
    (hbc : BareCargoEquiv B B') : ¬ SSaturated B' := by
  intro hs
  exact pull_landing_not_saturated hA hstep ((ssaturated_bareCargo_iff hbc).mpr hs)

/-- The same at the state level, for a witness pull ending at a saturated
state: impossible.  (The `WF` of the pull's origin is all the licence needs.) -/
theorem pull_not_into_saturated {A B : State} {c : Card} {b : Base}
    (hA : A.WF) (hstep : State.step A (Move.foundToTab c b) = some B)
    (hsat : SSaturated B) : False :=
  pull_landing_not_saturated hA hstep hsat

/-!
## §2. A saturated state has no reversible raise
-/

/-- **THE REVERSIBILITY ORACLE READS `CanRaise`.**  A reversible raise at a
`WF` state is vanilla-raisable there. -/
theorem canRaise_of_reversible_raise {F : State} {d : Card} (hF : F.WF)
    (hrev : reversibleAtW F (Move.tabToFound d)) : CanRaise F d :=
  SatDifferCensus.canRaise_of_tabToFoundR
    ((tabToFoundR_iff_reversibleAtW hF d).mpr hrev)

/-- **NO REVERSIBLE RAISE AT A SATURATED STATE.**  Hence no raise edge leaves a
`SAT` fibre: `SSaturated` is exactly `∀ c, ¬ CanRaiseS`, and a reversible raise
already licenses its own card. -/
theorem ssaturated_no_raise {F : State} (hF : F.WF) (hsat : SSaturated F)
    (c : Card) (hrev : reversibleAtW F (Move.tabToFound c)) : False :=
  hsat c (CanRaiseS.now c (canRaise_of_reversible_raise hF hrev))

/-- **A WITNESS PLAY OUT OF A SATURATED STATE DOES NOT START WITH A RAISE.** -/
theorem saturated_play_head_ne_raise {u v : State} {c : Card} {ρ : List Move}
    (hplay : ShufflePlayW u (Move.tabToFound c :: ρ) v)
    (huwf : u.WF) (hsat : SSaturated u) : False := by
  cases hplay with
  | cons hrev _ _ => exact ssaturated_no_raise huwf hsat c hrev

/-- **A WITNESS PLAY INTO A SATURATED STATE DOES NOT END WITH A PULL.** -/
theorem saturated_play_last_ne_pull {u v : State} {ρ : List Move} {c : Card}
    {b : Base}
    (hplay : ShufflePlayW u (ρ ++ [Move.foundToTab c b]) v)
    (huwf : u.WF) (hsat : SSaturated v) : False := by
  obtain ⟨F, hpre, hlast⟩ :=
    ValleyElim.ShufflePlayW_split hplay ρ [Move.foundToTab c b] rfl
  have hF : F.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  cases hlast with
  | cons _ hstep hrest =>
      cases hrest
      exact pull_not_into_saturated hF hstep hsat

/-!
## §3. In a free corridor the pull's suit is the raise's card
-/

/-- **FREE CORRIDOR, SAME SUIT ⟹ SAME CARD.**  The free interior cannot change
the pull's column (`foundTop_eq_of_avoids`), the raise made `c` that column's
top (`BaseEn.foundTop_raiseSt_self`), and the pull reads `d` off it
(`step_foundToTab_inv`).  Hence `d = c`.

This is the fibre-graph statement `Cin(F) = Cout(F)` at one corridor: the
boundary of a fibre carries one card per suit, so a free corridor that changes
the suit is exactly one that changes the card. -/
theorem free_corridor_same_suit_eq {u v : State} {pre γ tail : List Move}
    {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v)
    (hfree : CrossSuit.FreeOnly γ) (hsu : c.suit = d.suit) : d = c := by
  obtain ⟨A, -, hrest⟩ := ValleyElim.ShufflePlayW_split hplay pre
    (Move.tabToFound c :: γ ++ Move.foundToTab d b :: tail)
    (by simp only [List.append_assoc])
  obtain ⟨T, -, hstep, htail⟩ := Bubble.walk_cons_inv hrest
  obtain ⟨-, a, -, hs1⟩ := step_tabToFound_inv hstep
  have hT : T = raiseSt A c a := by rw [hs1]; rfl
  rw [hT] at htail
  obtain ⟨P, hγ, hrest2⟩ :=
    ValleyElim.ShufflePlayW_split htail γ (Move.foundToTab d b :: tail) rfl
  cases hrest2 with
  | cons _ hstepP _ =>
      obtain ⟨d', htop, hd', -, -⟩ := step_foundToTab_inv hstepP
      rw [hd'] at htop
      have htr : P.foundTop d.suit = (raiseSt A c a).foundTop d.suit :=
        CrossSuit.foundTop_eq_of_avoids hγ (CrossSuit.freeOnly_avoids hfree)
      have hsrc : (raiseSt A c a).foundTop d.suit = some c := by
        rw [← hsu]
        exact BaseEn.foundTop_raiseSt_self A c a
      have hsome : some d = some c := by rw [← htop, htr, hsrc]
      exact Option.some.inj hsome

/-- **A FREE CORRIDOR THAT DOES NOT CANCEL IS CROSS-SUIT.**  Contrapositive of
§3: in a free corridor, `d ≠ c` already gives `c.suit ≠ d.suit`.  So the
`c.suit ≠ d.suit` hypothesis of the free-corridor residual is not extra
strength — it is the "not a same-card relocation" gate. -/
theorem free_corridor_suit_ne_of_card_ne {u v : State} {pre γ tail : List Move}
    {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v)
    (hfree : CrossSuit.FreeOnly γ) (hcd : d ≠ c) : c.suit ≠ d.suit := by
  intro hsu
  exact hcd (free_corridor_same_suit_eq hplay hfree hsu)

/-- The `iff` form: on a free corridor, "cross-suit" **is** "different card". -/
theorem free_corridor_crossSuit_iff_card_ne {u v : State} {pre γ tail : List Move}
    {c d : Card} {b : Base}
    (hplay : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v)
    (hfree : CrossSuit.FreeOnly γ) : (c.suit ≠ d.suit ↔ d ≠ c) :=
  ⟨fun hne hdc => hne (by rw [hdc]),
   fun hcd => free_corridor_suit_ne_of_card_ne hplay hfree hcd⟩

/-!
## §4. The residuals are the same statement
-/

/-- **`FreeCorridorCancels`** — the fibre-level reading of the free-corridor
residual: a minimal `SSaturated`→`SSaturated` play never has a free corridor
`raise c ; (free) ; pull d` that does not pull back the card it raised. -/
def FreeCorridorCancels : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ρ = (pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail →
    CrossSuit.FreeOnly γ → d ≠ c → False

/-- **THE CAMPAIGN'S FREE RESIDUAL IS THE CANCELLATION RESIDUAL.**  §3 turns
`d ≠ c` into `c.suit ≠ d.suit` and back, so the cross-suit phrasing of the
free corridor carries no extra content. -/
theorem crossSuitFreeResidual_iff_freeCorridorCancels :
    CrossSuit.CrossSuitFreeCorridorResidual ↔ FreeCorridorCancels := by
  constructor
  · intro hX u v ρ pre γ tail c d b hwf hu hv hplay hmin heq hfree hdc
    exact hX u v ρ pre γ tail c d b hwf hu hv hplay hmin heq
      (free_corridor_suit_ne_of_card_ne (heq ▸ hplay) hfree hdc) hfree
  · intro hN u v ρ pre γ tail c d b hwf hu hv hplay hmin heq hne hfree
    exact hN u v ρ pre γ tail c d b hwf hu hv hplay hmin heq hfree
      (fun hdc => hne (by rw [hdc]))

end Fibre

/-! ## §5. Axiom battery -/

#print axioms Fibre.pull_landing_not_saturated
#print axioms Fibre.no_sat_member_of_pull_landing
#print axioms Fibre.pull_not_into_saturated
#print axioms Fibre.canRaise_of_reversible_raise
#print axioms Fibre.ssaturated_no_raise
#print axioms Fibre.saturated_play_head_ne_raise
#print axioms Fibre.saturated_play_last_ne_pull
#print axioms Fibre.free_corridor_same_suit_eq
#print axioms Fibre.free_corridor_suit_ne_of_card_ne
#print axioms Fibre.free_corridor_crossSuit_iff_card_ne
#print axioms Fibre.crossSuitFreeResidual_iff_freeCorridorCancels
