import Orig2.StratifiedQuotient
import Orig2.FreeOrbit
import Orig2.OrbitFactor

/-!
# Orig2.Position - THE GAME-POSITION QUOTIENT (the grid card)

THE MISSION (the owner's grid program, opened 2026-10-31): quotient
the game by the free-card orbit campaign's invariant.  The campaign
certified that the S-license is an (orbit, rung-tuple) invariant
(`canRaiseS_orbit_rung`, `Orig2/FreeOrbit.lean` par.5): at equal
rungs, orbit-mates share every card's license - the possible
`tabToFound` moves cannot tell them apart.  This card makes that
literal.

THE SHAPE: the game fibers over the four-dimensional rung grid.
Within a fiber, the reversible moves are the quotient's own glue -
they vanish; the raises are the grid's deterministic edges (+e_suit),
the pulls their mirrors (-e_suit).  Because raises are reversible,
orbits CROSS rungs - so the position is the MEET of the macro class
and the ledger: orbit-mates at equal rungs.

* **par.1-2 THE SETOID AND THE QUOTIENT** - `RungEq`, `WFState`,
`orbitRungSetoid`, and `Position` live in the vocabulary registry
(`Orig2/Vocab.lean`), moved there per the owner's ruling of
2026-10-31; this card consumes them and owns the descended maps.
* **par.3 THE DESCENT** - `rungsOf`, `foundsOf`, and `spec` (the
license spectrum: the possible `tabToFound` moves as a
position-function - the campaign theorem's respect proof), with its
flat probe `specB`.
* **par.4 THE SOUNDNESS** - the spectrum can't tell representatives
apart (`spec_sound`, via `Quotient.sound`); the probe reads the
spectrum (`specB_iff`).
* **par.9 THE BATTERY**.

THE NEXT SITTINGS: the rung-step arithmetic (raise +e_suit, pull
-e_suit, free moves 0), the free moves' vanishing, and the raise's
class-determinism (the pull-back + orbit-walk + raise concatenation)
- then the residue campaign runs on the grid.
-/

/-! ## par.1. The setoid (in the registry) -/

/- `RungEq`, `WFState`, `orbitRungSetoid`, and `Position` live in the
vocabulary registry (`Orig2/Vocab.lean`), moved there from this card
per the owner's ruling of 2026-10-31 (`WFState` promoted from
`Orig2/StratifiedQuotient.lean` in the same move).  This card owns
the descended maps and the grid rows. -/

/-! ## par.3. The descent -/

/-- Bool equality from iff-of-true (the flat-probe bridge). -/
private theorem bool_eq_of_iff_true {a b : Bool} (h : (a = true) ↔ (b = true)) :
    a = b := by
  cases a with
  | false =>
      cases b with
      | false => rfl
      | true => exact h.mpr rfl
  | true =>
      cases b with
      | false => exact (h.mp rfl).symm
      | true => rfl

/-- **rungsOf** - the grid coordinate: the position's rung vector
(every suit's founded count).  The respect is the meet's ledger
component. -/
def rungsOf : Position → Suit → Nat :=
  Quotient.lift (fun p σ => rungAt p.1 σ) (fun _ _ h => funext h.2)

/-- **foundsOf** - the foundations: equal rungs force equal founds
(the take-prefix discipline, `found_congr_of_rungs`). -/
def foundsOf : Position → Suit → List Card :=
  Quotient.lift (fun p => p.1.found)
    (fun p p' h => funext fun σ => found_congr_of_rungs p.2 p'.2 (h.2 σ))

/-- **spec** - THE LICENSE SPECTRUM: the possible `tabToFound` moves
as a function of the position.  The respect proof IS the campaign's
theorem (`canRaiseS_orbit_rung`), descended through `propext`. -/
def spec : Position → Card → Prop :=
  Quotient.lift (fun p c => CanRaiseS p.1 c)
    (fun p _p' h => funext fun _c => propext (canRaiseS_orbit_rung p.2 h.1 h.2))

/-- **specB** - the spectrum's flat probe: the campaign's decidable
checker, descended. -/
def specB : Position → Card → Bool :=
  Quotient.lift (fun p => canRaiseSB p.1)
    (fun p p' h => funext fun _c =>
      bool_eq_of_iff_true (by
        rw [canRaiseSB_iff p.2, canRaiseSB_iff p'.2]
        exact canRaiseS_orbit_rung p.2 h.1 h.2))

/-! ## par.4. The soundness -/

/-- The spectrum reads any representative's license (the lift's
defining equation). -/
theorem spec_mk (p : WFState) (c : Card) :
    spec (Quotient.mk orbitRungSetoid p) c ↔ CanRaiseS p.1 c := Iff.rfl

/-- The flat probe reads any representative's computation. -/
theorem specB_mk (p : WFState) (c : Card) :
    specB (Quotient.mk orbitRungSetoid p) c = canRaiseSB p.1 c := rfl

/-- The rung vector reads any representative's rungs. -/
theorem rungsOf_mk (p : WFState) (σ : Suit) :
    rungsOf (Quotient.mk orbitRungSetoid p) σ = rungAt p.1 σ := rfl

/-- The foundations read any representative's founds. -/
theorem foundsOf_mk (p : WFState) (σ : Suit) :
    foundsOf (Quotient.mk orbitRungSetoid p) σ = p.1.found σ := rfl

/-- **THE SPECTRUM CAN'T TELL REPRESENTATIVES APART** - the possible
`tabToFound` moves are a function of the position: the campaign's
theorem, now as the quotient's soundness. -/
theorem spec_sound {p p' : WFState} (h : orbitRungSetoid.r p p') (c : Card) :
    spec (Quotient.mk orbitRungSetoid p) c ↔
      spec (Quotient.mk orbitRungSetoid p') c := by
  rw [Quotient.sound h]

/-- The flat probe computes the spectrum. -/
theorem specB_iff {q : Position} {c : Card} :
    specB q c = true ↔ spec q c := by
  refine Quotient.inductionOn q (fun p => ?_)
  rw [specB_mk, spec_mk]
  exact canRaiseSB_iff p.2

/-! ## par.5. The rung-step arithmetic -/

/-- **THE RAISE CLIMBS ONE RUNG** - a `tabToFound` step raises the
played suit's rung by exactly one and fixes every other suit: the
grid's deterministic forward edge (+e_suit). -/
theorem rungAt_tabToFound {u v : State} {c : Card}
    (hstep : State.step u (Move.tabToFound c) = some v) (σ : Suit) :
    rungAt v σ = if σ = c.suit then rungAt u σ + 1 else rungAt u σ := by
  obtain ⟨-, a, -, hv⟩ := step_tabToFound_inv hstep
  have hfv : v.found σ = if σ = c.suit then u.found c.suit ++ [c] else u.found σ := by
    rw [hv]; rfl
  by_cases hσ : σ = c.suit
  · subst hσ
    unfold rungAt
    rw [hfv, if_pos rfl, if_pos rfl]
    simp [List.length_append]
  · unfold rungAt
    rw [hfv, if_neg hσ, if_neg hσ]

/-- **THE PULL DESCENDS ONE RUNG** - a `foundToTab` step lowers the
pulled suit's rung by exactly one and fixes every other suit: the
raise's mirror edge (-e_suit). -/
theorem rungAt_foundToTab {u v : State} {c : Card} {b : Base}
    (hstep : State.step u (Move.foundToTab c b) = some v) (σ : Suit) :
    rungAt v σ = if σ = c.suit then rungAt u σ - 1 else rungAt u σ := by
  obtain ⟨c', hft, hc', -, hv⟩ := step_foundToTab_inv hstep
  rw [hc'] at hft
  have hlast : lastOf (u.found c.suit) = some c := hft
  have hcl : (chop (u.found c.suit)).length + 1 = (u.found c.suit).length := by
    have hlen := congrArg List.length (lastOf_chop hlast)
    rw [List.length_append] at hlen
    simp at hlen
    exact hlen.symm
  have hfv : v.found σ = if σ = c.suit then chop (u.found c.suit) else u.found σ := by
    rw [hv, putCard_found]; rfl
  by_cases hσ : σ = c.suit
  · subst hσ
    unfold rungAt
    rw [hfv, if_pos rfl, if_pos rfl]
    omega
  · unfold rungAt
    rw [hfv, if_neg hσ, if_neg hσ]

/-- **THE DRAW HOLDS THE LEDGER** - the draw letter moves only stock
and waste: every rung is fixed. -/
theorem rungAt_draw {u v : State}
    (hstep : State.step u Move.draw = some v) (σ : Suit) :
    rungAt v σ = rungAt u σ := by
  have hff : foundsFixed u v := (chart_draw hstep).2.1
  simp only [rungAt]
  rw [hff σ]

/-- **THE SLIDE HOLDS THE LEDGER** - a tableau slide moves only
piles: every rung is fixed. -/
theorem rungAt_tabToTab {u v : State} {c : Card} {b : Base}
    (hstep : State.step u (Move.tabToTab c b) = some v) (σ : Suit) :
    rungAt v σ = rungAt u σ := by
  obtain ⟨a, -, -, -, hv⟩ := step_tabToTab_inv hstep
  simp only [rungAt]
  rw [hv, putRun_found, setPile_found]

/-- **THE WASTE PLACEMENT HOLDS THE LEDGER** - moving the waste top
to the tableau moves only piles and waste: every rung is fixed. -/
theorem rungAt_wasteToTab {u v : State} {c : Card} {b : Base}
    (hstep : State.step u (Move.wasteToTab c b) = some v) (σ : Suit) :
    rungAt v σ = rungAt u σ := by
  obtain ⟨-, x, xs, -, hv⟩ := step_wasteToTab_inv hstep
  have hfv : v.found σ = (u.putCard c b).found σ := by rw [hv]
  simp only [rungAt]
  rw [hfv, putCard_found]

/-- **pullSpec q c** - the pullable cards at a position: `c` tops
its suit's foundation.  The `foundToTab` moves counted by card - the
destination sensitivity (`canPlace`) is quotiented away, exactly as
the raise's moves are counted by the license spectrum (the move
signature `tabToFound c` carries no destination; `foundToTab c b`
does, so only its card-set descends).  Defined directly from the
descended founds: no lift needed. -/
def pullSpec (q : Position) (c : Card) : Prop :=
  lastOf (foundsOf q c.suit) = some c

/-- The pullable cards read any representative's found tops. -/
theorem pullSpec_mk (p : WFState) (c : Card) :
    pullSpec (Quotient.mk orbitRungSetoid p) c ↔ p.1.foundTop c.suit = some c :=
  Iff.rfl

/-! ## par.7. The pull's base-independence -/

/-- THE SINGLE-CARD LANDING IS THE SINGLETON-RUN LANDING: the pull's
letter and the slide's letter write the same pile.  The base-independence
route's vocabulary bridge (the pull at any base lands in the same
position class and the same `BareCargoEquiv` class: the two pulls are
joined by the slide of the pulled card from one landing to the other,
`bareCargo_of_slide` + `bareCargo_sameOrbit` then carry both classes). -/
private theorem putCard_eq_putRun (st : State) (c : Card) (b : Base) :
    st.putCard c b = st.putRun [c] b := by
  cases b with
  | inl a => rfl
  | inr z => cases hz : st.pileOfTop z <;> rfl

/-- The inl-landing locality: away from the landing pile, the pull's
target piles are the source's. -/
private theorem pull_piles_inl_ne {u v : State} {c : Card} {a₁ k : Anchor}
    (hstep : State.step u (Move.foundToTab c (Sum.inl a₁)) = some v) (hne : k ≠ a₁) :
    v.piles k = u.piles k := by
  obtain ⟨-, -, -, -, hv⟩ := step_foundToTab_inv hstep
  rw [hv, putCard_eq_putRun, putRun_piles_inl_ne _ _ _ _ hne]
  rfl

/-- The inr-landing locality: away from the landing pile, the pull's
target piles are the source's. -/
private theorem pull_piles_inr_ne {u v : State} {c z₁ : Card} {k₁ k : Anchor}
    (hstep : State.step u (Move.foundToTab c (Sum.inr z₁)) = some v)
    (hpt : u.pileOfTop z₁ = some k₁) (hne : k ≠ k₁) :
    v.piles k = u.piles k := by
  obtain ⟨-, -, -, -, hv⟩ := step_foundToTab_inv hstep
  have hpt' : (u.setFound c.suit (chop (u.found c.suit))).pileOfTop z₁ = some k₁ := hpt
  rw [hv, putCard_eq_putRun,
    putRun_piles_inr_ne (u.setFound c.suit (chop (u.found c.suit))) [c] z₁ k₁ hpt' hne]
  rfl

/-- The inr-fit's guard: the base card is a located pile top, and
the fit is the card arithmetic. -/
private theorem canPlace_inr_guard {S : State} {c z : Card}
    (h : S.canPlace c (Sum.inr z) = true) :
    ∃ k, S.pileOfTop z = some k ∧ canSitOn c z = true := by
  simp only [State.canPlace] at h
  cases hpt : S.pileOfTop z with
  | none => rw [hpt] at h; exact absurd h (by simp)
  | some k => rw [hpt] at h; exact ⟨k, rfl, h⟩

/-- **THE FIT SURVIVES THE LANDING** - after pulling `c` onto `b₁`,
the fit for a different base `b₂` (which held at the source) still
holds at the target: the landing writes one pile, the fit reads the
target pile. -/
private theorem canPlace_pull {u v : State} {c : Card} {b₁ b₂ : Base}
    (hwf : u.WF) (hwfv : v.WF)
    (hstep : State.step u (Move.foundToTab c b₁) = some v)
    (h₁ : u.canPlace c b₁ = true) (h₂ : u.canPlace c b₂ = true)
    (hne : b₁ ≠ b₂) : v.canPlace c b₂ = true := by
  cases b₁ with
  | inl a₁ =>
      have h1g := canPlace_inl h₁
      cases b₂ with
      | inl a₂ =>
          have hae : a₁ ≠ a₂ := fun h => hne (by rw [h])
          have hloc : v.piles a₂ = u.piles a₂ :=
            pull_piles_inl_ne hstep (fun hcon => hae hcon.symm)
          simp only [State.canPlace]
          rw [hloc]
          exact h₂
      | inr z₂ =>
          obtain ⟨k₂, hpt₂, hfit⟩ := canPlace_inr_guard h₂
          have hk₂ : k₂ ≠ a₁ := by
            intro hcon
            have hmem : z₂ ∈ (u.piles a₁).faceUp :=
              lastOf_mem (show lastOf (u.piles a₁).faceUp = some z₂ from
                (pileOfTop_eq_some_iff hwf).mp (by rw [← hcon]; exact hpt₂))
            rw [Pile.isEmpty_eq_false_of_mem hmem] at h1g
            exact Bool.noConfusion h1g.1
          have hvpt : v.pileOfTop z₂ = some k₂ := by
            refine (pileOfTop_eq_some_iff hwfv).2 ?_
            rw [pull_piles_inl_ne hstep hk₂]
            exact (pileOfTop_eq_some_iff hwf).mp hpt₂
          simp only [State.canPlace]
          rw [hvpt]
          exact hfit
  | inr z₁ =>
      obtain ⟨k₁, hpt₁, -⟩ := canPlace_inr_guard h₁
      cases b₂ with
      | inl a₂ =>
          have h2g := canPlace_inl h₂
          have hak : a₂ ≠ k₁ := by
            intro hcon
            have hmem : z₁ ∈ (u.piles a₂).faceUp :=
              lastOf_mem (show lastOf (u.piles a₂).faceUp = some z₁ from
                (pileOfTop_eq_some_iff hwf).mp (by rw [hcon]; exact hpt₁))
            rw [Pile.isEmpty_eq_false_of_mem hmem] at h2g
            exact Bool.noConfusion h2g.1
          simp only [State.canPlace]
          rw [pull_piles_inr_ne hstep hpt₁ hak]
          exact h₂
      | inr z₂ =>
          obtain ⟨k₂, hpt₂, hfit⟩ := canPlace_inr_guard h₂
          have hkk : k₂ ≠ k₁ := by
            intro hcon
            have ht1 : (u.piles k₁).top = some z₁ := (pileOfTop_eq_some_iff hwf).mp hpt₁
            have ht2 : (u.piles k₂).top = some z₂ := (pileOfTop_eq_some_iff hwf).mp hpt₂
            rw [hcon] at ht2
            exact hne (by rw [Option.some.inj (ht1.symm.trans ht2)])
          have hvpt : v.pileOfTop z₂ = some k₂ := by
            refine (pileOfTop_eq_some_iff hwfv).2 ?_
            rw [pull_piles_inr_ne hstep hpt₁ hkk]
            exact (pileOfTop_eq_some_iff hwf).mp hpt₂
          simp only [State.canPlace]
          rw [hvpt]
          exact hfit

/-- The appended-top landing reading: the below-part of a run whose
top is an appended `c` (with `c` absent below) is the old run. -/
private theorem below_append_notmem {c : Card} : ∀ {old : List Card},
    c ∉ old → below c (old ++ [c]) = old := by
  intro old
  induction old with
  | nil => intro _; show below c [c] = []; rw [below_cons, if_pos rfl]
  | cons x t ih =>
      intro hnc
      rw [List.cons_append, below_cons,
        if_neg (fun (hcon : x = c) => hnc (List.mem_cons.mpr (Or.inl hcon.symm)))]
      exact congrArg (List.cons x) (ih (fun hcon => hnc (List.mem_cons.mpr (Or.inr hcon))))

/-- The appended-top landing reading: the fromCard of a run whose
top is an appended `c` (with `c` absent below) is the singleton. -/
private theorem fromCard_append_notmem {c : Card} : ∀ {old : List Card},
    c ∉ old → fromCard c (old ++ [c]) = [c] := by
  intro old
  induction old with
  | nil => intro _; show fromCard c [c] = [c]; rw [tfc_fromCard_cons, if_pos rfl]
  | cons x t ih =>
      intro hnc
      rw [List.cons_append, tfc_fromCard_cons,
        if_neg (fun (hcon : x = c) => hnc (List.mem_cons.mpr (Or.inl hcon.symm)))]
      exact ih (fun hcon => hnc (List.mem_cons.mpr (Or.inr hcon)))

/-- The setPile-restore: writing the source's pile back at the
landing undoes the landing (the state's fields ride the locality). -/
private theorem pull_setPile_restore {u v : State} {c : Card} {b : Base} {A : Anchor}
    (hv : v = (u.setFound c.suit (chop (u.found c.suit))).putCard c b)
    (hloc : ∀ a', a' ≠ A → v.piles a' = u.piles a') :
    v.setPile A (u.piles A) = u.setFound c.suit (chop (u.found c.suit)) := by
  apply State.ext
  · rw [setPile_found, hv, putCard_found]
  · funext a'
    simp only [State.setPile]
    by_cases ha' : a' = A
    · rw [if_pos ha', ha']
      rfl
    · rw [if_neg ha', hloc a' ha']
      rfl
  · rw [show (v.setPile A (u.piles A)).stock = v.stock from rfl, hv, putCard_stock]
  · rw [show (v.setPile A (u.piles A)).waste = v.waste from rfl, hv, putCard_waste]
  · rw [show (v.setPile A (u.piles A)).drawStep = v.drawStep from rfl, hv, putCard_drawStep]

/-- **THE SLIDE BETWEEN THE PULLS** - sliding the pulled card from
its `b₁`-landing to `b₂` lands exactly at the `b₂`-pull's target:
the two pulls of the same card are one reversible slide apart. -/
private theorem pull_slide_pull {u v₁ v₂ : State} {c : Card} {b₁ b₂ : Base}
    (hwf : u.WF) (hwf₁ : v₁.WF)
    (h₁ : State.step u (Move.foundToTab c b₁) = some v₁)
    (h₂ : State.step u (Move.foundToTab c b₂) = some v₂)
    (hne : b₁ ≠ b₂) :
    State.step v₁ (Move.tabToTab c b₂) = some v₂ := by
  obtain ⟨c', hft, hc', hcp₁, hv₁⟩ := step_foundToTab_inv h₁
  obtain ⟨-, -, -, hcp₂, hv₂⟩ := step_foundToTab_inv h₂
  rw [hc'] at hft
  have hfit₂ : v₁.canPlace c b₂ = true := canPlace_pull hwf hwf₁ h₁ hcp₁ hcp₂ hne
  cases b₁ with
  | inl a₁ =>
      have hpile : v₁.piles a₁ = ⟨[], [c]⟩ := by
        rw [hv₁, putCard_eq_putRun]
        exact putRun_piles_inl_self _ _ _
      have hhold : v₁.pileHolding c = some a₁ :=
        (pileHolding_eq_some_iff hwf₁).2 (by
          rw [hpile]
          exact List.mem_cons_self ..)
      have hrun : fromCard c (v₁.piles a₁).faceUp = [c] := by
        rw [hpile]
        show fromCard c [c] = [c]
        rw [tfc_fromCard_cons, if_pos rfl]
      have hbelow : below c (v₁.piles a₁).faceUp = (u.piles a₁).faceUp := by
        rw [hpile]
        show below c [c] = (u.piles a₁).faceUp
        rw [below_cons, if_pos rfl]
        exact (((Pile.isEmpty_eq _).mp (canPlace_inl hcp₁).1).2).symm
      have hX : Pile.afterRunRemoved (v₁.piles a₁) (below c (v₁.piles a₁).faceUp)
          = u.piles a₁ := by
        obtain ⟨hd, hf⟩ := (Pile.isEmpty_eq _).mp (canPlace_inl hcp₁).1
        rw [hbelow, hpile, hf]
        show Pile.revealTop { (⟨[], [c]⟩ : Pile) with faceUp := [] } = u.piles a₁
        rw [show Pile.revealTop { (⟨[], [c]⟩ : Pile) with faceUp := [] }
            = (⟨[], []⟩ : Pile) from rfl,
          show u.piles a₁ = (⟨(u.piles a₁).hidden, (u.piles a₁).faceUp⟩ : Pile) from rfl,
          hd, hf]
      have hrestore : v₁.setPile a₁ (u.piles a₁)
          = u.setFound c.suit (chop (u.found c.suit)) :=
        pull_setPile_restore hv₁ (fun a' ha' => pull_piles_inl_ne h₁ ha')
      simp only [State.step, hhold, hfit₂, hrun]
      rw [hX, hrestore, ← putCard_eq_putRun, ← hv₂, if_pos trivial]
  | inr z₁ =>
      obtain ⟨k₁, hpt₁, -⟩ := canPlace_inr_guard hcp₁
      have hcfound : c ∈ u.found c.suit := lastOf_mem hft
      have hnc : c ∉ (u.piles k₁).faceUp := fun hcon =>
        ((mem_found_unique hwf hcfound).1 k₁).2 hcon
      have hpile : v₁.piles k₁ = {u.piles k₁ with faceUp := (u.piles k₁).faceUp ++ [c]} := by
        rw [hv₁, putCard_eq_putRun]
        exact putRun_piles_inr_self _ _ _ _ hpt₁
      have hhold : v₁.pileHolding c = some k₁ :=
        (pileHolding_eq_some_iff hwf₁).2 (by
          rw [hpile]
          exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
      have hrun : fromCard c (v₁.piles k₁).faceUp = [c] := by
        rw [hpile]
        exact fromCard_append_notmem hnc
      have hbelow : below c (v₁.piles k₁).faceUp = (u.piles k₁).faceUp := by
        rw [hpile]
        exact below_append_notmem hnc
      have holdne : (u.piles k₁).faceUp ≠ [] := by
        intro hcon
        have hmem : z₁ ∈ (u.piles k₁).faceUp :=
          lastOf_mem (show lastOf (u.piles k₁).faceUp = some z₁ from
            (pileOfTop_eq_some_iff hwf).mp hpt₁)
        rw [hcon] at hmem
        exact absurd hmem (by simp)
      have hX : Pile.afterRunRemoved (v₁.piles k₁) (below c (v₁.piles k₁).faceUp)
          = u.piles k₁ := by
        rw [hbelow]
        cases hold : (u.piles k₁).faceUp with
        | nil => exact absurd hold holdne
        | cons w t =>
            show {v₁.piles k₁ with faceUp := w :: t} = u.piles k₁
            rw [hpile,
              show u.piles k₁ = (⟨(u.piles k₁).hidden, (u.piles k₁).faceUp⟩ : Pile) from rfl,
              hold]
      have hrestore : v₁.setPile k₁ (u.piles k₁)
          = u.setFound c.suit (chop (u.found c.suit)) :=
        pull_setPile_restore hv₁ (fun a' ha' => pull_piles_inr_ne h₁ hpt₁ ha')
      simp only [State.step, hhold, hfit₂, hrun]
      rw [hX, hrestore, ← putCard_eq_putRun, ← hv₂, if_pos trivial]

/-- **THE PULL'S BASE-INDEPENDENCE, THE CARGO CLASS** - pulling `c`
to any base lands in the same `BareCargoEquiv` class: the slide
between the pulls is a reversible cargo leg (the undo-play is the
mirrored slide). -/
theorem pull_base_bareCargo {u v₁ v₂ : State} {c : Card} {b₁ b₂ : Base}
    (hwf : u.WF) (hwf₁ : v₁.WF) (hwf₂ : v₂.WF)
    (h₁ : State.step u (Move.foundToTab c b₁) = some v₁)
    (h₂ : State.step u (Move.foundToTab c b₂) = some v₂) :
    BareCargoEquiv v₁ v₂ := by
  by_cases hne : b₁ = b₂
  · rw [hne] at h₁
    have hvv : v₁ = v₂ := Option.some.inj (h₁.symm.trans h₂)
    rw [hvv]
    exact ⟨Steps.refl _, Steps.refl _⟩
  · have hslide := pull_slide_pull hwf hwf₁ h₁ h₂ hne
    have hslide' := pull_slide_pull hwf hwf₂ h₂ h₁ (fun h => hne h.symm)
    refine bareCargo_of_slide hwf₁ hslide ⟨v₂, [Move.tabToTab c b₁], hslide, ?_⟩
    show (match v₂.step (Move.tabToTab c b₁) with
            | some s1 => s1.run [] | none => none) = some v₁
    rw [hslide']
    exact rfl

/-- **THE PULL'S BASE-INDEPENDENCE, THE POSITION** - pulling `c` to
any base lands in the same position: the cargo class carries the
orbit, the rung arithmetic the ledger. -/
theorem pull_base_position {u v₁ v₂ : State} {c : Card} {b₁ b₂ : Base}
    (hwf : u.WF) (hwf₁ : v₁.WF) (hwf₂ : v₂.WF)
    (h₁ : State.step u (Move.foundToTab c b₁) = some v₁)
    (h₂ : State.step u (Move.foundToTab c b₂) = some v₂) :
    (Quotient.mk orbitRungSetoid ⟨v₁, hwf₁⟩ : Position)
      = Quotient.mk orbitRungSetoid ⟨v₂, hwf₂⟩ :=
  Quotient.sound ⟨bareCargo_sameOrbit (pull_base_bareCargo hwf hwf₁ hwf₂ h₁ h₂),
    fun σ => by rw [rungAt_foundToTab h₁ σ, rungAt_foundToTab h₂ σ]⟩

/-- **THE WASTE RAISE CLIMBS ONE RUNG** - a `wasteToFound` step
raises the played suit's rung by exactly one and fixes every other
suit: the one non-positional edge's ledger. -/
theorem rungAt_wasteToFound {u v : State} {c : Card}
    (hstep : State.step u (Move.wasteToFound c) = some v) (σ : Suit) :
    rungAt v σ = if σ = c.suit then rungAt u σ + 1 else rungAt u σ := by
  obtain ⟨-, x, xs, -, hv⟩ := step_wasteToFound_inv hstep
  have hfv : v.found σ = if σ = c.suit then u.found c.suit ++ [c] else u.found σ := by
    rw [hv]; rfl
  by_cases hσ : σ = c.suit
  · subst hσ
    unfold rungAt
    rw [hfv, if_pos rfl, if_pos rfl]
    simp [List.length_append]
  · unfold rungAt
    rw [hfv, if_neg hσ, if_neg hσ]

/-- **THE REVERSIBLE SLIDE VANISHES** - a reversible tableau slide
holds the ledger and rides the cargo class: it never changes the
position.  The quotient's own glue (the free moves are exactly the
draws and the reversible slides: `wasteToTab` is never reversible -
`wasteToTab_not_reversibleAtW` - and the draw's vanishing awaits
the stock-waste cycle construction). -/
theorem slide_position {u v : State} {c : Card} {b : Base} (hwf : u.WF)
    (hstep : State.step u (Move.tabToTab c b) = some v)
    (hrev : reversibleAtW u (Move.tabToTab c b)) :
    (Quotient.mk orbitRungSetoid ⟨u, hwf⟩ : Position)
      = Quotient.mk orbitRungSetoid ⟨v, step_wf hwf hstep⟩ :=
  Quotient.sound ⟨bareCargo_sameOrbit (bareCargo_of_slide hwf hstep hrev),
    fun σ => (rungAt_tabToTab hstep σ).symm⟩

/-! ## par.6-bis. The raise's round-trip and class-determinism -/

/-- `pileOfTop` reads only the piles (the congruence). -/
private theorem pileOfTop_piles {u v : State} (h : u.piles = v.piles) (z : Card) :
    u.pileOfTop z = v.pileOfTop z := by
  have htop : u.topOf = v.topOf := by
    funext a'
    show (u.piles a').top = (v.piles a').top
    rw [h]
  unfold State.pileOfTop
  rw [htop]

/-- Lineage: Classification's private `putCard_inr_eq_setPile` —
restated per the kit rule. -/
private theorem putCard_inr_eq_setPile {st : State} {c z : Card} {k : Anchor}
    (hz : st.pileOfTop z = some k) :
    st.putCard c (Sum.inr z) =
      { st with piles := fun a' =>
          if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
          else st.piles a' } := by
  simp only [State.putCard, hz]
  rfl

/-- **THE RAISE UNDOES BY A SINGLE PULL** - a reversible raise of
`c` is undone by a literal `foundToTab c b` back to the very
source: the base is where `c` came from (the card directly below,
or the empty anchor for the lone king over no hidden deck — the
certified bare row). -/
theorem tabToFound_pull_back {s t : State} {c : Card}
    (hwf : s.WF) (hstep : State.step s (Move.tabToFound c) = some t)
    (hrev : reversibleAtW s (Move.tabToFound c)) :
    ∃ b, State.step t (Move.foundToTab c b) = some s := by
  obtain ⟨hn, a, hloc, hs⟩ := step_tabToFound_inv hstep
  have hlast : lastOf (s.piles a).faceUp = some c :=
    (pileOfTop_eq_some_iff hwf).mp hloc
  have hfeq : (s.piles a).faceUp = chop (s.piles a).faceUp ++ [c] := lastOf_chop hlast
  have hR : tabToFoundR s c = true := (tabToFoundR_iff_reversibleAtW hwf c).mpr hrev
  simp only [tabToFoundR, hn, hloc] at hR
  cases hchop : chop (s.piles a).faceUp with
  | nil =>
      rw [hchop] at hR
      cases hhidden : (s.piles a).hidden with
      | cons h hh =>
          rw [hhidden] at hR
          exact absurd hR (by simp)
      | nil =>
          rw [hhidden] at hR
          exact ⟨Sum.inl a, step_foundToTab_of_tabToFound_bare hstep hloc hchop hhidden
            (of_decide_eq_true hR)⟩
  | cons w rest =>
      have hrok : runOK ((s.piles a).faceUp) = true := hwf.2.1 a
      obtain ⟨z, hz0⟩ := lastOf_exists
        (show chop (s.piles a).faceUp ≠ [] by rw [hchop]; simp)
      have hz2 : chop (s.piles a).faceUp
          = chop (chop (s.piles a).faceUp) ++ [z] := lastOf_chop hz0
      have hrok2 : runOK (chop (chop (s.piles a).faceUp) ++ z :: c :: []) = true := by
        have h1 : chop (chop (s.piles a).faceUp) ++ z :: c :: []
            = (s.piles a).faceUp := by
          rw [show z :: c :: [] = [z] ++ [c] from rfl, ← List.append_assoc, ← hz2]
          exact hfeq.symm
        rw [h1]
        exact hrok
      have hfit : canSitOn c z = true := SeedKit.runOK_adjacent_fit z c _ [] hrok2
      have htpa2 : t.piles a = { (s.piles a) with
          faceUp := chop (s.piles a).faceUp } := by
        rw [hs]
        show (if a = a then Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
            else s.piles a) = _
        rw [ite_eq_left rfl, hchop]
        rfl
      have htpne : ∀ a', a' ≠ a → t.piles a' = s.piles a' := by
        intro a' ha'
        rw [hs]
        show (if a' = a then Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
            else s.piles a') = s.piles a'
        rw [ite_eq_right ha']
      have hwft : t.WF := step_wf hwf hstep
      have htopz : (t.piles a).top = some z := by
        rw [htpa2, hchop]
        rw [hchop] at hz0
        show lastOf (w :: rest) = some z
        exact hz0
      have hptz : t.pileOfTop z = some a :=
        (pileOfTop_eq_some_iff hwft).mpr htopz
      have hcp : t.canPlace c (Sum.inr z) = true := by
        show (match t.pileOfTop z with
              | some _ => canSitOn c z | none => false) = true
        rw [hptz]
        exact hfit
      obtain ⟨hf1, hf2, hf3⟩ := tabToFound_found_trio hs
      refine ⟨Sum.inr z, ?_⟩
      simp only [State.step, hf3]
      rw [hcp]
      refine congrArg some (?_ :
        (t.setFound c.suit (chop (t.found c.suit))).putCard c (Sum.inr z) = s)
      have hzp : (t.setFound c.suit (chop (t.found c.suit))).pileOfTop z = some a := by
        rw [pileOfTop_piles (rfl :
          (t.setFound c.suit (chop (t.found c.suit))).piles = t.piles)]
        exact hptz
      rw [putCard_inr_eq_setPile hzp]
      have hwritten : { t.piles a with faceUp := (t.piles a).faceUp ++ [c] }
          = s.piles a := by
        rw [htpa2]
        refine Pile.ext ?_ ?_
        · rfl
        · show chop (s.piles a).faceUp ++ [c] = (s.piles a).faceUp
          exact hfeq.symm
      refine State.ext (funext fun σ => ?_) (funext fun a' => ?_) ?_ ?_ ?_
      · show (if σ = c.suit then chop (t.found c.suit) else t.found σ) = s.found σ
        by_cases hσ : σ = c.suit
        · rw [hσ, ite_eq_left rfl, hf1, chop_snoc]
        · rw [ite_eq_right hσ]
          exact hf2 σ hσ
      · show (if a' = a then { t.piles a with faceUp := (t.piles a).faceUp ++ [c] }
            else t.piles a') = s.piles a'
        by_cases ha' : a' = a
        · rw [ha', ite_eq_left rfl]
          exact hwritten
        · rw [ite_eq_right ha']
          exact htpne a' ha'
      · show t.stock = s.stock
        rw [hs]
        rfl
      · show t.waste = s.waste
        rw [hs]
        rfl
      · show t.drawStep = s.drawStep
        rw [hs]
        rfl

/-- **THE RAISE'S CLASS-DETERMINISM** - at equal rungs, two
REVERSIBLE raises of the same card from orbit-mates land in the
same class: the pull-back (the round-trip), the orbit-walk between
the sources, and the raise compose into witness walks both ways.
The reversible raises are exactly the ones the witness journeys
use - the quotient game's forward edge is well-defined on them. -/
theorem raise_class_position {s s₁ t t₁ : State} {c : Card}
    (hwf : s.WF) (hwf₁ : s₁.WF)
    (horb : sameOrbitSetoid.r s s₁) (hrung : RungEq s s₁)
    (hstep : State.step s (Move.tabToFound c) = some t)
    (hstep₁ : State.step s₁ (Move.tabToFound c) = some t₁)
    (hrev : reversibleAtW s (Move.tabToFound c))
    (hrev₁ : reversibleAtW s₁ (Move.tabToFound c)) :
    (Quotient.mk orbitRungSetoid ⟨t, step_wf hwf hstep⟩ : Position)
      = Quotient.mk orbitRungSetoid ⟨t₁, step_wf hwf₁ hstep₁⟩ := by
  obtain ⟨b, hb⟩ := tabToFound_pull_back hwf hstep hrev
  obtain ⟨b₁, hb₁⟩ := tabToFound_pull_back hwf₁ hstep₁ hrev₁
  obtain ⟨ρ, hρ, τ, hτ⟩ := horb
  have hw1 : ShufflePlayW t [Move.foundToTab c b] s :=
    Walk.cons (reversible_mirrorW hb hstep) hb (Walk.nil s)
  have hw3 : ShufflePlayW s [Move.tabToFound c] t :=
    Walk.cons hrev hstep (Walk.nil t)
  have hw1₁ : ShufflePlayW t₁ [Move.foundToTab c b₁] s₁ :=
    Walk.cons (reversible_mirrorW hb₁ hstep₁) hb₁ (Walk.nil s₁)
  have hw3₁ : ShufflePlayW s₁ [Move.tabToFound c] t₁ :=
    Walk.cons hrev₁ hstep₁ (Walk.nil t₁)
  have hA : ShufflePlayW t₁ ([Move.foundToTab c b₁] ++ ρ ++ [Move.tabToFound c]) t :=
    ShufflePlayW_append (ShufflePlayW_append hw1₁ hρ) hw3
  have hB : ShufflePlayW t ([Move.foundToTab c b] ++ τ ++ [Move.tabToFound c]) t₁ :=
    ShufflePlayW_append (ShufflePlayW_append hw1 hτ) hw3₁
  refine Quotient.sound ⟨⟨[Move.foundToTab c b₁] ++ ρ ++ [Move.tabToFound c], hA,
    [Move.foundToTab c b] ++ τ ++ [Move.tabToFound c], hB⟩, ?_⟩
  intro σ
  rw [rungAt_tabToFound hstep σ, rungAt_tabToFound hstep₁ σ]
  by_cases hσ : σ = c.suit
  · rw [if_pos hσ, if_pos hσ, hrung σ]
  · rw [if_neg hσ, if_neg hσ]
    exact hrung σ
/-! ## par.7. The draw's vanishing -/

/-- The board-move closure is reflexive (the empty plays). -/
private theorem NoDrawPlayW_refl (u : State) : NoDrawPlayW u u :=
  ⟨[], Walk.nil u, by simp, [], Walk.nil u, by simp⟩

/-- One reversible draw is a forward draws-only witness journey. -/
private theorem draw_forward_DrawPlayW {u v : State}
    (hstep : State.step u Move.draw = some v)
    (hrev : reversibleAtW u Move.draw) :
    DrawPlayW u [Move.draw] v :=
  ⟨Walk.cons hrev hstep (Walk.nil v), by simp⟩

/-- **THE DRAW VANISHES, GIVEN THE CYCLE** - a reversible draw
holds the ledger (the draw never touches the founds), and given
the all-draw witness return (the rest of the draw cycle - the
phase loop algebra's remaining row: from the post-draw state,
drain the stock by in-phase draws, recycle at the empty base,
and the divider returns), the orbit factorization composes the
orbit.  The remaining gap is exactly the cycle row:
`∃ τ, DrawPlayW v τ u` from one reversible draw. -/
theorem draw_position_of_cycle {u v : State} (hwf : u.WF) (hwfv : v.WF)
    (hstep : State.step u Move.draw = some v)
    (hrev : reversibleAtW u Move.draw)
    (hcycle : ∃ τ, DrawPlayW v τ u) :
    (Quotient.mk orbitRungSetoid ⟨u, hwf⟩ : Position)
      = Quotient.mk orbitRungSetoid ⟨v, hwfv⟩ := by
  obtain ⟨τ, hτ⟩ := hcycle
  refine Quotient.sound ⟨?_, ?_⟩
  · refine (sameOrbit_factor hwf hwfv).mpr ⟨u, NoDrawPlayW_refl u, ?_⟩
    exact ⟨[Move.draw], τ, draw_forward_DrawPlayW hstep hrev, hτ⟩
  · intro σ
    exact (rungAt_draw hstep σ).symm

/-- **THE drawR INVARIANT** - the reversible-draw shape is closed
under the draw: the phase trap (an in-phase position stays
in-phase through the draw, and the empty stock is in-phase
trivially) plus the waste's nonemptiness (the deal only appends).
The whole draw cycle carries this invariant - it is why every leg
of the cycle is reversible. -/
theorem drawR_invariant {x y : State} (hd : 0 < x.drawStep)
    (hstep : State.step x Move.draw = some y) (h : drawR x = true) :
    drawR y = true := by
  have hstep' : x.stepDraw = some y := hstep
  have hwx : x.waste ≠ [] := by
    cases hst : x.stock with
    | nil =>
        simp only [drawR, hst] at h
        exact of_decide_eq_true h
    | cons w t =>
        simp only [drawR, hst, Bool.and_eq_true] at h
        exact of_decide_eq_true h.1
  have hphx : inPhase x = true := by
    cases hst : x.stock with
    | nil => exact inPhase_eq_true_of_nil hst
    | cons w t =>
        rw [inPhase_eq_decide_of_cons hst]
        simp only [drawR, hst, Bool.and_eq_true] at h
        exact h.2
  have hphy : inPhase y = true := draw_keeps_inPhase hstep' hphx
  have hwy : y.waste ≠ [] := by
    cases hst : x.stock with
    | nil =>
        rw [base_draw_shape hst hwx] at hstep'
        injection hstep' with hcon
        rw [← hcon]
        intro hcon2
        have hlen : ((x.waste.reverse.take x.drawStep).reverse
            ++ ([] : List Card)).length = 0 := congrArg List.length hcon2
        rw [List.length_append, List.length_nil, List.length_reverse,
          List.length_take, List.length_reverse, Nat.min_def] at hlen
        have hpos : 0 < x.waste.length := by
          obtain ⟨w0, t0, hc0⟩ := list_cons_of_ne_nil hwx
          rw [hc0, List.length_cons]; omega
        by_cases hle : x.drawStep ≤ x.waste.length
        · rw [if_pos hle] at hlen; omega
        · rw [if_neg hle] at hlen; omega
    | cons w t =>
        have hxne : x.stock ≠ [] := by
          intro hcon
          rw [hcon] at hst
          exact absurd hst (by simp)
        rw [plain_draw_shape hxne] at hstep'
        injection hstep' with hcon
        rw [← hcon]
        intro hcon2
        have hlen : ((x.stock.take x.drawStep).reverse ++ x.waste).length = 0 :=
          congrArg List.length hcon2
        rw [List.length_append, List.length_reverse, List.length_take] at hlen
        have hpos : 0 < x.waste.length := by
          obtain ⟨w0, t0, hc0⟩ := list_cons_of_ne_nil hwx
          rw [hc0, List.length_cons]; omega
        omega
  cases hsty : y.stock with
  | nil =>
      unfold drawR
      rw [hsty]
      show decide (y.waste ≠ []) = true
      exact decide_eq_true hwy
  | cons w t =>
      unfold drawR
      rw [hsty]
      show (decide (y.waste ≠ []) && decide (y.waste.length % y.drawStep = 0)) = true
      rw [decide_eq_true hwy, Bool.true_and]
      rw [inPhase_eq_decide_of_cons hsty] at hphy
      exact hphy

/-! ## par.8. The saturation descent -/

/-- **THE SATURATION FRONTIER AT THE POSITION LEVEL** - the level-k
frontier probe, descended: decidable per position (any
representative computes it).  The campaign's Q-family now reads on
positions: Q1's vacuity ("can class-mates at different rungs both
be saturated?") is a question about two `Position`s, and the
residue's witnesses are position-data. -/
def rankSatB_pos (k : Nat) : Position → Bool :=
  Quotient.lift (fun p => rankSatB k p.1)
    (fun p p' hr => bool_eq_of_iff_true (by
      rw [rankSatB_iff p.2, rankSatB_iff p'.2]
      exact ⟨fun h c hc hS => h c hc ((canRaiseS_orbit_rung p.2 hr.1 hr.2).mpr hS),
        fun h c hc hS => h c hc ((canRaiseS_orbit_rung p.2 hr.1 hr.2).mp hS)⟩))

/-- The position-level frontier reads any representative's
computation (the lift's defining equation). -/
theorem rankSatB_pos_mk (k : Nat) (p : WFState) :
    rankSatB_pos k (Quotient.mk orbitRungSetoid p) = rankSatB k p.1 := rfl

/-- **THE SATURATION TRANSFERS** - at equal rungs, orbit-mates
share the level-k saturation frontier (the invariance, repackaged
at the grade the ceiling campaign runs on). -/
theorem rankSat_position {k : Nat} {u v : State} (hwf : u.WF)
    (horb : sameOrbitSetoid.r u v) (hrung : RungEq u v)
    (hsat : RankSat k u) : RankSat k v :=
  fun c hc hcan => hsat c hc ((canRaiseS_orbit_rung hwf horb hrung).mpr hcan)

/-- The S-saturation transfers (the full-grade frontier). -/
theorem ssaturated_position {u v : State} (hwf : u.WF)
    (horb : sameOrbitSetoid.r u v) (hrung : RungEq u v)
    (hsat : SSaturated u) : SSaturated v :=
  fun c hcan => hsat c ((canRaiseS_orbit_rung hwf horb hrung).mpr hcan)

/-- The saturation is the empty spectrum (the position-level
reading of the campaign's grade). -/
theorem ssaturated_iff_spec (p : WFState) :
    SSaturated p.1 ↔ ∀ c, ¬ spec (Quotient.mk orbitRungSetoid p) c := by
  constructor
  · intro h c hsc; exact h c ((spec_mk _ _).mp hsc)
  · intro h c hcan; exact h c ((spec_mk _ _).mpr hcan)

/-! ## par.9. The battery -/

#print axioms rungsOf
#print axioms foundsOf
#print axioms spec
#print axioms specB
#print axioms spec_sound
#print axioms specB_iff
#print axioms rungAt_tabToFound
#print axioms rungAt_foundToTab
#print axioms rungAt_draw
#print axioms rungAt_tabToTab
#print axioms rungAt_wasteToTab
#print axioms pullSpec
#print axioms pullSpec_mk
#print axioms pull_piles_inl_ne
#print axioms pull_piles_inr_ne
#print axioms canPlace_inr_guard
#print axioms canPlace_pull
#print axioms below_append_notmem
#print axioms fromCard_append_notmem
#print axioms pull_setPile_restore
#print axioms pull_slide_pull
#print axioms pull_base_bareCargo
#print axioms pull_base_position
#print axioms rungAt_wasteToFound
#print axioms slide_position
#print axioms rankSatB_pos
#print axioms rankSatB_pos_mk
#print axioms rankSat_position
#print axioms ssaturated_position
#print axioms ssaturated_iff_spec
#print axioms tabToFound_pull_back
#print axioms raise_class_position
#print axioms draw_position_of_cycle
#print axioms drawR_invariant
