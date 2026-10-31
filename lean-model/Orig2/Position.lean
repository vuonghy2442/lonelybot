import Orig2.StratifiedQuotient
import Orig2.FreeOrbit

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
