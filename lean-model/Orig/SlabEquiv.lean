import Orig.PairName
import Orig.BracketDecomp
import Orig.FoundKit

/-!
# Orig.SlabEquiv — THE TWIN-SLAB TABLEAU EQUIVALENCE

The owner's twin-side refinement of the fork's low slab (2026-10-12):
the slab of a fork (witness card `x`, fork point `x.rank.toIdx`) is the
TWIN SIDE ALONE — `rungAt w x.twin.suit ≤ x.rank.toIdx`, i.e. the
covered twin is not founded — replacing the earlier both-suits draft
(within a fork's macro class the just-landed one-founding row of
`Orig/PairConfine.lean`'s door complex bars both pair members being
founded, so the twin side carries the whole content and x-lift
members are absorbed into the slab).  This leaf proves the
arrangement face of that read: at WF endpoints joined by a witness
journey, the slab condition is EQUIVALENT to the covered twin's
physical residency in the tableau (face-up or hidden on some pile of
`w`), given it starts tableau-resident at the journey's origin.
Downstream, THE LOW-SLAB SUFFICIENCY (`Orig/LowSlab.lean`) consumes
the equivalence as the duplicate's arrangement anchor: a slab member
is one whose covered twin still EXISTS in the tableau, so a matching
duplicate's takeback checklist names cards physically presentable
there.

* §0 the private kit: the founded-bridge pair (upward: a rung
  strictly above a card's index has founded it; downward: a founded
  card's index sits strictly below its rung, the take-position
  read), the suit-fixity row (a foundation row holds only its own
  suit's cards), the five-zone residency census, and the draw-cycle
  kit (the `dealUpTo` membership rows, the reverse-membership row,
  the recycle's union-preservation row) — per-file copies per the
  house dedup discipline (templates: `Orig/CrossFamilyStatic.lean`
  §0, `Orig/PairConfine.lean`'s private rows).
* §1 **`cycle_zone_pin`** (proved, zero-sorry) — THE TWO-ZONE PIN:
  along a witness journey, stock-or-waste MEMBERSHIP is exactly
  preserved in both directions.  The waste letters never ride (the
  banked census `journey_never_wasteToFound` and
  `journey_never_wasteToTab`); every board letter keeps the zone
  verbatim (the banked keep rows); and the draw — the zone's only
  other writer — pays its dealt cards from the recycled stock back
  into the waste (`draw_unfold` + `dealUpTo_eq_take_drop`'s take/drop
  split), so the zone neither gains nor loses a resident.  This is
  the NEVER-GAIN row of the equivalence route (w-side residency
  implies st-side residency) together with its closure companion,
  landed outright and PUBLIC so the census sibling program can
  consume or swap it.
* §2 **`twin_slab_tableau`** — THE EQUIVALENCE: the covered twin sits
  in `w`'s tableau iff its suit's rung reads at most the fork point.
  (⇒) tableau residency pins the twin off every foundation
  (`mem_faceUp_only`/`mem_hidden_only`), and a rung strictly above
  the fork point would have founded it (the upward bridge).
  (⇐) a bounded rung keeps the twin unfounded (the downward bridge);
  a cycle-zone twin would reach the stock-or-waste of the ORIGIN
  against the origin's own pile pin (`cycle_zone_pin` + the
  origin-side `mem_faceUp_only`/`mem_hidden_only`), so the
  five-zone census leaves the tableau as the only seat.

House compliance: additive leaf below the Lowbridge assembly's
closure (`Orig.PairName` + `Orig.BracketDecomp`, resolved
empirically — both needed: the journey rows ride
`Orig.BracketDecomp`'s closure, the WF census and zone rows ride
`Orig.PairName`'s); the census rows are per-file private copies;
every fresh head audited below; no `Classical.choice` (the
non-arithmetic closures in §2 are `exfalso`-premised).
-/

/-! ## §0. The private kit (per-file copies, the house dedup discipline) -/

/-! ### The draw-cycle kit (the zone's only writers) -/

/-- A deal pays a `dealUpTo` member home: a list member lands in the
dealt half or the remaining half (the per-file copy of
`conf_dealUpTo_mem`). -/
private theorem sequ_dealUpTo_memL (d : Card) :
    ∀ (k : Nat) (l : List Card),
      d ∈ l → d ∈ (State.dealUpTo k l).1 ∨ d ∈ (State.dealUpTo k l).2 := by
  intro k
  induction k with
  | zero => intro l hd; exact Or.inr hd
  | succ k ih =>
      intro l hd
      cases l with
      | nil => exact absurd hd (by simp)
      | cons x xs =>
          by_cases hdx : x = d
          · subst hdx
            left
            simp only [State.dealUpTo]
            exact List.mem_cons_self ..
          · rcases List.mem_cons.mp hd with heq | htl
            · exact absurd heq (fun hcon => hdx hcon.symm)
            · rcases ih xs htl with h1 | h2
              · left
                simp only [State.dealUpTo]
                exact List.mem_cons.mpr (Or.inr h1)
              · right
                simp only [State.dealUpTo]
                exact h2

/-- The dealt half only pays existing stock (`dealUpTo` is the
take/drop split, banked as `dealUpTo_eq_take_drop`). -/
private theorem sequ_dealUpTo_mem_take {d : Card} (k : Nat) (l : List Card)
    (h : d ∈ (State.dealUpTo k l).1) : d ∈ l := by
  rw [dealUpTo_eq_take_drop k l] at h
  exact FoundKit.mem_of_take l k h

/-- The remaining half only holds existing stock. -/
private theorem sequ_dealUpTo_mem_drop {d : Card} (k : Nat) (l : List Card)
    (h : d ∈ (State.dealUpTo k l).2) : d ∈ l := by
  rw [dealUpTo_eq_take_drop k l] at h
  exact FoundKit.mem_of_drop l k h

/-- Membership in a reversed list is membership in the list (the
one-line kit row; the induction is over the cons equation). -/
private theorem sequ_mem_of_reverse {c : Card} :
    ∀ {l : List Card}, c ∈ l.reverse ↔ c ∈ l := by
  intro l
  induction l with
  | nil => exact Iff.rfl
  | cons a t ih =>
      rw [List.reverse_cons]
      constructor
      · intro h
        rcases List.mem_append.mp h with h' | h'
        · exact List.mem_cons_of_mem a (ih.mp h')
        · rw [List.mem_singleton] at h'
          rw [h']
          exact List.mem_cons_self ..
      · intro h
        rcases List.mem_cons.mp h with he | h'
        · rw [he]
          exact List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))
        · exact List.mem_append.2 (Or.inl (ih.mpr h'))

/-- The recycle permutes the two-zone world: membership in the
recycled stock-or-waste is exactly membership in the original (the
three recycle arms read directly off `State.recycle`). -/
private theorem sequ_recycle_union (s : State) (c : Card) :
    (c ∈ (State.recycle s).stock ∨ c ∈ (State.recycle s).waste) ↔
      (c ∈ s.stock ∨ c ∈ s.waste) := by
  cases hs : s.stock with
  | nil =>
      cases hw : s.waste with
      | nil =>
          rw [recycle_allEmpty s hs hw, hs, hw]
      | cons x xs =>
          have hne : s.waste ≠ [] := by rw [hw]; simp
          rw [recycle_nil s hs hne, hw]
          constructor
          · intro hcc
            rcases hcc with h | h
            · exact Or.inr (sequ_mem_of_reverse.mp h)
            · exact absurd h (by simp)
          · intro hcc
            rcases hcc with h | h
            · exact absurd h (by simp)
            · exact Or.inl (sequ_mem_of_reverse.mpr h)
  | cons y ys =>
      have hne : s.stock ≠ [] := by rw [hs]; simp
      rw [recycle_keep s hne, hs]

/-! ## §1. THE TWO-ZONE PIN (the cycle-zone census along witness journeys) -/

/-- **THE TWO-ZONE PIN** — along a witness journey the stock and the
waste are a CLOSED two-zone world for their residents: membership in
the union is EXACTLY preserved (both directions).  The waste letters
never ride (the banked census `journey_never_wasteToFound` /
`journey_never_wasteToTab`); the three board letters keep the zone
verbatim (their successor records write no zone field); the draw —
the zone's only writer — pays its dealt cards from the recycled
stock back into the waste, and the recycle itself only reshuffles
the union (`draw_unfold`, the `dealUpTo` membership rows, the
recycle's union row).  Landed outright here: this covers the
NEVER-GAIN direction the equivalence route prices AND its closure
companion; PUBLIC so the census sibling program can consume or swap
it wholesale. -/
theorem cycle_zone_pin {st : State} : ∀ {τ : List Move} {w : State},
    ShufflePlayW st τ w → ∀ (c : Card),
      (c ∈ w.stock ∨ c ∈ w.waste) ↔ (c ∈ st.stock ∨ c ∈ st.waste) := by
  intro τ w h
  induction h with
  | nil u => intro c; exact Iff.rfl
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro c
      rw [ih c]
      cases m with
      | draw =>
          have hd : s₀.stepDraw = some s₁ := hstep
          obtain ⟨r, hrEq, -, hyEq⟩ := draw_unfold hd
          rw [hyEq]
          have hmid : (c ∈ (State.dealUpTo r.drawStep r.stock).2 ∨
                c ∈ (State.dealUpTo r.drawStep r.stock).1.reverse ++ r.waste) ↔
              (c ∈ r.stock ∨ c ∈ r.waste) := by
            constructor
            · intro hc
              rcases hc with hs | hw
              · exact Or.inl (sequ_dealUpTo_mem_drop r.drawStep r.stock hs)
              · rcases List.mem_append.mp hw with h' | h'
                · exact Or.inl (sequ_dealUpTo_mem_take r.drawStep r.stock
                    (sequ_mem_of_reverse.mp h'))
                · exact Or.inr h'
            · intro hc
              rcases hc with hs | hw
              · rcases sequ_dealUpTo_memL c r.drawStep r.stock hs with h' | h'
                · exact Or.inr
                    (List.mem_append.2 (Or.inl (sequ_mem_of_reverse.mpr h')))
                · exact Or.inl h'
              · exact Or.inr (List.mem_append.2 (Or.inr hw))
          rw [hmid, ← hrEq, sequ_recycle_union s₀ c]
      | wasteToFound c₀ =>
          exact absurd hrev (journey_never_wasteToFound hstep)
      | wasteToTab c₀ b =>
          exact absurd hrev (journey_never_wasteToTab hstep)
      | tabToFound c₀ =>
          obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
          rw [hs]
          exact Iff.rfl
      | foundToTab c₀ b =>
          obtain ⟨c', -, -, -, hs⟩ := step_foundToTab_inv hstep
          rw [hs]
          have hstock : ((s₀.setFound c₀.suit (chop (s₀.found c₀.suit))).putCard c₀ b).stock
              = s₀.stock := by
            rw [putCard_stock]
            exact setFound_stock s₀ c₀.suit (chop (s₀.found c₀.suit))
          have hwaste : ((s₀.setFound c₀.suit (chop (s₀.found c₀.suit))).putCard c₀ b).waste
              = s₀.waste := by
            rw [putCard_waste]
            exact setFound_waste s₀ c₀.suit (chop (s₀.found c₀.suit))
          rw [hstock, hwaste]
      | tabToTab c₀ b =>
          obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv hstep
          rw [hs]
          have hstock : ((s₀.setPile a (Pile.afterRunRemoved (s₀.piles a)
              (below c₀ (s₀.piles a).faceUp))).putRun
              (fromCard c₀ (s₀.piles a).faceUp) b).stock = s₀.stock := by
            rw [putRun_stock]
            exact setPile_stock s₀ a (Pile.afterRunRemoved (s₀.piles a)
              (below c₀ (s₀.piles a).faceUp))
          have hwaste : ((s₀.setPile a (Pile.afterRunRemoved (s₀.piles a)
              (below c₀ (s₀.piles a).faceUp))).putRun
              (fromCard c₀ (s₀.piles a).faceUp) b).waste = s₀.waste := by
            rw [putRun_waste]
            exact setPile_waste s₀ a (Pile.afterRunRemoved (s₀.piles a)
              (below c₀ (s₀.piles a).faceUp))
          rw [hstock, hwaste]

/-! ## §2. THE EQUIVALENCE -/

/-- **THE TWIN-SLAB TABLEAU EQUIVALENCE** — at WF endpoints joined by
a witness journey, the covered twin sits in the end state's tableau
(face-up or hidden on some pile) iff its suit's rung reads at most
the fork point — the owner's twin-side slab, read as an arrangement
fact.  The tableau hypothesis at the journey's origin (`htwinst`)
carries the (⇐) arm's disjointness; the origin's WF pins the twin off
the cycle zones there, so the journey can never import it into them.

(⇒) TABLEAU ⇒ BOUNDED RUNG: tableau residency pins the twin off every
foundation (`mem_faceUp_only` / `mem_hidden_only` at the end state),
and a rung strictly above the fork point would have founded it (the
upward founded-bridge) — `Nat.le_of_not_gt` reads the bounded rung
off the refuted dichotomy.

(⇐) BOUNDED RUNG ⇒ TABLEAU: the downward founded-bridge keeps the
twin unfounded at the end state's own foundation; a cycle-zone twin
would reach the ORIGIN's stock-or-waste by the two-zone pin
(`cycle_zone_pin`'s never-gain direction), against the origin's own
pile pin (`mem_faceUp_only`/`mem_hidden_only` there, either arm of
`htwinst`); the suit-fixity row kills the wrong-suit foundations; and
the five-zone residency census leaves the tableau as the only seat. -/
theorem twin_slab_tableau {st w : State} {x : Card}
    (hwfst : st.WF) (hwfw : w.WF)
    {τ : List Move} (hτ : ShufflePlayW st τ w)
    (htwinst : ∃ a, x.twin ∈ (st.piles a).faceUp ∨ x.twin ∈ (st.piles a).hidden) :
    (∃ a, x.twin ∈ (w.piles a).faceUp ∨ x.twin ∈ (w.piles a).hidden) ↔
      rungAt w x.twin.suit ≤ x.rank.toIdx := by
  have hstcx : x.twin ∉ st.stock ∧ x.twin ∉ st.waste := by
    obtain ⟨a, hfa | hhi⟩ := htwinst
    · exact ⟨(mem_faceUp_only hwfst hfa).2.2.1,
        (mem_faceUp_only hwfst hfa).2.2.2.1⟩
    · exact ⟨(mem_hidden_only hwfst hhi).2.2.1,
        (mem_hidden_only hwfst hhi).2.2.2.1⟩
  have hle : (∀ s, x.twin ∉ w.found s) →
      rungAt w x.twin.suit ≤ x.rank.toIdx := fun hall =>
    Nat.le_of_not_gt (fun hgt =>
      hall x.twin.suit (FoundKit.mem_found_of_rung hwfw hgt))
  constructor
  · intro htab
    obtain ⟨a, hfw | hhw⟩ := htab
    · exact hle ((mem_faceUp_only hwfw hfw).2.2.2.2)
    · exact hle ((mem_hidden_only hwfw hhw).2.2.2.2)
  · intro hrung
    have hnf : x.twin ∉ w.found x.twin.suit := by
      intro hmem
      have hlt₀ := FoundKit.mem_found_rank_lt hwfw hmem
      have hlt : x.twin.rank.toIdx < rungAt w x.twin.suit := hlt₀
      rw [Card.twin_rank] at hlt
      exfalso
      omega
    have hcyc : ¬ (x.twin ∈ w.stock ∨ x.twin ∈ w.waste) := by
      intro hc
      obtain ⟨hss, hww⟩ := hstcx
      rcases (cycle_zone_pin hτ x.twin).mp hc with hs | hw
      · exact hss hs
      · exact hww hw
    rcases FoundKit.zone_residency w hwfw x.twin with ⟨s, hfw⟩ | ⟨k, hkw⟩ |
      ⟨k, hfw⟩ | hsw | hww
    · by_cases hs : s = x.twin.suit
      · rw [hs] at hfw
        exact absurd hfw hnf
      · exact absurd (FoundKit.found_suit hwfw hfw).symm hs
    · exact ⟨k, Or.inr hkw⟩
    · exact ⟨k, Or.inl hfw⟩
    · exact absurd (Or.inl hsw) hcyc
    · exact absurd (Or.inr hww) hcyc

/-! ## The audit battery

`#print axioms` per fresh head: every §0 kit row and the §1 pin are
zero-`sorry` and read banked-chain grade (`[propext]` /
`[propext, Quot.sound]` per the chain); THE equivalence head
`twin_slab_tableau` is fully PROVED — this leaf's single ticket-free
landing: no `sorryAx` anywhere in the battery. -/

#print axioms sequ_dealUpTo_memL
#print axioms sequ_dealUpTo_mem_take
#print axioms sequ_dealUpTo_mem_drop
#print axioms sequ_mem_of_reverse
#print axioms sequ_recycle_union
#print axioms cycle_zone_pin
#print axioms twin_slab_tableau
