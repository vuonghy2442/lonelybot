import Orig2.CargoRaise
import Orig2.SeatMateStack
import Orig2.Integrity
import Orig2.CeilingBridge

/-!
# Orig2.FreeOrbit — THE FREE-CARD ORBIT INVARIANCE (the campaign card)

THE MISSION (owner line 2026-10-27): the tableau-readiness probe
`freeCardS` is an (orbit, rung-tuple) invariant:

  `sameOrbitSetoid.r s s' → (∀ σ, rungAt s σ = rungAt s' σ) →
   ∀ c, freeCardS s c = freeCardS s' c`

— the strongest invariance row in the campaign.  With
`canRaiseS_split` (the license = foundation-gate ∧ readiness) and
`nextUp`'s tuple-determination, the CanRaiseS SETS then agree at
equal rungs — the residue (`SatDifferFork`) is thereby confined to
the rung ledger, exactly as its route (the LIFO exodus, the
first-passage twin-raise) assumes.

THE LETTER TABLE (the per-step induction substrate): a `ShufflePlayW`
is a `Walk` at `reversibleAtW`, and the two waste letters are never
reversible (in-tree), so the induction splits over four letters:

* `draw` — the pool set is preserved (recycle reverses, dealing
  splits); no pile is touched.
* `tabToTab` — the cargo oracle `tabToTabR`: below ≠ [] ∨ bare-king;
  the step's `afterRunRemoved` reveals only at an empty prefix, so
  no letter of this shape reveals; run members keep their parents,
  the head lands on a parent.
* `tabToFound` — the raise oracle `tabToFoundR`: nextUp ∧ top ∧
  (chop ≠ [] ∨ hidden = [] ∧ king); the step writes
  `afterRunRemoved p (chop p.faceUp)` — reveals fire only at
  chop = [], and both oracle arms exclude that with hidden ≠ [].
* `foundToTab` — the pull oracle `foundToTabR`; `putCard` touches no
  hidden deck; a non-king landing is `inr` (`canPlace_inl` requires
  king).

THE ARCHITECTURE (the four sections, landing in proof order):

* THE SEAT ROWS (landed first) — parented-ness (non-kings: sits on
  something) and bareness (kings: the face-up bottom, seat-arm
  `hidden = []`) are invariants.  Bare non-king bottoms are frozen
  (the cargo oracle's king-check; the raise oracle's bare-non-king
  bar); parented cards stay parented (run slides keep members
  parented, excursion returns are `inr` for non-kings).  The
  TWO-SEAT LEMMA is the cornerstone: a card's legal parents are one
  twin pair, so SEATED = PARENTED and no move takes a card to a
  parent outside the pair it started in.
* THE ZONE ROWS — the face-up set is (orbit, tuple)-invariant:
  `found` from the tuple and canonical prefixes (`found_prefix`),
  the hidden decks per pile from `rev_step_hidden_eq`
  (SeatMateStack, public), the pool set from the draw row, the zone
  census from `mem_pile_unique`.  This row also delivers the
  EXCURSION CLOSURE: every card raised mid-journey returns (its
  face-up membership is an endpoint fact).
* THE HATCH FACTORIZATION — `freeCardS`'s last clause is
  ¬(covered c ∧ covered c.twin) on the twin-face-up slice and
  ¬covered(c) on the other; both reduce to the PARENTED-COUNT of
  the sitter pair (two-seat again — the sitters of a parent pair
  are themselves one twin pair).
* THE ASSEMBLY — the theorem and the CanRaiseS-set corollary.

House compliance: additive leaf (`Orig2.CargoRaise` for the probe
and the split, `Orig2.SeatMateStack` for the fit arithmetic and the
hidden ledger, `Orig2.Integrity` for the census); zero `sorry`, zero
`Classical.choice`; the battery at the tail.
-/

/-! ## §1. The seat rows — the two-seat lemma (the cornerstone) -/

/-- The two-color pigeonhole.  Lineage: `Orig2/SeatMateStack.lean`'s
private `color_eq_of_ne` — restated here per the kit rule rather
than widening that card's surface. -/
private theorem color_eq_of_ne {a b z : Color} (h1 : a ≠ z) (h2 : b ≠ z) :
    a = b := by
  cases a <;> cases b <;> cases z <;> simp_all

/-- **THE TWO-SEAT LEMMA, PAIR-CLOSURE FORM** — any two legal parents
of one card are equal or twins: a card's sitting options are exactly
one twin pair.  The campaign's cornerstone — SEATED = PARENTED (a
parented card sits somewhere in ITS pair), and no move can take a
card to a parent outside the pair it started in.  Lineage: the
arithmetic over `canSitOn_eq` (Orig/Basic, the seam) +
`card_eq_twin_of_rank_color` (SeatMateStack, public). -/
theorem canSitOn_twin_pair {u z z' : Card}
    (hz : canSitOn u z = true) (hz' : canSitOn u z' = true) :
    z' = z ∨ z' = z.twin := by
  obtain ⟨hrank, hcol⟩ := (canSitOn_eq u z).mp hz
  obtain ⟨hrank', hcol'⟩ := (canSitOn_eq u z').mp hz'
  have hr : z'.rank = z.rank := Rank.toIdx_inj (by omega)
  have hc : z'.suit.color = z.suit.color :=
    color_eq_of_ne hcol'.symm hcol.symm
  exact card_eq_twin_of_rank_color hr hc

/-! ## §2. The zone rows — the face-up set invariance -/

/-- Membership transport along stock/waste equalities. -/
private theorem pool_of_eq {u v : State} (hs : v.stock = u.stock) (hw : v.waste = u.waste) :
    ∀ c, (c ∈ u.stock ∨ c ∈ u.waste) → (c ∈ v.stock ∨ c ∈ v.waste) := by
  intro c hc
  rw [hs, hw]
  exact hc

/-- **A reversible step preserves the pool**: the draw conserves
`drawPool` (`chart_draw`), the board letters never write stock or
waste (the inv literals + the kit's `putCard`/`putRun` field rows),
and the waste letters are not reversible (in-tree). -/
theorem step_pool_rev {u v : State} {m : Move}
    (hstep : State.step u m = some v) (hrev : reversibleAtW u m) :
    ∀ c, (c ∈ u.stock ∨ c ∈ u.waste) → (c ∈ v.stock ∨ c ∈ v.waste) := by
  cases m with
  | draw =>
      have hpool := (chart_draw hstep).2.2.2
      intro c hc
      have h1 : c ∈ drawPool u := by
        rcases hc with h | h
        · exact List.mem_append.mpr (Or.inl (List.mem_reverse.mpr h))
        · exact List.mem_append.mpr (Or.inr h)
      rw [hpool] at h1
      rcases List.mem_append.mp h1 with h | h
      · exact Or.inl (List.mem_reverse.mp h)
      · exact Or.inr h
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW u c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW u c b)
  | tabToFound c =>
      obtain ⟨hnext, ap, hpa, hv⟩ := step_tabToFound_inv hstep
      exact pool_of_eq (by rw [hv]; rfl) (by rw [hv]; rfl)
  | foundToTab c b =>
      obtain ⟨c', hft, heq, hcp, hv⟩ := step_foundToTab_inv hstep
      exact pool_of_eq
        (by rw [hv, putCard_stock (u.setFound c.suit (chop (u.found c.suit))) c b]; rfl)
        (by rw [hv, putCard_waste (u.setFound c.suit (chop (u.found c.suit))) c b]; rfl)
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hfr, hv⟩ := step_tabToTab_inv hstep
      exact pool_of_eq (by rw [hv, putRun_stock]; rfl) (by rw [hv, putRun_waste]; rfl)

/-- **A witness shuffle preserves the pool** (one way; the return
journey gives the other). -/
theorem walk_pool_rev {u : State} {ρ : List Move} {v : State}
    (h : ShufflePlayW u ρ v) :
    ∀ c, (c ∈ u.stock ∨ c ∈ u.waste) → (c ∈ v.stock ∨ c ∈ v.waste) := by
  induction h with
  | nil st => exact fun c hc => hc
  | @cons st s1 W m ρ' hlet hstep hrest ih =>
      exact fun c hc => ih c (step_pool_rev hstep hlet c hc)

/-- **A witness shuffle keeps every hidden deck** (the walk-level
compose of SeatMateStack's `rev_step_hidden_eq`). -/
theorem walk_hidden_eq {u : State} (hwf : u.WF) {ρ : List Move} {v : State}
    (h : ShufflePlayW u ρ v) : ∀ a, (v.piles a).hidden = (u.piles a).hidden := by
  revert hwf
  induction h with
  | nil st => exact fun _ a => rfl
  | @cons st s1 W m ρ' hlet hstep hrest ih =>
      intro hwf a
      rw [ih (step_wf hwf hstep) a]
      exact rev_step_hidden_eq hwf hstep hlet a

/-- **Well-formedness survives a witness shuffle.** -/
theorem walk_wf {u : State} (hwf : u.WF) {ρ : List Move} {v : State}
    (h : ShufflePlayW u ρ v) : v.WF := by
  revert hwf
  induction h with
  | nil st => exact fun h => h
  | @cons st s1 W m ρ' hlet hstep hrest ih =>
      intro hwf
      exact ih (step_wf hwf hstep)

/-- The census totality: every card sits in some zone (the count is
one, so the filtered zone list cannot be empty). -/
private theorem mem_zones_of_wf {st : State} (hwf : st.WF) (c : Card) :
    c ∈ st.zones.flatMap id := by
  have h1 : st.cardCount c = 1 := hwf.2.2.1 c (Card.mem_universe c)
  unfold State.cardCount at h1
  cases hf : ((st.zones.flatMap id).filter fun x => decide (x = c)) with
  | nil => rw [hf] at h1; simp at h1
  | cons x t =>
      have hx : x ∈ ((st.zones.flatMap id).filter fun x => decide (x = c)) := by
        rw [hf]; exact List.mem_cons_self ..
      obtain ⟨hm, hxc⟩ := List.mem_filter.mp hx
      rw [← of_decide_eq_true hxc]
      exact hm

/-- The zone decomposition: a card in the zones that is in no
foundation, no hidden deck and not in the pool is face-up
somewhere. -/
private theorem zone_faceUp_of {st : State} {c : Card}
    (hz : c ∈ st.zones.flatMap id)
    (hnf : ∀ σ, c ∉ st.found σ)
    (hnh : ∀ a, c ∉ (st.piles a).hidden)
    (hns : c ∉ st.stock) (hnw : c ∉ st.waste) :
    ∃ a, c ∈ (st.piles a).faceUp := by
  obtain ⟨zs, hzs, hczs⟩ := List.mem_flatMap.mp hz
  rcases List.mem_append.mp hzs with h | h
  · rcases List.mem_append.mp h with h' | h'
    · obtain ⟨σ, -, hzeq⟩ := List.mem_map.mp h'
      rw [← hzeq] at hczs
      exact absurd hczs (hnf σ)
    · obtain ⟨a, -, hzeq⟩ := List.mem_map.mp h'
      rw [← hzeq] at hczs
      rcases List.mem_append.mp hczs with hcon | hcon
      · exact absurd hcon (hnh a)
      · exact ⟨a, hcon⟩
  · rcases List.mem_cons.mp h with rfl | h
    · exact absurd hczs hns
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd hczs hnw
      · exact absurd h (List.not_mem_nil)

/-- The rung vector determines the foundations (the all-suit
packaging of CeilingBridge's `found_congr_of_rungs`). -/
private theorem found_eq_of_rungVec (hu : u.WF) (hv : v.WF)
    (h : ∀ σ, rungAt u σ = rungAt v σ) : ∀ σ, u.found σ = v.found σ :=
  fun σ => found_congr_of_rungs hu hv (h σ)

/-- **THE ONE-WAY ZONE TRANSFER** — along a witness shuffle with
equal rungs, every face-up card is still face-up: its exclusions
(found, hidden, pool) transport through the shuffle's invariants,
and the census totality leaves the face-up zones as the only home. -/
private theorem faceUp_of_walk {s s' : State} (hwf : s.WF) (hwf' : s'.WF)
    {τ : List Move} (hj : ShufflePlayW s τ s')
    {ρ : List Move} (hj' : ShufflePlayW s' ρ s)
    (hrung : ∀ σ, rungAt s σ = rungAt s' σ) :
    ∀ c, (∃ a, c ∈ (s.piles a).faceUp) → (∃ a, c ∈ (s'.piles a).faceUp) := by
  rintro c ⟨a0, hmem⟩
  have hpu := mem_pile_unique hwf (Or.inr hmem)
  have hnh : ∀ a', c ∉ (s.piles a').hidden := by
    intro a'
    by_cases haa' : a' = a0
    · rw [haa']; exact mem_faceUp_not_hidden hwf hmem
    · exact (hpu.1 a' haa').1
  have hhid : ∀ a', (s'.piles a').hidden = (s.piles a').hidden :=
    walk_hidden_eq hwf hj
  have hpool := walk_pool_rev hj'
  have hfd : ∀ σ, s.found σ = s'.found σ :=
    found_eq_of_rungVec hwf hwf' hrung
  refine zone_faceUp_of (mem_zones_of_wf hwf' c) ?_ ?_ ?_ ?_
  · intro σ hcon
    rw [← hfd σ] at hcon
    exact hpu.2.2.2 σ hcon
  · intro a' hcon
    rw [hhid a'] at hcon
    exact hnh a' hcon
  · intro hcon
    rcases hpool c (Or.inl hcon) with h | h
    · exact hpu.2.1 h
    · exact hpu.2.2.1 h
  · intro hcon
    rcases hpool c (Or.inr hcon) with h | h
    · exact hpu.2.1 h
    · exact hpu.2.2.1 h

/-- **THE ZONE ROW — THE FACE-UP SET IS AN (ORBIT, TUPLE) INVARIANT**
(the excursion closure): at equal rungs, an orbit-mate holds exactly
the same cards face-up.  Every card raised mid-journey returns —
its face-up membership is an endpoint fact, priced by the census
and the shuffle's pool/hidden conservation. -/
theorem faceUp_iff {s s' : State} (hwf : s.WF)
    (horb : sameOrbitSetoid.r s s')
    (hrung : ∀ σ, rungAt s σ = rungAt s' σ) :
    ∀ c, (∃ a, c ∈ (s.piles a).faceUp) ↔ (∃ a, c ∈ (s'.piles a).faceUp) := by
  obtain ⟨ρ, hj1, τ, hj2⟩ := horb
  have hwf' : s'.WF := walk_wf hwf hj2
  refine fun c => ⟨?_, ?_⟩
  · exact faceUp_of_walk hwf hwf' hj2 hj1 hrung c
  · exact faceUp_of_walk hwf' hwf hj1 hj2 (fun σ => (hrung σ).symm) c

/-! ## §9. The battery -/

#print axioms canSitOn_twin_pair
#print axioms step_pool_rev
#print axioms walk_pool_rev
#print axioms walk_hidden_eq
#print axioms walk_wf
#print axioms faceUp_iff
