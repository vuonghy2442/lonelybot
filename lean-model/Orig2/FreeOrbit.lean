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

/-! ## §3. The seat rows — parented-ness and the class census -/

/-- The custom `lastOf` never answers `none` on a nonempty list.
Lineage: CargoRaise §4's private row — restated here per the kit
rule. -/
private theorem lastOf_eq_none : ∀ (l : List Card), lastOf l = none → l = [] := by
  intro l
  cases l with
  | nil => intro _; rfl
  | cons w t =>
      cases t with
      | nil =>
          intro h
          rw [show lastOf [w] = some w from rfl] at h
          exact absurd h (Option.some_ne_none w)
      | cons w2 t2 =>
          intro h
          rw [show lastOf (w :: w2 :: t2) = lastOf (w2 :: t2) from rfl] at h
          exact absurd (lastOf_eq_none (w2 :: t2) h) (List.cons_ne_nil w2 t2)

/-- **Parented st c** — the card sits on some parent (a non-king's
seat condition; a king sits on nothing by the rank arithmetic, so
its seat condition is bareness instead). -/
def Parented (st : State) (c : Card) : Prop :=
  ∃ z, seatOf st c = some (Sum.inr z)

/-- **THE SEAT-ARM BRIDGE** — for a held card, the flat iff's
`bs ≠ []` arm is exactly the parented reading: the below-part is
nonempty iff the seat is an `inr` (the parent, the below-part's
last). -/
theorem parented_iff_below {st : State} {c : Card} {a : Anchor}
    (hh : st.pileHolding c = some a) :
    Parented st c ↔ below c ((st.piles a).faceUp) ≠ [] := by
  have hseat : seatOf st c = match List.getLast? (below c ((st.piles a).faceUp)) with
    | none => some (Sum.inl a) | some z => some (Sum.inr z) := tfc_seatOf_pair hh
  constructor
  · rintro ⟨z, hz⟩
    intro hnil
    simp only [hseat, hnil, List.getLast?] at hz
    injection hz with hz2
    cases hz2
  · intro hne
    have h1 : List.getLast? (below c ((st.piles a).faceUp)) ≠ none := by
      intro hcon
      have h2 : lastOf (below c ((st.piles a).faceUp)) = none := by
        rw [← tfc_getLast?_lastOf]; exact hcon
      exact hne (lastOf_eq_none _ h2)
    cases hlast : List.getLast? (below c ((st.piles a).faceUp)) with
    | none => exact absurd hlast h1
    | some z => exact ⟨z, by rw [hseat, hlast]⟩

/-- **A REVERSIBLE SLIDE IS A CARGO-CLASS PAIR** — the forward leg
is the leg itself; the return is the mirror (a single `tabToTab`,
`tabToTab_mirror`), itself reversible (`reversible_mirrorW`).  This
is the bridge that carries the orbit's slide letters into the
certified class machinery. -/
theorem bareCargo_of_slide {u v : State} {d : Card} {b : Base} (hwf : u.WF)
    (hstep : State.step u (Move.tabToTab d b) = some v)
    (hrev : reversibleAtW u (Move.tabToTab d b)) : BareCargoEquiv u v := by
  obtain ⟨b₂, hfire2⟩ := tabToTab_mirror hwf hstep hrev
  exact ⟨Steps.cons ⟨d, b, hstep, hrev⟩ (Steps.refl v),
    Steps.cons ⟨d, b₂, hfire2, reversible_mirrorW hfire2 hstep⟩ (Steps.refl u)⟩

/-- **THE CLASS CENSUS, ONE WAY** — across a bare-cargo pair, every
non-king's parented-ness is preserved: the split iff's twin-carry
clause forces every seat change to go `inr → inr.twin` (parented to
parented), and unchanged seats are unchanged. -/
private theorem parented_of_bareCargo {u v : State} (hwf : u.WF) (hwf' : v.WF)
    (h : BareCargoEquiv u v) {c : Card} (hk : c.rank ≠ Rank.king)
    (hp : Parented u c) : Parented v c := by
  obtain ⟨z, hz⟩ := hp
  have hc := ((bareCargo_iff_split hwf hwf').mp h).1.2 c hk
  by_cases hchg : seatOf u c = seatOf v c
  · refine ⟨z, ?_⟩
    rw [← hchg]; exact hz
  · obtain ⟨z', hu', hv'⟩ := hc hchg
    exact ⟨z'.twin, hv'⟩

/-- **THE CLASS CENSUS** — across a bare-cargo pair (in particular:
across every single reversible slide), a non-king card is parented
at one end iff at the other.  The orbit's slide letters inherit
this wholesale. -/
theorem parented_bareCargo {u v : State} (hwf : u.WF) (hwf' : v.WF)
    (h : BareCargoEquiv u v) {c : Card} (hk : c.rank ≠ Rank.king) :
    Parented u c ↔ Parented v c :=
  ⟨parented_of_bareCargo hwf hwf' h hk,
    parented_of_bareCargo hwf' hwf ⟨h.2, h.1⟩ hk⟩

/-- **THE PULL'S RETURN LANDS PARENTED** — a non-king returning
from the foundation sits on a parent (the `inr` landing: the empty
anchor is king-only), with the host pile's old face-up as its
below-part. -/
theorem pull_parented {u v : State} {c : Card} {b : Base} (hwf : u.WF)
    (hstep : State.step u (Move.foundToTab c b) = some v)
    (hk : c.rank ≠ Rank.king) : Parented v c := by
  obtain ⟨c', hft, hc', hcp, hv⟩ := step_foundToTab_inv hstep
  cases b with
  | inl a =>
      obtain ⟨-, hkg⟩ := canPlace_inl hcp
      exact absurd hkg hk
  | inr z =>
      obtain ⟨k, hz, hsit⟩ := canPlace_inr hcp
      have hzmid : (u.setFound c.suit (chop (u.found c.suit))).pileOfTop z = some k :=
        hz
      have hpk : (v.piles k).faceUp = (u.piles k).faceUp ++ [c] := by
        rw [hv]
        have hput : ((u.setFound c.suit (chop (u.found c.suit))).putCard c (Sum.inr z)).piles k
            = { (u.setFound c.suit (chop (u.found c.suit))).piles k with
                faceUp := ((u.setFound c.suit (chop (u.found c.suit))).piles k).faceUp ++ [c] } := by
          simp only [State.putCard, hzmid, setPile_piles_self]
        rw [hput]
        rfl
      have hmem : c ∈ (v.piles k).faceUp := by
        rw [hpk]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      have hhold : v.pileHolding c = some k :=
        (pileHolding_eq_some_iff (step_wf hwf hstep)).2 hmem
      have hcf : c ∈ u.found c.suit := by
        have hlast : lastOf (u.found c.suit) = some c := by
          show u.foundTop c.suit = some c
          rw [hc'] at hft
          exact hft
        exact lastOf_mem hlast
      have hnotmem : c ∉ (u.piles k).faceUp := by
        intro hcon
        exact ((mem_found_unique hwf hcf).1 k).2 hcon
      refine (parented_iff_below hhold).mpr ?_
      rw [hpk, below_snoc_not_mem hnotmem]
      exact (pileOfTop_top hz).1

/-- The census complement: a card that is nowhere face-up lives in
the foundations, some hidden deck, or the pool.  (The constructive
zones-unfolding — no case split on undecidable existentials.) -/
private theorem zone_notFaceUp {st : State} (hwf : st.WF) {c : Card}
    (h : ¬ ∃ a, c ∈ (st.piles a).faceUp) :
    (∃ σ, c ∈ st.found σ) ∨ (∃ a, c ∈ (st.piles a).hidden) ∨ (c ∈ st.stock ∨ c ∈ st.waste) := by
  obtain ⟨zs, hzs, hczs⟩ := List.mem_flatMap.mp (mem_zones_of_wf hwf c)
  rcases List.mem_append.mp hzs with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · obtain ⟨σ, -, hzeq⟩ := List.mem_map.mp h2
      rw [← hzeq] at hczs
      exact Or.inl ⟨σ, hczs⟩
    · obtain ⟨a, -, hzeq⟩ := List.mem_map.mp h2
      rw [← hzeq] at hczs
      rcases List.mem_append.mp hczs with hmem | hmem
      · exact Or.inr (Or.inl ⟨a, hmem⟩)
      · exact absurd ⟨a, hmem⟩ h
  · rcases List.mem_cons.mp h1 with rfl | h1
    · exact Or.inr (Or.inr (Or.inl hczs))
    · rcases List.mem_cons.mp h1 with rfl | h1
      · exact Or.inr (Or.inr (Or.inr hczs))
      · exact absurd h1 (List.not_mem_nil)

/-- The exclusion trio: a card in the foundations, a hidden deck, or
the pool is nowhere face-up. -/
private theorem not_faceUp_of_found {st : State} (hwf : st.WF) {c : Card} {σ : Suit}
    (hm : c ∈ st.found σ) : ¬ ∃ a, c ∈ (st.piles a).faceUp := by
  rintro ⟨a, hcon⟩
  exact ((mem_found_unique hwf hm).1 a).2 hcon

private theorem not_faceUp_of_hidden {st : State} (hwf : st.WF) {c : Card} {a : Anchor}
    (hm : c ∈ (st.piles a).hidden) : ¬ ∃ a', c ∈ (st.piles a').faceUp := by
  rintro ⟨a', hcon⟩
  by_cases haa' : a' = a
  · rw [haa'] at hcon
    exact mem_hidden_not_faceUp hwf hm hcon
  · exact ((mem_pile_unique hwf (Or.inl hm)).1 a' haa').2 hcon

private theorem not_faceUp_of_pool {st : State} (hwf : st.WF) {c : Card}
    (hm : c ∈ st.stock ∨ c ∈ st.waste) : ¬ ∃ a, c ∈ (st.piles a).faceUp := by
  rintro ⟨a, hcon⟩
  rcases hm with hs | hw'
  · exact ((mem_stock_unique hwf hs).1 a).2 hcon
  · exact ((mem_waste_unique hwf hw').1 a).2 hcon

/-- **THE FOUND-MEMBERSHIP STEP ROW** — a reversible step preserves
foundation membership for every card it does not pull: the draw
conserves the founds, the raise appends (the prefix survives), the
pull chops only its own top, the slide never writes found. -/
private theorem step_found_mem {u v : State} {m : Move} {c : Card}
    (hstep : State.step u m = some v) (hrev : reversibleAtW u m)
    (hmem : ∃ σ, c ∈ u.found σ) (hne : ∀ b, m ≠ Move.foundToTab c b) :
    ∃ σ, c ∈ v.found σ := by
  cases m with
  | draw =>
      obtain ⟨σ, hm⟩ := hmem
      refine ⟨σ, ?_⟩
      rw [← (chart_draw hstep).2.1 σ]
      exact hm
  | wasteToFound d => exact absurd hrev (wasteToFound_not_reversibleAtW u d)
  | wasteToTab d b => exact absurd hrev (wasteToTab_not_reversibleAtW u d b)
  | tabToFound d =>
      obtain ⟨hnext, ap, hpa, hv⟩ := step_tabToFound_inv hstep
      obtain ⟨σ, hm⟩ := hmem
      refine ⟨σ, ?_⟩
      rw [hv]
      show c ∈ (u.setFound d.suit (u.found d.suit ++ [d])).found σ
      simp only [State.setFound]
      by_cases hsd : σ = d.suit
      · rw [if_pos hsd]
        rw [hsd] at hm
        exact List.mem_append.mpr (Or.inl hm)
      · rw [if_neg hsd]
        exact hm
  | foundToTab d b =>
      have hne' : d ≠ c := by
        intro hcon
        exact hne b (by rw [hcon])
      obtain ⟨c', hft, hc', hcp, hvl⟩ := step_foundToTab_inv hstep
      obtain ⟨σ, hm⟩ := hmem
      refine ⟨σ, ?_⟩
      rw [hvl, putCard_found]
      show c ∈ (u.setFound d.suit (chop (u.found d.suit))).found σ
      simp only [State.setFound]
      by_cases hsd : σ = d.suit
      · rw [if_pos hsd]
        rw [hsd] at hm
        have hlast : lastOf (u.found d.suit) = some d := by
          rw [hc'] at hft
          show u.foundTop d.suit = some d
          exact hft
        have hsplit : u.found d.suit = chop (u.found d.suit) ++ [d] :=
          lastOf_chop hlast
        rw [hsplit] at hm
        rcases List.mem_append.mp hm with h' | h'
        · exact h'
        · exact absurd (List.mem_singleton.mp h') (fun hcon => hne' hcon.symm)
      · rw [if_neg hsd]
        exact hm
  | tabToTab d b =>
      obtain ⟨a, hh, hcp, hfr, hv⟩ := step_tabToTab_inv hstep
      obtain ⟨σ, hm⟩ := hmem
      refine ⟨σ, ?_⟩
      rw [hv, putRun_found, setPile_found]
      exact hm

/-- **THE NO-ARRIVAL ROW** — a reversible step that does not pull `c`
cannot bring it face-up (the zone route: the census complement at
the origin, the three conservations, the exclusion trio). -/
private theorem step_notFaceUp_of_ne {u v : State} {m : Move} (hwf : u.WF)
    (hstep : State.step u m = some v) (hrev : reversibleAtW u m) {c : Card}
    (hnu : ¬ ∃ a, c ∈ (u.piles a).faceUp) (hne : ∀ b, m ≠ Move.foundToTab c b) :
    ¬ ∃ a, c ∈ (v.piles a).faceUp := by
  rintro ⟨a, hy⟩
  have hwf' : v.WF := step_wf hwf hstep
  rcases zone_notFaceUp hwf hnu with ⟨σ, hf⟩ | ⟨a', hh⟩ | (hs | hw')
  · obtain ⟨σ', hm'⟩ := step_found_mem hstep hrev ⟨σ, hf⟩ hne
    exact not_faceUp_of_found hwf' hm' ⟨a, hy⟩
  · have hh' : c ∈ (v.piles a').hidden := by
      rw [rev_step_hidden_eq hwf hstep hrev a']
      exact hh
    exact not_faceUp_of_hidden hwf' hh' ⟨a, hy⟩
  · exact not_faceUp_of_pool hwf' (step_pool_rev hstep hrev c (Or.inl hs)) ⟨a, hy⟩
  · exact not_faceUp_of_pool hwf' (step_pool_rev hstep hrev c (Or.inr hw')) ⟨a, hy⟩

/-- **THE ARRIVAL IDENTIFICATION** — the only letter that brings a
card face-up is its own pull: if a reversible step takes `c` from
off-board to face-up, the move is `foundToTab c b`. -/
theorem step_arrival {u v : State} {m : Move} (hwf : u.WF)
    (hstep : State.step u m = some v) (hrev : reversibleAtW u m) {c : Card}
    (hnu : ¬ ∃ a, c ∈ (u.piles a).faceUp) (hy : ∃ a, c ∈ (v.piles a).faceUp) :
    ∃ b, m = Move.foundToTab c b := by
  cases m with
  | draw =>
      exact absurd hy (step_notFaceUp_of_ne hwf hstep hrev hnu
        (fun _ hb => absurd hb (by simp)))
  | wasteToFound d => exact absurd hrev (wasteToFound_not_reversibleAtW u d)
  | wasteToTab d b => exact absurd hrev (wasteToTab_not_reversibleAtW u d b)
  | tabToFound d =>
      exact absurd hy (step_notFaceUp_of_ne hwf hstep hrev hnu
        (fun _ hb => absurd hb (by simp)))
  | tabToTab d b =>
      exact absurd hy (step_notFaceUp_of_ne hwf hstep hrev hnu
        (fun _ hb => absurd hb (by simp)))
  | foundToTab d b =>
      by_cases hdc : d = c
      · refine ⟨b, ?_⟩
        rw [hdc]
      · exact absurd hy (step_notFaceUp_of_ne hwf hstep hrev hnu
          (fun _ hb => by injection hb with hb'; exact hdc hb'))

/-- Face-up cards have seats. -/
private theorem seatOf_ne_of_faceUp {st : State} {c : Card} (hwf : st.WF)
    (h : ∃ a, c ∈ (st.piles a).faceUp) : seatOf st c ≠ none := by
  obtain ⟨a, hm⟩ := h
  have hh : st.pileHolding c = some a := (pileHolding_eq_some_iff hwf).2 hm
  rw [tfc_seatOf_eq]
  cases hhold : st.pileHolding c with
  | none => exact absurd hh (by rw [hhold]; simp)
  | some a₂ =>
      simp only [hhold]
      cases hlast : List.getLast? (below c ((st.piles a₂).faceUp)) with
      | none => simp only [hlast]; exact Option.some_ne_none _
      | some z => simp only [hlast]; exact Option.some_ne_none _

/-- The raise removes its card from the face-up board. -/
private theorem raise_notFaceUp {u v : State} {c : Card} (hwf : u.WF)
    (hstep : State.step u (Move.tabToFound c) = some v) :
    ¬ ∃ a, c ∈ (v.piles a).faceUp := by
  obtain ⟨hnext, ap, hpa, hv⟩ := step_tabToFound_inv hstep
  have hcf : c ∈ v.found c.suit := by
    rw [hv]
    change c ∈ (if c.suit = c.suit then u.found c.suit ++ [c] else u.found c.suit)
    have hss : c.suit = c.suit := rfl
    rw [if_pos hss]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  rintro ⟨a, hcon⟩
  exact ((mem_found_unique (step_wf hwf hstep) hcf).1 a).2 hcon

/-- **THE PER-STEP PARENTED CENSUS** — along one reversible step, a
non-king that is face-up at both ends keeps its parented-ness: the
draw preserves every seat; the slide is a cargo pair (the class
census); the raise preserves every other seated card's seat; the
pull preserves every non-pulled card's seat, and the pulled card
itself lands parented. -/
theorem step_parented {u v : State} {m : Move} (hwf : u.WF)
    (hstep : State.step u m = some v) (hrev : reversibleAtW u m) {c : Card}
    (hk : c.rank ≠ Rank.king)
    (hu : ∃ a, c ∈ (u.piles a).faceUp) (hv : ∃ a, c ∈ (v.piles a).faceUp)
    (hp : Parented u c) : Parented v c := by
  cases m with
  | wasteToFound d => exact absurd hrev (wasteToFound_not_reversibleAtW u d)
  | wasteToTab d b => exact absurd hrev (wasteToTab_not_reversibleAtW u d b)
  | draw =>
      obtain ⟨z, hz⟩ := hp
      refine ⟨z, ?_⟩
      rw [(chart_draw hstep).1 c]
      exact hz
  | tabToFound d =>
      by_cases hcd : c = d
      · subst hcd
        exact absurd hv (raise_notFaceUp hwf hstep)
      · obtain ⟨z, hz⟩ := hp
        have hseat := raise_seat_change_of_seated hstep hrev
          (seatOf_ne_of_faceUp hwf hu) hcd
        refine ⟨z, ?_⟩
        rw [hseat]; exact hz
  | foundToTab d b =>
      by_cases hcd : c = d
      · subst hcd
        exact pull_parented hwf hstep hk
      · obtain ⟨z, hz⟩ := hp
        have hseat := pull_seat_change hstep c hcd
        refine ⟨z, ?_⟩
        rw [hseat]; exact hz
  | tabToTab d b =>
      exact (parented_bareCargo hwf (step_wf hwf hstep)
        (bareCargo_of_slide hwf hstep hrev) hk).mp hp

/-- A parented card is face-up (the seat exists). -/
private theorem faceUp_of_parented {st : State} {c : Card} (hp : Parented st c) :
    ∃ a, c ∈ (st.piles a).faceUp := by
  obtain ⟨z, hz⟩ := hp
  rw [tfc_seatOf_eq] at hz
  cases hh : st.pileHolding c with
  | none =>
      rw [hh] at hz
      exact absurd (show none = some (Sum.inr z) from hz)
        (fun hcon => Option.some_ne_none _ hcon.symm)
  | some a => exact ⟨a, pileHolding_mem hh⟩

/-- An unheld card is nowhere face-up. -/
private theorem not_faceUp_of_holding_none {st : State} (hwf : st.WF) {c : Card}
    (hh : st.pileHolding c = none) : ¬ ∃ a, c ∈ (st.piles a).faceUp := by
  rintro ⟨a, hm⟩
  rw [(pileHolding_eq_some_iff hwf).2 hm] at hh
  exact (Option.some_ne_none a) hh

/-- **THE JOURNEY CENSUS, FROZEN FORM** — along a witness shuffle, a
non-king that is face-up at the far end is parented unless it was
already unparented-face-up at the origin.  The disjunction form
carries both the stay-cases (the per-step census) and the
away-intervals (an arrival is its own pull, which lands parented);
the contrapositive is the unparented-bottom freeze: a face-up
unparented card at the end was face-up unparented at the start. -/
theorem walk_parented {u : State} (hwf : u.WF) {ρ : List Move} {v : State}
    (h : ShufflePlayW u ρ v) : ∀ c, c.rank ≠ Rank.king →
    (∃ a, c ∈ (v.piles a).faceUp) →
    ((¬ ∃ a, c ∈ (u.piles a).faceUp) ∨ Parented u c) → Parented v c := by
  revert hwf
  induction h with
  | nil st =>
      intro _ _ _ hy hdisj
      rcases hdisj with hnu | hp
      · exact absurd hy hnu
      · exact hp
  | @cons st s1 W m ρ' hlet hstep hrest ih =>
      intro hwf c hk hy hdisj
      have hwf1 : s1.WF := step_wf hwf hstep
      rcases hdisj with hnu | hp
      · cases hh : s1.pileHolding c with
        | none =>
            exact ih hwf1 c hk hy (Or.inl (not_faceUp_of_holding_none hwf1 hh))
        | some a =>
            obtain ⟨b, hmb⟩ := step_arrival hwf hstep hlet hnu ⟨a, pileHolding_mem hh⟩
            rw [hmb] at hstep
            exact ih hwf1 c hk hy (Or.inr (pull_parented hwf hstep hk))
      · have huf : ∃ a, c ∈ (st.piles a).faceUp := faceUp_of_parented hp
        cases hh : s1.pileHolding c with
        | none =>
            exact ih hwf1 c hk hy (Or.inl (not_faceUp_of_holding_none hwf1 hh))
        | some a =>
            exact ih hwf1 c hk hy (Or.inr
              (step_parented hwf hstep hlet hk huf ⟨a, pileHolding_mem hh⟩ hp))

/-- **THE ORBIT PARENTED ROW** — at equal rungs, an orbit-mate
preserves every non-king's parented-ness: the journey census along
both directions of the orbit, riding the zone row for the face-up
transport. -/
theorem parented_orbit_rung {s s' : State} (hwf : s.WF)
    (horb : sameOrbitSetoid.r s s')
    (hrung : ∀ σ, rungAt s σ = rungAt s' σ) {c : Card} (hk : c.rank ≠ Rank.king) :
    Parented s c ↔ Parented s' c := by
  have hiff := faceUp_iff hwf horb hrung
  obtain ⟨ρ, hj1, τ, hj2⟩ := horb
  have hwf' : s'.WF := walk_wf hwf hj2
  constructor
  · intro hp
    exact walk_parented hwf hj2 c hk ((hiff c).mp (faceUp_of_parented hp)) (Or.inr hp)
  · intro hp
    exact walk_parented hwf' hj1 c hk ((hiff c).mpr (faceUp_of_parented hp)) (Or.inr hp)

/-- **Bare st c** — the card is held and its pile's hidden deck is
empty (the king's seat condition: a king sits on nothing, so its
flat arm is exactly the hidden emptiness). -/
def Bare (st : State) (c : Card) : Prop :=
  ∃ a, st.pileHolding c = some a ∧ (st.piles a).hidden = []

/-- A king cannot sit on anything (the rank arithmetic: the sitter
would need a rank above king). -/
private theorem canSitOn_ne_king {c z : Card} (h : canSitOn c z = true) :
    c.rank ≠ Rank.king := by
  intro hking
  obtain ⟨hrank, -⟩ := (canSitOn_eq c z).mp h
  have hidx : c.rank.toIdx = 12 := by rw [hking]; rfl
  have hlt := Rank.toIdx_lt z.rank
  rw [hidx] at hrank
  omega

/-- **A HELD KING'S SEAT IS THE ANCHOR** — kings sit on nothing, so
a held king is the face-up bottom: its seat is `inl a` and its
below-part is empty. -/
private theorem king_seat_inl {st : State} {K : Card} {a : Anchor} (hwf : st.WF)
    (hking : K.rank = Rank.king) (hh : st.pileHolding K = some a) :
    seatOf st K = some (Sum.inl a) ∧ below K ((st.piles a).faceUp) = [] := by
  rw [tfc_seatOf_pair hh]
  cases hlast : List.getLast? (below K ((st.piles a).faceUp)) with
  | none =>
      refine ⟨rfl, ?_⟩
      rw [tfc_getLast?_lastOf] at hlast
      exact lastOf_eq_none _ hlast
  | some z =>
      exfalso
      rw [tfc_getLast?_lastOf] at hlast
      exact (canSitOn_ne_king (tfc_seat_parent hwf hh hlast).1) hking

/-- An `inl` seat determines the holding pile. -/
private theorem holding_of_seat_inl {st : State} {c : Card} {a : Anchor}
    (h : seatOf st c = some (Sum.inl a)) : st.pileHolding c = some a := by
  rw [tfc_seatOf_eq] at h
  cases hh : st.pileHolding c with
  | none =>
      rw [hh] at h
      exact absurd (show none = some (Sum.inl a) from h)
        (fun hcon => Option.some_ne_none _ hcon.symm)
  | some a' =>
      rw [hh] at h
      cases hlast : List.getLast? (below c ((st.piles a').faceUp)) with
      | none =>
          simp only [hlast] at h
          injection h with h2
          injection h2 with h3
          rw [h3]
      | some z =>
          simp only [hlast] at h
          injection h with h2
          cases h2

/-- Both arms of the king orbit's fuel set have empty hidden decks. -/
private theorem hidden_eq_of_VKSet {st : State} {j : Anchor} (h : VKSet st j) :
    (st.piles j).hidden = [] := by
  rcases h with hvac | ⟨cc, hseat, -, hhidden⟩
  · exact ((Pile.isEmpty_eq _).mp hvac).1
  · exact hhidden

/-- **A RETURNING KING LANDS BARE** — the pull of a king can only
target an empty anchor (a king sits on nothing), whose hidden deck
is empty by construction. -/
theorem pull_king_bare {u v : State} {K : Card} {b : Base} (hwf : u.WF)
    (hstep : State.step u (Move.foundToTab K b) = some v)
    (hking : K.rank = Rank.king) : Bare v K := by
  obtain ⟨c', hft, hc', hcp, hv⟩ := step_foundToTab_inv hstep
  cases b with
  | inl a' =>
      have hpile : v = (u.setFound K.suit (chop (u.found K.suit))).setPile a' ⟨[], [K]⟩ := by
        rw [hv]; rfl
      have hwfv := step_wf hwf hstep
      rw [hpile] at hwfv
      rw [hpile]
      refine ⟨a', (pileHolding_eq_some_iff hwfv).2 ?_, ?_⟩
      · rw [setPile_piles_self]; exact List.mem_cons_self ..
      · rw [setPile_piles_self]
  | inr z =>
      obtain ⟨k, hz, hsit⟩ := canPlace_inr hcp
      exact absurd hking (canSitOn_ne_king hsit)

/-- **THE PER-STEP KING BARENESS CENSUS** — along one reversible
step, a king held at both ends keeps its bareness: the draw, raise
and pull of other cards preserve the seat (hence the holding) and
the hidden deck; the slide is a cargo pair, and the split iff's
king clause sends every seat change to a fuel anchor — both of
whose arms have empty hidden decks, which the step's hidden
invariance transports. -/
theorem step_king_bare {u v : State} {m : Move} (hwf : u.WF)
    (hstep : State.step u m = some v) (hrev : reversibleAtW u m) {K : Card}
    (hking : K.rank = Rank.king)
    (hu : ∃ a, K ∈ (u.piles a).faceUp) (hv : ∃ a, K ∈ (v.piles a).faceUp)
    (hb : Bare u K) : Bare v K := by
  obtain ⟨a, hhold, hhidden⟩ := hb
  have hseat := (king_seat_inl hwf hking hhold).1
  have hhid : ∀ a', (v.piles a').hidden = (u.piles a').hidden :=
    rev_step_hidden_eq hwf hstep hrev
  cases m with
  | wasteToFound d => exact absurd hrev (wasteToFound_not_reversibleAtW u d)
  | wasteToTab d b => exact absurd hrev (wasteToTab_not_reversibleAtW u d b)
  | draw =>
      have hseatv : seatOf v K = some (Sum.inl a) := by
        rw [(chart_draw hstep).1 K]; exact hseat
      exact ⟨a, holding_of_seat_inl hseatv, by rw [hhid a]; exact hhidden⟩
  | tabToFound d =>
      by_cases hkd : K = d
      · rw [← hkd] at hstep
        exact absurd hv (raise_notFaceUp hwf hstep)
      · have hseatv : seatOf v K = some (Sum.inl a) := by
          rw [raise_seat_change_of_seated hstep hrev
            (seatOf_ne_of_faceUp hwf hu) hkd]
          exact hseat
        exact ⟨a, holding_of_seat_inl hseatv, by rw [hhid a]; exact hhidden⟩
  | foundToTab d b =>
      by_cases hkd : K = d
      · rw [← hkd] at hstep
        exact pull_king_bare hwf hstep hking
      · have hseatv : seatOf v K = some (Sum.inl a) := by
          rw [pull_seat_change hstep K hkd]
          exact hseat
        exact ⟨a, holding_of_seat_inl hseatv, by rw [hhid a]; exact hhidden⟩
  | tabToTab d b =>
      have hkc := ((bareCargo_iff_split hwf (step_wf hwf hstep)).mp
        (bareCargo_of_slide hwf hstep hrev)).1.1 K hking
      by_cases hchg : seatOf u K = seatOf v K
      · have hseatv : seatOf v K = some (Sum.inl a) := by
          rw [← hchg]; exact hseat
        exact ⟨a, holding_of_seat_inl hseatv, by rw [hhid a]; exact hhidden⟩
      · obtain ⟨a', hseatv, hvk⟩ := hkc hchg
        exact ⟨a', holding_of_seat_inl hseatv,
          by rw [hhid a']; exact hidden_eq_of_VKSet hvk⟩

/-- A bare card is face-up (the holding exists). -/
private theorem faceUp_of_bare {st : State} {c : Card} (hb : Bare st c) :
    ∃ a, c ∈ (st.piles a).faceUp := by
  obtain ⟨a, hhold, -⟩ := hb
  exact ⟨a, pileHolding_mem hhold⟩

/-- **THE JOURNEY CENSUS FOR KINGS, FROZEN FORM** — along a witness
shuffle, a king that is face-up at the far end is bare unless it
was already off-board at the origin: the disjunction form carries
the stay-cases (the per-step census) and the away-intervals (a
returning king lands bare). -/
theorem walk_king_bare {u : State} (hwf : u.WF) {ρ : List Move} {v : State}
    (h : ShufflePlayW u ρ v) : ∀ c, c.rank = Rank.king →
    (∃ a, c ∈ (v.piles a).faceUp) →
    ((¬ ∃ a, c ∈ (u.piles a).faceUp) ∨ Bare u c) → Bare v c := by
  revert hwf
  induction h with
  | nil st =>
      intro _ _ _ hy hdisj
      rcases hdisj with hnu | hb
      · exact absurd hy hnu
      · exact hb
  | @cons st s1 W m ρ' hlet hstep hrest ih =>
      intro hwf c hkng hy hdisj
      have hwf1 : s1.WF := step_wf hwf hstep
      rcases hdisj with hnu | hb
      · cases hh : s1.pileHolding c with
        | none =>
            exact ih hwf1 c hkng hy (Or.inl (not_faceUp_of_holding_none hwf1 hh))
        | some a =>
            obtain ⟨b, hmb⟩ := step_arrival hwf hstep hlet hnu ⟨a, pileHolding_mem hh⟩
            rw [hmb] at hstep
            exact ih hwf1 c hkng hy (Or.inr (pull_king_bare hwf hstep hkng))
      · have hu : ∃ a, c ∈ (st.piles a).faceUp :=
          faceUp_of_bare hb
        cases hh : s1.pileHolding c with
        | none =>
            exact ih hwf1 c hkng hy (Or.inl (not_faceUp_of_holding_none hwf1 hh))
        | some a =>
            have hv : ∃ a, c ∈ (s1.piles a).faceUp := ⟨a, pileHolding_mem hh⟩
            exact ih hwf1 c hkng hy (Or.inr
              (step_king_bare hwf hstep hlet hkng hu hv hb))

/-- **THE ORBIT KING ROW** — at equal rungs, an orbit-mate preserves
every king's bareness: the journey census along both directions of
the orbit, riding the zone row for the face-up transport. -/
theorem king_bare_orbit_rung {s s' : State} (hwf : s.WF)
    (horb : sameOrbitSetoid.r s s')
    (hrung : ∀ σ, rungAt s σ = rungAt s' σ) {c : Card} (hking : c.rank = Rank.king) :
    Bare s c ↔ Bare s' c := by
  have hiff := faceUp_iff hwf horb hrung
  obtain ⟨ρ, hj1, τ, hj2⟩ := horb
  have hwf' : s'.WF := walk_wf hwf hj2
  constructor
  · intro hb
    exact walk_king_bare hwf hj2 c hking ((hiff c).mp (faceUp_of_bare hb)) (Or.inr hb)
  · intro hb
    exact walk_king_bare hwf' hj1 c hking ((hiff c).mpr (faceUp_of_bare hb)) (Or.inr hb)

/-! ## §4. The hatch factorization -/

/-- `below` membership is membership.  Lineage: Classification's
private `below_mem` — restated per the kit rule. -/
private theorem below_mem {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ below c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      rw [below_cons] at h
      by_cases hyc : y = c
      · rw [if_pos hyc] at h; cases h
      · rw [if_neg hyc] at h
        rcases List.mem_cons.mp h with rfl | h'
        · exact List.mem_cons_self ..
        · exact List.mem_cons.mpr (Or.inr (ih h'))

/-- No card is below itself. -/
private theorem below_irrefl {c : Card} : ∀ {l : List Card}, c ∉ below c l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons y t ih =>
      intro h
      rw [below_cons] at h
      by_cases hyc : y = c
      · rw [if_pos hyc] at h; cases h
      · rw [if_neg hyc] at h
        rcases List.mem_cons.mp h with rfl | h'
        · exact hyc rfl
        · exact ih h'

/-- A card strictly inside a nodup append is not in the front part.
Lineage: CargoRaise §4's private row — restated per the kit rule. -/
private theorem nodup_mid_notmem (d : Card) :
    ∀ (l rest : List Card), (l ++ d :: rest).Nodup → d ∉ l := by
  intro l
  induction l with
  | nil => intro rest _ hm; exact absurd hm (by simp)
  | cons x xs ih =>
      intro rest hnd hm
      rcases List.mem_cons.mp hm with rfl | hin
      · exact absurd (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
          ((List.nodup_cons.mp hnd).1)
      · exact ih rest ((List.nodup_cons.mp hnd).2) hin

/-- Append cancellation. -/
private theorem append_cancel {α : Type} : ∀ (l₁ t₁ t₂ : List α),
    l₁ ++ t₁ = l₁ ++ t₂ → t₁ = t₂ := by
  intro l₁
  induction l₁ with
  | nil => intro t₁ t₂ h; exact h
  | cons x xs ih =>
      intro t₁ t₂ h
      injection h with h1 h2
      exact ih t₁ t₂ h2

/-- The sitters of one sittee are a twin pair (the sittee-side
two-seat: the fit equation pins the rank, the two-color pigeonhole
the color, the deck arithmetic the card). -/
private theorem sitter_pair {d e c : Card} (hd : canSitOn d c = true)
    (he : canSitOn e c = true) : d = e ∨ d = e.twin := by
  obtain ⟨hrd, hcd⟩ := (canSitOn_eq d c).mp hd
  obtain ⟨hre, hce⟩ := (canSitOn_eq e c).mp he
  exact card_eq_twin_of_rank_color (Rank.toIdx_inj (by omega))
    (color_eq_of_ne hcd hce)

/-- The fit is twin-blind in the target. -/
private theorem canSitOn_twin_target (e c : Card) : canSitOn e c.twin = canSitOn e c := by
  have hc2 : c.twin.suit.color = c.suit.color := by
    rcases c with ⟨s, r⟩
    cases s <;> rfl
  rw [show canSitOn e c.twin
      = (decide (e.rank.toIdx + 1 = c.twin.rank.toIdx)
          && decide (e.suit.color ≠ c.twin.suit.color)) from rfl,
    show canSitOn e c
      = (decide (e.rank.toIdx + 1 = c.rank.toIdx)
          && decide (e.suit.color ≠ c.suit.color)) from rfl,
    show c.twin.rank.toIdx = c.rank.toIdx from rfl, hc2]

/-- The front part of a `w`-headed representation is the below-of-w. -/
private theorem below_w_eq {w : Card} {X F : List Card} (hwX : w ∉ X) :
    ∀ (l : List Card), l = X ++ w :: F → below w l = X := by
  intro l hl
  rw [hl, (tfc_below_fromCard_excl w X (w :: F) hwX).1, below_cons_self, List.append_nil]

/-- **THE SEAT'S POSITIONAL UNIQUENESS** — at most one card sits
directly on any given card: two `inr w` seats are the same card
(the below/fromCard arithmetic at the unique occurrence, with the
run discipline's duplicate-freedom). -/
theorem seat_inr_inj {st : State} {y z w : Card} (hwf : st.WF)
    (hy : seatOf st y = some (Sum.inr w)) (hz : seatOf st z = some (Sum.inr w)) :
    y = z := by
  obtain ⟨a_y, hhy, -, hly⟩ := tfc_seatOf_of_inr hy
  obtain ⟨a_z, hhz, -, hlz⟩ := tfc_seatOf_of_inr hz
  have hhwy : st.pileHolding w = some a_y :=
    (pileHolding_eq_some_iff hwf).2 (below_mem (lastOf_mem hly))
  have hhwz : st.pileHolding w = some a_z :=
    (pileHolding_eq_some_iff hwf).2 (below_mem (lastOf_mem hlz))
  have ha : a_y = a_z := by
    injection (hhwz.symm.trans hhwy) with h
    exact h.symm
  subst ha
  -- the two representations of the pile:
  have hrep_y : (st.piles a_y).faceUp
      = chop (below y ((st.piles a_y).faceUp))
        ++ w :: fromCard y ((st.piles a_y).faceUp) := by
    have h1 : below y ((st.piles a_y).faceUp)
        = chop (below y ((st.piles a_y).faceUp)) ++ [w] := lastOf_chop hly
    have h2 := tfc_below_fromCard y ((st.piles a_y).faceUp)
    rw [h1, List.append_assoc] at h2
    exact h2.symm
  have hrep_z : (st.piles a_y).faceUp
      = chop (below z ((st.piles a_y).faceUp))
        ++ w :: fromCard z ((st.piles a_y).faceUp) := by
    have h1 : below z ((st.piles a_y).faceUp)
        = chop (below z ((st.piles a_y).faceUp)) ++ [w] := lastOf_chop hlz
    have h2 := tfc_below_fromCard z ((st.piles a_y).faceUp)
    rw [h1, List.append_assoc] at h2
    exact h2.symm
  have hnd : ((st.piles a_y).faceUp).Nodup := runOK_nodup (hwf.2.1 a_y)
  have hwXy : w ∉ chop (below y ((st.piles a_y).faceUp)) := by
    intro hcon
    exact nodup_mid_notmem w _ _ (by rw [← hrep_y]; exact hnd) hcon
  have hwXz : w ∉ chop (below z ((st.piles a_y).faceUp)) := by
    intro hcon
    exact nodup_mid_notmem w _ _ (by rw [← hrep_z]; exact hnd) hcon
  have hXy : below w ((st.piles a_y).faceUp)
      = chop (below y ((st.piles a_y).faceUp)) :=
    below_w_eq hwXy _ hrep_y
  have hXz : below w ((st.piles a_y).faceUp)
      = chop (below z ((st.piles a_y).faceUp)) :=
    below_w_eq hwXz _ hrep_z
  rw [← hXy] at hrep_y
  rw [← hXz] at hrep_z
  -- cancel the common prefix:
  have h5 := append_cancel _ _ _ (hrep_y.symm.trans hrep_z)
  have hyin : y ∈ (st.piles a_y).faceUp := pileHolding_mem hhy
  have hzin : z ∈ (st.piles a_y).faceUp := pileHolding_mem hhz
  obtain ⟨r_y, hry⟩ := tfc_fromCard_cons_head _ hyin
  obtain ⟨r_z, hrz⟩ := tfc_fromCard_cons_head _ hzin
  have h6 : fromCard y ((st.piles a_y).faceUp)
      = fromCard z ((st.piles a_y).faceUp) := congrArg List.tail h5
  have hfin : y :: r_y = z :: r_z := hry.symm.trans (h6.trans hrz)
  injection hfin with hA hB

/-- **THE RUN-HEAD COVER** — if the fromCard tail is nonempty,
its head sits directly on `c` (the adjacent fit of the run
discipline, reflected into the seat). -/
theorem cover_of_run {st : State} {c : Card} {a : Anchor} {run : List Card}
    (hwf : st.WF) (hhold : st.pileHolding c = some a)
    (hfc : fromCard c ((st.piles a).faceUp) = c :: run) (hrne : run ≠ []) :
    ∃ d, seatOf st d = some (Sum.inr c) := by
  obtain ⟨d, rest', hrun⟩ : ∃ d rest', run = d :: rest' := by
    cases run with
    | nil => exact absurd rfl hrne
    | cons w t => exact ⟨w, t, rfl⟩
  have hshape : (st.piles a).faceUp
      = below c ((st.piles a).faceUp) ++ c :: d :: rest' := by
    have h := tfc_below_fromCard c ((st.piles a).faceUp)
    rw [hfc, hrun] at h
    exact h.symm
  have hnd : ((st.piles a).faceUp).Nodup := runOK_nodup (hwf.2.1 a)
  have hresh : (below c ((st.piles a).faceUp) ++ [c]) ++ d :: rest'
      = (st.piles a).faceUp := by
    rw [List.append_assoc, List.cons_append, List.nil_append]
    exact hshape.symm
  rw [← hresh] at hnd
  have hdnotin : d ∉ below c ((st.piles a).faceUp) ++ [c] :=
    nodup_mid_notmem d _ _ hnd
  have hcd : c ≠ d := by
    intro hcon
    apply hdnotin
    rw [← hcon]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hbelod : below d ((st.piles a).faceUp)
      = below c ((st.piles a).faceUp) ++ [c] := by
    have hdnotbelow : d ∉ below c ((st.piles a).faceUp) :=
      fun hcon => hdnotin (List.mem_append.mpr (Or.inl hcon))
    have hex := (tfc_below_fromCard_excl d
      (below c ((st.piles a).faceUp)) (c :: d :: rest') hdnotbelow).1
    rw [← hshape] at hex
    rw [hex, below_cons, if_neg hcd, below_cons_self]
  have hdmem : d ∈ (st.piles a).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))
  refine ⟨d, ?_⟩
  rw [tfc_seatOf_pair ((pileHolding_eq_some_iff hwf).2 hdmem), hbelod,
    tfc_getLast?_lastOf, lastOf_snoc]

/-- **THE NIL-RUN KILLS COVERS** — if `c` is the last card of its
pile's face-up run, nothing sits on it (the cover's fromCard
cancellation). -/
theorem no_cover_of_nil_run {st : State} {c y : Card} {a : Anchor}
    (hwf : st.WF) (hhold : st.pileHolding c = some a)
    (hfc : fromCard c ((st.piles a).faceUp) = c :: [])
    (hcov : seatOf st y = some (Sum.inr c)) : False := by
  obtain ⟨a_y, hhy, -, hly⟩ := tfc_seatOf_of_inr hcov
  have hhc : st.pileHolding c = some a_y :=
    (pileHolding_eq_some_iff hwf).2 (below_mem (lastOf_mem hly))
  have ha : a_y = a := Option.some.inj (hhc.symm.trans hhold)
  subst ha
  have hnd : ((st.piles a_y).faceUp).Nodup := runOK_nodup (hwf.2.1 a_y)
  have hrep : (st.piles a_y).faceUp
      = chop (below y ((st.piles a_y).faceUp))
        ++ c :: fromCard y ((st.piles a_y).faceUp) := by
    have h1 : below y ((st.piles a_y).faceUp)
        = chop (below y ((st.piles a_y).faceUp)) ++ [c] := lastOf_chop hly
    have h2 := tfc_below_fromCard y ((st.piles a_y).faceUp)
    rw [h1, List.append_assoc] at h2
    exact h2.symm
  have hcX : c ∉ chop (below y ((st.piles a_y).faceUp)) := by
    intro hcon
    exact nodup_mid_notmem c _ _ (by rw [← hrep]; exact hnd) hcon
  have hfc2 : fromCard c ((st.piles a_y).faceUp)
      = c :: fromCard y ((st.piles a_y).faceUp) := by
    have hex := (tfc_below_fromCard_excl c
      (chop (below y ((st.piles a_y).faceUp)))
      (c :: fromCard y ((st.piles a_y).faceUp)) hcX).2
    rw [← hrep] at hex
    rw [hex, fromCard_head_eq]
  rw [hfc] at hfc2
  have hyin : y ∈ fromCard y ((st.piles a_y).faceUp) := by
    obtain ⟨r, hr⟩ := tfc_fromCard_cons_head _ (pileHolding_mem hhy)
    rw [hr]
    exact List.mem_cons_self ..
  injection hfc2 with hc1 hc2
  rw [← hc2] at hyin
  exact absurd hyin (by simp)

/-- **HELD AND UNCOVERED MEANS TOPPING** — a face-up card with
nothing on it tops its pile. -/
theorem tops_of_held_no_cover {st : State} {c : Card}
    (hwf : st.WF) (hheld : ∃ a, c ∈ (st.piles a).faceUp)
    (hnocov : ¬ ∃ y, seatOf st y = some (Sum.inr c)) :
    st.pileOfTop c ≠ none := by
  obtain ⟨a, hmem⟩ := hheld
  have hhold : st.pileHolding c = some a := (pileHolding_eq_some_iff hwf).2 hmem
  obtain ⟨run, hfc⟩ := tfc_fromCard_cons_head _ hmem
  have hrun : run = [] := by
    cases run with
    | nil => rfl
    | cons d rest' =>
        exact absurd (cover_of_run hwf hhold hfc (by simp)) (by
          rintro ⟨d, hd⟩
          exact hnocov ⟨d, hd⟩)
  have htop : (st.piles a).top = some c := by
    show lastOf ((st.piles a).faceUp) = some c
    have h1 := tfc_below_fromCard c ((st.piles a).faceUp)
    rw [hfc, hrun] at h1
    rw [← h1, lastOf_snoc]
  have hpt := (pileOfTop_eq_some_iff hwf).2 htop
  intro hcon
  rw [hcon] at hpt
  exact Option.some_ne_none _ hpt.symm

/-- The fit is twin-blind in the sitter (the sitter pair of `c` is
closed under twin). -/
private theorem canSitOn_twin_sitter (e c : Card) : canSitOn e.twin c = canSitOn e c := by
  have hc2 : e.twin.suit.color = e.suit.color := by
    rcases e with ⟨s, r⟩
    cases s <;> rfl
  rw [show canSitOn e.twin c
      = (decide (e.twin.rank.toIdx + 1 = c.rank.toIdx)
          && decide (e.twin.suit.color ≠ c.suit.color)) from rfl,
    show canSitOn e c
      = (decide (e.rank.toIdx + 1 = c.rank.toIdx)
          && decide (e.suit.color ≠ c.suit.color)) from rfl,
    show e.twin.rank.toIdx = e.rank.toIdx from rfl, hc2]

/-- A seated card's parent is a fit target of the twin pair: the
parent is `c` or `c.twin` (the sittee-side two-seat). -/
private theorem parent_of_seat {st : State} {x c z : Card} (hwf : st.WF)
    (hseat : seatOf st x = some (Sum.inr z)) (hfit : canSitOn x c = true) :
    z = c ∨ z = c.twin := by
  obtain ⟨a_x, hhold_x, -, hlast_x⟩ := tfc_seatOf_of_inr hseat
  exact canSitOn_twin_pair hfit (tfc_seat_parent hwf hhold_x hlast_x).1

/-- The covered card is face-up (it is below its cover). -/
private theorem faceUp_of_covered {st : State} {x z : Card}
    (hseat : seatOf st x = some (Sum.inr z)) :
    ∃ a', z ∈ (st.piles a').faceUp := by
  obtain ⟨a_x, hhold_x, -, hlast_x⟩ := tfc_seatOf_of_inr hseat
  exact ⟨a_x, below_mem (lastOf_mem hlast_x)⟩

/-- A seated card's parent is not a top (the cover hides it). -/
private theorem no_top_of_seat {st : State} {x z : Card} (hwf : st.WF)
    (hseat : seatOf st x = some (Sum.inr z)) : st.pileOfTop z = none := by
  obtain ⟨a_x, hhold_x, -, hlast_x⟩ := tfc_seatOf_of_inr hseat
  exact (tfc_seat_parent hwf hhold_x hlast_x).2

/-- No `inr` seat means unparented (the seat is the parentedness
witness-function). -/
private theorem not_parented_of_no_inr {st : State} {x : Card}
    (h : ∀ z, seatOf st x ≠ some (Sum.inr z)) : ¬ Parented st x := by
  intro hz
  rcases hz with ⟨z, hz2⟩
  exact h z hz2

/-- A `none` seat kills every `inr` seat equation. -/
private theorem no_inr_of_none {st : State} {x z : Card} (h : seatOf st x = none) :
    seatOf st x ≠ some (Sum.inr z) := by rw [h]; simp

/-- An `inl` seat kills every `inr` seat equation. -/
private theorem no_inr_of_inl {st : State} {x z : Card} {b' : Anchor}
    (h : seatOf st x = some (Sum.inl b')) :
    seatOf st x ≠ some (Sum.inr z) := by rw [h]; simp

/-- **THE HATCH FACTORIZATION** — the readiness hatch's cover clause
(the run empty, or the twin topping some pile) is, at `WF`, exactly the
sitter-pair census: either no sitter of `c` is parented, or the twin
is face-up and not both sitters are parented.  The four components —
the sitters' parentedness and the twin's face-up membership — are the
orbit-rung invariants the assembly rides.  Aces are vacuous (no card
fits on an ace, so no sitter ever instantiates the quantifier). -/
theorem hatch_iff {st : State} {c : Card} {a : Anchor} {run : List Card}
    (hwf : st.WF) (hhold : st.pileHolding c = some a)
    (hfc : fromCard c ((st.piles a).faceUp) = c :: run) :
    (run = [] ∨ st.pileOfTop c.twin ≠ none) ↔
      ∀ e, canSitOn e c = true →
        ((¬ Parented st e ∧ ¬ Parented st e.twin) ∨
          ((∃ a', c.twin ∈ (st.piles a').faceUp) ∧
            ¬ (Parented st e ∧ Parented st e.twin))) := by
  constructor
  · rintro (hrun | hpt) e he
    · -- Case A: nothing sits on c
      have hnc : ∀ y, seatOf st y = some (Sum.inr c) → False :=
        fun y hy => no_cover_of_nil_run hwf hhold (by rw [hfc, hrun]) hy
      have he_t : canSitOn e.twin c = true := (canSitOn_twin_sitter e c).trans he
      have hbranch : (∀ z, seatOf st e ≠ some (Sum.inr z)) →
          ((¬ Parented st e ∧ ¬ Parented st e.twin) ∨
            ((∃ a', c.twin ∈ (st.piles a').faceUp) ∧
              ¬ (Parented st e ∧ Parented st e.twin))) := by
        intro hE
        have hnotP : ¬ Parented st e := not_parented_of_no_inr hE
        cases hseatT : seatOf st e.twin with
        | none =>
            exact Or.inl ⟨hnotP,
              not_parented_of_no_inr (fun z => no_inr_of_none hseatT)⟩
        | some s =>
            cases s with
            | inl b' =>
                exact Or.inl ⟨hnotP,
                  not_parented_of_no_inr (fun z => no_inr_of_inl hseatT)⟩
            | inr z_t =>
                rcases parent_of_seat hwf hseatT he_t with hzc | hzct
                · exact (hnc e.twin (by rw [hzc] at hseatT; exact hseatT)).elim
                · rw [hzct] at hseatT
                  exact Or.inr ⟨faceUp_of_covered hseatT, fun hp => hnotP hp.1⟩
      cases hseatE : seatOf st e with
      | none => exact hbranch (fun z => no_inr_of_none hseatE)
      | some s =>
          cases s with
          | inl b' => exact hbranch (fun z => no_inr_of_inl hseatE)
          | inr z_e =>
              rcases parent_of_seat hwf hseatE he with hzc | hzct
              · exact (hnc e (by rw [hzc] at hseatE; exact hseatE)).elim
              · rw [hzct] at hseatE
                refine Or.inr ⟨faceUp_of_covered hseatE, ?_⟩
                rintro ⟨-, ⟨z_t, hz_t⟩⟩
                rcases parent_of_seat hwf hz_t he_t with hzc2 | hzct2
                · exact (hnc e.twin (by rw [hzc2] at hz_t; exact hz_t)).elim
                · rw [hzct2] at hz_t
                  exact (card_twin_ne e (seat_inr_inj hwf hz_t hseatE)).elim
    · -- Case B: the twin tops some pile
      have hH : ∃ a', c.twin ∈ (st.piles a').faceUp :=
        match hps : st.pileOfTop c.twin with
        | none => absurd hps hpt
        | some a' => ⟨a', lastOf_mem
            (show lastOf ((st.piles a').faceUp) = some c.twin from
              (pileOfTop_eq_some_iff hwf).1 hps)⟩
      have he_t : canSitOn e.twin c = true := (canSitOn_twin_sitter e c).trans he
      have hbranch : (∀ z, seatOf st e ≠ some (Sum.inr z)) →
          ((¬ Parented st e ∧ ¬ Parented st e.twin) ∨
            ((∃ a', c.twin ∈ (st.piles a').faceUp) ∧
              ¬ (Parented st e ∧ Parented st e.twin))) := by
        intro hE
        have hnotP : ¬ Parented st e := not_parented_of_no_inr hE
        cases hseatT : seatOf st e.twin with
        | none =>
            exact Or.inl ⟨hnotP,
              not_parented_of_no_inr (fun z => no_inr_of_none hseatT)⟩
        | some s =>
            cases s with
            | inl b' =>
                exact Or.inl ⟨hnotP,
                  not_parented_of_no_inr (fun z => no_inr_of_inl hseatT)⟩
            | inr z_t =>
                exact Or.inr ⟨hH, fun hp => hnotP hp.1⟩
      cases hseatE : seatOf st e with
      | none => exact hbranch (fun z => no_inr_of_none hseatE)
      | some s =>
          cases s with
          | inl b' => exact hbranch (fun z => no_inr_of_inl hseatE)
          | inr z_e =>
              have hzne : z_e ≠ c.twin := fun hzct =>
                hpt (by rw [← hzct]; exact no_top_of_seat hwf hseatE)
              have hzec : z_e = c := by
                rcases parent_of_seat hwf hseatE he with h | h'
                · exact h
                · exact absurd h' hzne
              refine Or.inr ⟨hH, ?_⟩
              rintro ⟨-, ⟨z_t, hz_t⟩⟩
              have hztc : z_t = c := by
                rcases parent_of_seat hwf hz_t he_t with h | h'
                · exact h
                · exact absurd h' (fun hzct =>
                    hpt (by rw [← hzct]; exact no_top_of_seat hwf hz_t))
              rw [hzec] at hseatE
              rw [hztc] at hz_t
              exact (card_twin_ne e (seat_inr_inj hwf hz_t hseatE)).elim
  · intro hrhs
    cases run with
    | nil => exact Or.inl rfl
    | cons w t =>
        obtain ⟨d, hcv⟩ := cover_of_run hwf hhold hfc (by simp)
        obtain ⟨a_d, hhold_d, -, hlast_d⟩ := tfc_seatOf_of_inr hcv
        have hd_fit : canSitOn d c = true := (tfc_seat_parent hwf hhold_d hlast_d).1
        rcases hrhs d hd_fit with ⟨h1, -⟩ | ⟨hH, -⟩
        · exact absurd ⟨c, hcv⟩ h1
        cases hpt : st.pileOfTop c.twin with
        | some a' => exact Or.inr (Option.some_ne_none _)
        | none =>
            exfalso
            obtain ⟨a2, hmem⟩ := hH
            have hhold_t : st.pileHolding c.twin = some a2 :=
              (pileHolding_eq_some_iff hwf).2 hmem
            obtain ⟨run', hfc_t⟩ := tfc_fromCard_cons_head _ hmem
            cases run' with
            | nil =>
                have htop : (st.piles a2).top = some c.twin := by
                  show lastOf ((st.piles a2).faceUp) = some c.twin
                  have h1 := tfc_below_fromCard c.twin ((st.piles a2).faceUp)
                  rw [hfc_t] at h1
                  rw [← h1, lastOf_snoc]
                exact Option.some_ne_none a2
                  (((pileOfTop_eq_some_iff hwf).2 htop).symm.trans hpt)
            | cons g t2 =>
                obtain ⟨f, hcv_f⟩ := cover_of_run hwf hhold_t hfc_t (by simp)
                obtain ⟨a_f, hhold_f, -, hlast_f⟩ := tfc_seatOf_of_inr hcv_f
                have hf_fit : canSitOn f c = true :=
                  (canSitOn_twin_target f c).symm.trans
                    (tfc_seat_parent hwf hhold_f hlast_f).1
                rcases hrhs f hf_fit with ⟨h1, -⟩ | ⟨-, hne_f⟩
                · exact absurd ⟨c.twin, hcv_f⟩ h1
                have hnf : ¬ Parented st f.twin :=
                  fun hQ => hne_f ⟨⟨c.twin, hcv_f⟩, hQ⟩
                rcases sitter_pair hd_fit hf_fit with rdf | rdft
                · rw [rdf] at hcv
                  exact (card_twin_ne c
                    (Sum.inr.inj (Option.some.inj (hcv_f.symm.trans hcv)))).elim
                · exact hnf (by rw [← rdft]; exact ⟨c, hcv⟩)

/-- `isSome` reads off non-`none`. -/
private theorem isSome_of_ne_none {α : Type} {o : Option α} (h : o ≠ none) :
    o.isSome = true := by
  cases hps : o with
  | none => exact absurd hps h
  | some a' => rfl

/-- Non-`none` reads off `isSome`. -/
private theorem ne_none_of_isSome {α : Type} {o : Option α} (h : o.isSome = true) :
    o ≠ none := by
  intro hcon
  rw [hcon] at h
  exact absurd h (by simp)

/-- **THE READINESS SEMANTICS** — the probe's flat computation is the
invariant reading: held, seated with company (non-king) or bare
(king), and the hatch's sitter-pair census.  Every component of the
right-hand side is an (orbit, rung-tuple) invariant. -/
theorem freeCardS_sem {st : State} {c : Card} (hwf : st.WF) :
    freeCardS st c = true ↔
      ∃ a, st.pileHolding c = some a ∧
        ((Parented st c ∧ c.rank ≠ Rank.king) ∨
          (Bare st c ∧ c.rank = Rank.king)) ∧
        (∀ e, canSitOn e c = true →
          ((¬ Parented st e ∧ ¬ Parented st e.twin) ∨
            ((∃ a', c.twin ∈ (st.piles a').faceUp) ∧
              ¬ (Parented st e ∧ Parented st e.twin)))) := by
  constructor
  · intro h
    rw [freeCardS] at h
    cases hhold : st.pileHolding c with
    | none => simp only [hhold] at h; exact absurd h (by simp)
    | some a =>
        simp only [hhold] at h
        have hcmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
        obtain ⟨run0, hcrr⟩ := tfc_fromCard_cons_head _ hcmem
        cases hF : fromCard c ((st.piles a).faceUp) with
        | nil =>
            rw [hF] at hcrr
            exact absurd hcrr (by simp)
        | cons x run =>
            rw [hF] at hcrr
            injection hcrr with hchd hrun
            simp only [hF] at h
            rw [Bool.and_eq_true] at h
            obtain ⟨hseat, hrot⟩ := h
            have hfc : fromCard c ((st.piles a).faceUp) = c :: run := by
              rw [hF, hchd]
            refine ⟨a, rfl, ?_, ?_⟩
            · rw [Bool.or_eq_true] at hseat
              rcases hseat with hbs | hhk
              · have hbl : below c ((st.piles a).faceUp) ≠ [] := decide_eq_true_iff.mp hbs
                have hk : c.rank ≠ Rank.king := fun hcon =>
                  hbl (king_seat_inl hwf hcon hhold).2
                exact Or.inl ⟨(parented_iff_below hhold).2 hbl, hk⟩
              · rw [Bool.and_eq_true] at hhk
                obtain ⟨hd1, hd2⟩ := hhk
                exact Or.inr ⟨⟨a, hhold, decide_eq_true_iff.mp hd1⟩,
                  decide_eq_true_iff.mp hd2⟩
            · rw [← hatch_iff hwf hhold hfc]
              rw [Bool.or_eq_true] at hrot
              rcases hrot with hr | his
              · exact Or.inl (decide_eq_true_iff.mp hr)
              · exact Or.inr (ne_none_of_isSome his)
  · rintro ⟨a, hhold, hseat, hh⟩
    have hcmem : c ∈ (st.piles a).faceUp := pileHolding_mem hhold
    obtain ⟨run, hcrr⟩ := tfc_fromCard_cons_head _ hcmem
    simp only [freeCardS, hhold, hcrr]
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [Bool.or_eq_true]
      rcases hseat with ⟨hp, hk⟩ | ⟨hb, hk⟩
      · exact Or.inl (decide_eq_true ((parented_iff_below hhold).mp hp))
      · rcases hb with ⟨a', hhold', hhidden'⟩
        have ha' : a' = a := Option.some.inj (hhold'.symm.trans hhold)
        rw [ha'] at hhidden'
        rw [Bool.and_eq_true]
        exact Or.inr ⟨decide_eq_true hhidden', decide_eq_true hk⟩
    · rw [Bool.or_eq_true]
      rcases (hatch_iff hwf hhold hcrr).2 hh with hr | hne
      · exact Or.inl (decide_eq_true hr)
      · exact Or.inr (isSome_of_ne_none hne)

/-- **THE READINESS IS AN (ORBIT, RUNG-TUPLE) INVARIANT** — at equal
rungs, an orbit-mate preserves every card's tableau-readiness: the
excursion closure carries the holdings, the seat census the
parented/bare arms, the hatch factorization the cover clause.  This is
the campaign's theorem — the S-license's tableau content cannot tell
orbit-mates apart. -/
theorem freeCardS_orbit_rung {s s' : State} (hwf : s.WF)
    (horb : sameOrbitSetoid.r s s')
    (hrung : ∀ σ, rungAt s σ = rungAt s' σ)
    {c : Card} : freeCardS s c = true ↔ freeCardS s' c = true := by
  have hiff := faceUp_iff hwf horb hrung
  have hpar : ∀ x : Card, x.rank ≠ Rank.king → (Parented s x ↔ Parented s' x) :=
    fun _ hx => parented_orbit_rung hwf horb hrung hx
  have hking : ∀ x : Card, x.rank = Rank.king → (Bare s x ↔ Bare s' x) :=
    fun _ hx => king_bare_orbit_rung hwf horb hrung hx
  obtain ⟨ρ, hj1, τ, hj2⟩ := horb
  have hwf' : s'.WF := walk_wf hwf hj2
  rw [freeCardS_sem hwf, freeCardS_sem hwf']
  constructor
  · rintro ⟨a, hhold, hseat, hh⟩
    have hmem : c ∈ (s.piles a).faceUp := pileHolding_mem hhold
    obtain ⟨a', hmem'⟩ := (hiff c).mp ⟨a, hmem⟩
    refine ⟨a', (pileHolding_eq_some_iff hwf').2 hmem', ?_, ?_⟩
    · rcases hseat with ⟨hp, hk⟩ | ⟨hb, hk⟩
      · exact Or.inl ⟨(hpar c hk).mp hp, hk⟩
      · exact Or.inr ⟨(hking c hk).mp hb, hk⟩
    · intro e he
      have heng : e.rank ≠ Rank.king := canSitOn_ne_king he
      have hetng : e.twin.rank ≠ Rank.king := by
        rcases e with ⟨s2, r2⟩
        exact heng
      rcases hh e he with h1 | ⟨hH, hne⟩
      · exact Or.inl ⟨fun hP' => h1.1 ((hpar e heng).mpr hP'),
          fun hQ' => h1.2 ((hpar e.twin hetng).mpr hQ')⟩
      · refine Or.inr ⟨(hiff c.twin).mp hH, ?_⟩
        rintro ⟨hP', hQ'⟩
        exact hne ⟨(hpar e heng).mpr hP', (hpar e.twin hetng).mpr hQ'⟩
  · rintro ⟨a', hhold', hseat', hh'⟩
    have hmem' : c ∈ (s'.piles a').faceUp := pileHolding_mem hhold'
    obtain ⟨a, hmem⟩ := (hiff c).mpr ⟨a', hmem'⟩
    refine ⟨a, (pileHolding_eq_some_iff hwf).2 hmem, ?_, ?_⟩
    · rcases hseat' with ⟨hp, hk⟩ | ⟨hb, hk⟩
      · exact Or.inl ⟨(hpar c hk).mpr hp, hk⟩
      · exact Or.inr ⟨(hking c hk).mpr hb, hk⟩
    · intro e he
      have heng : e.rank ≠ Rank.king := canSitOn_ne_king he
      have hetng : e.twin.rank ≠ Rank.king := by
        rcases e with ⟨s2, r2⟩
        exact heng
      rcases hh' e he with h1 | ⟨hH, hne⟩
      · exact Or.inl ⟨fun hP => h1.1 ((hpar e heng).mp hP),
          fun hQ => h1.2 ((hpar e.twin hetng).mp hQ)⟩
      · refine Or.inr ⟨(hiff c.twin).mpr hH, ?_⟩
        rintro ⟨hP, hQ⟩
        exact hne ⟨(hpar e heng).mp hP, (hpar e.twin hetng).mp hQ⟩

/-- **THE LICENSE COROLLARY** — at equal rungs, an orbit-mate
preserves the full S-license: the foundation gate rides the rung
congruence (`nextUp` reads the rung), the tableau-readiness the
campaign's theorem.  The residue's stage is set: within a rung
class, the license cannot tell orbit-mates apart. -/
theorem canRaiseS_orbit_rung {s s' : State} (hwf : s.WF)
    (horb : sameOrbitSetoid.r s s')
    (hrung : ∀ σ, rungAt s σ = rungAt s' σ) {c : Card} :
    CanRaiseS s c ↔ CanRaiseS s' c := by
  have hfree := freeCardS_orbit_rung (c := c) hwf horb hrung
  obtain ⟨ρ, hj1, τ, hj2⟩ := horb
  have hwf' : s'.WF := walk_wf hwf hj2
  have hnext : s.nextUp c = s'.nextUp c := by
    rw [State.nextUp, State.nextUp,
      show s.foundHeight c.suit = s'.foundHeight c.suit from hrung c.suit]
  rw [canRaiseS_split hwf, canRaiseS_split hwf', hnext, hfree]

/-! ## §9. The battery -/

#print axioms canSitOn_twin_pair
#print axioms step_pool_rev
#print axioms walk_pool_rev
#print axioms walk_hidden_eq
#print axioms walk_wf
#print axioms faceUp_iff
#print axioms parented_iff_below
#print axioms bareCargo_of_slide
#print axioms parented_bareCargo
#print axioms pull_parented
#print axioms step_arrival
#print axioms step_parented
#print axioms walk_parented
#print axioms parented_orbit_rung
#print axioms pull_king_bare
#print axioms step_king_bare
#print axioms walk_king_bare
#print axioms king_bare_orbit_rung
#print axioms seat_inr_inj
#print axioms cover_of_run
#print axioms no_cover_of_nil_run
#print axioms tops_of_held_no_cover
#print axioms hatch_iff
#print axioms freeCardS_sem
#print axioms freeCardS_orbit_rung
#print axioms canRaiseS_orbit_rung
