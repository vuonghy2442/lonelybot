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
