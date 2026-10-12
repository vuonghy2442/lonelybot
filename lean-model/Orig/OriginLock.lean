import Orig.PairConfine

/-!
# Orig.OriginLock — THE ORIGIN LOCK (the downward axis of the no-lock pairClass)

Within any macro class containing a `forkState`, a fork cannot witness
a LOWER rank of the same suit family: the downward sibling of
`Orig.PairConfine`'s upward card (`forkState_sameFamily_rankCeiling`,
the rank-never-advances half, carried there by the named residue
`crossing_door_barred`).  Together the two halves force the SAME RANK
at every same-family fork of one class, and `forkState_sameFamily_samePair`
then closes the family case of the no-lock pairClass theorem: same-family
forks of one class agree as pairs.  The empirical cross-check is the
probes' banked down-pair boards (`Orig/EpochProbeVis.lean`, `Orig/EpochProbe.lean`
`down_pair`/`vis_pair`: the rank-5 and rank-4 forks on one economy whose
only connecting leg — the dressing — is a certified commitment; this card
is those rows' theorem-grade general form).

THE CARD'S LADDER:

* §1 **THE FOUNDATION-RESIDENCY READ** — at the origin `st₁` (rank-`r`
  fork, witness `x` of rank index `r := x.rank.toIdx`), both family suit
  rungs pin at `r`, so by `pair_lowFamily_founded` every family card of
  rank index below `r` is FOUNDED — in particular the LOWER fork's
  would-be pair `{y, y.twin}` (rank index `r* := y.rank.toIdx < r`).
  Any witness journey to a lower-rank same-family end must therefore
  PULL: the per-suit raise/pull census (`witness_rung_census`) forces
  `raisesOf + (r − r*) ≤ pullsOf` on both family suits.
* §2 **THE SANDWICH ROLES** — at the lower fork `st₂` the endpoint
  pack (`forkState_witness_canRaise`, `pair_cover_pins`, the deck
  census): the witness `y` TOPS its own seat-sound pile, the twin sits
  DIRECTLY under the dress `d` (rank index `r*−1`, opposite family),
  the dress tops the twin's pile RANK-LOCKED OFF next-up (`st₂.nextUp d =
  false`, else the S-saturation of the fork fires a third live card),
  the two pair members live in TWO DIFFERENT piles, and the dress's
  whole card-directed landing lattice is exactly `{y, y.twin}` with the
  empty seat king-dead.
* §3 **THE DRESSER LOCK** (the mechanism rows, all proved): the deck
  census lattice (`dress_legalSeats_pair`: a family-opposite rank-`r*−1`
  card sits face-up only bare, or directly on a pair member); at the
  origin every on-board dresser is ISOLATED (`origin_dresser_isolated`,
  its would-be under- and over-neighbors are `r*−`family cards FOUND AT
  THE ORIGIN) and therefore FROZEN (`origin_dresser_frozen`: every
  reversible-journey leg preserves its bottom seat — the bare escapes
  all die: over a hidden deck by the reveal jury
  `journey_tabToTab_never_reveal`/`journey_tabToFound_never_reveal`,
  over an empty one by THE PILLAR — the king-refill copy
  `lock_emptyOrKingHead_play`: a non-king's emptied pile can never be
  restored); hidden-resident dressers are PINNED (`shuffle_hiddenPinned`)
  and stock/waste-resident dressers are CLOSED under witness journeys
  (`lock_stockWaste_closed`).  The one honestly-open case — the cover
  FOUNDED at the origin, the staircase/pollution endgame — is the
  card's single named residue `origin_cover_founded_case_barred`,
  carrying its complete route (the LIFO pull toggle, the descent
  drag, the census self-pollution — the `downAlt_pollutes` mechanism
  in the general form).
* §4 **THE ASSEMBLY** — `forkState_rankDrop_locked`: the forward
  witness play (`sameOrbit_forward`) hands every leg a
  `reversibleAtW` witness; the cover's origin residency trichotomy
  kills all but the founded case, and the residue closes it.
* §5 **THE FLOOR COROLLARY** — `forkState_family_rankFloor` (from
  `st₁`'s perspective no class member witnesses below `r`) and the
  assembly row `forkState_family_pairClass` (with PairConfine's
  rankCeiling in the other direction: same-family forks of one class
  agree in rank, hence — by `forkState_sameFamily_samePair` — as pairs).

House compliance: additive leaf; per-file copies of the banked private
rows per the house dedup discipline; every fresh head audited
(`#print axioms`); the one named residue carries its route in its
docstring.
-/

/-! ## §0. The private kit (per-file copies, the house dedup discipline) -/

/-- Two colors that both differ from a third agree (the copy of
`Orig/RunOrTwin.lean`'s private `color_pair`; `Orig/PairConfine.lean`
carries an identical copy). -/
private theorem lock_color_pair {a u v : Color} (h1 : a ≠ u) (h2 : a ≠ v) : u = v := by
  rcases a <;> rcases u <;> rcases v <;> simp_all

/-- **THE DECK CENSUS** — the cards of one rank and one color are
exactly the twin pair (the copy of `Orig/RunOrTwin.lean`'s private
`rankColor_pair`). -/
private theorem lock_rankColor_pair {c z : Card}
    (hr : z.rank.toIdx = c.rank.toIdx) (hc : z.suit.color = c.suit.color) :
    z = c ∨ z = c.twin := by
  rcases z with ⟨zs, zr⟩
  rcases c with ⟨cs, cr⟩
  have hrank : zr = cr := Rank.toIdx_inj hr
  subst hrank
  cases cs <;> cases zs <;> simp_all [Suit.color, Suit.twin, Card.twin]

/-- The adjacent-fit row of the run discipline (the copy of
`Orig/RunOrTwin.lean`'s private `runOK_adjacent_fit`): a card
directly covered in a well-formed run fits on the card below it. -/
private theorem lock_runOK_adjacent (c d : Card) :
    ∀ (X R : List Card), runOK (X ++ c :: d :: R) = true → canSitOn d c = true := by
  intro X
  induction X with
  | nil =>
      intro R h
      have h2 : runOK (c :: d :: R) = true := h
      rw [runOK, Bool.and_eq_true] at h2
      exact h2.1
  | cons w ws ih =>
      intro R h
      have h2 : runOK (w :: (ws ++ c :: d :: R)) = true := h
      cases hxs : (ws ++ c :: d :: R) with
      | nil =>
          cases ws with
          | nil => rw [List.nil_append] at hxs; exact absurd hxs (by simp)
          | cons v vs => rw [List.cons_append] at hxs; exact absurd hxs (by simp)
      | cons y ys =>
          rw [hxs] at h2
          rw [runOK, Bool.and_eq_true] at h2
          have htail : runOK (ws ++ c :: d :: R) = true := by
            rw [hxs]
            exact h2.2
          exact ih R htail

/-- The mnist-split: a card's face-up pile splits below it, at it. -/
private theorem lock_mem_split (c : Card) :
    ∀ (l : List Card), c ∈ l → ∃ bs rest, l = bs ++ c :: rest := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons z t ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | hm
      · exact ⟨[], t, rfl⟩
      · obtain ⟨bs, rest, hs⟩ := ih hm
        exact ⟨z :: bs, rest, by rw [hs]; rfl⟩

/-! ## §1. The foundation-residency read -/

/-- **THE LOWER-PAIR ORIGIN RESIDENCY** — at the origin `st₁`
(the rank-`r` fork witnessing `x`), the LOWER fork's would-be pair
cards `{y, y.twin}` (same suit family, rank index `r* < r`) are both
FOUNDED, and both family suit rungs pin at `r`: everything of the
family BELOW the fork's rank lives in the foundations at the origin,
so any journey to a lower-rank fork must PULL it back out. -/
theorem origin_lowerPairResident {st₁ : State} (hwf₁ : st₁.WF)
    {x y : Card} (hx : ForkWitness st₁ x)
    (hfam : y.suit = x.suit ∨ y.suit = x.twin.suit)
    (hlt : y.rank.toIdx < x.rank.toIdx) :
    y ∈ st₁.found y.suit ∧
      y.twin ∈ st₁.found y.twin.suit ∧
      rungAt st₁ y.suit = x.rank.toIdx ∧
      rungAt st₁ y.twin.suit = x.rank.toIdx := by
  have hcolfam : y.suit.color = x.suit.color := by
    rcases hfam with h | h
    · rw [h]
    · rw [h, Card.twin_suit, Suit.color_twin]
  have hcoltt : y.twin.suit.color = y.suit.color := by
    rw [Card.twin_suit, Suit.color_twin]
  refine ⟨pair_lowFamily_founded hwf₁ hx hcolfam hlt, ?_, ?_, ?_⟩
  · exact pair_lowFamily_founded hwf₁ hx (hcoltt.trans hcolfam)
      (by rw [Card.twin_rank]; exact hlt)
  · rcases hfam with h | h
    · rw [h]
      exact canRaiseS_rung ((hx.1 x).mp (Or.inl rfl))
    · rw [h]
      have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
      rwa [Card.twin_rank] at h2
  · rcases hfam with h | h
    · have hs : y.twin.suit = x.twin.suit := by
        simp only [Card.twin_suit, h]
      rw [hs]
      have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
      rwa [Card.twin_rank] at h2
    · have hs : y.twin.suit = x.suit := by
        simp only [Card.twin_suit, h, Suit.twin_twin]
      rw [hs]
      exact canRaiseS_rung ((hx.1 x).mp (Or.inl rfl))

/-- **THE PULL CENSUS** — along any witness journey from the origin to
the lower-rank same-family end, each family suit is pulled more than
it is raised — strictly more often than everything else, by exactly
the rank drop `r − r*`: the rung ledger of `witness_rung_census`
with both ends' rung pins. -/
theorem origin_lowerJourney_pulls {st₁ st₂ : State} (hwf₁ : st₁.WF)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hfam : y.suit = x.suit ∨ y.suit = x.twin.suit)
    {play : List Move} (hplay : ShufflePlayW st₁ play st₂)
    (hlt : y.rank.toIdx < x.rank.toIdx) :
    raisesOf play y.suit + (x.rank.toIdx - y.rank.toIdx) ≤ pullsOf play y.suit ∧
      raisesOf play y.twin.suit + (x.rank.toIdx - y.rank.toIdx)
        ≤ pullsOf play y.twin.suit := by
  obtain ⟨-, -, hr₁, hr₂⟩ := origin_lowerPairResident hwf₁ hx hfam hlt
  have he₁ : rungAt st₂ y.suit = y.rank.toIdx :=
    canRaiseS_rung ((hy.1 y).mp (Or.inl rfl))
  have he₂ : rungAt st₂ y.twin.suit = y.rank.toIdx := by
    have h2 := canRaiseS_rung ((hy.1 y.twin).mp (Or.inr rfl))
    rwa [Card.twin_rank] at h2
  have hc₁ := witness_rung_census hplay y.suit
  have hc₂ := witness_rung_census hplay y.twin.suit
  constructor <;> omega

/-- A card is never its own twin (the copy of the in-tree private row). -/
private theorem lock_card_twin_ne (c : Card) : c.twin ≠ c := by
  intro hcon
  exact Suit.twin_ne c.suit (congrArg Card.suit hcon)

/-! ## §2. The sandwich roles — the lower fork's endpoint geometry -/

/-- **THE SANDWICH GEOMETRY AT THE LOWER FORK** — the endpoint pack
consumed by the dresser lock: the witness `y` TOPS its own seat-sound
pile `a`; the covered twin sits DIRECTLY under the DRESS `d` (rank
index `r*−1`, opposite family color), the dress tops the twin's pile
`c` — a DIFFERENT pile (the run discipline's strict descent bars one
pile from holding both equal-rank pair members) — RANK-LOCKED OFF
next-up (`st₂.nextUp d = false`, else the fork's S-saturation fires
`d` as a third live card), king-dead (no empty-seat recourse), and its
whole card-directed landing lattice is exactly the pair `{y, y.twin}`. -/
theorem lower_sandwich {st₂ : State} (hwf₂ : st₂.WF) {y : Card}
    (hy : ForkWitness st₂ y) :
    ∃ (a c : Anchor) (bsC : List Card) (d : Card),
      st₂.pileOfTop y = some a ∧
      (chop (st₂.piles a).faceUp ≠ [] ∨
        ((st₂.piles a).hidden = [] ∧ y.rank = Rank.king)) ∧
      (st₂.piles c).faceUp = bsC ++ [y.twin, d] ∧
      d.rank.toIdx + 1 = y.rank.toIdx ∧
      d.suit.color ≠ y.suit.color ∧
      st₂.pileOfTop d = some c ∧ a ≠ c ∧
      st₂.nextUp d = false ∧
      d.rank ≠ Rank.king ∧
      (∀ z, st₂.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin) ∧
      (∀ k, st₂.canPlace d (Sum.inl k) = true → False) := by
  -- the witness's own vanilla liveness: it tops, with its seat intact
  obtain ⟨-, a, hpo, hseat⟩ := id (forkState_witness_canRaise hwf₂ hy.1 hy.2)
  -- the twin's final cover package
  obtain ⟨c, bsC, d, hshape, -, hfit, hpod, hnext, -⟩ := pair_cover_pins hwf₂ hy
  -- the fit arithmetic: the dress is one rank below, opposite family
  obtain ⟨hrk, hcd⟩ := (canSitOn_eq d y.twin).mp hfit
  rw [Card.twin_rank] at hrk
  have hcoltt : y.twin.suit.color = y.suit.color := by
    rw [Card.twin_suit, Suit.color_twin]
  have hcdy : d.suit.color ≠ y.suit.color := by rw [← hcoltt]; exact hcd
  -- the dress is no king: r* < 13 forces its rank below the king index
  have h13 := Rank.toIdx_lt y.rank
  have hK : d.rank ≠ Rank.king := by
    intro hcon
    rw [hcon] at hrk
    have hk12 : Rank.king.toIdx = 12 := rfl
    omega
  refine ⟨a, c, bsC, d, hpo, hseat, hshape, hrk, hcdy, hpod, ?_, hnext, hK, ?_, ?_⟩
  · -- the two pair members live in DIFFERENT piles
    by_cases hac : a = c
    · exfalso
      have hymem : y ∈ (st₂.piles a).faceUp := Pile.mem_of_top (pileOfTop_top hpo).2
      rw [hac] at hymem
      have hytmem : y.twin ∈ (st₂.piles c).faceUp := by
        rw [hshape]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      have hytne : y ≠ y.twin := fun hcon =>
        lock_card_twin_ne y hcon.symm
      have hydne : y ≠ d := fun hcon =>
        hcdy (by rw [hcon])
      rw [hshape] at hymem
      rcases List.mem_append.mp hymem with hybs | hytl
      · have hok : runOK (bsC ++ [y.twin, d]) = true := by
          rw [← hshape]
          exact hwf₂.runOK_of c
        have hdesc := runOK_desc (P := bsC) (S := [y.twin, d]) hok hybs
          (List.mem_cons.2 (Or.inl rfl))
        rw [Card.twin_rank] at hdesc
        omega
      · rcases List.mem_cons.mp hytl with heq | hdl
        · exact hytne heq
        · exact hydne (List.mem_singleton.mp hdl)
    · exact hac
  · -- the lattice: every card-directed placement of the dress tops a pair member
    intro z hcp
    obtain ⟨k, -, hsit⟩ := canPlace_inr hcp
    obtain ⟨hrkz, hcolz⟩ := (canSitOn_eq d z).mp hsit
    have hrz : z.rank.toIdx = y.rank.toIdx := by omega
    exact lock_rankColor_pair hrz (lock_color_pair hcdy hcolz).symm
  · -- the empty seat is king-only and the dress is no king
    intro k hcp
    obtain ⟨-, hking⟩ := canPlace_inl hcp
    exact hK hking

/-- The `below` read at a non-head position (the copy of the banked
row, spelled off `State.below_cons`). -/
private theorem lock_below_cons_ne {c x : Card} {t : List Card} (h : x ≠ c) :
    below c (x :: t) = x :: below c t := by
  rw [below_cons, ite_eq_right h]

/-! ## §3. THE DRESSER LOCK — the mechanism rows -/

/-- **THE UNDER-SEAT LATTICE** (the deck census read): a family-opposite
card of rank index `r*−1`, face-up in a well-formed pile, sits BARE, or
DIRECTLY on a pair member `{y, y.twin}` — the twin-blind fit lattice
consumed by the lock: the lawful landlord of a dresser seat is always
one of the two pair cards themselves. -/
theorem dress_legalSeats_pair {st : State} (hwf : st.WF) {y c : Card}
    {a : Anchor} {bs rest : List Card}
    (hdcol : c.suit.color ≠ y.suit.color)
    (hrankc : c.rank.toIdx + 1 = y.rank.toIdx)
    (hshape : (st.piles a).faceUp = bs ++ c :: rest) :
    bs = [] ∨ ∃ w, lastOf bs = some w ∧ (w = y ∨ w = y.twin) := by
  by_cases hbs : bs = []
  · exact Or.inl hbs
  · obtain ⟨w, hw⟩ := lastOf_exists hbs
    obtain ⟨bs', hbsw⟩ := lastOf_eq_snoc hw
    have hshape' : (st.piles a).faceUp = bs' ++ w :: c :: rest := by
      rw [hshape, hbsw]
      simp
    have hok : runOK (bs' ++ w :: c :: rest) = true := by
      rw [← hshape']
      exact hwf.runOK_of a
    obtain ⟨hrk, hcol⟩ := (canSitOn_eq c w).mp (lock_runOK_adjacent w c bs' rest hok)
    refine Or.inr ⟨w, hw, ?_⟩
    have hrw : w.rank.toIdx = y.rank.toIdx := by omega
    exact lock_rankColor_pair hrw (lock_color_pair hdcol hcol).symm

/-- **THE ORIGIN ISOLATION** — at the class origin `st₁` every
on-board dresser (family-opposite, rank index `r*−1 < r`) is
ISOLATED: its pile's whole face-up content is the dresser alone.
Below it would sit a family pair card (the under-seat lattice) — but
every family card of rank below `r` is FOUNDED at the origin; above it
would sit a family card of rank index `r*−2` — founded as well. -/
theorem origin_dresser_isolated {st₁ : State} (hwf₁ : st₁.WF)
    {x y : Card} (hx : ForkWitness st₁ x)
    (hfam : y.suit = x.suit ∨ y.suit = x.twin.suit)
    (hlt : y.rank.toIdx < x.rank.toIdx)
    {c : Card} (hdcolx : c.suit.color ≠ x.suit.color)
    (hrankc : c.rank.toIdx + 1 = y.rank.toIdx)
    {a : Anchor} (hmem : c ∈ (st₁.piles a).faceUp) :
    (st₁.piles a).faceUp = [c] := by
  have hcolfam : y.suit.color = x.suit.color := by
    rcases hfam with h | h
    · rw [h]
    · rw [h, Card.twin_suit, Suit.color_twin]
  have hcoltt : y.twin.suit.color = y.suit.color := by
    rw [Card.twin_suit, Suit.color_twin]
  have hdcoly : c.suit.color ≠ y.suit.color := fun h =>
    hdcolx (by rw [← hcolfam]; exact h)
  obtain ⟨bs, rest, hshape⟩ := lock_mem_split c (st₁.piles a).faceUp hmem
  rcases dress_legalSeats_pair hwf₁ (st := st₁) (y := y) (c := c) (a := a)
    (bs := bs) (rest := rest) hdcoly hrankc hshape with rfl | ⟨w, hw, hwyz⟩
  · -- bare below: the above-seat also dies — any first cover would be a
    -- founded low family card
    cases rest with
    | nil => rw [hshape]; rfl
    | cons u us =>
        exfalso
        have hok : runOK ([] ++ c :: u :: us) = true := by
          rw [← hshape]
          exact hwf₁.runOK_of a
        obtain ⟨hrk, hcol⟩ := (canSitOn_eq u c).mp (lock_runOK_adjacent c u [] us hok)
        have huColx : u.suit.color = x.suit.color :=
          (lock_color_pair hdcolx (fun h => hcol h.symm)).symm
        have huLt : u.rank.toIdx < x.rank.toIdx := by omega
        have huf := pair_lowFamily_founded hwf₁ hx huColx huLt
        have huUp : u ∈ (st₁.piles a).faceUp := by
          rw [hshape]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))
        exact (mem_faceUp_only hwf₁ huUp).2.2.2.2 u.suit huf
  · exfalso
    -- the landlord branch: a face-up pair member under the dresser —
    -- but it is FOUNDED at the origin
    have hwbs : w ∈ bs := lastOf_mem hw
    have hwUp : w ∈ (st₁.piles a).faceUp := by
      rw [hshape]
      exact List.mem_append.mpr (Or.inl hwbs)
    have hwcolx : w.suit.color = x.suit.color := by
      rcases hwyz with h | h
      · rw [h, hcolfam]
      · rw [h, hcoltt, hcolfam]
    have hwr : w.rank.toIdx = y.rank.toIdx := by
      rcases hwyz with h | h
      · rw [h]
      · rw [h, Card.twin_rank]
    have hwlt : w.rank.toIdx < x.rank.toIdx := by
      rw [hwr]
      exact hlt
    exact (mem_faceUp_only hwf₁ hwUp).2.2.2.2 w.suit
      (pair_lowFamily_founded hwf₁ hx hwcolx hwlt)

/-! ### The pillar (the king-refill read, per-file copies of the
banked `Orig/PositionSeat` placeholders) -/

private theorem lock_fromCard_run_head (e : Card) :
    ∀ (l : List Card), fromCard e l ≠ [] → ∃ tr, fromCard e l = e :: tr := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [fromCard])
  | cons z zs ih =>
      intro h
      by_cases hze : z = e
      · exact ⟨zs, by rw [hze, fromCard_cons_self]⟩
      · rw [fromCard_cons_ne zs hze] at h
        obtain ⟨tr, htr⟩ := ih h
        exact ⟨tr, by rw [fromCard_cons_ne zs hze]; exact htr⟩

private theorem lock_afterRunRemoved_bare {p : Pile} (hh : p.hidden = []) :
    Pile.afterRunRemoved p ([] : List Card) = (⟨[], []⟩ : Pile) := by
  show Pile.revealTop { p with faceUp := [] } = _
  rcases p with ⟨hl, fl⟩
  cases hl with
  | nil => rfl
  | cons g gs => exact absurd hh (by simp)

private theorem lock_afterRunRemoved_cons {p : Pile} {u : Card} {us : List Card} :
    Pile.afterRunRemoved p (u :: us) = (⟨p.hidden, u :: us⟩ : Pile) := rfl

private theorem lock_canPlace_inl_king {s : State} {w : Card} {k : Anchor}
    (h : s.canPlace w (Sum.inl k) = true) : w.rank = Rank.king := by
  rw [State.canPlace, Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

private theorem lock_pileOfTop_of_piles {s t : State} (z : Card)
    (hp : s.piles = t.piles) : s.pileOfTop z = t.pileOfTop z := by
  show (firstWhere (fun a' => decide ((s.piles a').top = some z)) Anchor.all) =
    (firstWhere (fun a' => decide ((t.piles a').top = some z)) Anchor.all)
  rw [hp]

/-- The run-removal read at the invariant's own pile (the copy of
`Orig/PositionSeat`'s private `arr_Q`). -/
private theorem lock_arr_Q {P : Pile} {e : Card}
    (hmemE : e ∈ P.faceUp)
    (hQ : (P.faceUp = [] ∧ P.hidden = []) ∨
      ∃ K t, P.faceUp = K :: t ∧ K.rank = Rank.king ∧ P.hidden = []) :
    (Pile.afterRunRemoved P (below e P.faceUp)).faceUp = [] ∧
      (Pile.afterRunRemoved P (below e P.faceUp)).hidden = [] ∨
      ∃ K t, (Pile.afterRunRemoved P (below e P.faceUp)).faceUp = K :: t ∧
        K.rank = Rank.king ∧ (Pile.afterRunRemoved P (below e P.faceUp)).hidden = [] := by
  by_cases hpre : below e P.faceUp = []
  · have hhQ : P.hidden = [] := by
      rcases hQ with ⟨-, hh⟩ | ⟨-, -, -, -, hh⟩
      · exact hh
      · exact hh
    rw [hpre, lock_afterRunRemoved_bare hhQ]
    exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨w, ws, hpc⟩ := list_cons_of_ne_nil hpre
    rw [hpc, lock_afterRunRemoved_cons]
    rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
    · exfalso
      rw [hfup] at hmemE
      exact absurd hmemE (by simp)
    · by_cases hE : e = K
      · exfalso
        rw [hfup, hE, below_cons_self] at hpc
        exact absurd hpc (by simp)
      · rw [hfup, below_cons_ne t (fun hc => hE hc.symm)] at hpc
        injection hpc with hw hws
        rw [← hw, ← hws]
        exact Or.inr ⟨K, below e t, rfl, hK, hhA⟩

/-- The one-step preservation of the empty-or-king-headed pile
invariant (the copy of `Orig/PositionSeat`'s private `oneStep_pileInv`). -/
private theorem lock_oneStep_pileInv {A : Anchor} {s s' : State} {m : Move}
    (hstep : State.step s m = some s')
    (hQ : ((s.piles A).faceUp = [] ∧ (s.piles A).hidden = []) ∨
      ∃ K t, (s.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
        (s.piles A).hidden = []) :
    ((s'.piles A).faceUp = [] ∧ (s'.piles A).hidden = []) ∨
      ∃ K t, (s'.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
        (s'.piles A).hidden = [] := by
  cases m with
  | draw =>
      have hd : s.stepDraw = some s' := hstep
      rw [stepDraw_piles hd]
      exact hQ
  | wasteToFound w =>
      obtain ⟨-, x, xs, hwst, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      have hp : (({s.setFound w.suit (s.found w.suit ++ [w]) with waste := xs} : State).piles A)
          = s.piles A := rfl
      rw [hp]
      exact hQ
  | wasteToTab w b =>
      obtain ⟨hg, x, xs, hwst, hs⟩ := step_wasteToTab_inv hstep
      rw [Bool.and_eq_true] at hg
      rw [hs]
      cases b with
      | inl k =>
          have hp : (({s.putCard w (Sum.inl k) with waste := xs} : State).piles A)
              = (if A = k then (⟨[], [w]⟩ : Pile) else s.piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨w, [], rfl, lock_canPlace_inl_king hg.2, rfl⟩
            · exfalso
              obtain ⟨hemp, -⟩ := canPlace_inl hg.2
              rw [← hAk] at hemp
              have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
              rw [hfup] at hfupE
              exact absurd hfupE (by simp)
          · rw [ite_eq_right hAk]
            exact hQ
      | inr z =>
          obtain ⟨kk, hpin, -⟩ := canPlace_inr hg.2
          have hp : (({s.putCard w (Sum.inr z) with waste := xs} : State).piles A)
              = (if A = kk then { s.piles kk with faceUp := (s.piles kk).faceUp ++ [w] }
                 else s.piles A) := by
            simp only [putCard_piles_inr _ _ _ _ hpin]
          rw [hp]
          by_cases hAk : A = kk
          · rw [ite_eq_left hAk]
            rw [hAk] at hQ
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
            · exfalso
              have hne := (pileOfTop_top hpin).1
              rw [hfup] at hne
              exact absurd hne (by simp)
            · refine Or.inr ⟨K, t ++ [w], ?_, hK, hhA⟩
              show (s.piles kk).faceUp ++ [w] = K :: (t ++ [w])
              rw [hfup, List.cons_append]
          · rw [ite_eq_right hAk]
            exact hQ
  | tabToFound w =>
      obtain ⟨-, k, hpod, hs⟩ := step_tabToFound_inv hstep
      have hpileEq : s'.piles A = (if A = k then
          Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
          else s.piles A) := by rw [hs]
      rw [hpileEq]
      by_cases hAk : A = k
      · rw [hAk] at hQ
        have hself : (if A = k then Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
            else s.piles A) = Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp) :=
          ite_eq_left hAk
        rw [hself]
        rcases hQ with ⟨hfup, hhA⟩ | ⟨K, t, hfup, hK, hhA⟩
        · have hch : chop (s.piles k).faceUp = [] := by rw [hfup]; rfl
          rw [hch, lock_afterRunRemoved_bare hhA]
          exact Or.inl ⟨rfl, rfl⟩
        · cases t with
          | nil =>
              have hch : chop (s.piles k).faceUp = [] := by rw [hfup]; rfl
              rw [hch, lock_afterRunRemoved_bare hhA]
              exact Or.inl ⟨rfl, rfl⟩
          | cons u us =>
              have hch : chop (s.piles k).faceUp = K :: chop (u :: us) := by rw [hfup]; rfl
              rw [hch, lock_afterRunRemoved_cons]
              exact Or.inr ⟨K, chop (u :: us), rfl, hK, hhA⟩
      · have helse : (if A = k then Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
            else s.piles A) = s.piles A := ite_eq_right hAk
        rw [helse]
        exact hQ
  | foundToTab w b =>
      obtain ⟨c', ht, heqw, hg, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      have hmidp : (s.setFound w.suit (chop (s.found w.suit))).piles = s.piles :=
        setFound_piles s w.suit (chop (s.found w.suit))
      cases b with
      | inl k =>
          have hp : (((s.setFound w.suit (chop (s.found w.suit))).putCard w (Sum.inl k)).piles A)
              = (if A = k then (⟨[], [w]⟩ : Pile) else s.piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨w, [], rfl, lock_canPlace_inl_king hg, rfl⟩
            · exfalso
              obtain ⟨hemp, -⟩ := canPlace_inl hg
              rw [← hAk] at hemp
              have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
              rw [hfup] at hfupE
              exact absurd hfupE (by simp)
          · rw [ite_eq_right hAk]
            exact hQ
      | inr z =>
          obtain ⟨kk, hpin, -⟩ := canPlace_inr hg
          have hmidpin : (s.setFound w.suit (chop (s.found w.suit))).pileOfTop z = some kk := by
            rw [lock_pileOfTop_of_piles z hmidp]
            exact hpin
          have hp : (((s.setFound w.suit (chop (s.found w.suit))).putCard w (Sum.inr z)).piles A)
              = (if A = kk then { s.piles kk with faceUp := (s.piles kk).faceUp ++ [w] }
                 else s.piles A) := by
            simp only [putCard_piles_inr _ _ _ _ hmidpin]
            rw [hmidp]
          rw [hp]
          by_cases hAk : A = kk
          · rw [ite_eq_left hAk]
            rw [hAk] at hQ
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
            · exfalso
              have hne := (pileOfTop_top hpin).1
              rw [hfup] at hne
              exact absurd hne (by simp)
            · refine Or.inr ⟨K, t ++ [w], ?_, hK, hhA⟩
              show (s.piles kk).faceUp ++ [w] = K :: (t ++ [w])
              rw [hfup, List.cons_append]
          · rw [ite_eq_right hAk]
            exact hQ
  | tabToTab e b =>
      obtain ⟨Asrc, hhold, hcp, hfr, hs'⟩ := step_tabToTab_inv hstep
      have hmemE : e ∈ (s.piles Asrc).faceUp := pileHolding_mem hhold
      rw [hs']
      cases b with
      | inl k =>
          have hp : (((s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                (below e ((s.piles Asrc).faceUp)))).putRun
              (fromCard e ((s.piles Asrc).faceUp)) (Sum.inl k)).piles A)
              = (if A = k then (⟨[], fromCard e ((s.piles Asrc).faceUp)⟩ : Pile)
                 else (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                    (below e ((s.piles Asrc).faceUp)))).piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            obtain ⟨tr, hrun⟩ := lock_fromCard_run_head e ((s.piles Asrc).faceUp) hfr
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨e, tr, by rw [hrun], lock_canPlace_inl_king hcp, rfl⟩
            · exfalso
              obtain ⟨hemp, -⟩ := canPlace_inl hcp
              rw [← hAk] at hemp
              have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
              rw [hfup] at hfupE
              exact absurd hfupE (by simp)
          · rw [ite_eq_right hAk]
            by_cases hAs : A = Asrc
            · rw [hAs] at hQ
              rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
              exact lock_arr_Q hmemE hQ
            · rw [setPile_afterRunRemoved_piles_ne s Asrc e A hAs]
              exact hQ
      | inr z =>
          cases hz : (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
              (below e ((s.piles Asrc).faceUp)))).pileOfTop z with
          | none =>
              rw [putRun_inr_none hz]
              by_cases hAs : A = Asrc
              · rw [hAs] at hQ
                rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
                exact lock_arr_Q hmemE hQ
              · rw [setPile_afterRunRemoved_piles_ne s Asrc e A hAs]
                exact hQ
          | some kk =>
              rw [putRun_inr_eq hz]
              by_cases hAk : A = kk
              · rw [hAk, setPile_piles_self]
                have hneMid := (pileOfTop_top hz).1
                by_cases hAs : A = Asrc
                · rw [hAs] at hQ
                  have hka : kk = Asrc := hAk.symm.trans hAs
                  rw [hka, setPile_afterRunRemoved_piles_self s Asrc e] at hneMid ⊢
                  rcases lock_arr_Q hmemE hQ with ⟨h1, h2⟩ | ⟨K, tm, h1, hK, h2⟩
                  · exact absurd h1 hneMid
                  · refine Or.inr ⟨K, tm ++ fromCard e ((s.piles Asrc).faceUp), ?_, hK, h2⟩
                    rw [h1, List.cons_append]
                · have hmidA : (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                        (below e ((s.piles Asrc).faceUp)))).piles kk = s.piles A := by
                    rw [← hAk]
                    exact setPile_afterRunRemoved_piles_ne s Asrc e A hAs
                  rw [hmidA] at hneMid ⊢
                  rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
                  · exfalso
                    rw [hfup] at hneMid
                    exact absurd hneMid (by simp)
                  · refine Or.inr ⟨K, t ++ fromCard e ((s.piles Asrc).faceUp), ?_, hK, hhA⟩
                    rw [hfup, List.cons_append]
              · rw [setPile_piles_ne hAk]
                by_cases hAs : A = Asrc
                · rw [hAs] at hQ
                  rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
                  exact lock_arr_Q hmemE hQ
                · rw [setPile_afterRunRemoved_piles_ne s Asrc e A hAs]
                  exact hQ

/-! ### The pillar: a fully-emptied pile rebuilds only to a king head
(the play-lift of the one-step invariant) -/

/-- The pillar play-lift (the copy of `Orig/PositionSeat`'s private
`emptyOrKingHead_play`): from a fully-empty pile (no hidden, no
face-up), every play leaves it fully empty or king-headed. -/
private theorem lock_emptyOrKingHead_play {A : Anchor} :
    ∀ (s : State) (play : List Move) (s' : State),
      ((s.piles A).faceUp = [] ∧ (s.piles A).hidden = [] ∨
        ∃ K t, (s.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
          (s.piles A).hidden = []) →
      State.run s play = some s' →
      ((s'.piles A).faceUp = [] ∧ (s'.piles A).hidden = [] ∨
        ∃ K t, (s'.piles A).faceUp = K :: t ∧ K.rank = Rank.king ∧
          (s'.piles A).hidden = []) := by
  intro s play
  revert s
  induction play with
  | nil =>
      intro s s' hQ hrun
      have hred : (some s : Option State) = some s' := hrun
      injection hred with hcon
      rw [← hcon]
      exact hQ
  | cons p rest ih =>
      intro s s' hQ hrun
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      exact ih s₁ s' (lock_oneStep_pileInv hstep hQ) hrest

/-- **THE BARE-DEPARTURE BAR** — a non-king heading its whole run out
of a pile with no face-up content below and no hidden deck leaves the
pile FULLY EMPTY, and no play can ever restore a NON-KING bottom there
(the pillar): an irreversible departure. -/
private theorem lock_bareDeparture_irr {s : State} {c : Card} {b : Base}
    {a : Anchor} {rest : List Card}
    (hhold : s.pileHolding c = some a)
    (hshape : (s.piles a).faceUp = c :: rest)
    (hhid : (s.piles a).hidden = [])
    (hK : c.rank ≠ Rank.king) :
    ¬ reversibleAtW s (Move.tabToTab c b) := by
  rintro ⟨s₁, pl, hstep, hret⟩
  obtain ⟨Asrc, hhold', hcp, hfr, hs₁⟩ := step_tabToTab_inv hstep
  have hA : Asrc = a := Option.some.inj (hhold'.symm.trans hhold)
  rw [hA] at hs₁
  have hmidP : (s.setPile a (Pile.afterRunRemoved (s.piles a)
      (below c ((s.piles a).faceUp)))).piles a = (⟨[], []⟩ : Pile) := by
    rw [show below c ((s.piles a).faceUp) = [] from by
        rw [hshape, below_cons_self],
      lock_afterRunRemoved_bare hhid, setPile_piles_self]
  have hs₁pa : s₁.piles a = (⟨[], []⟩ : Pile) := by
    rw [hs₁]
    cases b with
    | inl k =>
        obtain ⟨hemp, -⟩ := canPlace_inl hcp
        have hkna : k ≠ a := by
          intro hcon
          rw [hcon] at hemp
          have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
          rw [hshape] at hfupE
          exact absurd hfupE (by simp)
        have hank : a ≠ k := fun hcon => hkna hcon.symm
        simp only [putRun_piles_inl]
        rw [ite_eq_right hank]
        exact hmidP
    | inr z =>
        cases hz : (s.setPile a (Pile.afterRunRemoved (s.piles a)
            (below c ((s.piles a).faceUp)))).pileOfTop z with
        | none =>
            rw [putRun_inr_none hz]
            exact hmidP
        | some kk =>
            simp only [putRun_piles_inr _ _ _ _ hz]
            by_cases hak : a = kk
            · exfalso
              have hne := (pileOfTop_top hz).1
              rw [← hak] at hne
              rw [hmidP] at hne
              exact absurd hne (by simp)
            · rw [ite_eq_right hak]
              exact hmidP
  have hQend := lock_emptyOrKingHead_play (A := a) s₁ pl s
    (Or.inl ⟨by rw [hs₁pa], by rw [hs₁pa]⟩) hret
  rcases hQend with ⟨hfupE, -⟩ | ⟨K0, t0, hfupE, hK0, -⟩
  · exfalso
    rw [hshape] at hfupE
    exact absurd hfupE (by simp)
  · exfalso
    rw [hshape] at hfupE
    injection hfupE with hK0c _
    rw [← hK0c] at hK0
    exact absurd hK0 hK

/-- **THE BARE-RAISE BAR** — raising the non-king off a bare seat over
no hidden deck empties its pile fully, so the return play would have
to restore a non-king bottom on a fully-emptied pile: the pillar bars
it (the undo `tabToFound_undo_bare` needs a king). -/
private theorem lock_bareRaise_irr {s : State} {c : Card} {a : Anchor}
    (hwfs : s.WF) (hshape : (s.piles a).faceUp = [c])
    (hhid : (s.piles a).hidden = [])
    (hK : c.rank ≠ Rank.king) :
    ¬ reversibleAtW s (Move.tabToFound c) := by
  rintro ⟨s₁, pl, hstep, hret⟩
  obtain ⟨-, k, hpod, hs₁⟩ := step_tabToFound_inv hstep
  have htopa : (s.piles a).top = some c := by
    show lastOf (s.piles a).faceUp = some c
    rw [hshape]
    rfl
  have hpoCa : s.pileOfTop c = some a := (pileOfTop_eq_some_iff hwfs).2 htopa
  have hak : a = k := Option.some.inj (hpoCa.symm.trans hpod)
  have hchop : chop (s.piles a).faceUp = [] := by rw [hshape]; rfl
  have hpileEq : s₁.piles a = (if a = k then
      Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
      else s.piles a) := by rw [hs₁]
  have hs₁pa : s₁.piles a = (⟨[], []⟩ : Pile) := by
    rw [hpileEq, ite_eq_left hak, ← hak, hchop, lock_afterRunRemoved_bare hhid]
  have hQend := lock_emptyOrKingHead_play (A := a) s₁ pl s
    (Or.inl ⟨by rw [hs₁pa], by rw [hs₁pa]⟩) hret
  rcases hQend with ⟨hfupE, -⟩ | ⟨K0, t0, hfupE, hK0, -⟩
  · exfalso
    rw [hshape] at hfupE
    exact absurd hfupE (by simp)
  · exfalso
    rw [hshape] at hfupE
    injection hfupE with hK0c _
    rw [← hK0c] at hK0
    exact absurd hK0 hK

/-! ### THE FREEZE — no reversible leg ever moves an isolated dresser -/

/-- One leg of the freeze: a reversible leg at a state whose pile `a`
holds the isolated non-king `c` at the bottom leaves `c` at the bottom
of pile `a` at the successor.  The escaping legs all die: the c-headed
bare departure by the reveal jury over a hidden deck or the pillar over
an empty one; the bare raise the same two ways; every other leg either
leaves the pile alone or appends above `c`. -/
private theorem lock_freeze_step {s s' : State} (hwfs : s.WF) {c : Card} {a : Anchor}
    {rest0 : List Card} (hshape : (s.piles a).faceUp = c :: rest0)
    {m : Move} (hstep : State.step s m = some s')
    (hK : c.rank ≠ Rank.king)
    (hrev : reversibleAtW s m) :
    ∃ rest0', (s'.piles a).faceUp = c :: rest0' := by
  cases m with
  | draw =>
      have hd : s.stepDraw = some s' := hstep
      rw [stepDraw_piles hd]
      exact ⟨rest0, hshape⟩
  | wasteToFound w =>
      obtain ⟨-, x, xs, hwst, hs⟩ := step_wasteToFound_inv hstep
      rw [hs]
      have hp : (({s.setFound w.suit (s.found w.suit ++ [w]) with waste := xs} : State).piles a)
          = s.piles a := rfl
      rw [hp]
      exact ⟨rest0, hshape⟩
  | wasteToTab w b =>
      exact absurd hrev (journey_never_wasteToTab hstep)
  | tabToFound u =>
      obtain ⟨-, k, hpod, hs⟩ := step_tabToFound_inv hstep
      have hpileEq : s'.piles a = (if a = k then
          Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
          else s.piles a) := by rw [hs]
      rw [hpileEq]
      by_cases hak : a = k
      · rw [← hak] at hpod
        have htopa : lastOf (s.piles a).faceUp = some u := (pileOfTop_top hpod).2
        cases rest0 with
        | nil =>
            exfalso
            rw [hshape] at htopa
            have hucl : lastOf [c] = some c := rfl
            have huc : u = c := (Option.some.inj (hucl.symm.trans htopa)).symm
            rw [huc] at hstep hrev hpod
            by_cases hh : (s.piles a).hidden = []
            · exact absurd hrev (lock_bareRaise_irr hwfs hshape hh hK)
            · exact absurd hrev (journey_tabToFound_never_reveal hstep hpod
                (by rw [hshape]; rfl) hh)
        | cons z zs =>
            refine ⟨chop (z :: zs), ?_⟩
            rw [ite_eq_left hak, ← hak]
            have hchop : chop (s.piles a).faceUp = c :: chop (z :: zs) := by
              rw [hshape]; rfl
            rw [hchop, afterRunRemoved_ne (by simp)]
      · refine ⟨rest0, ?_⟩
        rw [ite_eq_right hak]
        exact hshape
  | foundToTab w b =>
      obtain ⟨c', ht, heqw, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hs]
      have hmidp : (s.setFound w.suit (chop (s.found w.suit))).piles = s.piles :=
        setFound_piles s w.suit (chop (s.found w.suit))
      cases b with
      | inl k =>
          have hp : (((s.setFound w.suit (chop (s.found w.suit))).putCard w (Sum.inl k)).piles a)
              = (if a = k then (⟨[], [w]⟩ : Pile) else s.piles a) := rfl
          rw [hp]
          by_cases hak : a = k
          · exfalso
            obtain ⟨hemp, -⟩ := canPlace_inl hcp
            rw [← hak] at hemp
            obtain ⟨-, hfE⟩ := (Pile.isEmpty_eq _).mp hemp
            rw [hshape] at hfE
            exact absurd hfE (by simp)
          · refine ⟨rest0, ?_⟩
            rw [ite_eq_right hak]
            exact hshape
      | inr z =>
          obtain ⟨kk, hpin, -⟩ := canPlace_inr hcp
          have hmidpin : (s.setFound w.suit (chop (s.found w.suit))).pileOfTop z = some kk := by
            rw [lock_pileOfTop_of_piles z hmidp]
            exact hpin
          have hp : (((s.setFound w.suit (chop (s.found w.suit))).putCard w (Sum.inr z)).piles a)
              = (if a = kk then { s.piles kk with faceUp := (s.piles kk).faceUp ++ [w] }
                 else s.piles a) := by
            simp only [putCard_piles_inr _ _ _ _ hmidpin]
            rw [hmidp]
          rw [hp]
          by_cases hak : a = kk
          · refine ⟨rest0 ++ [w], ?_⟩
            rw [ite_eq_left hak, ← hak]
            show (s.piles a).faceUp ++ [w] = c :: (rest0 ++ [w])
            rw [hshape, List.cons_append]
          · refine ⟨rest0, ?_⟩
            rw [ite_eq_right hak]
            exact hshape
  | tabToTab u b =>
      obtain ⟨Asrc, hhold, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
      rw [hs]
      by_cases hAs : a = Asrc
      · -- the departure is from OUR pile: the head is u ≠ c (the c-headed
        -- escape is barred) and the residue keeps the c-head
        rw [← hAs] at hhold ⊢
        have humem : u = c ∨ u ∈ rest0 := by
          have hmmem : u ∈ (s.piles a).faceUp := pileHolding_mem hhold
          rw [hshape] at hmmem
          exact List.mem_cons.mp hmmem
        rcases humem with huc | huR
        · exfalso
          rw [huc] at hhold hstep hrev
          by_cases hh : (s.piles a).hidden = []
          · exact absurd hrev (lock_bareDeparture_irr hhold hshape hh hK)
          · exact absurd hrev (journey_tabToTab_never_reveal hstep hhold
              (by rw [hshape, below_cons_self]) hh)
        · have hnd : (s.piles a).faceUp.Nodup := runOK_nodup (hwfs.runOK_of a)
          have hcNr : c ∉ rest0 := by
            rw [hshape] at hnd
            exact (List.nodup_cons.mp hnd).1
          have hune : u ≠ c := fun hcon => hcNr (hcon ▸ huR)
          have hnonemp : (c :: below u rest0 : List Card) ≠ [] := by simp
          have hpreEq : below u ((s.piles a).faceUp) = c :: below u rest0 := by
            rw [hshape, lock_below_cons_ne (Ne.symm hune)]
          cases b with
          | inl k =>
              obtain ⟨hemp, -⟩ := canPlace_inl hcp
              have hkna : k ≠ a := by
                intro hcon
                rw [hcon] at hemp
                obtain ⟨-, hfE⟩ := (Pile.isEmpty_eq _).mp hemp
                rw [hshape] at hfE
                exact absurd hfE (by simp)
              have hne : a ≠ k := fun hcon => hkna hcon.symm
              rw [putRun_eq_inl, setPile_piles_ne hne,
                setPile_afterRunRemoved_piles_self s a u, hpreEq,
                afterRunRemoved_ne hnonemp]
              exact ⟨below u rest0, rfl⟩
          | inr z =>
              cases hzm : (s.setPile a (Pile.afterRunRemoved (s.piles a)
                  (below u ((s.piles a).faceUp)))).pileOfTop z with
              | none =>
                  rw [putRun_inr_none hzm, setPile_afterRunRemoved_piles_self s a u,
                    hpreEq, afterRunRemoved_ne hnonemp]
                  exact ⟨below u rest0, rfl⟩
              | some kk =>
                  by_cases hak : a = kk
                  · -- lands back onto our pile: the c-headed residue appends
                    have hmidA : (((s.setPile a (Pile.afterRunRemoved (s.piles a)
                          (below u ((s.piles a).faceUp)))).piles a).faceUp)
                        = (c :: below u rest0 : List Card) := by
                      rw [setPile_afterRunRemoved_piles_self s a u, hpreEq,
                        afterRunRemoved_ne hnonemp]
                    refine ⟨below u rest0 ++ fromCard u ((s.piles a).faceUp), ?_⟩
                    simp only [putRun_piles_inr _ _ _ _ hzm]
                    rw [ite_eq_left hak, ← hak]
                    show (((s.setPile a (Pile.afterRunRemoved (s.piles a)
                        (below u ((s.piles a).faceUp)))).piles a).faceUp ++
                        fromCard u ((s.piles a).faceUp))
                      = c :: (below u rest0 ++ fromCard u ((s.piles a).faceUp))
                    rw [hmidA]
                    rfl
                  · simp only [putRun_piles_inr _ _ _ _ hzm]
                    rw [ite_eq_right hak,
                      setPile_afterRunRemoved_piles_self s a u, hpreEq,
                      afterRunRemoved_ne hnonemp]
                    exact ⟨below u rest0, rfl⟩
      · -- the departure is NOT from our pile: only the landing matters
        have hmidEq : (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
            (below u ((s.piles Asrc).faceUp)))).piles a = s.piles a :=
          setPile_afterRunRemoved_piles_ne s Asrc u a hAs
        cases b with
        | inl k =>
            obtain ⟨hemp, -⟩ := canPlace_inl hcp
            have hkna : k ≠ a := by
              intro hcon
              rw [hcon] at hemp
              obtain ⟨-, hfE⟩ := (Pile.isEmpty_eq _).mp hemp
              rw [hshape] at hfE
              exact absurd hfE (by simp)
            have hne : a ≠ k := fun hcon => hkna hcon.symm
            rw [putRun_eq_inl, setPile_piles_ne hne, hmidEq]
            exact ⟨rest0, hshape⟩
        | inr z =>
            cases hzm : (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                (below u ((s.piles Asrc).faceUp)))).pileOfTop z with
            | none =>
                rw [putRun_inr_none hzm, hmidEq]
                exact ⟨rest0, hshape⟩
            | some kk =>
                by_cases hak : a = kk
                · refine ⟨rest0 ++ fromCard u ((s.piles Asrc).faceUp), ?_⟩
                  simp only [putRun_piles_inr _ _ _ _ hzm]
                  rw [ite_eq_left hak, ← hak]
                  show (((s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                      (below u ((s.piles Asrc).faceUp)))).piles a).faceUp ++
                      fromCard u ((s.piles Asrc).faceUp))
                    = c :: (rest0 ++ fromCard u ((s.piles Asrc).faceUp))
                  rw [hmidEq, hshape]
                  rfl
                · simp only [putRun_piles_inr _ _ _ _ hzm]
                  rw [ite_eq_right hak, hmidEq]
                  exact ⟨rest0, hshape⟩

/-- The freeze, journey-lifted: along any witness journey the isolated
non-king keeps its bottom seat in its own pile. -/
private theorem lock_freeze_journey {c : Card} {a : Anchor} (hK : c.rank ≠ Rank.king) :
    ∀ {s : State} {play : List Move} {w : State},
      ShufflePlayW s play w → s.WF →
      ∀ rest0, (s.piles a).faceUp = c :: rest0 →
      ∃ rest0', (w.piles a).faceUp = c :: rest0' := by
  intro s play w h
  induction h with
  | nil u => intro hwfs rest0 hshape; exact ⟨rest0, hshape⟩
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro hwfs rest0 hshape
      obtain ⟨rest1, hsh1⟩ := lock_freeze_step hwfs hshape hstep hK hrev
      obtain ⟨restw, hshw⟩ := ih (step_wf hwfs hstep) rest1 hsh1
      exact ⟨restw, hshw⟩

/-- **THE FREEZE** — from the class origin, every reversible journey
leaves the on-board dresser seated at the BOTTOM of its own pile: its
bare escapes (the c-headed slide, the bare raise) are all irreversible
— over a hidden deck by the reveal jury, over an empty one by THE
PILLAR — and no other leg moves it.  The isolated origin seat is
therefore a LIFE sentence along the whole class. -/
theorem origin_dresser_frozen {st₁ : State} (hwf₁ : st₁.WF)
    {x y : Card} (hx : ForkWitness st₁ x)
    (hfam : y.suit = x.suit ∨ y.suit = x.twin.suit)
    (hlt : y.rank.toIdx < x.rank.toIdx)
    {c : Card} (hdcolx : c.suit.color ≠ x.suit.color)
    (hrankc : c.rank.toIdx + 1 = y.rank.toIdx)
    {a : Anchor} (hmem : c ∈ (st₁.piles a).faceUp) :
    ∀ {w : State} {play : List Move}, ShufflePlayW st₁ play w →
      ∃ rest0, (w.piles a).faceUp = c :: rest0 := by
  intro w play hjourney
  have hiso : (st₁.piles a).faceUp = [c] :=
    origin_dresser_isolated hwf₁ hx hfam hlt hdcolx hrankc hmem
  have hK : c.rank ≠ Rank.king := by
    have h13 := Rank.toIdx_lt y.rank
    intro hcon
    rw [hcon] at hrankc
    have hk12 : Rank.king.toIdx = 12 := rfl
    omega
  exact lock_freeze_journey hK hjourney hwf₁ [] hiso

/-! ### The off-board closures -/

/-- The `dealUpTo` split: a member of the dealt-from list lands in the
dealt prefix or stays in the remainder. -/
private theorem lock_dealUpTo_mem (d : Card) : ∀ (k : Nat) (l : List Card),
    d ∈ l → d ∈ (State.dealUpTo k l).1 ∨ d ∈ (State.dealUpTo k l).2 := by
  intro k
  induction k with
  | zero =>
      intro l hd
      exact Or.inr hd
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
            · have hrec := ih xs htl
              rcases hrec with h1 | h2
              · left
                simp only [State.dealUpTo]
                exact List.mem_cons.mpr (Or.inr h1)
              · right
                simp only [State.dealUpTo]
                exact h2

/-- **THE DRAW-CYCLE CLOSURE** — along a witness journey the stock and
the waste are a closed two-zone world for their residents (the only
stock/waste writers are the draw's own recycle and deal; the waste
letters never ride). -/
theorem witness_stockWaste_closed (d : Card) :
    ∀ {s : State} {play : List Move} {w : State},
      ShufflePlayW s play w →
      (d ∈ s.stock ∨ d ∈ s.waste) → (d ∈ w.stock ∨ d ∈ w.waste) := by
  intro s play w h
  induction h with
  | nil u => intro hcyc; exact hcyc
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro hcyc
      have hmid : d ∈ s₁.stock ∨ d ∈ s₁.waste := by
        cases m with
        | draw =>
            have hd : s₀.stepDraw = some s₁ := hstep
            obtain ⟨r, hrEq, -, hyEq⟩ := draw_unfold hd
            rw [hyEq]
            rcases hcyc with hst | hwst
            · -- d in the origin's stock: the recycle is the identity there
              cases hss : s₀.stock with
              | nil => rw [hss] at hst; exact absurd hst (by simp)
              | cons x xs =>
                  have hrt : r = s₀ := by
                    rw [← hrEq]
                    exact recycle_keep s₀ (by rw [hss]; simp)
                  have hin : d ∈ r.stock := by rw [hrt]; exact hst
                  have hspl := lock_dealUpTo_mem d r.drawStep r.stock hin
                  rcases hspl with hD | hR
                  · exact Or.inr
                      (List.mem_append.mpr (Or.inl (List.mem_reverse.mpr hD)))
                  · exact Or.inl hR
            · -- d in the origin's waste
              cases hss : s₀.stock with
              | nil =>
                  cases hws : s₀.waste with
                  | nil => rw [hws] at hwst; exact absurd hwst (by simp)
                  | cons v vs =>
                      have hrt : r = { s₀ with stock := s₀.waste.reverse, waste := [] } := by
                        rw [← hrEq]
                        exact recycle_nil s₀ hss (by rw [hws]; simp)
                      have hin : d ∈ r.stock := by
                        rw [hrt]
                        exact List.mem_reverse.mpr hwst
                      have hspl := lock_dealUpTo_mem d r.drawStep r.stock hin
                      rcases hspl with hD | hR
                      · exact Or.inr
                          (List.mem_append.mpr (Or.inl (List.mem_reverse.mpr hD)))
                      · exact Or.inl hR
              | cons x xs =>
                  have hrt : r = s₀ := by
                    rw [← hrEq]
                    exact recycle_keep s₀ (by rw [hss]; simp)
                  exact Or.inr (List.mem_append.mpr (Or.inr (by rw [hrt]; exact hwst)))
        | wasteToFound walt =>
            exact absurd hrev (journey_never_wasteToFound hstep)
        | wasteToTab walt balt =>
            exact absurd hrev (journey_never_wasteToTab hstep)
        | tabToFound walt =>
            obtain ⟨-, k, -, hs⟩ := step_tabToFound_inv hstep
            rw [hs]
            exact hcyc
        | foundToTab walt balt =>
            obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv hstep
            rw [hs]
            obtain ⟨-, hP1, hP2, -⟩ :=
              putCard_keep (st := s₀.setFound walt.suit (chop (s₀.found walt.suit)))
                (c := walt) (b := balt)
            rw [hP1, hP2]
            exact hcyc
        | tabToTab walt balt =>
            obtain ⟨Asrc, -, -, -, hs⟩ := step_tabToTab_inv hstep
            rw [hs]
            obtain ⟨-, hP1, hP2, -⟩ :=
              putRun_keep (st := s₀.setPile Asrc (Pile.afterRunRemoved (s₀.piles Asrc)
                (below walt ((s₀.piles Asrc).faceUp))))
                (run := fromCard walt ((s₀.piles Asrc).faceUp)) (b := balt)
            rw [hP1, hP2]
            exact hcyc
      exact ih hmid

/-- **THE ZONE-RESIDENCY READ** — at any `WF` state every card of the
deck sits in one of the five zones (the conservation census, read
existentially). -/
theorem lock_zone_residency (st : State) (hwf : st.WF) (d : Card) :
    (∃ s, d ∈ st.found s) ∨ (∃ k, d ∈ (st.piles k).hidden) ∨
    (∃ k, d ∈ (st.piles k).faceUp) ∨ d ∈ st.stock ∨ d ∈ st.waste := by
  have h1 : st.cardCount d = 1 := hwf.cardCount_eq (Card.mem_universe d)
  unfold State.cardCount at h1
  cases hL : ((st.zones.flatMap id).filter fun x => decide (x = d)) with
  | nil =>
      rw [hL] at h1
      simp at h1
  | cons x xs =>
      have hxmem : x ∈ (st.zones.flatMap id).filter (fun x => decide (x = d)) := by
        rw [hL]
        exact List.mem_cons_self ..
      obtain ⟨hxeq, hxz⟩ := List.mem_filter.mp hxmem
      have hxd : x = d := of_decide_eq_true hxz
      obtain ⟨z, hz, hdz⟩ := List.mem_flatMap.mp hxeq
      have hdzd : d ∈ z := by rw [← hxd]; exact hdz
      have hspl : st.zones = (Suit.all.map st.found) ++
          ((Anchor.all.map fun a => (st.piles a).hidden ++ (st.piles a).faceUp) ++
            [st.stock, st.waste]) := rfl
      rw [hspl] at hz
      rcases List.mem_append.mp hz with hA | hB
      · obtain ⟨s, -, hzs⟩ := List.mem_map.mp hA
        exact Or.inl ⟨s, by rw [← hzs] at hdzd; exact hdzd⟩
      · rcases List.mem_append.mp hB with hC | hD
        · obtain ⟨k, -, hzk⟩ := List.mem_map.mp hC
          rw [← hzk] at hdzd
          rcases List.mem_append.mp hdzd with hH | hF
          · exact Or.inr (Or.inl ⟨k, hH⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨k, hF⟩))
        · rcases List.mem_cons.mp hD with heq | hrest
          · rw [heq] at hdzd
            exact Or.inr (Or.inr (Or.inr (Or.inl hdzd)))
          · rcases List.mem_cons.mp hrest with heq2 | hnil
            · rw [heq2] at hdzd
              exact Or.inr (Or.inr (Or.inr (Or.inr hdzd)))
            · exact absurd hnil (by simp)

/-! ## §3.5. The named residue — the founded-cover staircase -/

/-- **THE FOUNDED-COVER CASE** — the card's single named residue: the
one origin-residency case of the cover `d` that this card's landed
mechanism rows do not yet close (each other residency is fully closed
by §3: on-board ⇒ `origin_dresser_frozen`, hidden ⇒
`shuffle_hiddenPinned`, stock-or-waste ⇒ `witness_stockWaste_closed`;
see the §4 assembly).

**THE ROUTE** (complete):

1. **The LIFO toggle discipline.** At every witness-journey state
   `found σ = σ.upCards.take (rungAt σ)` (the `WF` reads), so each
   suit's foundation behaves as a strict stack: a pull
   (`foundToTab`) at rung `k+1` pops exactly the rank-`k` card of
   its suit, a raise (`tabToFound`) pushes back the rank-`k` card
   when the rung is `k` (`foundToTab_pops_currentTop`,
   `foundToTab_undo`). The cover `d` (rank index `r*−1`, `hdfound`
   forcing `rungAt st₁ d.suit ≥ r*`) can therefore leave its
   foundation only through a pull firing at rung exactly `r*`: the
   LIFO descent `h₀ → r*` pops the `d`-suit black cards of ranks
   `h₀−1 … r*−1` (`d` itself last), each landing
   `canPlace`-legally on a RED top of rank one above — for pop rank
   `k ∈ [r*, h₀)` a family rank-`(k+1)` card, each either pre-seated
   at `st₁` (rank ≥ `r`: the pair runs and their cargos — the
   anchor lattice of the probes' boards), or itself dragged out of a
   foundation by the same LIFO discipline.
2. **The reversible dress cycle.** A `d`-pull fires only when `d`
   tops its suit foundation (`rungAt = r*`), and lands `d` DIRECTLY
   on a topping pair member (`y` or `y.twin` — the
   `dress_legalSeats_pair` census, `d` being family-opposite,
   rank `r*−1`); its direct mirror — the re-raise by
   `foundToTab_undo` — makes every `d`-pull reversible (the probes'
   `down1`/`vis1` cells). Every slide departure of a dresser from a
   seat with residue needs the residue-top as a landlord — and the
   census reads every lawful landlord as a pair member again.
3. **The endpoint census kills the cycle.** At `st₂` the pack pins
   `st₂.nextUp d = false` with the piled-rung read
   (`conf_piled_rung`) forcing `rungAt st₂ d.suit ≤ r*−2`: so AFTER
   the LAST `d`-pull the `d`-suit rung must descend strictly below
   `d`'s own index — at least one further pop BELOW `d`: the black
   rank-`(r*−2)` card onto a RED rank-`(r*−1)` top — the two red
   rank-`(r*−1)` cards are FAMILY, hence FOUNDED at `st₁` (both
   family rungs pin at `r > r*−1`) and can only be dragged out themselves,
   iterating the drag one rank at a time down the staircase
   (`Orig/EpochProbe.lean`'s `downAlt_pollutes` is the rank-locked
   shadow of this row: a pulled cover is next-up at its own
   landing BY CONSTRUCTION).
4. **The crash.** Each dragged staircase card is NEXT-UP-LIVE at
   its own landing (its pull drops its suit rung to exactly its
   index), and washing it back re-raises the rung — while §1's
   census (`origin_lowerJourney_pulls`) prices net family pulls ≥
   `r − r*` on BOTH family suits. The staircase terminus at `st₂`:
   some dragged low card on-board with no legal seat — its every
   `canPlace` target is a family rank-top, but at `st₂` BOTH pair
   members are consumed (one tops its own seat pile `a`, the other
   sits DIRECTLY under `d` in the second pile, `a ≠ c`) and every
   other family card of that rank is foundation-resident
   (`pair_lowFamily_founded` at the OTHER end) — so the terminal
   card stands FACE-UP-LIVE against the lower fork's S-saturation
   (`canRaiseS_iff`: a third live card breaks `hy`'s pair select),
   the exact `downAlt` pollution crash. Hence no witness journey
   reaches the founded-cover endgame; the case is barred. -/
private theorem origin_cover_founded_case_barred {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hfam : y.suit = x.suit ∨ y.suit = x.twin.suit)
    (hlt : y.rank.toIdx < x.rank.toIdx)
    {play : List Move} (hplay : ShufflePlayW st₁ play st₂)
    (d : Card)
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hdcol : d.suit.color ≠ y.suit.color)
    (hdcover : ∃ c bsC, (st₂.piles c).faceUp = bsC ++ [y.twin, d] ∧
      st₂.pileOfTop d = some c)
    (hdfound : d ∈ st₁.found d.suit) :
    False := by
  sorry

/-! ## §4. THE ASSEMBLY -/

/-- The `upCards` membership carries its suit. -/
private theorem lock_upCards_suit {s : Suit} : ∀ {c : Card},
    c ∈ s.upCards → c.suit = s := by
  intro c hmem
  obtain ⟨r, -, hrc⟩ := List.mem_map.mp hmem
  rcases c with ⟨cs, cr⟩
  injection hrc with hs _
  exact hs.symm

/-- Membership stays under `take`. -/
private theorem lock_mem_take {d : Card} : ∀ (n : Nat) (l : List Card),
    d ∈ List.take n l → d ∈ l := by
  intro n
  induction n with
  | zero =>
      intro l hmem
      rw [show (List.take 0 l : List Card) = [] from rfl] at hmem
      exact absurd hmem (by simp)
  | succ k ih =>
      intro l hmem
      cases l with
      | nil =>
          rw [show (List.take (k + 1) ([] : List Card)) = ([] : List Card) from rfl] at hmem
          exact absurd hmem (by simp)
      | cons w ws =>
          rw [show (List.take (k + 1) (w :: ws)) = w :: List.take k ws from rfl] at hmem
          rcases List.mem_cons.mp hmem with heq | htl
          · rw [heq]
            exact List.mem_cons_self ..
          · exact List.mem_cons.mpr (Or.inr (ih ws htl))

/-- A foundation membership fixes the card's suit. -/
private theorem lock_found_suit {st : State} (hwf : st.WF) {d : Card} {s : Suit}
    (hmem : d ∈ st.found s) : s = d.suit := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  rw [hn] at hmem
  exact (lock_upCards_suit (lock_mem_take n s.upCards hmem)).symm

/-- **THE ORIGIN LOCK** — downward: a same-class fork of the same
suit family cannot witness a LOWER rank.  The class's forward witness
play (`sameOrbit_forward`) hands every leg its own `reversibleAtW`
witness; the lower fork's dress `d` (§2's pack) must live somewhere
at the origin (`lock_zone_residency`), and every residency but one
is closed on the spot: ON-BOARD by the FREEZE (the isolated bare seat
is an irreversible life sentence — reveal jury, pillar), HIDDEN by
the PIN, STOCK-OR-WASTE by the DRAW-CYCLE CLOSURE; the FOUND case
falls to the card's named residue (§3.5). -/
theorem forkState_rankDrop_locked (st₁ st₂ : State) (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hfam : y.suit = x.suit ∨ y.suit = x.twin.suit) :
    ¬ (y.rank.toIdx < x.rank.toIdx) := by
  have hcolfam : y.suit.color = x.suit.color := by
    rcases hfam with h | h
    · rw [h]
    · rw [h, Card.twin_suit, Suit.color_twin]
  intro hlt
  obtain ⟨τ, hτ⟩ := sameOrbit_forward hcls
  obtain ⟨a, c, bsC, d, hpo, -, hshape, hrankd, hcold, hpod, hne, hnext, hKd, -, -⟩ :=
    lower_sandwich hwf₂ hy
  have hdcolx : d.suit.color ≠ x.suit.color :=
    fun h => hcold (h.trans hcolfam.symm)
  have hdmem : d ∈ (st₂.piles c).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.2 (Or.inr (by simp))))
  rcases lock_zone_residency st₁ hwf₁ d with
    ⟨s, hf⟩ | ⟨k, hhid⟩ | ⟨k, hfu⟩ | hstock | hwaste
  · -- FOUNDED at the origin: the named residue (§3.5)
    have hsuit : s = d.suit := lock_found_suit hwf₁ hf
    have hdfound : d ∈ st₁.found d.suit := by rw [← hsuit]; exact hf
    exact origin_cover_founded_case_barred hwf₁ hwf₂ hx hy hfam hlt hτ d hrankd hcold
      ⟨c, bsC, hshape, hpod⟩ hdfound
  · -- HIDDEN at the origin: the pin transports the hidden seat to st₂
    exfalso
    have hpin := shuffle_hiddenPinned hτ k
    have hdhid : d ∈ (st₂.piles k).hidden := by
      rw [hpin]
      exact hhid
    rcases Decidable.em (k = c) with hkc | hkc
    · rw [hkc] at hdhid
      exact (mem_faceUp_only hwf₂ hdmem).2.1 hdhid
    · exact (mem_faceUp_unique hwf₂ hdmem k hkc).2.1 hdhid
  · -- ON-BOARD at the origin: the freeze — the life sentence crashes
    -- against the sandwich's twin-under-dress seat
    exfalso
    obtain ⟨rest0, hfrz⟩ := origin_dresser_frozen hwf₁ hx hfam hlt hdcolx hrankd hfu hτ
    have hdk : d ∈ (st₂.piles k).faceUp := by
      rw [hfrz]
      exact List.mem_cons_self ..
    rcases Decidable.em (k = c) with hkc | hkc
    · rw [hkc] at hfrz
      have hytm : y.twin ∈ (st₂.piles c).faceUp := by
        rw [hshape]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      have hytne : y.twin ≠ d := by
        intro hcon
        rw [← hcon] at hcold
        rw [Card.twin_suit, Suit.color_twin] at hcold
        exact hcold rfl
      rw [hfrz] at hytm
      rcases List.mem_cons.mp hytm with heq | htl
      · exact absurd heq hytne
      · have hok' : runOK (([d] : List Card) ++ rest0) = true := by
          show runOK (d :: rest0) = true
          rw [← hfrz]
          exact hwf₂.runOK_of c
        have hdesc := runOK_desc (P := [d]) (S := rest0) hok' (List.mem_cons_self ..) htl
        have hytr : y.twin.rank.toIdx = y.rank.toIdx := by rw [Card.twin_rank]
        omega
    · exact absurd hdk (mem_faceUp_unique hwf₂ hdmem k hkc).1
  · -- STOCK at the origin: the draw cycle keeps its residents off-board
    exfalso
    rcases witness_stockWaste_closed (d := d) hτ (Or.inl hstock) with hst2 | hws2
    · exact (mem_faceUp_only hwf₂ hdmem).2.2.1 hst2
    · exact (mem_faceUp_only hwf₂ hdmem).2.2.2.1 hws2
  · -- WASTE at the origin: likewise
    exfalso
    rcases witness_stockWaste_closed (d := d) hτ (Or.inr hwaste) with hst2 | hws2
    · exact (mem_faceUp_only hwf₂ hdmem).2.2.1 hst2
    · exact (mem_faceUp_only hwf₂ hdmem).2.2.2.1 hws2

/-! ## §5. The floor corollary and the pairClass assembly -/

/-- **THE FAMILY RANK FLOOR** — from `st₁`'s perspective no same-family
witness of a macro-class member can sit BELOW the origin fork's
rank: the downward half of the family pairClass story (the floor
under every same-family fork of the class). -/
theorem forkState_family_rankFloor (st₁ st₂ : State) (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    (x : Card) (hx : ForkWitness st₁ x) {y : Card} (hy : ForkWitness st₂ y)
    (hfam : y.suit = x.suit ∨ y.suit = x.twin.suit) :
    x.rank.toIdx ≤ y.rank.toIdx := by
  rcases Nat.lt_trichotomy x.rank.toIdx y.rank.toIdx with h | h | h
  · exact Nat.le_of_lt h
  · exact Nat.le_of_eq h
  · exact absurd h (forkState_rankDrop_locked st₁ st₂ hwf₁ hwf₂ hcls hx hy hfam)

/-- **THE PAIRCLASS ASSEMBLY ROW** — same-family forks of one macro
class AGREE: this card's floor (`forkState_family_rankFloor`,
`x.rank ≤ y.rank`) together with `Orig.PairConfine`'s
`forkState_sameFamily_rankCeiling` (`y.rank ≤ x.rank`, the upward
half) forces the SAME rank, and `forkState_sameFamily_samePair` then
reads the lower fork's witness as one of the origin pair's two cards:
the family case of the no-lock pairClass theorem — same-family forks
of one class agree as pairs. -/
theorem forkState_family_pairClass (st₁ st₂ : State) (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    (x : Card) (hx : ForkWitness st₁ x) {y : Card} (hy : ForkWitness st₂ y)
    (hfam : y.suit = x.suit ∨ y.suit = x.twin.suit) :
    y.rank.toIdx = x.rank.toIdx ∧ (y = x ∨ y = x.twin) := by
  have hce := forkState_sameFamily_rankCeiling hwf₁ ((forkState_iff).mpr ⟨x, hx⟩) hcls x hx hy hfam
  have hfl := forkState_family_rankFloor st₁ st₂ hwf₁ hwf₂ hcls x hx hy hfam
  have hys : x.suit = y.suit ∨ x.suit = y.twin.suit := by
    rcases hfam with h | h
    · exact Or.inl h.symm
    · refine Or.inr ?_
      rw [Card.twin_suit] at h
      have htwin : y.suit.twin = (x.suit.twin).twin := congrArg Suit.twin h
      rw [Suit.twin_twin] at htwin
      rw [show y.twin.suit = y.suit.twin from Card.twin_suit y]
      exact htwin.symm
  refine ⟨by omega, forkState_sameFamily_samePair hwf₁ ((forkState_iff).mpr ⟨x, hx⟩) hcls x hx hy hfam (by omega)⟩

/-! ### The audit battery

Fresh heads `#print axioms`-audited: every landed row sits in
`[propext]` or `[propext, Quot.sound]`; the public rows that consume
the named residue (§3.5) echo its `sorryAx` (and
`forkState_family_pairClass` additionally echoes PairConfine's
upward `crossing_door_barred` residue, its own card's honest carry);
zero other axioms - no `Classical.choice`. -/

#print axioms origin_lowerPairResident
#print axioms origin_lowerJourney_pulls
#print axioms lower_sandwich
#print axioms dress_legalSeats_pair
#print axioms origin_dresser_isolated
#print axioms origin_dresser_frozen
#print axioms witness_stockWaste_closed
#print axioms lock_zone_residency
#print axioms forkState_rankDrop_locked
#print axioms forkState_family_rankFloor
#print axioms forkState_family_pairClass
