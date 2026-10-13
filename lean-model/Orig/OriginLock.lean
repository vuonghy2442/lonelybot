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
  FOUNDED at the origin, the staircase/pollution endgame — is closed
  by the §3.5 founded-cover composition: the LIFO toggle arithmetic
  and the below-`d` pull rows are LANDED
  (`origin_foundedCover_rungSqueeze`, `origin_foundedCover_belowPull`,
  over the founded-exodus row `lock_found_exit`); the terminal
  pollution crash `origin_foundedCover_pollutesCrash` is LANDED
  ZERO-SORRY as the origin-anchored census crash (its docstring
  carries the route: the d-suit next-up card hot at the terminus,
  Below-seated by the archaeology engine, its fit-neighbor founded
  by the family census against the Below face-up read).
* §4 **THE ASSEMBLY** — `forkState_rankDrop_locked`: the forward
  witness play (`sameOrbit_forward`) hands every leg a
  `reversibleAtW` witness; the cover's origin residency trichotomy
  kills all but the founded case, and the §3.5 staircase closes it
  (the pollution crash landed; zero residue).
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

/-! ### The build-position kit (per-file copies of the banked private
rows of `Orig/Classify.lean` and `Orig/CrossFamily.lean`) -/

/-- The rank of a zero-based index, tabulated by kernel computation
(the copy of `Orig/Classify.lean`'s private `Rk`). -/
private def lockRk : Nat → Rank
  | 0 => .ace | 1 => .two | 2 => .three | 3 => .four | 4 => .five | 5 => .six
  | 6 => .seven | 7 => .eight | 8 => .nine | 9 => .ten | 10 => .jack | 11 => .queen
  | 12 => .king | _ => .ace

private theorem lockRk_toIdx : ∀ (k : Nat), k < 13 → (lockRk k).toIdx = k := by
  intro k hk
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | w + 13 => exact absurd hk (by omega)


/-- **THE PILED-RUNG ROW** — a face-up card's suit rung sits weakly
below its rank index: a taller rung would have founded it, and
conservation forbids a card in two zones (the copy of
`Orig/PairConfine.lean`'s private `conf_piled_rung`, spelled directly
on `rungAt`). -/
private theorem lock_piled_rung {st : State} (hwf : st.WF) {z : Card} {a : Anchor}
    (hmem : z ∈ (st.piles a).faceUp) : rungAt st z.suit ≤ z.rank.toIdx := by
  have hnot : z ∉ st.found z.suit := (mem_faceUp_only hwf hmem).2.2.2.2 z.suit
  rcases Nat.lt_trichotomy (rungAt st z.suit) (z.rank.toIdx) with h | h | h
  · exact Nat.le_of_lt h
  · exact Nat.le_of_eq h
  · exact absurd (mem_found_of_height hwf h) hnot

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
    exact SeedKit.rankColor_pair hrz (SeedKit.color_pair hcdy hcolz).symm
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
    obtain ⟨hrk, hcol⟩ := (canSitOn_eq c w).mp (SeedKit.runOK_adjacent_fit w c bs' rest hok)
    refine Or.inr ⟨w, hw, ?_⟩
    have hrw : w.rank.toIdx = y.rank.toIdx := by omega
    exact SeedKit.rankColor_pair hrw (SeedKit.color_pair hdcol hcol).symm

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
        obtain ⟨hrk, hcol⟩ := (canSitOn_eq u c).mp (SeedKit.runOK_adjacent_fit c u [] us hok)
        have huColx : u.suit.color = x.suit.color :=
          (SeedKit.color_pair hdcolx (fun h => hcol h.symm)).symm
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

/-! ### The exodus kit — a founded card leaves only by its own pull -/

/-- Witness shuffles preserve `WF` (the journey-lift of `step_wf`). -/
private theorem lock_shuffle_wf (s : State) : ∀ {play : List Move} {w : State},
    ShufflePlayW s play w → s.WF → w.WF := by
  intro play w h
  induction h with
  | nil u => intro hwfs; exact hwfs
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro hwfs
      exact ih (step_wf hwfs hstep)

/-- **THE FOUNDED EXODUS** — along a witness shuffle, a card resident
on its own suit's foundation at the start and absent at the end has
left through its OWN pull: some interior leg is literally
`Move.foundToTab c b`, flanked by witness-journey segments (with the
leg's own reversibility witness).  A pull chops exactly the top card
and the step's own LIFO guard names the popped card as the
foundation's top, so the departing leg's card is the departing card
itself (the per-move found-content read: the draw, the slides and
the waste letters write no foundation; the raise appends; only the
pull chops). -/
private theorem lock_found_exit {c : Card} :
    ∀ {s : State} {play : List Move} {w : State},
      ShufflePlayW s play w → s.WF → c ∈ s.found c.suit → c ∉ w.found c.suit →
      ∃ (π ρ : List Move) (b : Base) (u v : State),
        ShufflePlayW s π u ∧
          State.step u (Move.foundToTab c b) = some v ∧
          reversibleAtW u (Move.foundToTab c b) ∧
          ShufflePlayW v ρ w := by
  intro s play w h
  induction h with
  | nil u => intro _hwfs hin hout; exact absurd hin hout
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro hwfs hin hout
      have hwf1 : s₁.WF := step_wf hwfs hstep
      by_cases hc : c ∈ s₁.found c.suit
      · obtain ⟨π, ρ, b, u, v, hp1, hp2, hp3, hp4⟩ := ih hwf1 hc hout
        exact ⟨m :: π, ρ, b, u, v, .cons hrev hstep hp1, hp2, hp3, hp4⟩
      · -- the departure fires at this very leg
        cases m with
        | draw =>
            have hd : s₀.stepDraw = some s₁ := hstep
            have hmem1 : c ∈ s₁.found c.suit := by
              rw [stepDraw_found hd]
              exact hin
            exact absurd hmem1 hc
        | wasteToFound wt =>
            obtain ⟨-, -, xs, -, hs⟩ := step_wasteToFound_inv hstep
            have hmem1 : c ∈ s₁.found c.suit := by
              rw [hs]
              by_cases hsc : c.suit = wt.suit
              · rw [hsc]
                show c ∈ (s₀.setFound wt.suit (s₀.found wt.suit ++ [wt])).found wt.suit
                rw [setFound_found_self]
                exact List.mem_append.mpr (Or.inl (hsc ▸ hin))
              · show c ∈ (s₀.setFound wt.suit (s₀.found wt.suit ++ [wt])).found c.suit
                rw [setFound_found_ne (fun hcon => hsc hcon)]
                exact hin
            exact absurd hmem1 hc
        | wasteToTab wt bt =>
            obtain ⟨_g, _x, _xs, _w, hs⟩ := step_wasteToTab_inv hstep
            have hmem1 : c ∈ s₁.found c.suit := by
              rw [hs]
              show c ∈ (s₀.putCard wt bt).found c.suit
              rw [putCard_found]
              exact hin
            exact absurd hmem1 hc
        | tabToFound wt =>
            obtain ⟨-, k, hpod, hs⟩ := step_tabToFound_inv hstep
            obtain ⟨hself, hothers, -⟩ := tabToFound_found_trio (a := k) hs
            have hmem1 : c ∈ s₁.found c.suit := by
              by_cases hsc : c.suit = wt.suit
              · rw [hsc, hself]
                exact List.mem_append.mpr (Or.inl (hsc ▸ hin))
              · rw [hothers c.suit (fun hcon => hsc hcon)]
                exact hin
            exact absurd hmem1 hc
        | foundToTab wt bt =>
            obtain ⟨ctop, htop, hct, hcp, hs⟩ := step_foundToTab_inv hstep
            rw [hct] at htop
            have hchopself : s₁.found wt.suit = chop (s₀.found wt.suit) := by
              rw [hs, putCard_found, setFound_found_self]
            have hchopne : ∀ σ, σ ≠ wt.suit → s₁.found σ = s₀.found σ := by
              intro σ hσ
              rw [hs, putCard_found]
              exact setFound_found_ne hσ
            by_cases hsc : c.suit = wt.suit
            · -- the chop removed c: c was the top, and the LIFO guard
              -- names the top as the leg's own card
              have hLw : s₀.found wt.suit = chop (s₀.found wt.suit) ++ [wt] :=
                lastOf_chop (show lastOf (s₀.found wt.suit) = some wt from htop)
              have hLc : s₀.found c.suit = chop (s₀.found c.suit) ++ [wt] := by
                rw [hsc]
                exact hLw
              have hch : s₁.found c.suit = chop (s₀.found c.suit) := by
                rw [hsc]
                exact hchopself
              have hcchop : c ∉ chop (s₀.found c.suit) := fun hmem2 =>
                hc (hch ▸ hmem2)
              have hcwt : c = wt := by
                rcases List.mem_append.mp (hLc ▸ hin) with h1 | h2
                · exact absurd h1 hcchop
                · exact List.mem_singleton.mp h2
              subst hcwt
              exact ⟨[], rest, bt, s₀, s₁, .nil _, hstep, hrev, hrest⟩
            · have hmem1 : c ∈ s₁.found c.suit := by
                rw [hchopne c.suit (fun hcon => hsc hcon)]
                exact hin
              exact absurd hmem1 hc
        | tabToTab wt bt =>
            obtain ⟨_a, _hh, _cp, _fr, hs⟩ := step_tabToTab_inv hstep
            have hmem1 : c ∈ s₁.found c.suit := by
              rw [hs, putRun_found, setPile_found]
              exact hin
            exact absurd hmem1 hc

/-! ## §3.5. The named residue — the founded-cover staircase -/

/-- **The self-pollution read at the pull's own landing** (zero-sorry):
a `foundToTab` pull lands its card with the suit rung dropped to exactly
the card's own index, so the pulled card itself reads NEXT-UP at the
landing — the census-visible live card every debt-servicing pull
manufactures, the staircase's re-arming step. -/
private theorem pollutesCrash_landing_live {v : State} {w : Card}
    (hrung : rungAt v w.suit = w.rank.toIdx) :
    v.nextUp w = true := by
  have hf : v.foundHeight w.suit = rungAt v w.suit := rfl
  rw [State.nextUp, hf, hrung]
  simp

/-- **Stage 1's chop length read** (zero-sorry): chopping a nonempty
list drops exactly its last element — the pull bracket's arithmetic
base. -/
private theorem pollutesCrash_chop_len : ∀ l : List Card, l ≠ [] →
    (chop l).length + 1 = l.length := by
  intro l
  induction l with
  | nil => intro hne; exact absurd rfl hne
  | cons a t ih =>
      cases t with
      | nil => intro _; rfl
      | cons z t' =>
          intro _
          have hne : z :: t' ≠ [] := by
            intro hcon
            exact nomatch hcon
          have hih := ih hne
          have hch : chop (a :: z :: t') = a :: chop (z :: t') := rfl
          rw [hch, List.length_cons, List.length_cons]
          omega

/-- **Stage 1's per-pop bracket** (zero-sorry): a pull (`foundToTab`)
whose firing state holds the popped card's own index plus one lands the
suit rung at exactly the popped card's own index — the surfaced card's
own epoch shape, the re-arming read's firing half. -/
private theorem pollutesCrash_pull_bracket {s s' : State} {c : Card} {b : Base}
    (hstep : State.step s (Move.foundToTab c b) = some s')
    (hpin : rungAt s c.suit = c.rank.toIdx + 1) :
    rungAt s' c.suit = c.rank.toIdx := by
  obtain ⟨_c0, htop0, hceq, _hcp, hs⟩ := step_foundToTab_inv hstep
  rw [hceq] at htop0
  have hsplt : s.found c.suit = chop (s.found c.suit) ++ [c] :=
    lastOf_chop (show lastOf (s.found c.suit) = some c from htop0)
  have hpull : s'.found c.suit = chop (s.found c.suit) := by
    rw [hs, putCard_found, setFound_found_self]
  have hne : s.found c.suit ≠ [] := by
    intro hcon
    rw [hcon] at hsplt
    exact nomatch hsplt.symm
  have hb : (s.found c.suit).length = c.rank.toIdx + 1 := hpin
  have hch := pollutesCrash_chop_len (s.found c.suit) hne
  show (s'.found c.suit).length = c.rank.toIdx
  rw [hpull]
  omega

/-- **The piles-read congruence** (Stage support, zero-sorry): the
seat-finder reads only the piles board, so equal piles give equal
`pileOfTop` — the draw-leg carrier's seat half. -/
private theorem pollutesCrash_pileOfTop_congr {s s' : State} (z : Card)
    (hp : s'.piles = s.piles) : s'.pileOfTop z = s.pileOfTop z := by
  unfold State.pileOfTop State.topOf
  simp only [hp]

/-- The none/some constructor clash at explicit type (zero-sorry; a tiny
row lemma so the mover cells avoid open-variable decide). -/
private theorem pollutesCrash_none_ne_some (z : Card) :
    (none : Option Card) = some z → False := by
  intro h
  nomatch h




/-- Any nonempty list splits at its own last element. -/
private theorem pollutesCrash_snocSplit :
    ∀ L : List Card, L ≠ [] → ∃ init LL, L = init ++ [LL] := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons u us ih =>
      intro _
      by_cases hus : us = []
      · rw [hus]
        exact ⟨[], u, rfl⟩
      · obtain ⟨init, LL, h⟩ := ih hus
        exact ⟨u :: init, LL, by rw [h, List.cons_append]⟩

/-! ### The founded-form widening's mechanical bricks
(zero-sorry, banked for the re-thread): the FOUNDED-form carry
`∃ PRE STACK, s.found m₀.suit = PRE ++ [m₀] ++ STACK` with the
founding-position pin `PRE.length = m₀.rank.toIdx` (the mint rides
its own suit's row at its own bracket, possibly buried under later
same-suit raises — the stack).  These five banked rows are the
per-leg row-content the widened mover arms consume; the re-seat
row and the nil-branch census are priced in the ledger stamps. -/

/-- The re-seat row (the re-exhume's landing kit, the widening's last
loose end before the mover assembly): a pop of the mint itself — its
row read at the founding bracket — lands the mint NEXT-UP-LIVE at
its own bracket (the pull-bracket), seated top of its landing pile
in the light kit's very shape (either the bare king over an empty
seat, or over the fit's host pile whose chop tail is live).  The
row is the founded-form carry's switch-back constructor: the arms
of the widened mover consume it verbatim. -/
private theorem pollutesCrash_reseat_pop {vp s₁ : State} {m₀ : Card}
    {b : Base}
    (hwfs : vp.WF)
    (hrungv : rungAt vp m₀.suit = m₀.rank.toIdx + 1)
    (hstep : State.step vp (Move.foundToTab m₀ b) = some s₁) :
    (s₁.nextUp m₀ = true ∧ ∃ ke se, (s₁.piles ke).faceUp = se ++ [m₀] ∧
      s₁.pileOfTop m₀ = some ke ∧
      (chop (s₁.piles ke).faceUp ≠ [] ∨
        ((s₁.piles ke).hidden = [] ∧ m₀.rank = Rank.king))) := by
  have hwfs₁ : s₁.WF := step_wf hwfs hstep
  obtain ⟨_c₀, _htop0, _hceq, hcp, hs⟩ := step_foundToTab_inv hstep
  -- the landing rung is the mint's own index (the founding bracket, one under)
  have hbran : rungAt s₁ m₀.suit = m₀.rank.toIdx :=
    pollutesCrash_pull_bracket hstep hrungv
  have hn1 : s₁.nextUp m₀ = true :=
    pollutesCrash_landing_live hbran
  refine ⟨hn1, ?_⟩
  cases b with
  | inl a₂ =>
      -- the bare king landing: chop dies but the king line holds
      obtain ⟨hemp, hking⟩ := canPlace_inl hcp
      have hlens : s₁.piles a₂ = ⟨[], [m₀]⟩ := by
        rw [hs, putCard_eq_inl, setPile_piles_self]
      refine ⟨a₂, [], ?_, ?_, Or.inr ?_⟩
      · rw [hlens]
        show (⟨[], [m₀]⟩ : Pile).faceUp = ([] : List Card) ++ [m₀]
        rfl
      · exact (pileOfTop_eq_some_iff hwfs₁).2 (by
          show (s₁.piles a₂).top = some m₀
          rw [hlens]
          show (⟨[], [m₀]⟩ : Pile).top = some m₀
          rfl)
      · rw [hlens]
        show (⟨[], [m₀]⟩ : Pile).hidden = [] ∧ m₀.rank = Rank.king
        exact ⟨rfl, hking⟩
  | inr z =>
      obtain ⟨k₀', hholdz', _hsitz'⟩ := canPlace_inr hcp
      -- the mid-state is piles-verbatim under setFound, so the host
      -- read re-anchors at the fit's own pile
      have hmidpot : (vp.setFound m₀.suit (chop (vp.found m₀.suit))).pileOfTop z
          = some k₀' :=
        (pollutesCrash_pileOfTop_congr z
          (setFound_piles vp m₀.suit (chop (vp.found m₀.suit)))).trans
          hholdz'
      have hlens : s₁
          = (vp.setFound m₀.suit (chop (vp.found m₀.suit))).setPile k₀'
            { vp.piles k₀' with
                faceUp := (vp.piles k₀').faceUp ++ [m₀] } := by
            rw [hs]
            rw [show (vp.setFound m₀.suit (chop (vp.found m₀.suit))).putCard m₀
                  (Sum.inr z)
                = (vp.setFound m₀.suit (chop (vp.found m₀.suit))).setPile k₀'
                  { (vp.setFound m₀.suit (chop (vp.found m₀.suit))).piles k₀' with
                    faceUp := ((vp.setFound m₀.suit
                      (chop (vp.found m₀.suit))).piles k₀').faceUp ++ [m₀] }
              from by simp only [State.putCard, hmidpot]]
            rw [setFound_piles vp m₀.suit (chop (vp.found m₀.suit))]
      have hshape1 : (s₁.piles k₀').faceUp
          = (vp.piles k₀').faceUp ++ [m₀] := by
        rw [hlens, setPile_piles_self]
      have hhold1 : s₁.pileOfTop m₀ = some k₀' :=
        (pileOfTop_eq_some_iff hwfs₁).2 (by
          show lastOf (s₁.piles k₀').faceUp = some m₀
          rw [hshape1]
          exact lastOf_snoc)
      have hcond1 : chop (s₁.piles k₀').faceUp ≠ [] ∨
          ((s₁.piles k₀').hidden = [] ∧ m₀.rank = Rank.king) := by
        refine Or.inl ?_
        rw [hshape1, chop_snoc]
        show (vp.piles k₀').faceUp ≠ []
        intro hcon
        have hz2 : lastOf ((vp.piles k₀').faceUp) = some z :=
          (pileOfTop_top hholdz').2
        rw [hcon] at hz2
        exact pollutesCrash_none_ne_some z hz2
      exact ⟨k₀', (vp.piles k₀').faceUp, hshape1, hhold1, hcond1⟩

/-- **THE TERMINAL-HOT SEAT ROW** — the successor-archaeology's engine
(the census corner's priced fuel, zero-sorry): along a witness
shuffle, a NON-KING card founded at the origin and HOT at the
terminus ends FACE-UP DIRECTLY ABOVE A BELOW-NEIGHBOR at the
terminus.  The route is the exodus decomposition (`lock_found_exit`:
the card left its row through its own pull), the fire-time bracket
read (the popped card tops its row, the rung one above its index),
the landing kit (`pollutesCrash_reseat_pop`: next-up-live, seat-top,
the light clause), the non-king gate (`hnk` kills the bare-king
line, so the landing seats the card over a live below-neighbor,
`chop_snoc`), and the public positional core (`Below_stable`)
transporting the seat over the remaining suffix; terminal hotness
bars the re-founding arm.  The row needs NO seat premise at any
state — the datum that priced the census corner — only the two
bracket reads (the ORIGIN HEIGHT and the TERMINAL HOTNESS), both of
which the founded-case head holds by `hsq1`-grade anchors.  The
king boundary stays with the consumer (the transport's own gate;
kings may land bare). -/
private theorem pollutesCrash_terminalHot_Below {st₁ sth : State}
    {play : List Move} (hplay : ShufflePlayW st₁ play sth)
    (hwf₁ : st₁.WF) (hwf₂ : sth.WF) {t : Card}
    (hnk : t.rank ≠ Rank.king)
    (horg : t.rank.toIdx < rungAt st₁ t.suit)
    (hhot : sth.nextUp t = true) :
    ∃ b, Below sth t b := by
  -- founded at the origin (the height bridge), un-founded at the end (hotness)
  have hinfound : t ∈ st₁.found t.suit :=
    mem_found_of_height hwf₁ horg
  have hnotfound : t ∉ sth.found t.suit := by
    intro hmem
    have hlt₀ := FoundKit.mem_found_rank_lt hwf₂ hmem
    have hlt : t.rank.toIdx < rungAt sth t.suit := hlt₀
    have heq : t.rank.toIdx = rungAt sth t.suit :=
      of_decide_eq_true hhot
    omega
  -- the exodus: the card left through its own pull, mid-journey
  obtain ⟨π, ρ, b, u, v, hpre, hstep, _hrev, hpost⟩ :=
    lock_found_exit (c := t) hplay hwf₁ hinfound hnotfound
  have hwfu : u.WF := lock_shuffle_wf st₁ hpre hwf₁
  have hwfv : v.WF := step_wf hwfu hstep
  -- the fire-time bracket: the popped card tops its row, the rung
  -- one above its own index
  have htop : u.foundTop t.suit = some t :=
    foundToTab_pops_currentTop hstep
  have hsplit : u.found t.suit = chop (u.found t.suit) ++ [t] :=
    lastOf_chop (show lastOf (u.found t.suit) = some t from htop)
  have hchoplen : (chop (u.found t.suit)).length = t.rank.toIdx :=
    wf_found_chop_toIdx hwfu htop
  have hru : rungAt u t.suit = t.rank.toIdx + 1 := by
    show (u.found t.suit).length = _
    rw [hsplit, List.length_append]
    have h1 : ([t] : List Card).length = 1 := rfl
    omega
  -- the landing: next-up-live, seat-top, in the light kit's own shape
  obtain ⟨_hn1, ke, se, hshape1, _hhold1, hcond1⟩ :=
    pollutesCrash_reseat_pop hwfu hru hstep
  -- the non-king gate: the landing seats the card over a live below-neighbor
  have hse : se ≠ [] := by
    rcases hcond1 with hch | ⟨_, hking⟩
    · rw [hshape1, chop_snoc] at hch
      exact hch
    · exact absurd hking hnk
  obtain ⟨se', z, hseSplit⟩ := pollutesCrash_snocSplit se hse
  have hgoal : (v.piles ke).faceUp = se' ++ [z, t] := by
    rw [hshape1, hseSplit]
    simp [List.append_assoc]
  have hbelowV : ∃ z, Below v t z :=
    ⟨z, ke, se', [], by
      show (v.piles ke).faceUp = se' ++ z :: t :: ([] : List Card)
      rw [hgoal]⟩
  -- the public positional core carries the seat over the suffix
  rcases Below_stable hwfv hpost (d := t) hnk (Or.inr hbelowV) with
    hf | ⟨z', hz'⟩
  · exact absurd hf hnotfound
  · exact ⟨z', hz'⟩

/-- The pull's bare landing transport: the successor's own-suit
foundation row is exactly the chopped firing row (the
`setFound`/`putCard` found-transport read of the pull's successor
equation, in the form the staircase seed consumes). -/
private theorem lock_pull_landing {s s' : State} {w : Card} {b : Base}
    (hs : s' = (s.setFound w.suit (chop (s.found w.suit))).putCard w b) :
    s'.found w.suit = chop (s.found w.suit) := by
  rw [hs, putCard_found, setFound_found_self]

/-- **THE RUNG SQUEEZE** — the founded-cover staircase's two-end
arithmetic (the LIFO toggle's bookkeeping face, route item 1): at the
origin the cover's home suit rung already stands past the cover's own
index (the founded-membership bridge — the cover is founded there),
and at the lower fork the cover's home suit rung stands TWO UNDER the
cover's index (the piled-rung row plus the sandwich's parked pin
`nextUp d = false`: the face-up cover cannot sit at exactly its own
index), so the journey census prices the squeeze as a PULL DEBT: the
witness play carries at least two more `d`-suit pulls than raises —
the debt the LIFO descent pays by dragging the cover and the card
below it out of their foundation. -/
private theorem origin_foundedCover_rungSqueeze {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF) {play : List Move}
    (hplay : ShufflePlayW st₁ play st₂)
    {d : Card} {c2 : Anchor} (hmem : d ∈ (st₂.piles c2).faceUp)
    (hnext : st₂.nextUp d = false)
    (hdfound : d ∈ st₁.found d.suit) :
    d.rank.toIdx + 1 ≤ rungAt st₁ d.suit ∧
      rungAt st₂ d.suit + 2 ≤ d.rank.toIdx + 1 ∧
      raisesOf play d.suit + 2 ≤ pullsOf play d.suit := by
  have hr1 : d.rank.toIdx < rungAt st₁ d.suit :=
    FoundKit.mem_found_rank_lt hwf₁ hdfound
  have hrP := lock_piled_rung hwf₂ hmem
  have hfh : st₂.foundHeight d.suit = rungAt st₂ d.suit := rfl
  have hne : d.rank.toIdx ≠ rungAt st₂ d.suit := by
    intro hcon
    rw [State.nextUp] at hnext
    rw [hcon, hfh] at hnext
    exact absurd hnext (by simp)
  have hsq2 : rungAt st₂ d.suit + 2 ≤ d.rank.toIdx + 1 := by omega
  have hc := witness_rung_census hplay d.suit
  exact ⟨by omega, hsq2, by omega⟩

/-- **THE BELOW-`d` PULL (the staircase seed)** — the squeeze's
two-rung drop forces the card ONE BELOW the cover in the cover's own
suit out of its foundation: founded at the origin (the origin rung
already stands past the cover's own index, a fortiori past the
below-cover's), NOT founded at the lower fork (the end rung stands two
under the cover's index).  By the founded-exodus row the departure
fires as the card's OWN `foundToTab` leg — the LIFO discipline popping
it exactly one above its index — and the landing lies on no empty
seat (the popped card, two ranks under the cover's index, is no king:
the pillar's king row bars the base), so it lands DIRECTLY on a
card-landlord one above it in the family color `yc` — the dress
lattice, one rung down the staircase — NEXT-UP-LIVE at its own landing
(`rungAt v = index`: the just-popped card is instantly re-foundable) —
with its firing-state and landing-state witness-shuffle segments
preserved for the pollution analysis to come. -/
private theorem origin_foundedCover_belowPull {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF) {play : List Move}
    (hplay : ShufflePlayW st₁ play st₂)
    {d : Card} {yc : Color}
    (hyc : yc ≠ d.suit.color)
    (hr1 : d.rank.toIdx + 1 ≤ rungAt st₁ d.suit)
    (hr2 : rungAt st₂ d.suit + 2 ≤ d.rank.toIdx + 1) :
    ∃ (w : Card) (b : Base) (zt : Card) (kk : Anchor) (bs : List Card)
        (π ρ : List Move) (u v : State),
      w.suit = d.suit ∧
        w.rank.toIdx + 2 ≤ d.rank.toIdx + 1 ∧
        ShufflePlayW st₁ π u ∧
        State.step u (Move.foundToTab w b) = some v ∧
        reversibleAtW u (Move.foundToTab w b) ∧
        ShufflePlayW v ρ st₂ ∧
        (v.piles kk).faceUp = bs ++ [zt, w] ∧
        v.pileOfTop w = some kk ∧
        zt.rank.toIdx = w.rank.toIdx + 1 ∧
        zt.suit.color = yc ∧
        rungAt u w.suit = w.rank.toIdx + 1 ∧
        rungAt v w.suit = w.rank.toIdx := by
  -- the below-cover card of the cover's own suit, one index down the build
  have hidx13 : d.rank.toIdx - 1 < 13 := by
    have h13 := Rank.toIdx_lt d.rank
    omega
  have hwidx : (lockRk (d.rank.toIdx - 1)).toIdx = d.rank.toIdx - 1 :=
    lockRk_toIdx (d.rank.toIdx - 1) hidx13
  obtain ⟨w, hws, hwr⟩ : ∃ w : Card, w.suit = d.suit ∧
      w.rank.toIdx = d.rank.toIdx - 1 :=
    ⟨Card.mk d.suit (lockRk (d.rank.toIdx - 1)), rfl, by
      show (lockRk (d.rank.toIdx - 1)).toIdx = d.rank.toIdx - 1
      rw [hwidx]⟩
  -- founded at the origin, not founded at the endstate
  have hinfound : w ∈ st₁.found w.suit :=
    mem_found_of_height hwf₁ (by
      show w.rank.toIdx < rungAt st₁ w.suit
      rw [hws]
      omega)
  have hnotfound : w ∉ st₂.found w.suit := by
    intro hmem
    have hlt₀ := FoundKit.mem_found_rank_lt hwf₂ hmem
    have hlt : w.rank.toIdx < rungAt st₂ w.suit := hlt₀
    rw [hws, hwr] at hlt
    omega
  -- the exodus: the below-cover card's own pull, mid-journey
  obtain ⟨π, ρ, b, u, v, hpre, hstep, hrev, hpost⟩ :=
    lock_found_exit (c := w) hplay hwf₁ hinfound hnotfound
  have hwfu : u.WF := lock_shuffle_wf st₁ hpre hwf₁
  have hwfv : v.WF := step_wf hwfu hstep
  -- the LIFO fire-time reads
  have htop : u.foundTop w.suit = some w := foundToTab_pops_currentTop hstep
  obtain ⟨_c0, _h0, _h1, hg, hs⟩ := step_foundToTab_inv hstep
  have hchoplen : (chop (u.found w.suit)).length = w.rank.toIdx :=
    wf_found_chop_toIdx hwfu htop
  have hsplit : u.found w.suit = chop (u.found w.suit) ++ [w] :=
    lastOf_chop (show lastOf (u.found w.suit) = some w from htop)
  have huvf : v.found w.suit = chop (u.found w.suit) :=
    lock_pull_landing hs
  have hru : rungAt u w.suit = w.rank.toIdx + 1 := by
    show (u.found w.suit).length = _
    rw [hsplit, List.length_append]
    have h1 : ([w] : List Card).length = 1 := rfl
    omega
  have hrv : rungAt v w.suit = w.rank.toIdx := by
    show (v.found w.suit).length = _
    rw [huvf]
    exact hchoplen
  -- the landing: no empty seat (a popped card two under the cover is
  -- no king), only a landlord
  cases b with
  | inl ka =>
      exfalso
      have hK := lock_canPlace_inl_king hg
      have hKeq : w.rank.toIdx = Rank.king.toIdx := by rw [hK]
      have hk12 : Rank.king.toIdx = 12 := rfl
      have hr1cap : rungAt st₁ d.suit ≤ 13 := by
        obtain ⟨n, hn⟩ := hwf₁.found_prefix d.suit
        show (st₁.found d.suit).length ≤ 13
        rw [hn, List.length_take, Suit.upCards_length]
        omega
      omega
  | inr zt =>
      obtain ⟨kk, hztop, hsit⟩ := canPlace_inr hg
      obtain ⟨hzrk, hzcol⟩ := (canSitOn_eq w zt).mp hsit
      have hzc : zt.suit.color = yc := by
        have h2 : w.suit.color ≠ yc := by
          rw [hws]
          exact fun hcon => hyc hcon.symm
        exact SeedKit.color_pair hzcol h2
      -- the landing pile: w lands directly on zt, in zt's own pile
      have hmidp : (u.setFound w.suit (chop (u.found w.suit))).piles = u.piles :=
        setFound_piles u w.suit _
      have hmidpo :
          (u.setFound w.suit (chop (u.found w.suit))).pileOfTop zt = some kk := by
        rw [lock_pileOfTop_of_piles zt hmidp]
        exact hztop
      have hvkk : v.piles kk
          = { (u.piles kk) with faceUp := (u.piles kk).faceUp ++ [w] } := by
        have hp : (((u.setFound w.suit (chop (u.found w.suit))).putCard
              w (Sum.inr zt)).piles kk)
            = (if kk = kk
                then { (u.setFound w.suit (chop (u.found w.suit))).piles kk with
                       faceUp := ((u.setFound w.suit (chop (u.found w.suit))).piles kk).faceUp
                         ++ [w] }
                else (u.setFound w.suit (chop (u.found w.suit))).piles kk) := by
          simp only [putCard_piles_inr _ _ _ _ hmidpo]
        rw [hs, hp, if_pos rfl, hmidp]
      have hzlast : lastOf (u.piles kk).faceUp = some zt := (pileOfTop_top hztop).2
      have hztshape : (u.piles kk).faceUp = chop (u.piles kk).faceUp ++ [zt] :=
        lastOf_chop hzlast
      have hshapev : (v.piles kk).faceUp
          = chop (u.piles kk).faceUp ++ [zt, w] := by
        have h1 : (u.piles kk).faceUp ++ [w]
            = (chop (u.piles kk).faceUp ++ [zt]) ++ [w] := by
          have hgen : ∀ E : List Card, (u.piles kk).faceUp = E ++ [zt] →
              (u.piles kk).faceUp ++ [w] = E ++ [zt] ++ [w] := by
            intro E hE
            rw [hE]
          exact hgen _ hztshape
        have h2 : (chop (u.piles kk).faceUp ++ [zt]) ++ [w]
            = chop (u.piles kk).faceUp ++ [zt, w] := by
          cases chop (u.piles kk).faceUp <;> simp [List.append_assoc]
        rw [hvkk]
        show (u.piles kk).faceUp ++ [w] = _
        rw [h1, h2]
      have hpot : v.pileOfTop w = some kk := by
        refine (pileOfTop_eq_some_iff hwfv).2 ?_
        show lastOf (v.piles kk).faceUp = some w
        rw [hvkk]
        show lastOf ((u.piles kk).faceUp ++ [w]) = some w
        exact lastOf_snoc
      refine ⟨w, Sum.inr zt, zt, kk, chop (u.piles kk).faceUp, π, ρ, u, v,
        hws, ?_, hpre, hstep, hrev, hpost, hshapev, hpot, hzrk.symm, hzc, hru, hrv⟩
      omega

namespace ForkKit

/-- **THE NEXT-UP EXILE CRASH** (the Phase B consolidation: the
composition-head kill promoted to its own citable row).  At any two WF
states joined by a witness shuffle, a fork `y` at the landing, and a
cover card `d` — one rank below the fork, off the fork's color, its
suit's rung past `d`'s index at the origin (`hsq1`) and two under it
at the terminus (`hsq2`) — there is NO SUCH JOURNEY.  ROUTE: the
d-suit HOT CARD at the terminus's own rung — `T := Card.mk d.suit
(lockRk (rungAt st₂ d.suit))`, hot by definition there
(`pollutesCrash_landing_live`: its rank index IS the terminus's
d-rung), non-king and origin-height by `omega` over
`hsq2`/`hsq1`/`hd` — was founded at the origin (the height bridge)
but is hot (never re-founded) at the terminus, so the
successor-archaeology engine `pollutesCrash_terminalHot_Below` (the
`lock_found_exit` exodus split, the fire-time bracket, the
`reseat_pop` landing kit, the `Below_stable` suffix transport) ends
it BELOW-SEATED at `st₂`; the seat fit (`SeedKit.runOK_adjacent_fit` +
`canSitOn_eq`) makes that below-neighbor FAMILY-colored
(`SeedKit.color_pair` against `hdcol`) and ranked strictly under the
fork (`omega` over `hsq2`), the fork's own family rungs both pin at
the pair rank (`canRaiseS_rung` off `hy`, the twin via
`Card.twin_rank`), so the neighbor is foundation-resident
(`mem_found_of_height`) while the Below seat reads it face-up
(`mem_found_unique`) — `False`, mint-suit-agnostic: no chase, no
twin datum, no census debt, anywhere.  Future endgames needing "the
third cell is census-full" cite this row directly. -/
theorem fork_nextUpExile_crash {st₁ st₂ : State} (hwf₁ : st₁.WF)
    (hwf₂ : st₂.WF) {y : Card} (hy : ForkWitness st₂ y)
    {play : List Move} (hplay : ShufflePlayW st₁ play st₂)
    {d : Card} (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hdcol : d.suit.color ≠ y.suit.color)
    (hsq1 : d.rank.toIdx + 1 ≤ rungAt st₁ d.suit)
    (hsq2 : rungAt st₂ d.suit + 2 ≤ d.rank.toIdx + 1) :
    False := by
  have hfam13 : y.rank.toIdx < 13 := Rank.toIdx_lt y.rank
  have hk13 : rungAt st₂ d.suit < 13 := by omega
  -- the d-suit hot card at the terminus's own rung (its hotness is
  -- definitional: its index IS the terminus's d-suit rung)
  obtain ⟨T, hTdef⟩ :
      ∃ c : Card, c = Card.mk d.suit (lockRk (rungAt st₂ d.suit)) :=
    ⟨_, rfl⟩
  have hTidx : T.rank.toIdx = rungAt st₂ d.suit := by
    rw [hTdef]
    exact lockRk_toIdx _ hk13
  have hTsuit : T.suit = d.suit := by
    rw [hTdef]
  have hhotT : st₂.nextUp T = true :=
    pollutesCrash_landing_live (by rw [hTsuit, hTidx])
  have hnkT : T.rank ≠ Rank.king := by
    intro hcon
    rw [hcon] at hTidx
    have hk12 : Rank.king.toIdx = 12 := rfl
    omega
  have horgT : T.rank.toIdx < rungAt st₁ T.suit := by
    rw [hTsuit, hTidx]
    omega
  obtain ⟨nb, a, L, R, hshp⟩ :=
    pollutesCrash_terminalHot_Below hplay hwf₁ hwf₂ hnkT horgT hhotT
  have hok : runOK (L ++ nb :: T :: R) = true := by
    rw [← hshp]
    exact hwf₂.runOK_of a
  obtain ⟨hrkbt, hcolbt⟩ :=
    (canSitOn_eq T nb).mp (SeedKit.runOK_adjacent_fit nb T L R hok)
  have hbcol : nb.suit.color = y.suit.color :=
    SeedKit.color_pair (a := d.suit.color)
      (by rw [← hTsuit]; exact hcolbt) hdcol
  have hyPin : rungAt st₂ y.suit = y.rank.toIdx :=
    canRaiseS_rung ((hy.1 y).mp (Or.inl rfl))
  have hytPin : rungAt st₂ y.twin.suit = y.rank.toIdx := by
    have h0 := canRaiseS_rung ((hy.1 y.twin).mp (Or.inr rfl))
    rwa [Card.twin_rank y] at h0
  have hsuit : nb.suit = y.suit ∨ nb.suit = y.twin.suit := by
    have hz : (Card.mk nb.suit y.rank) = y ∨
        (Card.mk nb.suit y.rank) = y.twin :=
      SeedKit.rankColor_pair rfl hbcol
    rcases hz with h | h
    · refine Or.inl ?_
      exact (congrArg Card.suit h :
        (Card.mk nb.suit y.rank).suit = y.suit)
    · refine Or.inr ?_
      exact (congrArg Card.suit h :
        (Card.mk nb.suit y.rank).suit = y.twin.suit)
  have hbmem : nb ∈ st₂.found nb.suit := by
    refine mem_found_of_height hwf₂ ?_
    have hbund : nb.rank.toIdx < y.rank.toIdx := by omega
    rcases hsuit with h | h
    · rw [h]
      show nb.rank.toIdx < rungAt st₂ y.suit
      rw [hyPin]
      exact hbund
    · rw [h]
      show nb.rank.toIdx < rungAt st₂ y.twin.suit
      rw [hytPin]
      exact hbund
  have hbface : nb ∈ (st₂.piles a).faceUp := by
    rw [hshp]
    exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
  obtain ⟨hh, _hS, _hW, _⟩ := mem_found_unique hwf₂ hbmem
  exact absurd hbface (hh a).2

end ForkKit

/-- **THE EXODUS-SEATING CENSUS** — the interval form of the orphan-seat
law, the campaign's Phase C consolidation: along a witness shuffle, ANY
suit whose foundation rung DROPS exiles its whole upper interval —
every σ-card with rank index in `[rungAt st₂ σ, rungAt st₁ σ)` was
founded at the journey's start (the height bridge's forward half) and
is unfounded at its end (the converse half, against the dropped
rung), so the orphan-seat law seats each one FACE-UP at the end
state, on a fitting below-neighbor.  THE PIGEONHOLE SHARPENING IS
BUILT INTO THE FIT: the below-neighbor of a rank-`i` exile is pinned
at rank `i + 1` (the run fit), so a width-`w` interval forces `w`
DISTINCT opposite-color face-up CELLS at the end state — against a
saturated lattice (a fork's family census holds every such cell
founded) the cell-count is the whole kill, with no per-card chase
anywhere.  `ForkKit.fork_nextUpExile_crash` above is the law's first
consumer by spirit (the boundary cell of a width-≥2 interval against
a saturated fork); future dragged-card endgames cite the census
directly.  The statement lives here rather than in
`Orig/OrphanSeat.lean` because the height bridge (`FoundKit`, in
`Orig/PairConfine.lean`) sits above the orphan chapter in the import
DAG. -/
theorem exodus_seating_census {st₁ st₂ : State} (hwf₁ : st₁.WF)
    {τ : List Move} (hτ : ShufflePlayW st₁ τ st₂)
    (σ : Suit) :
    ∀ r : Rank, rungAt st₂ σ ≤ r.toIdx → r.toIdx < rungAt st₁ σ →
      r ≠ Rank.king →
      ∃ (a : Anchor) (b : Card),
        (Card.mk σ r) ∈ (st₂.piles a).faceUp ∧
          b ∈ (st₂.piles a).faceUp ∧
            canSitOn (Card.mk σ r) b = true := by
  intro r hlo hhi hnk
  have hwf₂ : st₂.WF := lock_shuffle_wf st₁ hτ hwf₁
  have hmem : (Card.mk σ r) ∈ st₁.found σ :=
    FoundKit.mem_found_of_rung hwf₁ hhi
  have hout : (Card.mk σ r) ∉ st₂.found σ := by
    intro hc
    have hlt := FoundKit.mem_found_rank_lt hwf₂ hc
    have hlt' : r.toIdx < rungAt st₂ σ := hlt
    omega
  exact cross_orphan_seat hwf₁ hτ hnk hmem hout

set_option linter.unusedVariables false in
/-- **THE FOUNDED-COVER POLLUTION CRASH** — §3.5's terminal row, LANDED
ZERO-SORRY as THE ORIGIN-ANCHORED CENSUS CRASH (the nil census's landed
route, promoted to the composition head; the mint never enters), and
CONSOLIDATED at Phase B into the citable public row
`ForkKit.fork_nextUpExile_crash` directly above — its docstring carries
the full route (the d-suit hot card at the terminus's own rung,
Below-seated by the archaeology engine, its fit-neighbor family-colored
strictly under the fork's pinned family rungs — foundation-resident
against the Below face-up read; mint-suit-agnostic, no chase, no twin
datum).  The seed-side premises (`hpkg`, `hsq3`, `hpc1`, `hpc2`, the
cover/lattice pack and the origin-fork rows) stay as the frozen
scaffold's documented binders — the ρ-tail chase they once fed is
RETIRED FROM THE TREE (deleted unconsumed with the cleanup pass; its
covered-mint twin-top fork and its mover-local choice leak went with
it, and no audited head references any of it). -/
private theorem origin_foundedCover_pollutesCrash {st₁ st₂ : State}
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
    (hnext : st₂.nextUp d = false)
    (hlattice : ∀ z, st₂.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin)
    (hdfound : d ∈ st₁.found d.suit)
    (hsq1 : d.rank.toIdx + 1 ≤ rungAt st₁ d.suit)
    (hsq2 : rungAt st₂ d.suit + 2 ≤ d.rank.toIdx + 1)
    (hsq3 : raisesOf play d.suit + 2 ≤ pullsOf play d.suit)
    (hpc1 : raisesOf play y.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.suit)
    (hpc2 : raisesOf play y.twin.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.twin.suit)
    (hpkg : ∃ (w : Card) (b : Base) (zt : Card) (kk : Anchor) (bs : List Card)
        (π ρ : List Move) (u v : State),
      w.suit = d.suit ∧
        w.rank.toIdx + 2 ≤ d.rank.toIdx + 1 ∧
        ShufflePlayW st₁ π u ∧
        State.step u (Move.foundToTab w b) = some v ∧
        reversibleAtW u (Move.foundToTab w b) ∧
        ShufflePlayW v ρ st₂ ∧
        (v.piles kk).faceUp = bs ++ [zt, w] ∧
        v.pileOfTop w = some kk ∧
        zt.rank.toIdx = w.rank.toIdx + 1 ∧
        zt.suit.color = y.suit.color ∧
        rungAt u w.suit = w.rank.toIdx + 1 ∧
        rungAt v w.suit = w.rank.toIdx) :
    False := by
  -- THE ORIGIN-ANCHORED CENSUS CRASH, consolidated (Phase B) into the
  -- citable row above; the frozen scaffold's remaining binders (the
  -- seed `hpkg`, the migration counts `hsq3`/`hpc1`/`hpc2`, the
  -- cover/lattice pack, the origin-fork rows) are the set_option
  -- silenced documented package — nothing of them enters the proof
  exact ForkKit.fork_nextUpExile_crash hwf₁ hwf₂ hy hplay hd hdcol hsq1 hsq2

/-- **THE FOUNDED-COVER CASE** — the composition row: the one
origin-residency case of the cover `d` that §3's landed mechanism rows
do not close (each other residency is fully closed by §3: on-board ⇒
`origin_dresser_frozen`, hidden ⇒ `shuffle_hiddenPinned`,
stock-or-waste ⇒ `witness_stockWaste_closed`; see the §4 assembly).
The founded case decomposes as THE STAIRCASE:

1. **The LIFO toggle arithmetic** (LANDED:
   `origin_foundedCover_rungSqueeze`) — the cover, founded at the
   origin with its suit rung past its own index, sits face-up and
   PARKED (`nextUp d = false`) at the lower fork with its suit rung
   two under its index, so the census prices two more `d`-suit pulls
   than raises: the LIFO descent must drag the cover AND the card
   below it out of their foundation.
2. **The below-`d` pull** (LANDED: `origin_foundedCover_belowPull`) —
   the card one below the cover in the cover's own suit departs
   through its OWN `foundToTab` leg (the founded-exodus row: a pull
   chops exactly the top, and the step's guard names the popped card),
   landing NEXT-UP-LIVE on its family-color landlord one above — the
   dress lattice (`dress_legalSeats_pair`) one rung down, the
   staircase's seed.
 3. **The pollution crash** (LANDED, zero-sorry:
    `origin_foundedCover_pollutesCrash`, the ORIGIN-ANCHORED CENSUS
    CRASH) — the d-suit next-up card at the terminus's own rung is
    hot there by definition, Below-seated by the archaeology engine,
    and its fit-neighbor is family-colored strictly under the fork's
    pinned family rungs — foundation-resident against the Below
    face-up read: no witness journey reaches the founded-cover
    endgame. -/
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
    (hnext : st₂.nextUp d = false)
    (hlattice : ∀ z, st₂.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin)
    (hdfound : d ∈ st₁.found d.suit) :
    False := by
  obtain ⟨c, bsC, hshape, hpod⟩ := hdcover
  have hmem : d ∈ (st₂.piles c).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.2 (Or.inr (by simp))))
  -- the LIFO toggle arithmetic (route item 1)
  obtain ⟨hsq1, hsq2, hsq3⟩ :=
    origin_foundedCover_rungSqueeze hwf₁ hwf₂ hplay hmem hnext hdfound
  -- §1's family pull debt, on BOTH family suits
  obtain ⟨hpc1, hpc2⟩ := origin_lowerJourney_pulls hwf₁ hx hy hfam hplay hlt
  -- the below-`d` pull (route items 1-3's landed half)
  have hyc : y.suit.color ≠ d.suit.color := fun hcon => hdcol hcon.symm
  obtain hpkg := origin_foundedCover_belowPull hwf₁ hwf₂ hplay hyc hsq1 hsq2
  -- the pollution crash (the named residue)
  exact origin_foundedCover_pollutesCrash hwf₁ hwf₂ hx hy hfam hlt hplay d hd hdcol
    ⟨c, bsC, hshape, hpod⟩ hnext hlattice hdfound hsq1 hsq2 hsq3 hpc1 hpc2 hpkg

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
  obtain ⟨a, c, bsC, d, hpo, -, hshape, hrankd, hcold, hpod, hne, hnext, hKd, hlatt, -⟩ :=
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
      ⟨c, bsC, hshape, hpod⟩ hnext hlatt hdfound
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
  refine ⟨by omega, forkState_sameFamily_samePair hfam (by omega)⟩

/-! ### The audit battery

 Fresh heads `#print axioms`-audited: every landed row sits in
`[propext]` or `[propext, Quot.sound]` — including the staircase's
landed mechanism rows (`origin_foundedCover_rungSqueeze`,
`origin_foundedCover_belowPull`, with the exodus kit
`lock_found_exit` and the build-position copies) AND §3.5's terminal
`origin_foundedCover_pollutesCrash` — the origin-anchored census
crash, zero-`sorry` and zero-`Classical.choice`: the public rows that
consume it (`forkState_rankDrop_locked`,
`forkState_family_rankFloor`, `forkState_family_pairClass`) inherit
NO axiom from it, and PairConfine's upward chain (`crossing_door_barred`
onward) is also landed sorry-free — so `forkState_family_pairClass`
echoes NOTHING.  The ρ-tail chase that once carried the residue (the
descent/mover family with its `rhoOpen` guard and the mint kit) is
RETIRED FROM THE TREE — deleted unconsumed in the cleanup pass, its
covered-mint twin-top fork and its mover-local choice leak gone with
it; the only kit remaining is the engine's own (`landing_live`,
`chop_len`, `pull_bracket`, `pileOfTop_congr`, `none_ne_some`,
`snocSplit`, `reseat_pop`, `terminalHot_Below`), each consumed by the
head's crash chain.  The choice-noose's lesson stays banked (the
historical witness is the retired mover): `omega` instantiates a live
`∃` hypothesis in its context with `Classical.choose` — every
`omega` facing ∃-shaped premises runs only AFTER they are
destructured (the head's own obtain-first weld, and the retired
mover's head `obtain` likewise). -/

#print axioms origin_lowerPairResident
#print axioms origin_lowerJourney_pulls
#print axioms lower_sandwich
#print axioms dress_legalSeats_pair
#print axioms origin_dresser_isolated
#print axioms origin_dresser_frozen
#print axioms witness_stockWaste_closed
#print axioms lock_zone_residency
#print axioms origin_foundedCover_rungSqueeze
#print axioms origin_foundedCover_belowPull
#print axioms origin_foundedCover_pollutesCrash
#print axioms ForkKit.fork_nextUpExile_crash
#print axioms exodus_seating_census
#print axioms forkState_rankDrop_locked
#print axioms forkState_family_rankFloor
#print axioms forkState_family_pairClass
