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

/-- The build position of a card in a list (the copy of the banked
private `posOf` of `Orig/Dominance.lean` / `Orig/CrossFamily.lean`). -/
private def lock_posOf (x : Card) : List Card → Nat
  | [] => 0
  | y :: t => if y = x then 0 else lock_posOf x t + 1

private theorem lock_posOf_take_lt (x : Card) : ∀ (n : Nat) (l : List Card),
    x ∈ l.take n → lock_posOf x l < n := by
  intro n
  induction n with
  | zero =>
      intro l hmem
      rw [show (List.take 0 l : List Card) = [] from rfl] at hmem
      exact absurd hmem (by simp)
  | succ m ih =>
      intro l hmem
      cases l with
      | nil =>
          rw [show (List.take (m + 1) ([] : List Card)) = ([] : List Card) from rfl] at hmem
          exact absurd hmem (by simp)
      | cons a t =>
          have hmem' : x ∈ a :: t.take m := hmem
          rcases List.mem_cons.mp hmem' with heq | htl
          · rw [heq]
            have hp : lock_posOf a (a :: t) = 0 := by
              show (if a = a then 0 else lock_posOf a t + 1) = 0
              rw [if_pos rfl]
            rw [hp]
            omega
          · have hpos := ih t htl
            by_cases hax : a = x
            · rw [hax]
              have hp : lock_posOf x (x :: t) = 0 := by
                show (if x = x then 0 else lock_posOf x t + 1) = 0
                rw [if_pos rfl]
              rw [hp]
              omega
            · have hp : lock_posOf x (a :: t) = if a = x then 0 else lock_posOf x t + 1 :=
                rfl
              rw [hp, if_neg hax]
              omega

/-- The build order is the rank order (the copy of the banked private
`posOf_upCards`). -/
private theorem lock_posOf_upCards (s : Suit) (r : Rank) :
    lock_posOf (Card.mk s r) (Suit.upCards s) = r.toIdx := by
  cases s <;> cases r <;> rfl

/-- **THE FOUNDED-MEMBERSHIP BRIDGE, converse half** — a card on its
own suit's foundation sits strictly below the rung: the founded
prefix is the build order's take, so the card's build position (its
rank index) is bounded by the take length, and the build position IS
the rank index (the per-file copy of
`Orig/CrossFamily.lean`'s private `xfam_mem_found_rank_lt`, rebuilt
off the local kernel position kit). -/
private theorem lock_found_rank_lt {st : State} (hwf : st.WF) {c : Card}
    (hmem : c ∈ st.found c.suit) : c.rank.toIdx < rungAt st c.suit := by
  rcases c with ⟨s, r⟩
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  have hmem' : Card.mk s r ∈ (Suit.upCards s).take n := by
    rw [← hn]
    exact hmem
  have hpos := lock_posOf_take_lt (Card.mk s r) n (Suit.upCards s) hmem'
  rw [lock_posOf_upCards s r] at hpos
  have hr13 : r.toIdx < 13 := Rank.toIdx_lt r
  have hlen : (st.found s).length = min n (Suit.upCards s).length := by
    rw [hn, List.length_take]
  show r.toIdx < (st.found s).length
  rw [hlen, Suit.upCards_length]
  omega

/-- An element at position `i` belongs to the first `n` entries of the
list (the copy of `Orig/CanV3.lean`'s private `v3GetInTake`,
`Orig/PairConfine.lean`'s private `conf_get_in_take`). -/
private theorem lock_get_in_take : ∀ {α : Type} (l : List α) (n i : Nat)
    (hl : i < l.length) (hn : i < n), l.get ⟨i, hl⟩ ∈ l.take n := by
  intro α l n i hl hn
  induction n generalizing l i hl with
  | zero => exact absurd hn (by omega)
  | succ m ih =>
      cases l with
      | nil => exact absurd hl (by simp)
      | cons a t =>
          cases i with
          | zero =>
              show a ∈ a :: t.take m
              exact List.mem_cons.2 (Or.inl rfl)
          | succ i' =>
              simp only [List.length_cons] at hl
              refine List.mem_cons_of_mem a (ih t i' (by omega) (by omega))

/-- A card sits at its own build index in its suit's foundation
order (the copy of the banked private `upCards_get`). -/
private theorem lock_upCards_get (z : Card)
    (h : z.rank.toIdx < z.suit.upCards.length) :
    z.suit.upCards.get ⟨z.rank.toIdx, h⟩ = z := by
  rcases z with ⟨zs, zr⟩
  cases zr <;> rfl

/-- **THE FOUNDED-BRIDGE, forward half** — a suit rung strictly above a
card's rank index has already founded it (the copy of
`Orig/PairConfine.lean`'s private `conf_mem_found_of_rung`). -/
private theorem lock_found_of_rung {st : State} (hwf : st.WF) {c : Card}
    (hlt : c.rank.toIdx < rungAt st c.suit) : c ∈ st.found c.suit := by
  have hpre := rung_found_prefix st hwf c.suit
  have h13 : c.suit.upCards.length = 13 := Suit.upCards_length c.suit
  have hget : c.suit.upCards.get ⟨c.rank.toIdx, by
      rw [h13]; exact Rank.toIdx_lt c.rank⟩ = c :=
    lock_upCards_get c (by rw [h13]; exact Rank.toIdx_lt c.rank)
  have hmem0 : c.suit.upCards.get ⟨c.rank.toIdx, by
      rw [h13]; exact Rank.toIdx_lt c.rank⟩ ∈
      c.suit.upCards.take (rungAt st c.suit) :=
    lock_get_in_take c.suit.upCards (rungAt st c.suit) c.rank.toIdx
      (show c.rank.toIdx < c.suit.upCards.length by
        rw [h13]; exact Rank.toIdx_lt c.rank) hlt
  rw [hget] at hmem0
  have hmem : c ∈ c.suit.upCards.take (rungAt st c.suit) := hmem0
  rwa [← hpre] at hmem

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
  · exact absurd (lock_found_of_rung hwf h) hnot

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

/-- **The terminal saturation gate** (the §3.5 pollution crash's closing
move, landed zero-sorry): the lower fork's pair select admits no third
live card — every `CanRaiseS` witness at the fork state must be `y` or
`y.twin`.  The terminal dragged low card enters here, certified off-pair
by the rank/color ledger, and the crash closes. -/
private theorem pollutesCrash_saturation {st : State} {y c : Card}
    (hy : ForkWitness st y) (hcy : c ≠ y) (hct : c ≠ y.twin)
    (hcS : CanRaiseS st c) : False := by
  obtain ⟨hiff, -⟩ := hy
  rcases (hiff c).mpr hcS with h1 | h2
  · exact hcy h1
  · exact hct h2

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

/-- **The third live card minted at the landing epoch** (route item 1,
zero-sorry): the pulled card tops its own seat pile over the landlord
`zt` one rank up, so its `CanRaise` now-grade fires outright — the seat
intact, the face-up remainder nonempty under the pop. -/
private theorem pollutesCrash_landing_canRaiseS {v : State} {w zt : Card}
    {kk : Anchor} {bs : List Card}
    (hshape : (v.piles kk).faceUp = bs ++ [zt, w])
    (hhold : v.pileOfTop w = some kk)
    (hrung : rungAt v w.suit = w.rank.toIdx) :
    CanRaiseS v w := by
  refine CanRaiseS.now w ⟨pollutesCrash_landing_live hrung, kk, hhold, ?_⟩
  rw [hshape]
  cases bs with
  | nil =>
      left
      have hchop : chop ([] ++ [zt, w]) = [zt] := rfl
      rw [hchop]
      simp
  | cons a t =>
      left
      cases t with
      | nil =>
          have hchop : chop ([a] ++ [zt, w]) = [a, zt] := rfl
          rw [hchop]
          simp
      | cons z t' =>
          show chop (a :: z :: (t' ++ [zt, w])) ≠ []
          exact List.cons_ne_nil a _

/-- **The minted card's off-pair certificates** (zero-sorry): the
pulled card sits strictly below the cover's own rank index, hence
strictly below the fork rank — it can be neither fork member (ranks
decide; the twin carries the same rank). -/
private theorem pollutesCrash_w_offPair {w d y : Card}
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hwlw : w.rank.toIdx + 1 ≤ d.rank.toIdx) :
    w ≠ y ∧ w ≠ y.twin := by
  constructor
  · intro hcon
    have hidx : w.rank.toIdx = y.rank.toIdx := by rw [← hcon]
    omega
  · intro hcon
    have hidx : w.rank.toIdx = y.twin.rank.toIdx := by rw [← hcon]
    rw [Card.twin_rank] at hidx
    omega

/-- **The pre-leg π pull debt** (zero-sorry): the mid-leg bracket
`rungAt u w.suit = w.rank.toIdx + 1`, priced against the origin rung
already standing past the cover's index, prices the π-segment's `d`-suit
pulls by the journey census — the leg's own drag already lowered the
rung to one full index below the cover's, the staircase's first paid
installment. -/
private theorem pollutesCrash_pi_pullDebt {st₁ u : State} {π : List Move}
    {w d : Card} (hw : w.suit = d.suit)
    (hshpi : ShufflePlayW st₁ π u)
    (hu1 : rungAt u w.suit = w.rank.toIdx + 1)
    (hsq1 : d.rank.toIdx + 1 ≤ rungAt st₁ d.suit)
    (hrk : w.rank.toIdx + 1 ≤ d.rank.toIdx) :
    raisesOf π d.suit + (d.rank.toIdx - w.rank.toIdx) ≤ pullsOf π d.suit := by
  have hc := witness_rung_census hshpi d.suit
  rw [hw] at hu1
  omega

/-- **Stage 2's pair-liveness read** (zero-sorry): the fork's pair select
hands both pair members their `CanRaiseS` witnesses at the fork state
— the two live cards whose saturation the terminal third card crashes. -/
private theorem pollutesCrash_pairLive {st : State} {y : Card}
    (hy : ForkWitness st y) :
    CanRaiseS st y ∧ CanRaiseS st y.twin := by
  obtain ⟨hiff, -⟩ := hy
  exact ⟨(hiff y).mp (Or.inl rfl), (hiff y.twin).mp (Or.inr rfl)⟩

/-- **Stage 2's parked read** (zero-sorry, standalone): a face-up parked
card whose `nextUp` reads false sits off its own index — the cover's
rung cannot stand exactly at the card's rank (the squeeze's `hne`
read, extracted for `rhoLeg`'s confinement stage). -/
private theorem pollutesCrash_parked_pin {st : State} {d : Card}
    (hnext : st.nextUp d = false) :
    d.rank.toIdx ≠ rungAt st d.suit := by
  intro hcon
  rw [State.nextUp] at hnext
  have hf : st.foundHeight d.suit = rungAt st d.suit := rfl
  rw [hcon, hf] at hnext
  exact absurd hnext (by simp)

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

/-- The grade read of a `CanRaiseS` license (zero-sorry): every license
is either the immediate now-grade, or a reversible tabToTab slide chain
with its successor license one level down — the case split for the
per-mover transport, kept in a bare context. -/
private theorem pollutesCrash_canRaiseS_cases {st : State} {c : Card}
    (h : CanRaiseS st c) :
    CanRaise st c ∨
      (∃ st', ∃ d b, st.step (Move.tabToTab d b) = some st' ∧
        reversibleAtW st (Move.tabToTab d b) ∧ CanRaiseS st' c) := by
  induction h with
  | @now _stp _cp hnow => exact Or.inl hnow
  | @via _stp _st2 _cp hl hsub =>
      obtain ⟨d, b, hA, hB⟩ := hl
      exact Or.inr ⟨_, d, b, hA, hB, hsub⟩

/-- The none/some constructor clash at explicit type (zero-sorry; a tiny
row lemma so the mover cells avoid open-variable decide). -/
private theorem pollutesCrash_none_ne_some (z : Card) :
    (none : Option Card) = some z → False := by
  intro h
  nomatch h

/-- **The draw-leg now-grade carrier** (Stage 1 draw depth, zero-sorry):
a fired draw keeps the found and piles boards verbatim, so the light
kit (nextUp + seat + chop row) passes through wholesale — the
continuation runs at the drawn state. -/
private theorem pollutesCrash_rhoDraw_now {vp s₁ : State} {m : Card}
    (hd : vp.stepDraw = some s₁)
    (hn : vp.nextUp m = true)
    (hshape : ∃ ke se, (vp.piles ke).faceUp = se ++ [m] ∧
      vp.pileOfTop m = some ke ∧
      (chop (vp.piles ke).faceUp ≠ [] ∨
        ((vp.piles ke).hidden = [] ∧ m.rank = Rank.king))) :
    s₁.nextUp m = true ∧
      ∃ ke se, (s₁.piles ke).faceUp = se ++ [m] ∧
        s₁.pileOfTop m = some ke ∧
        (chop (s₁.piles ke).faceUp ≠ [] ∨
          ((s₁.piles ke).hidden = [] ∧ m.rank = Rank.king)) := by
  have hfd : s₁.found = vp.found := stepDraw_found hd
  have hpl : s₁.piles = vp.piles := stepDraw_piles hd
  obtain ⟨k2, se2, hshape2, hhold2, hcond2⟩ := hshape
  refine ⟨(nextUp_congr m hfd).trans hn, k2, se2, ?_, ?_, ?_⟩
  · rw [hpl]
    exact hshape2
  · rw [pollutesCrash_pileOfTop_congr m hpl]
    exact hhold2
  · rw [hpl]
    exact hcond2

/-- **ITEM-2's first survival half (zero-sorry): the mint's own
nextUp license survives a stranger's pull** — the pop's `setFound`
write touches only the popped card's own suit row, so the mint's suit
row, and with it the mint's nextUp read, re-reads verbatim at the
pop's landing. -/
private theorem pollutesCrash_rhoPull_nextUpKeep {vp s₁ : State}
    {w c : Card} {b : Base}
    (hstep : State.step vp (Move.foundToTab c b) = some s₁)
    (hnsc : w.suit ≠ c.suit)
    (hn : vp.nextUp w = true) :
    s₁.nextUp w = true := by
  obtain ⟨_c0, _htop0, _hceq, _hcp, hs⟩ := step_foundToTab_inv hstep
  have hfd : s₁.found w.suit = vp.found w.suit := by
    rw [hs, putCard_found]
    show (if w.suit = c.suit then chop (vp.found c.suit)
        else vp.found w.suit) = vp.found w.suit
    rw [if_neg hnsc]
  show decide (w.rank.toIdx = (s₁.found w.suit).length) = true
  rw [hfd]
  exact hn

/-- **ITEM-2's second survival half (zero-sorry): the mint's seat
shape survives a pull onto a different anchor** — the pop's `putCard`
write appends to the host anchor's face-up run alone, so the seat
pile's shape re-reads verbatim at the pop's landing (the light-kit
list pass-through). -/
private theorem pollutesCrash_rhoPull_shapeKeep {vp s₁ : State}
    {c : Card} {a k' : Anchor} {L : List Card}
    (hstep : State.step vp (Move.foundToTab c (Sum.inl a)) = some s₁)
    (hkna : k' ≠ a)
    (hshape : (vp.piles k').faceUp = L) :
    (s₁.piles k').faceUp = L := by
  obtain ⟨_c0, _htop0, _hceq, _hcp, hs⟩ := step_foundToTab_inv hstep
  have hpilk : s₁.piles k' = vp.piles k' := by
    rw [hs, putCard_eq_inl, setPile_piles]
    simp only []
    rw [if_neg hkna]
    rfl
  rw [hpilk]
  exact hshape

/-- **The per-anchor off-row (zero-sorrow):** under WF the card lives
in exactly one pile, so every other anchor's top misses it — the
ForkStateS `hnoTtwin` read, standalone, feeding the seat-preservation
column's `hoff` premise. -/
private theorem pollutesCrash_pileOfTop_offWF {st : State} {z : Card}
    {a : Anchor} (hwf : st.WF) (htop : st.pileOfTop z = some a) :
    ∀ y : Anchor, y ≠ a → st.topOf y ≠ some z := by
  intro y hy hcon
  exact (mem_faceUp_unique hwf (Pile.mem_of_top (pileOfTop_top htop).2) y
    hy).1 (Pile.mem_of_top hcon)

/-- **ITEM-2's seat-preservation read (zero-sorrow): the `firstWhere`
anchoring past the host-write** — the canonical ForkStateS `hmidx`
pattern in the pull-leg form: the pop writes exactly one off-seat
anchor (its new top is the popped card, not the mint), the mint's
seat anchor keeps its top, and no other anchor tops the mint — so the
mint's `pileOfTop` reads the same seat at the pop's landing. -/
private theorem pollutesCrash_rhoPull_pileOfTop_keep {vp s₁ : State}
    {w c : Card} {a k' : Anchor}
    (hstep : State.step vp (Move.foundToTab c (Sum.inl a)) = some s₁)
    (hkna : k' ≠ a)
    (hwnc : w ≠ c)
    (hhold : vp.pileOfTop w = some k')
    (hoff : ∀ y : Anchor, y ≠ k' → vp.topOf y ≠ some w) :
    s₁.pileOfTop w = some k' := by
  obtain ⟨_c0, _htop0, _hceq, _hcp, hs⟩ := step_foundToTab_inv hstep
  have hpilk : s₁.piles k' = vp.piles k' := by
    rw [hs, putCard_eq_inl, setPile_piles]
    simp only []
    rw [if_neg hkna]
    rfl
  show (firstWhere (fun a₂ =>
      decide (s₁.topOf a₂ = some w)) Anchor.all) = some k'
  refine firstWhere_find (Anchor.mem_all k') ?_ ?_
  · show decide (s₁.topOf k' = some w) = true
    have hk : s₁.topOf k' = vp.topOf k' := by
      show (s₁.piles k').top = (vp.piles k').top
      rw [hpilk]
    rw [hk]
    exact decide_eq_true (pileOfTop_top hhold).2
  · intro y _hy hyne
    show decide (s₁.topOf y = some w) = false
    by_cases hya : y = a
    · have hnewtop : s₁.topOf a ≠ some w := by
        show (s₁.piles a).top ≠ some w
        rw [hs, putCard_eq_inl, setPile_piles_self]
        show lastOf ([] ++ [c]) ≠ some w
        intro hcon
        have hsnoc : lastOf ([] ++ [c]) = some c := lastOf_snoc
        exact hwnc (Option.some.inj (hcon.symm.trans hsnoc))
      rw [hya]
      exact decide_false_of_not hnewtop
    · have hylk : s₁.piles y = vp.piles y := by
        rw [hs, putCard_eq_inl, setPile_piles]
        simp only []
        rw [if_neg hya]
        rfl
      have hytop : s₁.topOf y = vp.topOf y := by
        show (s₁.piles y).top = (vp.piles y).top
        rw [hylk]
      exact decide_false_of_not (fun hcon => hoff y hyne
        (hytop.symm.trans hcon))

/-- **The seat-shape survival, `inr` append form (zero-sorrow):** the
pop lands at a card-direct base (`Sum.inr z`) whose host pile is
another pile than the mint's seat — the append write touches the host
alone, so the seat shape re-reads verbatim at the pop's landing. -/
private theorem pollutesCrash_rhoPull_shapeKeep_inr {s s' : State}
    {z c : Card} {k k' : Anchor} {L : List Card}
    (hstep : State.step s (Move.foundToTab c (Sum.inr z)) = some s')
    (hhost : (s.setFound c.suit (chop (s.found c.suit))).pileOfTop z
      = some k')
    (hkn : k ≠ k')
    (hshape : (s.piles k).faceUp = L) :
    (s'.piles k).faceUp = L := by
  obtain ⟨_c0, _htop0, _hceq, _hcp, hs⟩ := step_foundToTab_inv hstep
  have hpilk : s'.piles k = s.piles k := by
    rw [hs]
    rw [show (s.setFound c.suit (chop (s.found c.suit))).putCard c
          (Sum.inr z)
        = (s.setFound c.suit (chop (s.found c.suit))).setPile k'
          { (s.setFound c.suit (chop (s.found c.suit))).piles k' with
            faceUp :=
              ((s.setFound c.suit (chop (s.found c.suit))).piles k').faceUp
              ++ [c] }
        from by simp only [State.putCard, hhost], setPile_piles]
    simp only []
    rw [if_neg hkn]
    rfl
  rw [hpilk]
  exact hshape

/-- The inr-pop's full-pile lens for an off-host landing (zero-sorry):
the pop's `putCard` write replaces the host anchor's pile alone, so
every other pile — including the mint's seat — reads verbatim (both
fields). -/
private theorem pollutesCrash_rhoPull_pilesKeep_inr {s s' : State}
    {c z : Card} {k k' : Anchor} (hkn : k ≠ k')
    (hstep : State.step s (Move.foundToTab c (Sum.inr z)) = some s')
    (hhost : (s.setFound c.suit (chop (s.found c.suit))).pileOfTop z
      = some k') :
    s'.piles k = s.piles k := by
  obtain ⟨_c₀, _htop0, _hceq, _hcp, hs⟩ := step_foundToTab_inv hstep
  rw [hs]
  rw [show (s.setFound c.suit (chop (s.found c.suit))).putCard c (Sum.inr z)
      = (s.setFound c.suit (chop (s.found c.suit))).setPile k'
        { (s.setFound c.suit (chop (s.found c.suit))).piles k' with
            faceUp := ((s.setFound c.suit (chop (s.found c.suit))).piles k').faceUp
              ++ [c] }
    from by simp only [State.putCard, hhost]]
  rw [setPile_piles]
  show (if k = k' then
      { (s.setFound c.suit (chop (s.found c.suit))).piles k' with
          faceUp := ((s.setFound c.suit (chop (s.found c.suit))).piles k').faceUp
            ++ [c] }
    else (s.setFound c.suit (chop (s.found c.suit))).piles k) = s.piles k
  rw [if_neg hkn, setFound_piles]

/-- The inl-pop's full-pile lens for the off-host king landing
(zero-sorry): the pop's `putCard` write empties the landing anchor's
pile alone, so every other pile reads verbatim (both fields). -/
private theorem pollutesCrash_rhoPull_pilesKeep_inl {s s' : State}
    {c : Card} {a k : Anchor} (hkna : k ≠ a)
    (hstep : State.step s (Move.foundToTab c (Sum.inl a)) = some s') :
    s'.piles k = s.piles k := by
  obtain ⟨_c₀, _htop0, _hceq, _hcp, hs⟩ := step_foundToTab_inv hstep
  rw [hs, putCard_eq_inl, setPile_piles]
  show (if k = a then (⟨[], [c]⟩ : Pile)
      else (s.setFound c.suit (chop (s.found c.suit))).piles k) = s.piles k
  rw [if_neg hkna, setFound_piles]

/-- **The seat-preservation read, `inr` append form (zero-sorrow):**
the `firstWhere` anchoring past an off-seat append host — the host
pile's new top is the popped card, never the mint; every untouched
pile keeps its top (the `hoff` column). -/
private theorem pollutesCrash_rhoPull_pileOfTop_keep_inr {s s' : State}
    {w z c : Card} {k k' : Anchor}
    (hstep : State.step s (Move.foundToTab c (Sum.inr z)) = some s')
    (hhost : (s.setFound c.suit (chop (s.found c.suit))).pileOfTop z
      = some k')
    (hkn : k ≠ k')
    (hwnc : w ≠ c)
    (hhold : s.pileOfTop w = some k)
    (hoff : ∀ y : Anchor, y ≠ k → s.topOf y ≠ some w) :
    s'.pileOfTop w = some k := by
  obtain ⟨_c0, _htop0, _hceq, _hcp, hs⟩ := step_foundToTab_inv hstep
  have hpilk : s'.piles k = s.piles k := by
    rw [hs]
    rw [show (s.setFound c.suit (chop (s.found c.suit))).putCard c
          (Sum.inr z)
        = (s.setFound c.suit (chop (s.found c.suit))).setPile k'
          { (s.setFound c.suit (chop (s.found c.suit))).piles k' with
            faceUp :=
              ((s.setFound c.suit (chop (s.found c.suit))).piles k').faceUp
              ++ [c] }
        from by simp only [State.putCard, hhost], setPile_piles]
    simp only []
    rw [if_neg hkn]
    rfl
  show (firstWhere (fun a₂ =>
      decide (s'.topOf a₂ = some w)) Anchor.all) = some k
  refine firstWhere_find (Anchor.mem_all k) ?_ ?_
  · show decide (s'.topOf k = some w) = true
    have hk : s'.topOf k = s.topOf k := by
      show (s'.piles k).top = (s.piles k).top
      rw [hpilk]
    rw [hk]
    exact decide_eq_true (pileOfTop_top hhold).2
  · intro y _hy hyne
    show decide (s'.topOf y = some w) = false
    by_cases hyk : y = k'
    · have hpilhost : s'.piles k'
            = { (s.setFound c.suit (chop (s.found c.suit))).piles k' with
                faceUp :=
                  ((s.setFound c.suit (chop (s.found c.suit))).piles k').faceUp
                  ++ [c] } := by
        rw [hs, show (s.setFound c.suit (chop (s.found c.suit))).putCard c
              (Sum.inr z)
            = (s.setFound c.suit (chop (s.found c.suit))).setPile k'
              { (s.setFound c.suit (chop (s.found c.suit))).piles k' with
                faceUp :=
                  ((s.setFound c.suit (chop (s.found c.suit))).piles k').faceUp
                  ++ [c] }
            from by simp only [State.putCard, hhost], setPile_piles_self]
      have hnewtop : s'.topOf k' ≠ some w := by
        show (s'.piles k').top ≠ some w
        rw [hpilhost]
        show lastOf ((s.piles k').faceUp ++ [c]) ≠ some w
        intro hcon
        have hsnoc : lastOf ((s.piles k').faceUp ++ [c]) = some c :=
          lastOf_snoc
        exact hwnc (Option.some.inj (hcon.symm.trans hsnoc))
      rw [hyk]
      exact decide_false_of_not hnewtop
    · have hylk : s'.piles y = s.piles y := by
        rw [hs]
        rw [show (s.setFound c.suit (chop (s.found c.suit))).putCard c
              (Sum.inr z)
            = (s.setFound c.suit (chop (s.found c.suit))).setPile k'
              { (s.setFound c.suit (chop (s.found c.suit))).piles k' with
                faceUp :=
                  ((s.setFound c.suit (chop (s.found c.suit))).piles k').faceUp
                  ++ [c] }
            from by simp only [State.putCard, hhost], setPile_piles]
        simp only []
        rw [if_neg hyk]
        rfl
      have hytop : s'.topOf y = s.topOf y := by
        show (s'.piles y).top = (s.piles y).top
        rw [hylk]
      exact decide_false_of_not (fun hcon => hoff y hyne
        (hytop.symm.trans hcon))

/-- The slide's found-keep row (the copy of `Orig/ForkStateS.lean`'s
private `slide_foundEq`): a fired `tabToTab` writes no foundation —
the base row of the movers' license regeneration. -/
private theorem pollutesCrash_slide_foundEq {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some st') :
    st'.found = st.found := by
  obtain ⟨_a, _hh, _hcp, _fr, hs⟩ := step_tabToTab_inv hstep
  rw [hs, putRun_found, setPile_found]

/-- **The license chain's root read** (zero-sorry): every `CanRaiseS`
license reads `nextUp` at its own root — the `via` mantle's slides
write no foundation, so the rung is invariant along the chain and the
now-grade's read at the chain's end re-reads at the root.  This
collapses the via-grade transport problem: every leg that preserves
the mint's suit's found row and the mint's seat re-arms the carry's
license as a fresh `now`-grade witness. -/
private theorem pollutesCrash_canRaiseS_nextUp {st : State} {w : Card}
    (hS : CanRaiseS st w) : st.nextUp w = true := by
  induction hS with
  | now _ hnow => exact hnow.1
  | @via st₀ st₂ c₀ hl _h ih =>
      obtain ⟨d, b, hstep, _hrev⟩ := hl
      obtain ⟨_a, _hh, _hcp, _fr, hs⟩ := step_tabToTab_inv hstep
      have hf : st₂.found = st₀.found := by rw [hs, putRun_found, setPile_found]
      show decide (c₀.rank.toIdx = (st₀.found c₀.suit).length) = true
      rw [← hf]
      exact ih

/-- The slide's mid-state host transplant (zero-sorry): removing the
run from the departure pile `a` never unmoves a card `z` that tops a
DIFFERENT pile at the firing state — the departure's new top is either
a face-up card below the raised run or a revealed hidden card, and WF
uniqueness keeps `z` out of both — so the top search still answers
`k₀` in the mid-state. -/
private theorem pollutesCrash_slide_hostKeep {st : State} (hwf : st.WF)
    {c z : Card} {a k₀ : Anchor} (hkna : k₀ ≠ a)
    (hhold₀ : st.pileOfTop z = some k₀)
    (hzf : z ∉ (st.piles a).faceUp) (hzh : z ∉ (st.piles a).hidden) :
    (st.setPile a (Pile.afterRunRemoved (st.piles a)
      (below c (st.piles a).faceUp))).pileOfTop z = some k₀ := by
  have hmidk₀ : ∀ y : Anchor, y ≠ a →
      (st.setPile a (Pile.afterRunRemoved (st.piles a)
        (below c (st.piles a).faceUp))).piles y = st.piles y :=
    fun y hy => setPile_afterRunRemoved_piles_ne st a c y hy
  have hmidanoz : (Pile.afterRunRemoved (st.piles a)
      (below c (st.piles a).faceUp)).top ≠ some z := by
    cases hb : below c (st.piles a).faceUp with
    | nil =>
        cases hh : (st.piles a).hidden with
        | nil =>
            intro hcon
            have hmem : z ∈ ([] : List Card) := by
              have hmem1 := Pile.mem_of_top hcon
              rw [lock_afterRunRemoved_bare hh] at hmem1
              exact hmem1
            exact absurd hmem (by simp)
        | cons g gs =>
            intro hcon
            have hface : (Pile.afterRunRemoved (st.piles a)
                ([] : List Card)).faceUp = [g] := by
              simp only [Pile.afterRunRemoved, Pile.revealTop, hh,
                List.nil_append]
            have hmem : z ∈ (Pile.afterRunRemoved (st.piles a)
                ([] : List Card)).faceUp := Pile.mem_of_top hcon
            rw [hface] at hmem
            have hzg : z = g := List.mem_singleton.mp hmem
            exact hzh (by rw [hzg, hh]; exact List.mem_cons_self ..)
    | cons u us =>
        intro htop
        have hmem : z ∈ u :: us :=
          lastOf_mem (show lastOf (u :: us) = some z from htop)
        rw [← hb] at hmem
        exact hzf (mem_below _ hmem)
  show (firstWhere (fun a₂ =>
      decide ((st.setPile a (Pile.afterRunRemoved (st.piles a)
        (below c (st.piles a).faceUp))).topOf a₂ = some z)) Anchor.all) = some k₀
  refine firstWhere_find (Anchor.mem_all k₀) ?_ ?_
  · show decide (((st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp))).piles k₀).top = some z) = true
    rw [hmidk₀ k₀ hkna]
    exact decide_eq_true (pileOfTop_top hhold₀).2
  · intro y _hy hyne
    show decide (((st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp))).piles y).top = some z) = false
    by_cases hya : y = a
    · rw [hya, setPile_afterRunRemoved_piles_self st a c]
      exact decide_false_of_not hmidanoz
    · have hoff := pollutesCrash_pileOfTop_offWF hwf hhold₀
      rw [hmidk₀ y hya]
      exact decide_false_of_not (hoff y hyne)

/-- The mint's seat-menu chop read (zero-sorry): the seat tail with
the landlord directly under the mint never chops to nothing. -/
private theorem pollutesCrash_chop_seatTail {zt w : Card} :
    ∀ X : List Card, chop (X ++ [zt, w]) ≠ [] := by
  intro X
  cases X with
  | nil =>
      show chop ([] ++ [zt, w]) ≠ []
      simp [chop]
  | cons a t =>
      cases t with
      | nil =>
          show chop ([a] ++ [zt, w]) ≠ []
          simp [chop]
      | cons u us =>
          show chop ((a :: u :: us) ++ [zt, w]) ≠ []
          exact List.cons_ne_nil a _

/-- The mint-carrying run's tail split (zero-sorry): a run headed at
`c` over the mint's own seat shape `se ++ [zt, w]` with `c ≠ w` ends
exactly at the `[zt, w]` tail — the seat conjunct's re-pairing read
for the mint-travel slides. -/
private theorem pollutesCrash_fromCard_seatTail {c zt w : Card} (hcw : c ≠ w) :
    ∀ se : List Card, (c ∈ se ∨ c = zt) →
      ∃ RR, fromCard c (se ++ [zt, w]) = RR ++ [zt, w] := by
  intro se
  induction se with
  | nil =>
      intro hmem
      rcases hmem with h | h
      · exact absurd h (by simp)
      · refine ⟨[], ?_⟩
        show fromCard c [zt, w] = [zt, w]
        rw [h, fromCard_cons_self]
  | cons u us ih =>
      intro hmem
      by_cases huc : u = c
      · refine ⟨u :: us, ?_⟩
        show fromCard c (u :: (us ++ [zt, w])) = (u :: us) ++ [zt, w]
        rw [huc, fromCard_cons_self]
        rfl
      · have hrec : c ∈ us ∨ c = zt :=
          Or.elim hmem
            (fun h1 => Or.elim (List.mem_cons.mp h1)
              (fun h2' => absurd h2' (fun hcon => huc hcon.symm))
              (fun h3 => Or.inl h3))
            (fun h2 => Or.inr h2)
        obtain ⟨RR, hRR⟩ := ih hrec
        refine ⟨RR, ?_⟩
        show fromCard c (u :: (us ++ [zt, w])) = RR ++ [zt, w]
        rw [fromCard_cons_ne (us ++ [zt, w]) huc]
        exact hRR

/-- The seat tail's top read (zero-sorry): a face-up list ending at
`[zt, w]` tops the mint. -/
private theorem pollutesCrash_top_seatTail {zt w : Card} :
    ∀ X : List Card, lastOf (X ++ [zt, w]) = some w := by
  intro X
  induction X with
  | nil => rfl
  | cons u us ih =>
      show lastOf (u :: (us ++ [zt, w])) = some w
      cases us with
      | nil => rfl
      | cons v vs => exact ih

/-- The below read at the list's own last occurrence (zero-sorry):
everything strictly below `c` in `X ++ [c]`, when nothing of `X` is
`c` itself. -/
private theorem pollutesCrash_below_lastOf {c : Card} :
    ∀ X : List Card, c ∉ X → below c (X ++ [c]) = X := by
  intro X
  induction X with
  | nil => intro _; exact below_cons_self c []
  | cons u us ih =>
      intro hmem
      have huc : u ≠ c := by
        intro hcon
        exact hmem (List.mem_cons.2 (Or.inl hcon.symm))
      show below c (u :: (us ++ [c])) = u :: us
      rw [lock_below_cons_ne huc]
      exact congrArg (u :: ·)
        (ih (fun hcon => hmem (List.mem_cons.2 (Or.inr hcon))))

/-- **The founded top's rank read** (zero-sorry): the foundation's own
top card of a suit sits exactly one under that suit's rung — the
founded-prefix discipline's last-element read (over
`wf_found_chop_toIdx` + the chop-length arithmetic).  Every `foundToTab`
pops the card one below the firing rung: this is the popped-bracket
input of `pollutesCrash_pull_bracket`, and the reason the wash-back's
same-suit guard names the mint. -/
private theorem pollutesCrash_foundTop_rank {st : State} (hwf : st.WF)
    {c : Card} (htop : st.foundTop c.suit = some c) :
    c.rank.toIdx + 1 = rungAt st c.suit := by
  have hchop := wf_found_chop_toIdx hwf htop
  have hne : st.found c.suit ≠ [] := by
    intro hcon
    rw [show st.foundTop c.suit = lastOf (st.found c.suit) from rfl, hcon] at htop
    exact absurd htop (by simp [lastOf])
  have hsnoc : (st.found c.suit).length
      = (chop (st.found c.suit)).length + 1 :=
    (pollutesCrash_chop_len _ hne).symm
  show c.rank.toIdx + 1 = (st.found c.suit).length
  omega

/-- **The mint's king ban** (zero-sorry): the dragged mint is no king —
the cover `d` sits strictly under the fork's rank, so the mint's index
is at least three under it, far from the king's. -/
private theorem pollutesCrash_w_notKing {w d y : Card}
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hrk : w.rank.toIdx + 1 ≤ d.rank.toIdx) :
    w.rank ≠ Rank.king := by
  intro hcon
  have hy12 : y.rank.toIdx < 13 := Rank.toIdx_lt y.rank
  have hk12 : Rank.king.toIdx = 12 := rfl
  rw [hcon, hk12] at hrk
  omega

/-- The mint's off-family color (zero-sorry): the mint sits directly
on its landlord `zt` (the run discipline), and the landlord carries the
fork family's color, so the mint carries the opposite family — every
cover that lands lawfully on the mint is family-colored by the fit's
color clause alone. -/
private theorem pollutesCrash_mintOffColor {st : State} (hwf : st.WF)
    {w zt y : Card} {k : Anchor} {se : List Card}
    (hshape : (st.piles k).faceUp = se ++ [zt, w])
    (hzcol : zt.suit.color = y.suit.color) :
    w.suit.color ≠ y.suit.color := by
  have hok : runOK (se ++ [zt, w]) = true := by
    rw [← hshape]
    exact hwf.runOK_of k
  obtain ⟨_hrk, hcol⟩ := (canSitOn_eq w zt).mp
    (lock_runOK_adjacent zt w se [] hok)
  rw [hzcol] at hcol
  exact hcol

/-- A snoc-nodup membership bar (the per-file copy of the banked
`Orig/ConjugateProof.lean` private row): a list that stays nodup under
the snoc never mentions its tip inside its front. -/
private theorem pollutesCrash_nodup_snocNotmem {bs : List Card} {d : Card}
    (hnd : (bs ++ [d]).Nodup) : d ∉ bs := by
  revert hnd
  induction bs with
  | nil => intro _hnd hcon; exact absurd hcon (by simp)
  | cons u us ih =>
      intro hnd hmem
      have hnd' : (u :: (us ++ [d])).Nodup := hnd
      rw [List.nodup_cons] at hnd'
      rcases List.mem_cons.mp hmem with hu | hrest
      · rw [hu] at hnd'
        exact absurd (List.mem_append.2
          (Or.inr (List.mem_singleton.mpr rfl))) hnd'.1
      · exact ih hnd'.2 hrest

/-- The below/fromCard split (zero-sorry): the below read is the
prefix before the first occurrence, and the fromCard run the suffix
from it — together they rebuild the list. -/
private theorem pollutesCrash_below_fromCard_split {c : Card} :
    ∀ l : List Card, below c l ++ fromCard c l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases hxc : x = c
      · have hbl : below c (x :: xs) = [] := by
          rw [hxc]
          exact below_cons_self c xs
        have hfc : fromCard c (x :: xs) = x :: xs := by
          rw [hxc]
          exact fromCard_cons_self c xs
        rw [hbl, hfc]
        rfl
      · rw [lock_below_cons_ne hxc, fromCard_cons_ne xs hxc]
        exact congrArg (x :: ·) ih

/-- **The interior-top ban** (zero-sorry): the under-card `z` of a
seated `[.., z, c]` tail in one pile tops NO pile at all — any pile
topping `z` would be the seat pile by WF uniqueness, but the seat
pile's own top is `c`, and the pile's nodup content keeps `z ≠ c` (the
round-trip and twin-hunt's `z = zt` bar). -/
private theorem pollutesCrash_interiorTop_nowhere {st : State} (hwf : st.WF)
    {c z : Card} {k y : Anchor} {se : List Card}
    (hshape : (st.piles k).faceUp = se ++ [z] ++ [c])
    (hyt : st.topOf y = some z) : False := by
  have hzmem : z ∈ (st.piles k).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
  have hzymem : z ∈ (st.piles y).faceUp := Pile.mem_of_top hyt
  have hynk : y = k := by
    by_cases hq : y = k
    · exact hq
    · exact absurd hzymem ((mem_faceUp_unique hwf hzmem) y hq).1
  rw [hynk] at hyt
  have hctop : st.topOf k = some c := by
    rw [show st.topOf k = lastOf ((st.piles k).faceUp) from rfl, hshape]
    exact lastOf_snoc
  have hzc : z = c := Option.some.inj (hyt.symm.trans hctop)
  have hnodup : (se ++ [z] ++ [c]).Nodup :=
    runOK_nodup (by rw [← hshape]; exact hwf.runOK_of k)
  rw [hzc] at hnodup
  have hztail : ((se ++ [c]) ++ [c]).Nodup := hnodup
  exact pollutesCrash_nodup_snocNotmem hztail
    (List.mem_append.2 (Or.inr (List.mem_singleton.mpr rfl)))

/-- **The home slide's round trip** (zero-sorry): when the mint slides
off its own landlord `zt` and the landing names the landlord itself,
the departure and landing writes EXACTLY cancel — the moving run is
the singleton `[w]` (the seat content is nodup, so the mint has no
earlier occurrence), the seat pile's face-up content round-trips
(`below` of the `[zt, w]` tail plus the `[w]` run re-appended), and
every other pile reads verbatim through both single-pile writes: the
whole piles board of the landing equals the firing state's. -/
private theorem pollutesCrash_slideHome_identity {st s₁ : State} (hwf : st.WF)
    {w zt : Card} {k : Anchor} {se : List Card}
    (hshape : (st.piles k).faceUp = (se ++ [zt]) ++ [w])
    (hstep : State.step st (Move.tabToTab w (Sum.inr zt)) = some s₁) :
    s₁.piles = st.piles := by
  obtain ⟨a, hh, _hcp, _hfr, hs⟩ := step_tabToTab_inv hstep
  have hmemk : w ∈ (st.piles k).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have hak : a = k := by
    have h1 := pileHolding_mem hh
    by_cases hq : a = k
    · exact hq
    · exact absurd h1 ((mem_faceUp_unique hwf hmemk) a hq).1
  rw [hak] at hs
  have hnodup : ((se ++ [zt]) ++ [w]).Nodup :=
    runOK_nodup (by rw [← hshape]; exact hwf.runOK_of k)
  have hwne : w ∉ se ++ [zt] := pollutesCrash_nodup_snocNotmem hnodup
  -- the moving run is the singleton [w]
  have hsplit := pollutesCrash_below_fromCard_split (c := w) ((se ++ [zt]) ++ [w])
  rw [pollutesCrash_below_lastOf (se ++ [zt]) hwne] at hsplit
  have hmem2 : w ∈ fromCard w ((se ++ [zt]) ++ [w]) := by
    have hmemw : w ∈ (se ++ [zt]) ++ [w] := by
      rw [← hshape]
      exact hmemk
    rw [← hsplit] at hmemw
    rcases List.mem_append.mp hmemw with h3 | h4
    · exact absurd h3 hwne
    · exact h4
  have hrun : fromCard w ((se ++ [zt]) ++ [w]) = [w] := by
    have hL := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_singleton] at hL
    have hlen : (fromCard w ((se ++ [zt]) ++ [w])).length = 1 := by omega
    cases hrun' : fromCard w ((se ++ [zt]) ++ [w]) with
    | nil =>
        rw [hrun'] at hmem2
        exact absurd hmem2 (by simp)
    | cons u us =>
        rw [hrun'] at hmem2 hlen
        cases us with
        | nil =>
            rcases List.mem_cons.mp hmem2 with hcon | hcon
            · exact (congrArg (fun q => [q]) hcon).symm
            · exact absurd hcon (by simp)
        | cons v vs =>
            exfalso
            rw [List.length_cons, List.length_cons] at hlen
            omega
  have hsrw : fromCard w (st.piles k).faceUp = [w] := by
    rw [show (st.piles k).faceUp = (se ++ [zt]) ++ [w] from hshape]
    exact hrun
  rw [hsrw] at hs
  -- the mid-state's seat read
  have hprene : se ++ [zt] ≠ [] := by cases se <;> simp
  have hpre : below w (st.piles k).faceUp = se ++ [zt] := by
    rw [show (st.piles k).faceUp = (se ++ [zt]) ++ [w] from hshape]
    exact pollutesCrash_below_lastOf (se ++ [zt]) hwne
  have hmidtopk : ((st.setPile k (Pile.afterRunRemoved (st.piles k)
      (below w (st.piles k).faceUp))).piles k).top = some zt := by
    rw [setPile_afterRunRemoved_piles_self st k w, hpre,
      afterRunRemoved_ne hprene]
    show lastOf (se ++ [zt]) = some zt
    exact lastOf_snoc
  have hmidoff : ∀ y : Anchor, y ≠ k →
      ((st.setPile k (Pile.afterRunRemoved (st.piles k)
        (below w (st.piles k).faceUp))).piles y).top ≠ some zt := by
    intro y hy
    rw [setPile_afterRunRemoved_piles_ne st k w y hy]
    intro hcon
    exact pollutesCrash_interiorTop_nowhere hwf hshape
      (show st.topOf y = some zt from hcon)
  have hmidpot : (st.setPile k (Pile.afterRunRemoved (st.piles k)
      (below w (st.piles k).faceUp))).pileOfTop zt = some k := by
    show (firstWhere (fun a₂ =>
        decide (((st.setPile k (Pile.afterRunRemoved (st.piles k)
          (below w (st.piles k).faceUp))).piles a₂).top = some zt))
        Anchor.all) = some k
    refine firstWhere_find (Anchor.mem_all k) ?_ ?_
    · show decide (((st.setPile k (Pile.afterRunRemoved (st.piles k)
            (below w (st.piles k).faceUp))).piles k).top = some zt) = true
      rw [hmidtopk]
      exact decide_eq_true rfl
    · intro y _hy hyne
      show decide (((st.setPile k (Pile.afterRunRemoved (st.piles k)
              (below w (st.piles k).faceUp))).piles y).top = some zt) = false
      exact decide_false_of_not (hmidoff y hyne)
  -- the round trip
  funext y
  by_cases hyk : y = k
  · rw [hyk, hs, putRun_inr_eq hmidpot, setPile_piles_self]
    refine Pile.ext ?_ ?_
    · rw [hpre, afterRunRemoved_ne hprene, setPile_piles_self]
    · rw [hpre, afterRunRemoved_ne hprene, setPile_piles_self, hshape]
  · rw [hs, putRun_inr_eq hmidpot, setPile_piles_ne hyk]
    exact setPile_afterRunRemoved_piles_ne st k w y hyk

/-- The run's membership read (zero-sorry): the moving run's cards are
the departure pile's own face-up cards. -/
private theorem pollutesCrash_mem_fromCard {c x : Card} :
    ∀ {l : List Card}, x ∈ fromCard c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [fromCard])
  | cons u us ih =>
      by_cases huc : u = c
      · intro h
        rw [huc, fromCard_cons_self] at h
        rw [huc]
        exact h
      · intro h
        rw [fromCard_cons_ne us huc] at h
        exact List.mem_cons.2 (Or.inr (ih h))

/-- The cover-run's tail sweep (the covered-fork self-safety input,
zero-sorry): with the head `c` strictly below the last cell `m`, the
run from `c` in `se ++ [m]` carries the whole tail — `m` rides the
suffix from the head. -/
private theorem pollutesCrash_mem_fromCard_snoc {c m : Card}
    (hcm : c ≠ m) :
    ∀ se : List Card, c ∈ se → m ∈ fromCard c (se ++ [m]) := by
  intro se
  induction se with
  | nil => intro hmem; exact absurd hmem (by simp)
  | cons u us ih =>
      intro hmem
      by_cases huc : u = c
      · rw [huc, List.cons_append, fromCard_cons_self]
        exact List.mem_cons.2 (Or.inr
          (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))))
      · have hrec : c ∈ us := by
          rcases List.mem_cons.mp hmem with h1 | h2
          · exact absurd h1.symm huc
          · exact h2
        rw [List.cons_append, fromCard_cons_ne (us ++ [m]) huc]
        exact ih hrec

/-- **The twin landing's twin identity** (zero-sorry): the mint-alone
slide's residual landing is forced INTO THE LANDLORD'S TWIN — the fit
arithmetic (the landing card sits one above the mint, opposite the
mint's color) plus the deck census pins it to `zt` OR `zt.twin`
exactly; the residual fork is the twin card by subtraction of the home
landing.  The twin hunt is thereby ANSWERED shape-side: what sits
under the mint at the landing epoch IS the landlord's twin, family
colored like the landlord itself. -/
private theorem pollutesCrash_twinLanding_color {st s₁ : State} (hwf : st.WF)
    {w zt z y : Card} {k2 : Anchor} {se : List Card}
    (hshape : (st.piles k2).faceUp = se ++ [zt, w])
    (hzrk : zt.rank.toIdx = w.rank.toIdx + 1)
    (hzcol : zt.suit.color = y.suit.color)
    (hstep : State.step st (Move.tabToTab w (Sum.inr z)) = some s₁)
    (hzzt : z ≠ zt) :
    z = zt.twin := by
  obtain ⟨_a, _hh, hcp, _hfr, _hs⟩ := step_tabToTab_inv hstep
  obtain ⟨_k0, _hholdz, hsit⟩ := canPlace_inr hcp
  obtain ⟨hrkz, hcolz⟩ := (canSitOn_eq w z).mp hsit
  have hwcol : w.suit.color ≠ y.suit.color :=
    pollutesCrash_mintOffColor hwf hshape hzcol
  have hzcolz : z.suit.color = zt.suit.color :=
    (lock_color_pair hcolz hwcol).trans hzcol.symm
  have hzrkz : z.rank.toIdx = zt.rank.toIdx := by omega
  rcases lock_rankColor_pair hzrkz hzcolz with h | h
  · exact absurd h hzzt
  · exact h

/-- **The burial slide's pins** (zero-sorry): a stranger run landing on
the mint buries the seat's own top.  The departure write cannot be the
seat pile (its run would carry the mint into its own landing, barred
by the self-safety row); the host read pins the seat through the
transplant row; the landing appends the run ON the mint.  The cover's
fit-pins make it family-colored relative to the mint and rank-locked
one under it; the mint's `nextUp` survives the slide (found
untouched).  The honest residue is the covered-mint license
(`canRaiseS_free`'s twin premise) plus the census pricing — the
composition-level bridge. -/
private theorem pollutesCrash_burialSlide_pins {st s₁ : State} (hwf : st.WF)
    {c w zt : Card} {k2 : Anchor} {se : List Card}
    (hshape : (st.piles k2).faceUp = se ++ [zt, w])
    (hhold : st.pileOfTop w = some k2)
    (hn : st.nextUp w = true)
    (hstep : State.step st (Move.tabToTab c (Sum.inr w)) = some s₁) :
    ∃ (dep : Anchor) (run : List Card),
      dep ≠ k2 ∧
        run = fromCard c (st.piles dep).faceUp ∧
        run ≠ [] ∧ w ∉ run ∧
        c.rank.toIdx + 1 = w.rank.toIdx ∧
        c.suit.color ≠ w.suit.color ∧
        (s₁.piles k2).faceUp = (se ++ [zt, w]) ++ run ∧
        s₁.nextUp w = true := by
  obtain ⟨a, hh, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
  obtain ⟨k₀, hhold', hsit⟩ := canPlace_inr hcp
  have hk₀ : k₀ = k2 := Option.some.inj (hhold'.symm.trans hhold)
  rw [hk₀] at hhold'
  obtain ⟨hrkz, hcolz⟩ := (canSitOn_eq c w).mp hsit
  have hcw : c ≠ w := by
    intro hcon
    rw [hcon] at hrkz
    omega
  have hmemw : w ∈ (st.piles k2).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr
      (Or.inr (List.mem_cons.2 (Or.inr (List.mem_singleton.mpr rfl))))
  have hcmem : c ∈ (st.piles a).faceUp := pileHolding_mem hh
  -- the departure pile is a stranger: the run would else carry the mint
  have hdep : a ≠ k2 := by
    intro hcon
    rw [hcon, hshape] at hcmem
    have hpre' : c ∈ se ∨ c = zt := by
      rcases List.mem_append.mp hcmem with h1 | h2
      · exact Or.inl h1
      · rcases List.mem_cons.mp h2 with h2' | h2''
        · exact Or.inr h2'
        · exact absurd (List.mem_singleton.mp h2'') hcw
    obtain ⟨RR, hRR⟩ := pollutesCrash_fromCard_seatTail hcw se hpre'
    have hwin : w ∈ fromCard c (st.piles k2).faceUp := by
      rw [hshape, hRR]
      exact List.mem_append.mpr
        (Or.inr (List.mem_cons.2 (Or.inr (List.mem_singleton.mpr rfl))))
    exact absurd hwin (canPlace_inr_target_off_run hwf hcp
      (show c ∈ (st.piles k2).faceUp from by rw [hshape]; exact hcmem))
  have hzfa : w ∉ (st.piles a).faceUp :=
    (mem_faceUp_unique hwf hmemw) a hdep |>.1
  have hzha : w ∉ (st.piles a).hidden :=
    (mem_faceUp_unique hwf hmemw) a hdep |>.2.1
  have hmidk2 : (st.setPile a (Pile.afterRunRemoved (st.piles a)
      (below c (st.piles a).faceUp))).piles k2 = st.piles k2 :=
    setPile_afterRunRemoved_piles_ne st a c k2 (fun hcon => hdep hcon.symm)
  have hmidpot := pollutesCrash_slide_hostKeep (c := c) (z := w)
    (a := a) (k₀ := k2) hwf (fun hcon => hdep hcon.symm) hhold hzfa hzha
  have hshp : (s₁.piles k2).faceUp
      = (st.piles k2).faceUp ++ fromCard c (st.piles a).faceUp := by
    rw [hs, putRun_inr_eq hmidpot, setPile_piles_self, hmidk2]
  have hnext : s₁.nextUp w = true :=
    (nextUp_congr w (pollutesCrash_slide_foundEq hstep)).trans hn
  exact ⟨a, fromCard c (st.piles a).faceUp, hdep, rfl, hfr,
    fun hwin => absurd (pollutesCrash_mem_fromCard hwin) hzfa,
    hrkz, hcolz, by rw [hshp, hshape], hnext⟩




/-- **THE CENSUS-DEBT READ, seeded** (zero-sorry, the ¶5 bridge's anchor):
at the minting landing epoch `v` the mint's own suit rung reads the
mint's index (hv1), so with the dropped identity `w.suit = d.suit` in
place the tail's census-debt equation READS AT ZERO — the seed pair the
widened carry threads from the tail's very first pre-state. -/
private theorem pollutesCrash_tailDebt_seed {v : State} {d w : Card}
    (hw : w.suit = d.suit)
    (hv1 : rungAt v w.suit = w.rank.toIdx) :
    ∃ ccRA ccPD : Nat, rungAt v d.suit + ccPD = w.rank.toIdx + ccRA := by
  rw [show rungAt v d.suit = rungAt v w.suit from by rw [hw]]
  exact ⟨0, 0, hv1⟩

/-- **The census-debt read, found-keep arm** (zero-sorry): every leg
whose successor preserves the foundations board verbatim carries the
equation with the SAME counter pair — the mechanical re-pair for the
draw and both waste arms. -/
private theorem pollutesCrash_tailDebt_keep {vp s₁ : State} {d w : Card}
    (hfk : s₁.found = vp.found)
    (hde : ∃ ccRA ccPD : Nat, rungAt vp d.suit + ccPD = w.rank.toIdx + ccRA) :
    ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD = w.rank.toIdx + ccRA := by
  obtain ⟨cRA, cPD, hde⟩ := hde
  refine ⟨cRA, cPD, ?_⟩
  rw [show rungAt s₁ d.suit = (s₁.found d.suit).length from rfl, hfk]
  exact hde

/-- **The census-debt read, raise arm** (zero-sorry): a raise of a card
NOT of the pinned suit keeps the equation pair verbatim; a raise of the
pinned suit itself increments the raise counter, pairing the guard's
own index read — the wash-back's guard arithmetic rides the same
increment (the pre-rung is the raised card's own index). -/
private theorem pollutesCrash_tailDebt_raise {vp s₁ : State} {d w c : Card}
    (hstep : State.step vp (Move.tabToFound c) = some s₁)
    (hde : ∃ ccRA ccPD : Nat, rungAt vp d.suit + ccPD = w.rank.toIdx + ccRA) :
    ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD = w.rank.toIdx + ccRA := by
  obtain ⟨_hnext_c, _a, _hp0, hs⟩ := step_tabToFound_inv hstep
  by_cases hesc : c.suit = d.suit
  · obtain ⟨cRA, cPD, hde⟩ := hde
    refine ⟨cRA + 1, cPD, ?_⟩
    · have hfd : s₁.found c.suit = vp.found c.suit ++ [c] := by
        rw [hs]
        exact setFound_found_self
      have hr : rungAt s₁ d.suit = (s₁.found c.suit).length := by
        show (s₁.found d.suit).length = (s₁.found c.suit).length
        rw [hesc]
      rw [hr, hfd, List.length_append, List.length_singleton]
      show (vp.found c.suit).length + 1 + cPD = w.rank.toIdx + (cRA + 1)
      have hde' : (vp.found c.suit).length + cPD = w.rank.toIdx + cRA := by
        rw [show (vp.found c.suit).length = (vp.found d.suit).length from by
          rw [hesc]]
        exact hde
      omega
  · obtain ⟨cRA, cPD, hde⟩ := hde
    refine ⟨cRA, cPD, ?_⟩
    have hfd : s₁.found d.suit = vp.found d.suit := by
      rw [hs]
      exact setFound_found_ne (fun hcon => hesc hcon.symm)
    rw [show rungAt s₁ d.suit = (s₁.found d.suit).length from rfl, hfd]
    exact hde

/-- **The census-debt read, pull arm** (zero-sorry): a `foundToTab`
leg of a card NOT of the pinned suit keeps the pair verbatim; a
same-pinned-suit pull increments the pull counter by the chop read —
the same-suit fork's pop price, one under the mint's index. -/
private theorem pollutesCrash_tailDebt_pull {vp s₁ : State} {d w c : Card}
    {b : Base}
    (hstep : State.step vp (Move.foundToTab c b) = some s₁)
    (hde : ∃ ccRA ccPD : Nat, rungAt vp d.suit + ccPD = w.rank.toIdx + ccRA) :
    ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD = w.rank.toIdx + ccRA := by
  obtain ⟨_c₀, htop0, hceq, _hcp, hs⟩ := step_foundToTab_inv hstep
  rw [hceq] at htop0
  by_cases hesc : c.suit = d.suit
  · obtain ⟨cRA, cPD, hde⟩ := hde
    refine ⟨cRA, cPD + 1, ?_⟩
    · have hfl : s₁.found d.suit = chop (vp.found c.suit) := by
        rw [hs, putCard_found, hesc.symm]
        exact setFound_found_self
      have hr : rungAt s₁ d.suit = (chop (vp.found c.suit)).length := by
        show (s₁.found d.suit).length = (chop (vp.found c.suit)).length
        rw [hfl]
      have hchoplen : (chop (vp.found c.suit)).length + 1
          = (vp.found c.suit).length :=
        pollutesCrash_chop_len (vp.found c.suit)
          (show (vp.found c.suit) ≠ [] from by
            intro hcon
            have hnone : vp.foundTop c.suit = none := by
              show lastOf (vp.found c.suit) = none
              rw [hcon]
              rfl
            rw [hnone] at htop0
            exact absurd htop0 (by simp))
      have hde' : (vp.found c.suit).length + cPD = w.rank.toIdx + cRA := by
        rw [show (vp.found c.suit).length = (vp.found d.suit).length from by
          rw [hesc]]
        exact hde
      show rungAt s₁ d.suit + (cPD + 1) = w.rank.toIdx + cRA
      rw [hr]
      omega
  · obtain ⟨cRA, cPD, hde⟩ := hde
    refine ⟨cRA, cPD, ?_⟩
    have hfd : s₁.found d.suit = vp.found d.suit := by
      rw [hs]
      rw [putCard_found]
      exact setFound_found_ne (fun hcon => hesc hcon.symm)
    rw [show rungAt s₁ d.suit = (s₁.found d.suit).length from rfl, hfd]
    exact hde

/-- **THE RAISE MOVER** (zero-sorry): a `tabToFound` leg of a card other
than the mint (`hcw`).  The license chain's root read
(`pollutesCrash_canRaiseS_nextUp`) puts the mint next-up at the firing
state, so the raise's guard pins the raised rank to the rung of its own
suit — and a raise naming the mint's suit at the mint's own index names
the mint itself, so the raised suit is forced off the mint's row; the
raised pile likewise cannot be the mint's seat (the seat tops the mint).
Hence the `setFound` write leaves the mint's found row alone and the
piles write never touches the seat: the carry re-reads wholesale at the
raise's landing, the license regenerating `now`-grade from the surviving
`nextUp`, seat shape and chop read. -/
private theorem pollutesCrash_rhoRaise {x y d w zt : Card}
    {play π : List Move}
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hdcol : d.suit.color ≠ y.suit.color)
    (hzrk : zt.rank.toIdx = w.rank.toIdx + 1)
    (hzcol : zt.suit.color = y.suit.color)
    (hrk : w.rank.toIdx + 1 ≤ d.rank.toIdx)
    (hwne : w ≠ y ∧ w ≠ y.twin)
    (hsq3 : raisesOf play d.suit + 2 ≤ pullsOf play d.suit)
    (hpc1 : raisesOf play y.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.suit)
    (hpc2 : raisesOf play y.twin.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.twin.suit)
    (hpid : raisesOf π d.suit + (d.rank.toIdx - w.rank.toIdx)
      ≤ pullsOf π d.suit)
    {vp s₁ sth : State} {m c : Card}
    (hwfs : vp.WF)
    (hn : vp.nextUp m = true)
    (hrkb : m.rank.toIdx + 2 ≤ y.rank.toIdx)
    (k2 : Anchor) (se2 : List Card)
    (hshape2 : (vp.piles k2).faceUp = se2 ++ [m])
    (hhold2 : vp.pileOfTop m = some k2)
    (hcond2 : chop (vp.piles k2).faceUp ≠ [] ∨
      ((vp.piles k2).hidden = [] ∧ m.rank = Rank.king))
    (hdebt : ∃ ccRA ccPD : Nat, rungAt vp d.suit + ccPD
      = w.rank.toIdx + ccRA)
    (hwfst' : sth.WF)
    (hy' : ForkWitness sth y)
    (hdcov' : ∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
      sth.pileOfTop d = some cc)
    (hlat' : ∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin)
    (hnext' : sth.nextUp d = false)
    (hsq2' : rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1)
    (hcw : c ≠ m)
    (hwleg : reversibleAtW vp (Move.tabToFound c))
    (hstep : State.step vp (Move.tabToFound c) = some s₁)
    (ih : (∃ m₀ : Card, s₁.WF ∧ s₁.nextUp m₀ = true ∧
        m₀.rank.toIdx + 2 ≤ y.rank.toIdx ∧
        ∃ ke se, (s₁.piles ke).faceUp = se ++ [m₀] ∧
          s₁.pileOfTop m₀ = some ke ∧
          (chop (s₁.piles ke).faceUp ≠ [] ∨
            ((s₁.piles ke).hidden = [] ∧ m₀.rank = Rank.king)) ∧
        ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD
          = w.rank.toIdx + ccRA) →
      sth.WF → ForkWitness sth y →
      (∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
        sth.pileOfTop d = some cc) →
      (∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin) →
      sth.nextUp d = false →
      rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1 →
      ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin) :
    ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin := by
  have hwfs₁ : s₁.WF := step_wf hwfs hstep
  obtain ⟨hnext_c, a, hp0, hs⟩ := step_tabToFound_inv hstep
  have hrungC : c.rank.toIdx = (vp.found c.suit).length :=
    of_decide_eq_true hnext_c
  have hrungM : m.rank.toIdx = (vp.found m.suit).length :=
    of_decide_eq_true hn
  -- the raised suit is off the mint's row: a same-suit guard names the mint
  have hsw : c.suit ≠ m.suit := by
    intro hcon
    have hcidx : c.rank.toIdx = m.rank.toIdx := by
      rw [hrungC, hcon, hrungM]
    apply hcw
    rcases c with ⟨cs, cr⟩
    rcases m with ⟨ms, mr⟩
    have hcr : cr = mr := Rank.toIdx_inj hcidx
    have hcs : cs = ms := hcon
    subst hcr
    subst hcs
    rfl
  -- the raised pile is not the mint's seat (the seat tops the mint)
  have htop2 : vp.topOf k2 = some m := (pileOfTop_top hhold2).2
  have hak2 : k2 ≠ a := by
    intro hcon
    rw [← hcon] at hp0
    exact hcw (Option.some.inj ((pileOfTop_top hp0).2.symm.trans htop2))
  -- the found row of the mint's suit survives the raise's write
  have hfd : s₁.found m.suit = vp.found m.suit := by
    rw [hs]
    exact setFound_found_ne (fun hcon => hsw hcon.symm)
  have hn1 : s₁.nextUp m = true := by
    show decide (m.rank.toIdx = (s₁.found m.suit).length) = true
    rw [hfd]
    exact hn
  -- the seat pile is off the raise's piles write
  have hpilk2 : s₁.piles k2 = vp.piles k2 := by
    rw [hs]
    show (if k2 = a then
        Pile.afterRunRemoved (vp.piles a) (chop (vp.piles a).faceUp)
      else vp.piles k2) = vp.piles k2
    rw [ite_eq_right hak2]
  exact ih ⟨m, hwfs₁, hn1, hrkb, k2, se2, by rw [hpilk2]; exact hshape2,
    (pileOfTop_eq_some_iff hwfs₁).2 (by
      show (s₁.piles k2).top = some m
      rw [hpilk2]
      exact htop2),
    by rw [hpilk2]; exact hcond2,
    pollutesCrash_tailDebt_raise hstep hdebt⟩
    hwfst' hy' hdcov' hlat' hnext' hsq2'

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

/-- The zone brick (the founded-mint impossibility cases): a card in
a suit's foundation row is nowhere in any pile — the two memberships
would double the conserved count. -/
private theorem pollutesCrash_foundCard_notInPile {st : State} (hwf : st.WF)
    {c : Card} {σ : Suit} (hf : c ∈ st.found σ) {a : Anchor}
    (hp : c ∈ (st.piles a).hidden ∨ c ∈ (st.piles a).faceUp) :
    False := by
  have hcount : st.cardCount c = 1 := hwf.cardCount_eq (Card.mem_universe c)
  have hsplit : st.zones =
      (Suit.all.map st.found) ++
        ((Anchor.all.map (fun a' =>
            (st.piles a').hidden ++ (st.piles a').faceUp)) ++
          [st.stock, st.waste]) := rfl
  have hl : c ∈ (Suit.all.map st.found).flatMap id :=
    (List.mem_flatMap).2 ⟨st.found σ,
      List.mem_map.2 ⟨σ, Suit.mem_all σ, rfl⟩, hf⟩
  have hz : c ∈ (st.piles a).hidden ++ (st.piles a).faceUp :=
    by
    rcases hp with h | h
    · exact (List.mem_append).2 (Or.inl h)
    · exact (List.mem_append).2 (Or.inr h)
  have hr : c ∈ ((Anchor.all.map (fun a' =>
          (st.piles a').hidden ++ (st.piles a').faceUp)) ++
          [st.stock, st.waste]).flatMap id :=
    (List.mem_flatMap).2 ⟨(st.piles a).hidden ++ (st.piles a).faceUp,
      (List.mem_append).2
        (Or.inl (List.mem_map.2 ⟨a, Anchor.mem_all a, rfl⟩)),
      hz⟩
  have h2 : 2 ≤ st.cardCount c := count_ge_two_of_split hsplit hl hr
  omega

/-- The zone brick's top corollary: a suit-row card tops no pile —
the founded mint cannot seat, cover as a base, or be re-founded
while it rides its row (both residual-guard shapes die here). -/
private theorem pollutesCrash_foundCard_notPileTop {st : State} (hwf : st.WF)
    {c : Card} {σ : Suit} (hf : lastOf (st.found σ) = some c) {a : Anchor} :
    (st.piles a).top ≠ some c := by
  intro htop
  have hmem : c ∈ (st.piles a).faceUp := Pile.mem_of_top htop
  exact pollutesCrash_foundCard_notInPile hwf (lastOf_mem hf) (Or.inr hmem)

/-- The same-suit raise brick (the stack grows at the top): raising a
card of the mint's own suit stacks it onto the row — the mint's
below-row and bracket position pin ride verbatim, the stack
absorbing the new top. -/
private theorem pollutesCrash_foundRaise_stackGrow {s s₁ : State}
    {m c : Card} {PRE STOCK : List Card}
    (hrow : s.found m.suit = PRE ++ [m] ++ STOCK)
    (happ : s₁.found m.suit = s.found m.suit ++ [c]) :
    s₁.found m.suit = PRE ++ [m] ++ (STOCK ++ [c]) := by
  rw [happ, hrow, List.append_assoc, List.append_assoc]

/-- The stack-shrink's snoc re-association (zero-sorry): the mint's
row tail with the stack's last cell pulled out to snoc position —
pure list algebra, proved by induction to sidestep the associativity
read. -/
private theorem pollutesCrash_rowSnoc_assoc {α : Type} :
    ∀ (PRE : List α) (m : α) (Y : List α) (t : α),
      PRE ++ [m] ++ (Y ++ [t]) = (PRE ++ [m] ++ Y) ++ [t] := by
  intro PRE
  induction PRE with
  | nil => intro m Y t; rfl
  | cons u us ih =>
      intro m Y t
      simp only [List.cons_append]
      rw [ih]

/-- The same-suit pop brick (the buried case): with at least one
card stacked above the mint, a pop of the row's top chops the stack
alone — the mint's own shape and position pin ride verbatim. -/
private theorem pollutesCrash_foundPull_stackShrink {s s₁ : State}
    {m : Card} {PRE STOCK : List Card} (hne : STOCK ≠ [])
    (hrow : s.found m.suit = PRE ++ [m] ++ STOCK)
    (hchop : s₁.found m.suit = chop (s.found m.suit)) :
    ∃ STOCK' : List Card, s₁.found m.suit = PRE ++ [m] ++ STOCK' := by
  obtain ⟨Y, t, hst⟩ := pollutesCrash_snocSplit STOCK hne
  refine ⟨Y, ?_⟩
  rw [hchop, hrow, hst, pollutesCrash_rowSnoc_assoc, chop_snoc]

/-- The re-exhume detector brick: with the stack empty the mint IS
the row's top — the pop it takes is the founding's own release,
the pre-state rung reading the founding bracket (the position
pin), the landing bracket read one under it. -/
private theorem pollutesCrash_foundTop_atOwn {st : State} {m : Card}
    {PRE : List Card}
    (hrow : st.found m.suit = PRE ++ [m]) :
    st.foundTop m.suit = some m ∧
      (st.found m.suit).length = PRE.length + 1 := by
  refine ⟨?_, ?_⟩
  · show lastOf (st.found m.suit) = some m
    rw [hrow]
    exact lastOf_snoc
  · have hL := congrArg List.length hrow
    simp only [List.length_append, List.length_singleton] at hL
    exact hL

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

/-- **The seed's Below-start witness** (the core's exact input,
zero-sorry): the hpkg seed shape `[bs ++ zt, w]` read in
`OrphanSeat.Below`'s own positional form — the seed mint seated ON
its landlord, the tail empty.  This is the hstart disjunct
`Below_stable` consumes for the whole-journey positional transport
of the seed card; it is the ONLY core input the composition side
can build without new premises (the founding-bracket endpoint read
and the twin's own start-pin are named in the ledger as the
transpose gaps). -/
private theorem pollutesCrash_seedBelow_start {v : State} {w zt : Card}
    {kk : Anchor} {bs : List Card}
    (htop : (v.piles kk).faceUp = bs ++ [zt, w]) :
    Below v w zt :=
  ⟨kk, bs, [], by rw [htop]⟩

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
    have hlt := lock_found_rank_lt hwf₂ hmem
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

/-- **THE ORIGIN-ANCHORED CRASH** — the composition's terminal
pollution crash, now direct: the terminus's d-suit hot card was
founded at the origin (the hsq1-grade anchor bounds it strictly
under the anchoring rung by the two-end squeeze) and is HOT at the
terminus (its index IS the terminus's d-suit rung), so the
archaeology engine (`pollutesCrash_terminalHot_Below`) seats it
BELOW a live neighbor at the terminus; that neighbor is
family-colored by the seat fit's color conservation
(`lock_color_pair`, the two-card census `lock_rankColor_pair`
reading the suit pair), ranked strictly under the fork's pinned
family rungs (both pinned at the pair's rank by `canRaiseS_rung`
off the fork's own `ForkWitness`), hence foundation-resident by
the height bridge — contradicting the Below read's own face-up
membership (`mem_found_unique`).  The fork's saturation crashes
the census, mint-suit-agnostic; the conclusion is the third-live
card shape every consumer arms. -/
private theorem pollutesCrash_originCrash {sth : State} {y d : Card}
    (hwfst : sth.WF)
    (hy : ForkWitness sth y)
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hdcol : d.suit.color ≠ y.suit.color)
    (hsq2 : rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1)
    {o : State} (hwfo : o.WF)
    (hsq1 : d.rank.toIdx + 1 ≤ rungAt o d.suit)
    (hjo : ∃ pf : List Move, ShufflePlayW o pf sth) :
    ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin := by
  obtain ⟨pf, hshpo⟩ := hjo
  have hfam : y.rank.toIdx < 13 := Rank.toIdx_lt y.rank
  have hk13 : rungAt sth d.suit < 13 := by omega
  obtain ⟨T, hTdef⟩ :
      ∃ c : Card, c = Card.mk d.suit (lockRk (rungAt sth d.suit)) :=
    ⟨_, rfl⟩
  have hTidx : T.rank.toIdx = rungAt sth d.suit := by
    rw [hTdef]
    exact lockRk_toIdx _ hk13
  have hTsuit : T.suit = d.suit := by
    rw [hTdef]
  have hhotT : sth.nextUp T = true :=
    pollutesCrash_landing_live (by rw [hTsuit, hTidx])
  have hnkT : T.rank ≠ Rank.king := by
    intro hcon
    rw [hcon] at hTidx
    have hk12 : Rank.king.toIdx = 12 := rfl
    omega
  have horgT : T.rank.toIdx < rungAt o T.suit := by
    rw [hTsuit, hTidx]
    omega
  obtain ⟨b, a, L, R, hshp⟩ :=
    pollutesCrash_terminalHot_Below hshpo hwfo hwfst hnkT horgT hhotT
  have hok : runOK (L ++ b :: T :: R) = true := by
    rw [← hshp]
    exact hwfst.runOK_of a
  obtain ⟨hrkbt, hcolbt⟩ :=
    (canSitOn_eq T b).mp (lock_runOK_adjacent b T L R hok)
  have hbcol : b.suit.color = y.suit.color :=
    lock_color_pair (a := d.suit.color)
      (by rw [← hTsuit]; exact hcolbt) hdcol
  have hyPin : rungAt sth y.suit = y.rank.toIdx :=
    canRaiseS_rung ((hy.1 y).mp (Or.inl rfl))
  have hytPin : rungAt sth y.twin.suit = y.rank.toIdx := by
    have h0 := canRaiseS_rung ((hy.1 y.twin).mp (Or.inr rfl))
    rwa [Card.twin_rank y] at h0
  have hsuit : b.suit = y.suit ∨ b.suit = y.twin.suit := by
    have hz : (Card.mk b.suit y.rank) = y ∨
        (Card.mk b.suit y.rank) = y.twin :=
      lock_rankColor_pair rfl hbcol
    rcases hz with h | h
    · refine Or.inl ?_
      exact (congrArg Card.suit h :
        (Card.mk b.suit y.rank).suit = y.suit)
    · refine Or.inr ?_
      exact (congrArg Card.suit h :
        (Card.mk b.suit y.rank).suit = y.twin.suit)
  have hbmem : b ∈ sth.found b.suit := by
    refine mem_found_of_height hwfst ?_
    have hbund : b.rank.toIdx < y.rank.toIdx := by omega
    rcases hsuit with h | h
    · rw [h]
      show b.rank.toIdx < rungAt sth y.suit
      rw [hyPin]
      exact hbund
    · rw [h]
      show b.rank.toIdx < rungAt sth y.twin.suit
      rw [hytPin]
      exact hbund
  have hbface : b ∈ (sth.piles a).faceUp := by
    rw [hshp]
    exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
  obtain ⟨hh, _hS, _hW, _⟩ := mem_found_unique hwfst hbmem
  exact absurd hbface (hh a).2

/-- **THE SLIDE MOVER** (zero-sorry): a `tabToTab` leg whose moving run
write sites (departure and landing) split against the mint's seat.  At
an off-seat departure the mint's seat pile reads verbatim (the landing
is off-seat too: an empty target is not the nonempty seat, and an `inr`
target other than `w` tops a pile that is not the seat).  At a
departure AT the mint's seat, `c ≠ w` keeps `[zt, w]` inside the
moving run (the tail split `pollutesCrash_fromCard_seatTail`), so the
seat conjunct re-pairs over the run's own `[zt, w]` tail at the landing
pile.  In every cell the anchor restores through `pileOfTop_eq_some_iff`
from the landing pile's top read, and the license regenerates
`now`-grade. -/
private theorem pollutesCrash_rhoSlide {x y d w zt : Card}
    {play π : List Move}
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hdcol : d.suit.color ≠ y.suit.color)
    (hzrk : zt.rank.toIdx = w.rank.toIdx + 1)
    (hzcol : zt.suit.color = y.suit.color)
    (hrk : w.rank.toIdx + 1 ≤ d.rank.toIdx)
    (hwne : w ≠ y ∧ w ≠ y.twin)
    (hsq3 : raisesOf play d.suit + 2 ≤ pullsOf play d.suit)
    (hpc1 : raisesOf play y.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.suit)
    (hpc2 : raisesOf play y.twin.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.twin.suit)
    (hpid : raisesOf π d.suit + (d.rank.toIdx - w.rank.toIdx)
      ≤ pullsOf π d.suit)
    {vp s₁ sth : State} {m c : Card} {b : Base}
    (hwfs : vp.WF)
    (hn : vp.nextUp m = true)
    (hrkb : m.rank.toIdx + 2 ≤ y.rank.toIdx)
    (k2 : Anchor) (se2 : List Card)
    (hshape2 : (vp.piles k2).faceUp = se2 ++ [m])
    (hhold2 : vp.pileOfTop m = some k2)
    (hcond2 : chop (vp.piles k2).faceUp ≠ [] ∨
      ((vp.piles k2).hidden = [] ∧ m.rank = Rank.king))
    (hdebt : ∃ ccRA ccPD : Nat, rungAt vp d.suit + ccPD
      = w.rank.toIdx + ccRA)
    (hwfst' : sth.WF)
    (hy' : ForkWitness sth y)
    (hdcov' : ∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
      sth.pileOfTop d = some cc)
    (hlat' : ∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin)
    (hnext' : sth.nextUp d = false)
    (hsq2' : rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1)
    (hcw : c ≠ m)
    (hbnw : b ≠ Sum.inr m)
    (hwleg : reversibleAtW vp (Move.tabToTab c b))
    (hstep : State.step vp (Move.tabToTab c b) = some s₁)
    (ih : (∃ m₀ : Card, s₁.WF ∧ s₁.nextUp m₀ = true ∧
        m₀.rank.toIdx + 2 ≤ y.rank.toIdx ∧
        ∃ ke se, (s₁.piles ke).faceUp = se ++ [m₀] ∧
          s₁.pileOfTop m₀ = some ke ∧
          (chop (s₁.piles ke).faceUp ≠ [] ∨
            ((s₁.piles ke).hidden = [] ∧ m₀.rank = Rank.king)) ∧
        ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD
          = w.rank.toIdx + ccRA) →
      sth.WF → ForkWitness sth y →
      (∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
        sth.pileOfTop d = some cc) →
      (∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin) →
      sth.nextUp d = false →
      rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1 →
      ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin) :
    ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin := by
  have hwfs₁ : s₁.WF := step_wf hwfs hstep
  have htop2 : vp.topOf k2 = some m := (pileOfTop_top hhold2).2
  have hfd : s₁.found = vp.found := pollutesCrash_slide_foundEq hstep
  have hdebt1 := pollutesCrash_tailDebt_keep hfd hdebt
  have hn1 : s₁.nextUp m = true := (nextUp_congr m hfd).trans hn
  obtain ⟨a, hhhold, hcp, hfrun, hs⟩ := step_tabToTab_inv hstep
  have hcmem : c ∈ (vp.piles a).faceUp := pileHolding_mem hhhold
  by_cases hak2 : a = k2
  · -- the departure IS the mint's seat: the run carries `[LL, m]`
    -- (c ≠ m), so the kit re-pairs over the run's own tail at the
    -- landing pile — the light seat's existential landlord roams.
    have hcmem' : c ∈ (vp.piles k2).faceUp := by
      rw [← hak2]
      exact hcmem
    rw [hshape2] at hcmem'
    -- c sits strictly below the mint: c ∈ se2 (c ≠ m)
    have hcse : c ∈ se2 := by
      rcases List.mem_append.mp hcmem' with h1 | h2
      · exact h1
      · exact absurd (List.mem_singleton.mp h2) hcw
    -- the seat content is nonempty below the mint (the chop row or the
    -- king line), and splits at its landlord
    have hse2ne : se2 ≠ [] := by
      intro hcon
      rcases hcond2 with h | h
      · rw [hshape2, hcon] at h
        exact absurd (show chop ([] ++ [m]) ≠ [] from h) (by simp [chop])
      · rw [hcon] at hcse
        exact absurd hcse (by simp)
    obtain ⟨init, LL, hse2split⟩ : ∃ init LL, se2 = init ++ [LL] :=
      pollutesCrash_snocSplit se2 hse2ne
    have hse : c ∈ init ∨ c = LL := by
      rw [hse2split] at hcse
      rcases List.mem_append.mp hcse with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (List.mem_singleton.mp h2)
    obtain ⟨RR, hRR⟩ := pollutesCrash_fromCard_seatTail (c := c)
      (zt := LL) (w := m) hcw init hse
    have hrunT : fromCard c (vp.piles k2).faceUp = RR ++ [LL, m] := by
      rw [hshape2, hse2split, show init ++ [LL] ++ [m] = init ++ [LL, m]
        from List.append_assoc init [LL] [m]]
      exact hRR
    cases b with
    | inl a2 =>
        -- the landing seat is empty (so not the nonempty mint's seat)
        obtain ⟨hemp2, -⟩ := canPlace_inl hcp
        have ha2k2 : a2 ≠ k2 := by
          intro hcon
          rw [hcon] at hemp2
          have hfupE := ((Pile.isEmpty_eq _).mp hemp2).2
          rw [hshape2] at hfupE
          exact absurd hfupE (by simp)
        have hlens : s₁.piles a2 = ⟨[], RR ++ [LL, m]⟩ := by
          rw [hs, putRun_eq_inl, setPile_piles_self, hak2, hrunT]
        have hshape1 : (s₁.piles a2).faceUp = (RR ++ [LL]) ++ [m] := by
          rw [hlens]
          show RR ++ [LL, m] = (RR ++ [LL]) ++ [m]
          exact (List.append_assoc RR [LL] [m]).symm
        have hhold1 : s₁.pileOfTop m = some a2 :=
          (pileOfTop_eq_some_iff hwfs₁).2 (by
            show lastOf (s₁.piles a2).faceUp = some m
            rw [hshape1]
            exact lastOf_snoc)
        have hcond1 : chop (s₁.piles a2).faceUp ≠ [] ∨
            ((s₁.piles a2).hidden = [] ∧ m.rank = Rank.king) :=
          Or.inl (by
            show chop (s₁.piles a2).faceUp ≠ []
            rw [hshape1, show (RR ++ [LL]) ++ [m] = RR ++ [LL, m] from
              List.append_assoc RR [LL] [m]]
            exact pollutesCrash_chop_seatTail (zt := LL) (w := m) RR)
        exact ih ⟨m, hwfs₁, hn1, hrkb, a2, RR ++ [LL], hshape1, hhold1,
          hcond1, hdebt1⟩ hwfst' hy' hdcov' hlat' hnext' hsq2'
    | inr z =>
        -- the landing host: the mid-state top search (the transplant row)
        obtain ⟨k₀, hholdz, _hsitz⟩ := canPlace_inr hcp
        have hk0a : k₀ ≠ a := fun hcon =>
          canPlace_inr_target_pile_ne hwfs hcp hcmem
            (by rw [← hcon]; exact hholdz)
        have hzonly := mem_faceUp_only hwfs
          (Pile.mem_of_top (pileOfTop_top hholdz).2)
        have hneak : a ≠ k₀ := fun hcon => hk0a hcon.symm
        have hzfa : z ∉ (vp.piles a).faceUp := (hzonly.1 a hneak).2
        have hzha : z ∉ (vp.piles a).hidden := (hzonly.1 a hneak).1
        have hmidz := pollutesCrash_slide_hostKeep (c := c) hwfs hk0a hholdz hzfa hzha
        have hmidk0 : (vp.setPile a (Pile.afterRunRemoved (vp.piles a)
            (below c (vp.piles a).faceUp))).piles k₀ = vp.piles k₀ :=
          setPile_afterRunRemoved_piles_ne vp a c k₀ hk0a
        have hlens : s₁
            = (vp.setPile a (Pile.afterRunRemoved (vp.piles a)
                (below c (vp.piles a).faceUp))).setPile k₀
              { vp.piles k₀ with
                  faceUp := (vp.piles k₀).faceUp
                    ++ fromCard c (vp.piles k2).faceUp } := by
          rw [hs, putRun_inr_eq hmidz, hmidk0, hak2]
        have hshape1 : (s₁.piles k₀).faceUp
            = ((vp.piles k₀).faceUp ++ RR) ++ [LL, m] := by
          rw [hlens, setPile_piles_self, hrunT]
          show (vp.piles k₀).faceUp ++ (RR ++ [LL, m])
              = ((vp.piles k₀).faceUp ++ RR) ++ [LL, m]
          rw [← List.append_assoc]
        have hshape1i : (s₁.piles k₀).faceUp
            = (((vp.piles k₀).faceUp ++ RR) ++ [LL]) ++ [m] := by
          rw [hshape1]
          exact (List.append_assoc ((vp.piles k₀).faceUp ++ RR) [LL] [m]).symm
        have hhold1 : s₁.pileOfTop m = some k₀ :=
          (pileOfTop_eq_some_iff hwfs₁).2 (by
            show lastOf (s₁.piles k₀).faceUp = some m
            rw [hshape1]
            exact pollutesCrash_top_seatTail (zt := LL) (w := m)
              ((vp.piles k₀).faceUp ++ RR))
        have hcond1 : chop (s₁.piles k₀).faceUp ≠ [] ∨
            ((s₁.piles k₀).hidden = [] ∧ m.rank = Rank.king) :=
          Or.inl (by
            show chop (s₁.piles k₀).faceUp ≠ []
            rw [hshape1]
            exact pollutesCrash_chop_seatTail (zt := LL) (w := m)
              ((vp.piles k₀).faceUp ++ RR))
        exact ih ⟨m, hwfs₁, hn1, hrkb, k₀,
          ((vp.piles k₀).faceUp ++ RR) ++ [LL], hshape1i, hhold1, hcond1,
          hdebt1⟩ hwfst' hy' hdcov' hlat' hnext' hsq2'
  · -- the departure is off the mint's seat: the seat pile reads verbatim
    have hk2a : k2 ≠ a := fun hcon => hak2 hcon.symm
    cases b with
    | inl a2 =>
        obtain ⟨hemp2, -⟩ := canPlace_inl hcp
        have ha2k2 : a2 ≠ k2 := by
          intro hcon
          rw [hcon] at hemp2
          have hfupE := ((Pile.isEmpty_eq _).mp hemp2).2
          rw [hshape2] at hfupE
          exact absurd hfupE (by simp)
        have hpilk2 : s₁.piles k2 = vp.piles k2 := by
          rw [hs, putRun_eq_inl, setPile_piles]
          show (if k2 = a2 then
              (⟨[], fromCard c (vp.piles a).faceUp⟩ : Pile)
            else (vp.setPile a (Pile.afterRunRemoved (vp.piles a)
                (below c (vp.piles a).faceUp))).piles k2) = vp.piles k2
          rw [ite_eq_right (fun hcon => ha2k2 hcon.symm)]
          rw [setPile_afterRunRemoved_piles_ne vp a c k2 hk2a]
        have hshape1 : (s₁.piles k2).faceUp = se2 ++ [m] := by
          rw [hpilk2]
          exact hshape2
        have hhold1 : s₁.pileOfTop m = some k2 :=
          (pileOfTop_eq_some_iff hwfs₁).2 (by
            show (s₁.piles k2).top = some m
            rw [hpilk2]
            exact htop2)
        have hcond1 : chop (s₁.piles k2).faceUp ≠ [] ∨
            ((s₁.piles k2).hidden = [] ∧ m.rank = Rank.king) := by
          rw [hpilk2]
          exact hcond2
        exact ih ⟨m, hwfs₁, hn1, hrkb, k2, se2, hshape1, hhold1, hcond1,
          hdebt1⟩ hwfst' hy' hdcov' hlat' hnext' hsq2'
    | inr z =>
        obtain ⟨k₀, hholdz, _hsitz⟩ := canPlace_inr hcp
        have hk0a : k₀ ≠ a := fun hcon =>
          canPlace_inr_target_pile_ne hwfs hcp hcmem
            (by rw [← hcon]; exact hholdz)
        have hzW : z ≠ m := fun hcon => hbnw (congrArg Sum.inr hcon)
        have hk0k2 : k₀ ≠ k2 := by
          intro hcon
          rw [hcon] at hholdz
          exact hzW (Option.some.inj
            ((pileOfTop_top hholdz).2.symm.trans htop2))
        have hzonly := mem_faceUp_only hwfs
          (Pile.mem_of_top (pileOfTop_top hholdz).2)
        have hneak : a ≠ k₀ := fun hcon => hk0a hcon.symm
        have hzfa : z ∉ (vp.piles a).faceUp := (hzonly.1 a hneak).2
        have hzha : z ∉ (vp.piles a).hidden := (hzonly.1 a hneak).1
        have hmidz := pollutesCrash_slide_hostKeep (c := c) hwfs hk0a hholdz hzfa hzha
        have hmidk0 : (vp.setPile a (Pile.afterRunRemoved (vp.piles a)
            (below c (vp.piles a).faceUp))).piles k₀ = vp.piles k₀ :=
          setPile_afterRunRemoved_piles_ne vp a c k₀ hk0a
        have hlens : s₁
            = (vp.setPile a (Pile.afterRunRemoved (vp.piles a)
                (below c (vp.piles a).faceUp))).setPile k₀
              { vp.piles k₀ with
                  faceUp := (vp.piles k₀).faceUp
                    ++ fromCard c (vp.piles a).faceUp } := by
          rw [hs, putRun_inr_eq hmidz, hmidk0]
        have hpilk2 : s₁.piles k2 = vp.piles k2 := by
          rw [hlens, setPile_piles]
          show (if k2 = k₀ then
              { vp.piles k₀ with
                  faceUp := (vp.piles k₀).faceUp
                    ++ fromCard c (vp.piles a).faceUp }
            else (vp.setPile a (Pile.afterRunRemoved (vp.piles a)
                (below c (vp.piles a).faceUp))).piles k2) = vp.piles k2
          rw [setPile_afterRunRemoved_piles_ne vp a c k2 hk2a]
          rw [ite_eq_right (fun hcon => hk0k2 hcon.symm)]
        have hshape1 : (s₁.piles k2).faceUp = se2 ++ [m] := by
          rw [hpilk2]
          exact hshape2
        have hhold1 : s₁.pileOfTop m = some k2 :=
          (pileOfTop_eq_some_iff hwfs₁).2 (by
            show (s₁.piles k2).top = some m
            rw [hpilk2]
            exact htop2)
        have hcond1 : chop (s₁.piles k2).faceUp ≠ [] ∨
            ((s₁.piles k2).hidden = [] ∧ m.rank = Rank.king) := by
          rw [hpilk2]
          exact hcond2
        exact ih ⟨m, hwfs₁, hn1, hrkb, k2, se2, hshape1, hhold1, hcond1,
          hdebt1⟩ hwfst' hy' hdcov' hlat' hnext' hsq2'

/-- **The seed twin check** (the covered-fork audit's compiled half,
zero-sorry): the seed landlord is NEVER the mint's twin — the rank
pin alone forbids it (the landlord rides one above the mint; the twin
shares the mint's own rank).  The color route agrees (`hzcol` +
`Suit.color_twin`: the landlord is family-colored, the mint's twin
keeps the mint's family-opposed color).  This stamps the
covered-mint seed-check: the landlord rows can never double as the
twin premise — the package seats no twin anywhere. -/
private theorem pollutesCrash_seedTwin_notLandlord {w zt : Card}
    (hzrk : zt.rank.toIdx = w.rank.toIdx + 1) : zt ≠ w.twin := by
  intro hcon
  rw [hcon, Card.twin_rank w] at hzrk
  omega

/-- The mover dispatcher's residual-fork predicate (the RE-MINT
restatement's shrunken residue): the TWO residual literals of ONE
family — the mint is FOUNDED or COVERED by the leg with no pinned
successor mid-walk: the wash-back raise (`tabToFound m₀`) and the
run-onto-mint burial slide (`tabToTab c (Sum.inr m₀)`, `c ≠ m₀`).
The third literal (the z-onto-mint pull burial — the pop lands its
card directly onto the seat's anchor) still routes here but CLOSES
in the dispatcher's open arm: the popped card re-mints over the
covered mint at its own bracket.  Every other sub-fork closes in
the dispatcher: the mint-alone
slides (king escape by the rank bound; ANY landing re-pairs the light
seat — the landlord roams), the same-suit pull (the bracket re-mint to
the popped card at its own index), the draw/waste legs, and all
stranger-suit survivals. -/
private def pollutesCrash_rhoOpen (m : Move) (st : State) (u : Card)
    (k : Anchor) : Bool :=
  match m with
  | Move.tabToFound c => decide (c = u)
  | Move.tabToTab c b =>
      decide (c ≠ u) &&
      match b with
      | Sum.inl _ => false
      | Sum.inr z => decide (z = u)
  | Move.foundToTab c b =>
      match b with
      | Sum.inl _ => false
      | Sum.inr z =>
          decide ((st.setFound c.suit (chop (st.found c.suit))).pileOfTop z
            = some k)
  | _ => false

/-- **THE MOVER DISPATCH — the ρ-tail's per-leg assembly over the two
landed movers.**  The draw leg and every deferred pull fork that the
upstream dispatchers route here now close IN-BODY: the discovery of
this increment is the license chain's root read
(`pollutesCrash_canRaiseS_nextUp`): every `CanRaiseS` license reads
`nextUp` at its own firing state (the `via` mantle's slides write no
foundation), so every leg that preserves the mint's suit's found row and
seating re-arms the carry's license as a fresh `now`-grade witness —
the via-grade transport (the residue's former headline, and ledger
item 4's draw-via sub-split with the §1 squares) is thereby DEAD: not
needed, on any leg.  The per-leg dispatch:

1. THE DRAW LEG closes in-body: found and piles boards ride verbatim,
   the license and seat regenerate.
2. THE WASTE MOVERS die by the journey census (unchanged).
3. THE RAISE LEG (`tabToFound c`) closes at `c ≠ m₀` over
   `pollutesCrash_rhoRaise` (the ∃-kit's own mint); the wash-back
   `tabToFound m₀` stays.
4. THE SLIDE LEG (`tabToTab c b`) closes over `pollutesCrash_rhoSlide`
   (the departure/landing two-site lens) at `c ≠ m₀ ∧ b ≠ Sum.inr m₀`.
   THE MINT-ALONE slide (`tabToTab m₀ _`) closes in-body at ANY
   landing: the empty-seat escape dies by the mint's rank-bound king
   ban, the self landing by the fit's own rank clause, and every
   `inr` host re-pairs the kit at the landing pile (the host
   transplant row `pollutesCrash_slide_hostKeep`, the singleton-run
   chop lens) — twin landing included
   (`pollutesCrash_twinLanding_color`'s shape answer: the residual
   landing card is the landlord's twin exactly).  The BURIAL SLIDE —
   a stranger run (`c ≠ m₀`) landing ON the mint's seat (`b =
   Sum.inr m₀`) — is the residue: the mint survives covered (its
   `nextUp` intact, the slide writes no foundation), but no seat-top
   mint remains to re-arm the carry; the honest residue is the
   covered-mint license (`canRaiseS_free`'s twin premise) plus the
   census pricing, both at the composition level
   (`pollutesCrash_burialSlide_pins` and
   `pollutesCrash_twinLanding_color` bank the reader data).
5. THE PULL LEG (`foundToTab c b`): the same-suit pop RE-MINTS to the
   popped card in-body (`pollutesCrash_pull_bracket` +
   `pollutesCrash_foundTop_rank` + `pollutesCrash_landing_live` —
   the ∃-kit admits the mint-swap; every `inl`/`inr` landing re-pairs
   at the popped card's own landing).  The stranger-suit pop closes
   at every off-seat host — the `inl` self-anchor wipe dies by the
   empty-pile guard row (the seat pile holds the mint face-up), the
   vanished `inr` landing keeps the piles board wholesale, and an
   off-seat host rides the two inr survival rows.  THE Z-ONTO-MINT
   PULL BURIAL (the mid-state seat read pins the landing pile to the
   mint's own seat) closes the same way: the popped card covers the
   mint, lands next-up-live at its own bracket, one rank under the
   mint by the landing fit — the census prices the pop bracket.

The residues are enumerated in `pollutesCrash_rhoOpen` — the single
`sorry` sits under TWO literal forks, each priced to its named
MISSING DATUM (audited absent at mover, composition, and hpkg head
alike): the WASH-BACK RAISE (the founded mint — its successor is
pinned next-up-live at the new bracket in-body; the missing data:
the successor's PILE-TOP SEAT plus the +3 rank gap) and the
COVERED-MINT BURIAL SLIDE (the stranger run landing on the mint's
seat — every `canRaiseS_free` input closes at the covered pile but
ONE; the missing datum: the mid-walk mint's TWIN's pile-top seat).
Every other sub-case is closed.  In every closed leg the finite
prefix cannot service the debts without minting the terminal card
at a barred epoch — the third live card that
`pollutesCrash_saturation` bans. -/
private theorem pollutesCrash_rhoMover {x y d w zt : Card}
    {play π : List Move}
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hdcol : d.suit.color ≠ y.suit.color)
    (hzrk : zt.rank.toIdx = w.rank.toIdx + 1)
    (hzcol : zt.suit.color = y.suit.color)
    (hrk : w.rank.toIdx + 1 ≤ d.rank.toIdx)
    (hwne : w ≠ y ∧ w ≠ y.twin)
    (hsq3 : raisesOf play d.suit + 2 ≤ pullsOf play d.suit)
    (hpc1 : raisesOf play y.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.suit)
    (hpc2 : raisesOf play y.twin.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.twin.suit)
    (hpid : raisesOf π d.suit + (d.rank.toIdx - w.rank.toIdx)
      ≤ pullsOf π d.suit)
    {vp s₁ sth : State} {m : Move} {m₀ : Card}
    (hw : w.suit = d.suit)
    (hwfs : vp.WF)
    (hn : vp.nextUp m₀ = true)
    (hrkb : m₀.rank.toIdx + 2 ≤ y.rank.toIdx)
    (k2 : Anchor) (se2 : List Card)
    (hshape2 : (vp.piles k2).faceUp = se2 ++ [m₀])
    (hhold2 : vp.pileOfTop m₀ = some k2)
    (hcond2 : chop (vp.piles k2).faceUp ≠ [] ∨
      ((vp.piles k2).hidden = [] ∧ m₀.rank = Rank.king))
    (hdebt : ∃ ccRA ccPD : Nat, rungAt vp d.suit + ccPD
      = w.rank.toIdx + ccRA)
    (hwfst' : sth.WF)
    (hy' : ForkWitness sth y)
    (hdcov' : ∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
      sth.pileOfTop d = some cc)
    (hlat' : ∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin)
    (hnext' : sth.nextUp d = false)
    (hsq2' : rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1)
    (hwleg : reversibleAtW vp m)
    (hstep : State.step vp m = some s₁)
    (harch : ∃ (o : State), o.WF ∧
      d.rank.toIdx + 1 ≤ rungAt o d.suit ∧
      ∃ (pf : List Move), ShufflePlayW o pf sth)
    (ihWide : ((∃ m₀ : Card, s₁.WF ∧ s₁.nextUp m₀ = true ∧
        m₀.rank.toIdx + 2 ≤ y.rank.toIdx ∧
        ∃ ke se, (s₁.piles ke).faceUp = se ++ [m₀] ∧
          s₁.pileOfTop m₀ = some ke ∧
          (chop (s₁.piles ke).faceUp ≠ [] ∨
            ((s₁.piles ke).hidden = [] ∧ m₀.rank = Rank.king)) ∧
        ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD
          = w.rank.toIdx + ccRA) ∨
       (∃ m₀ : Card, s₁.WF ∧ m₀.rank.toIdx + 2 ≤ y.rank.toIdx ∧
        ∃ PRE STOCK : List Card, s₁.found m₀.suit = PRE ++ [m₀] ++ STOCK ∧
          PRE.length = m₀.rank.toIdx ∧
        ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD
          = w.rank.toIdx + ccRA)) →
      sth.WF → ForkWitness sth y →
      (∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
        sth.pileOfTop d = some cc) →
      (∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin) →
      sth.nextUp d = false →
      rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1 →
      (∃ (o : State), o.WF ∧
        d.rank.toIdx + 1 ≤ rungAt o d.suit ∧
        ∃ (pf : List Move), ShufflePlayW o pf sth) →
      ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin) :
    ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin := by
  have hwfs₁ : s₁.WF := step_wf hwfs hstep
  have htop2 : vp.topOf k2 = some m₀ := (pileOfTop_top hhold2).2
  obtain ⟨ccRA, ccPD, hdE⟩ := hdebt
  -- the seat-grade view of the widened ih: every arm that re-pairs within
  -- the light kit's own shape consumes this wrapper verbatim; the wash-back
  -- arm emits the founded form through ihWide itself
  have ih : (∃ m₁ : Card, s₁.WF ∧ s₁.nextUp m₁ = true ∧
      m₁.rank.toIdx + 2 ≤ y.rank.toIdx ∧
      ∃ ke se, (s₁.piles ke).faceUp = se ++ [m₁] ∧
        s₁.pileOfTop m₁ = some ke ∧
        (chop (s₁.piles ke).faceUp ≠ [] ∨
          ((s₁.piles ke).hidden = [] ∧ m₁.rank = Rank.king)) ∧
      ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD
        = w.rank.toIdx + ccRA) →
    sth.WF → ForkWitness sth y →
    (∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
      sth.pileOfTop d = some cc) →
    (∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin) →
    sth.nextUp d = false →
    rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1 →
    ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin :=
    fun hk hwfst' hy' hdcov' hlat' hnext' hsq2' =>
      ihWide (Or.inl hk) hwfst' hy' hdcov' hlat' hnext' hsq2' harch
  cases hopenTF : pollutesCrash_rhoOpen m vp m₀ k2 with
  | true =>
      cases m with
      | draw =>
          -- the open guard reads false on the draw leg (constructor clash)
          exfalso
          exact Bool.noConfusion
            (hopenTF.symm.trans (rfl (a := false)))
      | wasteToFound c =>
          exfalso
          exact Bool.noConfusion
            (hopenTF.symm.trans (rfl (a := false)))
      | wasteToTab c b =>
          exfalso
          exact Bool.noConfusion
            (hopenTF.symm.trans (rfl (a := false)))
      | tabToFound c =>
          -- THE WASH-BACK RAISE (rhoOpen literal `decide (c = m₀)`): the
          -- carry's own mint founding — the guard's nose evidence `hn`
          -- is exactly the founding license.  THE RE-FOUNDING'S OWN
          -- POSITION, PINNED IN-BODY (the compiled pricing): the mint
          -- sits exactly at its own bracket at vp (the pre-rung pin
          -- `hrungM`, off `hn`); the founding stacks it onto its own
          -- suit row (the seat pile chopped below), landing the rung
          -- ONE ABOVE its index at s₁ (`hbrkS`, the landing bracket);
          -- and the walk-debt counters re-price it mechanically
          -- (`pollutesCrash_tailDebt_raise` constructible at need).
          -- Hence the mint's own-suit SUCCESSOR — the next card of
          -- the mint's suit, one rank up — is NEXT-UP-LIVE at its own
          -- bracket at s₁ (`hnlive`, the successor pin).  THE MISSING
          -- DATA (priced, not grouted): the successor's PILE-TOP SEAT
          -- shape (`∃ ke se, (s₁.piles ke).faceUp = se ++ [c*] ∧
          -- s₁.pileOfTop c* = some ke ∧ (chop ≠ [] ∨ …)`) plus the
          -- deeper rank gap (c*.idx + 3 ≤ y's index) — together they
          -- would re-arm the carry at the successor and run `ih`; each
          -- is absent at the mover, at the composition, and in the
          -- hpkg head likewise (the crossed-state rows there pin only
          -- the SEED mint's landlord and brackets; the census
          -- compositions price the founding's bracket, never the
          -- successor's seat): the FOUNDED-MINT residue, the named
          -- fork of the HOLD audit.
          -- ENDPOINT-CENSUS AUDIT (the two-exit frame, priced): the
          -- st₂ squeeze pins ALREADY ride every level (`hsq2'` is a
          -- standing premise — nothing to re-thread), and the
          -- walk-debt equation re-prices the founding mechanically
          -- (`tailDebt_raise` fires at need) — but NEITHER exit
          -- compiles body-only: (i) the re-exhume pull sits at a
          -- LATER leg, and every intermediate leg's mover call
          -- demands a seat-kit FROM THIS ARM'S LANDING — the walk
          -- breaks at the founding leg itself (consuming the
          -- re-exhume requires a FOUNDED-form carry, i.e. changing
          -- the ∃-kit's own shape — a statement-level object); (ii)
          -- the raised rung (m₀.ridx + 1) meets the squeeze cap
          -- (d.ridx − 1) CONSISTENTLY across the rank gap's normal
          -- range (m₀.ridx ≤ d.ridx − 2) — only the equality edge
          -- (m₀.ridx = d.ridx − 1, same-suit) squeezes, and its
          -- 'no-later-pull' half is a future-quantifier the mover's
          -- data does not carry (`ih` abstracts the remaining tail
          -- wholesale).  VERDICT: both exits priced OUT of the
          -- mover; the residue stands on the missing successor-seat.
          -- WIDENING STAMP (the founded-form drill, banked for the
          -- re-thread): the widened carry's FOUNDED arm —
          -- `∃ PRE STACK, s.found m₀.suit = PRE ++ [m₀] ++ STACK`
          -- with the position pin `PRE.length = m₀.rank.toIdx` — is
          -- fully serviced by the five banked bricks
          -- (`foundCard_notInPile`/`_notPileTop`: the tabo ветвь
          -- re-found-guard and the cover-as-base guard die by the
          -- zone census; `foundRaise_stackGrow`: the same-suit raise
          -- grows the stack; `foundPull_stackShrink`: the buried
          -- same-suit pop chops the stack alone; `foundTop_atOwn`:
          -- the re-exhume detector with the founding-bracket read).
          -- RE-THREAD POSITIONS: (1) rhoMover's seat-params split
          -- into the disjunction, wash-back arm emitting the founded
          -- form; (2) rhoLeg's explode-and-route adds the founded
          -- case to a new mover row; (3) rhoTail's statement widens
          -- its ∃-kit, nil-branch splitting saturation-gate |
          -- founded-arrival.  THE NIL CENSUS (priced): the fondée
          -- omega — hsq2' against the founded rung — closes ONLY
          -- the d-suit EDGE (m₀.ridx = d.ridx − 1); stranger-suit
          -- and sub-cap d-suit arrivals are consistent termini, so
          -- the founded-arrival arm waits on the BELOW core's
          -- successor-seat (the design line's post-widening content,
          -- Orig\OrphanSeat — not yet in hand).  Ledger: TWO sorry
          -- forks here (wash-back + covered), both priced; census
          -- sorry surfaces only at the re-thread.
          -- ATTACK-BRIEF VERDICT (verified in-context, no grouting):
          -- the Fork-A archaeology (successor c' = (d.suit,
          -- m₀.ridx+1) founded at st₁ via `rung_found_prefix` —
          -- banked at MacroInternal:738 — exodus over [st₁..s₁],
          -- landing-seed, Below-transport) engages ONLY when
          -- m₀.suit = d.suit, and leaves four named gaps: (A1) the
          -- st₁-era pins (hdfound/hsq1) and the prefix journey
          -- exist only at the composition head — the mover's frozen
          -- signature holds neither; delivering the start-pin to
          -- the arm is a premise-thread through all three rows
          -- (the held re-thread's second interlock); (A2) Below
          -- transports POSITION, not the top-shape — no census bans
          -- mid-suffix re-covers of c', so the kit's TOP-form (R =
          -- []) at s₁ stays missing even with the transport; (A3)
          -- STRANGER-suit m₀ wash-backs (the z-onto re-mint's own
          -- output) have no st₁ archaeology at all — a full strike
          -- must also close them; (A4) the edge subcase c' = d does
          -- not contradict hdcover (a mid-walk exhumed d re-seats
          -- by st₂ consistently) and d-as-kit-mint fails the rank
          -- clause outright (d.ridx + 2 = y.ridx + 1).  Fork A
          -- stays held on A1–A4; the archaelogy's usable core (the
          -- found_prefix membership at the composition head) is
          -- stamped for the next design line.
          -- DRILL UPDATE (banked): the re-exhume's landing kit is now a
          -- COMPILED constructor — `pollutesCrash_reseat_pop` (the pop
          -- of the mint at its founding bracket lands it next-up-live
          -- and seat-top in the light kit's own shape, either the bare
          -- king line or the fit's host pile) — the widened mover's
          -- switch-back arm is pure assembly.  RE-PRICING INVENTORY
          -- (the coordinator's supplement): the successor-seat ride is
          -- `pull_bracket` + `landing_live` + `reseat_pop` with the
          -- rank gap closing by `omega` over the priced census, once
          -- the `Below_stable` positional core (Orig\OrphanSeat, the
          -- seat line) lands by name; the nil-founded census re-prices
          -- against the same core then.
          -- CORE-RE-PRICING (against the LANDED signatures, OrphanSeat:
          -- `Below_stable : hwf → ShufflePlayW → hnk-nonking →
          --  (d ∈ st.found d.suit ∨ ∃ z, Below st d z) →
          --  (d ∈ u.found d.suit ∨ ∃ z, Below u d z)`): the core
          -- transports POSITION ONLY.  The nil-founded census's
          -- MISSING DATUM (named, no grouting): the endpoint BRACKET
          -- read — `nextUp sth (the transported card)`, i.e.
          -- `rungAt sth (its suit) = its index` — absent from the
          -- transported disjunct on both sides (the R = [] Below arm
          -- tops the card but reads no bracket; the R ≠ [] arm
          -- re-adds the twin-tops); the founded-arm disjunct stays
          -- CONSISTENT for sub-cap d-suit mints (the twice-audited
          -- edge analysis).  The hstart side is now BANKED
          -- (`pollutesCrash_seedBelow_start`: the hpkg seed shape is
          -- `Below v w zt` verbatim) but its thread starts at the
          -- descent caller — rhoTail's frozen premises do not carry
          -- the [zt, w] shape per-instance.  The three statement
          -- edits stay interlocked on this datum: the widened
          -- rhoTail would otherwise mint the census sorry in place
          -- of the mover's.
          have hcq : c = m₀ := by
            simp only [pollutesCrash_rhoOpen] at hopenTF
            exact of_decide_eq_true hopenTF
          rw [hcq] at hstep
          -- the pre-rung pin: the mint's own bracket at the firing state
          have hrungM : rungAt vp m₀.suit = m₀.rank.toIdx :=
            (show m₀.rank.toIdx = (vp.found m₀.suit).length from
              of_decide_eq_true hn).symm
          obtain ⟨hnx, a, hp, hs₁⟩ := step_tabToFound_inv hstep
          -- the landing bracket: the founding stacks the mint onto its
          -- own suit row — the rung lands one above its index
          have hbrkS : rungAt s₁ m₀.suit = m₀.rank.toIdx + 1 := by
            show (s₁.found m₀.suit).length = m₀.rank.toIdx + 1
            rw [(tabToFound_found_trio hs₁).1, List.length_append,
              List.length_singleton]
            have hlen : (vp.found m₀.suit).length = m₀.rank.toIdx := hrungM
            omega
          -- the successor pin: the mint's own-suit next card is
          -- next-up-live at its own bracket at the landing
          have hidx13 : m₀.rank.toIdx + 1 < 13 := by
            have h13 := Rank.toIdx_lt m₀.rank
            have hy13 := Rank.toIdx_lt y.rank
            omega
          have hcstar : (Card.mk m₀.suit (lockRk (m₀.rank.toIdx + 1))).rank.toIdx
              = m₀.rank.toIdx + 1 :=
            show (lockRk (m₀.rank.toIdx + 1)).toIdx = m₀.rank.toIdx + 1 from
              lockRk_toIdx _ hidx13
          have hrungstar : rungAt s₁ (Card.mk m₀.suit
              (lockRk (m₀.rank.toIdx + 1))).suit = (Card.mk m₀.suit
              (lockRk (m₀.rank.toIdx + 1))).rank.toIdx := by
            show rungAt s₁ m₀.suit = (Card.mk m₀.suit
                (lockRk (m₀.rank.toIdx + 1))).rank.toIdx
            rw [hcstar]
            exact hbrkS
          have hnlive : s₁.nextUp (Card.mk m₀.suit (lockRk (m₀.rank.toIdx + 1)))
              = true :=
            pollutesCrash_landing_live hrungstar
          -- THE WASH-BACK'S FOUNDED-FORM EMISSION (the re-thread's first
          -- live instance; the stamp's pure assembly): the mint rides
          -- its own suit's row at its own bracket — PRE the firing row
          -- (its length the mint's index, the pre-rung pin `hrungM`),
          -- STOCK empty (the founding snocs at the top) — and the debt
          -- re-prices by the raise arm.  The successor pin `hnlive`
          -- stays as census evidence for the nil archaeology cell (the
          -- widened nil census's stamped content), not the kit's data.
          have hftrio : s₁.found m₀.suit = vp.found m₀.suit ++ [m₀] :=
            (tabToFound_found_trio hs₁).1
          exact ihWide (Or.inr ⟨m₀, hwfs₁, hrkb, vp.found m₀.suit, [],
            by rw [List.append_nil]; exact hftrio,
            hrungM,
            pollutesCrash_tailDebt_raise hstep ⟨ccRA, ccPD, hdE⟩⟩)
            hwfst' hy' hdcov' hlat' hnext' hsq2' harch
      | tabToTab c b =>
          -- THE COVERED-MINT BURIAL (rhoOpen literal `c ≠ m₀ ∧ z = m₀`) —
          -- THE FLAT-IFF ATTEMPT, COMPILED TO ITS GAP: every input of
          -- `canRaiseS_iff`'s covered side is rebuilt below (the mint's
          -- surviving `nextUp`, the `bs ++ m₀ :: runCover` seat profile
          -- at the guard's pinned pile, the seat clause over the kit's
          -- own chop discipline, the covering run's own nonempty pin).
          cases b with
          | inl a₂ =>
              -- the open guard reads false on the empty-seat landing
              exfalso
              simp only [pollutesCrash_rhoOpen, Bool.and_false] at hopenTF
              exact Bool.noConfusion hopenTF.symm
          | inr z =>
              have hunf : pollutesCrash_rhoOpen (Move.tabToTab c (Sum.inr z))
                  vp m₀ k2 = (decide (c ≠ m₀) && decide (z = m₀)) := rfl
              rw [hunf, Bool.and_eq_true] at hopenTF
              obtain ⟨hd1, hd2⟩ := hopenTF
              have hcne : c ≠ m₀ := of_decide_eq_true hd1
              have hz : z = m₀ := of_decide_eq_true hd2
              rw [hz] at hstep
              obtain ⟨a, hhhold, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
              obtain ⟨k₀, hholdz, hsitz⟩ := canPlace_inr hcp
              have hk₀ : k₀ = k2 := Option.some.inj (hholdz.symm.trans hhold2)
              rw [hk₀] at hholdz
              -- the landing fit: the cover head sits directly on the mint
              obtain ⟨hrkz, hcolz⟩ := (canSitOn_eq c m₀).mp hsitz
              -- the departure is a stranger pile (the self-safety: else
              -- the run from c sweeps the mint into its own landing
              -- target, barred by the inr placement guard)
              have hm₀mem : m₀ ∈ (vp.piles k2).faceUp := by
                rw [hshape2]
                exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
              have hcmem : c ∈ (vp.piles a).faceUp := pileHolding_mem hhhold
              have hdep : a ≠ k2 := by
                intro hcon
                have hcmemK2 : c ∈ (vp.piles k2).faceUp := by
                  rw [← hcon]; exact hcmem
                have hcorm : c ∈ se2 ∨ c = m₀ := by
                  have hthis := hcmemK2
                  rw [hshape2] at hthis
                  rcases List.mem_append.mp hthis with h1 | h2
                  · exact Or.inl h1
                  · exact Or.inr (List.mem_singleton.mp h2)
                rcases hcorm with hcse | hcm
                · have hwin : m₀ ∈ fromCard c (vp.piles k2).faceUp := by
                    rw [hshape2]
                    exact pollutesCrash_mem_fromCard_snoc hcne se2 hcse
                  have hoff := canPlace_inr_target_off_run hwfs hcp hcmemK2
                  exact absurd hwin hoff
                · exact hcne hcm
              -- the mid-state transplant: the mint's seat read rides the
              -- departure write verbatim
              have hzfa : m₀ ∉ (vp.piles a).faceUp :=
                (mem_faceUp_unique hwfs hm₀mem) a hdep |>.1
              have hzha : m₀ ∉ (vp.piles a).hidden :=
                (mem_faceUp_unique hwfs hm₀mem) a hdep |>.2.1
              have hmidpot := pollutesCrash_slide_hostKeep (c := c) (z := m₀)
                (a := a) (k₀ := k2) hwfs (fun hcon => hdep hcon.symm) hholdz
                hzfa hzha
              have hmidk2 : (vp.setPile a (Pile.afterRunRemoved (vp.piles a)
                  (below c (vp.piles a).faceUp))).piles k2 = vp.piles k2 :=
                setPile_afterRunRemoved_piles_ne vp a c k2
                  (fun hcon => hdep hcon.symm)
              -- the landing profile: the cover's arrival appends the run
              -- ON the mint's seat pile
              have hshp : (s₁.piles k2).faceUp
                  = (vp.piles k2).faceUp ++ fromCard c (vp.piles a).faceUp := by
                rw [hs, putRun_inr_eq hmidpot, setPile_piles_self, hmidk2]
              -- nextUp survives the cover (the slide writes no found row)
              have hn1 : s₁.nextUp m₀ = true :=
                (nextUp_congr m₀ (pollutesCrash_slide_foundEq hstep)).trans hn
              -- THE FLAT-IFF SHAPE: `(s₁.piles k2).faceUp = se2 ++ m₀ ::
              -- runCover` — the iff's `bs ++ c :: run` at the mint
              have hshape' : (s₁.piles k2).faceUp
                  = se2 ++ m₀ :: fromCard c (vp.piles a).faceUp := by
                rw [hshp, hshape2]
                exact List.append_assoc se2 [m₀]
                  (fromCard c (vp.piles a).faceUp)
              -- the seat clause: the kit's chop discipline transfers
              -- (the landing's hidden rides its pile record verbatim)
              have hhid : (s₁.piles k2).hidden = (vp.piles k2).hidden := by
                rw [hs, putRun_inr_eq hmidpot, setPile_piles_self, hmidk2]
              have hseat' : se2 ≠ [] ∨
                  ((s₁.piles k2).hidden = [] ∧ m₀.rank = Rank.king) := by
                rcases hcond2 with hse | hhk
                · refine Or.inl ?_
                  rw [hshape2] at hse
                  rw [chop_snoc] at hse
                  exact hse
                · refine Or.inr ⟨?_, hhk.2⟩
                  rw [hhid]
                  exact hhk.1
              -- THE TWIN ARM, TYPED AT THE TERMINUS: `canRaiseS_iff`'s
              -- last conjunct on this input reads
              --   `runCover = [] ∨ s₁.pileOfTop m₀.twin ≠ none`
              -- with `hfr : runCover ≠ []` the LEFT arm is refuted by
              -- the step guard's own run pin — the flat route demands
              -- EXACTLY the twin-top read (`canRaiseS_iff`'s covered
              -- branch consumes it through `canRaiseS_free`, and its
              -- own sufficiency refutes the empty-run arm), the datum
              -- audited absent package-wide (the seed-check stamp:
              -- `pollutesCrash_seedTwin_notLandlord` and the
              -- crossed-state rows).  BEYOND it, even a granted license
              -- would land at s₁ — the wrong state — while the carry's
              -- re-pair needs a seat-TOP mint (`ih`'s kit shape): the
              -- covered-mint residue, priced on both halves, no
              -- grouting.
              -- RE-PRICING INVENTORY (the coordinator's supplement): the
              -- twin-top read's future ride is
              -- `journey_raise_seatUnfounded` (Orig\ForkStateUniqGate:480:
              -- the seat card extracted through runOK alone, with its
              -- rank-(r+1)/opposite-color/unfounded data) combined with
              -- the landed `pollutesCrash_twinLanding_color` (the
              -- residual landing card IS the landlord's twin) — the
              -- twin's pile-top datum becomes an omega-composable
              -- rank/color read once the `Below_stable` positional
              -- core (Orig\OrphanSeat) lands by name.  This fork
              -- re-prices against it then; no grouting before.
              -- CORE-RE-PRICING (against the LANDED signatures): the
              -- twin transpose MISSES its datum, named: NO row pins
              -- the mid-walk mint's twin (founded-or-Below) at ANY
              -- journey point — `journey_raise_seatUnfounded`'s seat
              -- card is rank-(r+1) OPPOSITE color (the landlord
              -- shape: it can never BE the twin, who shares the
              -- mint's own color), and `twinLanding_color` pins the
              -- residual landing card as the LANDLORD's twin
              -- (`zt.twin` — a different card once the mint roams
              -- off the seed); `Below_stable` transports only cards
              -- already pinned at a start.  The twin has no start
              -- pin anywhere in the package: the fork keeps its
              -- typed gap until the seat line pins one.
              -- ATTACK-BRIEF VERDICT (verified in-context, no
              -- grouting): the claimed start-pin "breakthrough" is
              -- UNSOUND as stated — `Card.twin` is the SAME-COLOR
              -- other suit (Twin.lean:33 with `Suit.color_twin`
              -- simp-banked at Basic.lean:42), so m₀.twin carries
              -- m₀'s own color: for a d-suited mint (the brief's
              -- own assumption m₀ = (d.suit, k)) the twin is
              -- OFF-family-colored and `pair_lowFamily_founded`'s
              -- color premise `c.suit.color = x.suit.color`
              -- (PairConfine:263) FAILS — the row does not pin it.
              -- The salvageable half: for a FAMILY-colored mint
              -- (the stranger re-mint subcase) the pin DOES fire
              -- (rank via m₀.ridx + 2 ≤ y.ridx < x.ridx) — the
              -- color-complement of Fork A.  The twin-TOP-at-s1
              -- question, priced on the brief's three roads:
              -- (a) the x-family re-cover census is not banked
              -- (the walks' per-suit mid-walk accounting has no
              -- twin-suit row); (b) dying-mint re-mint dies at the
              -- SAME bracket datum (cover-run cards carry none —
              -- the original twice-audited pricing; the
              -- stratum-down successor misses the rank clause:
              -- c''.rdx + 2 = m₀.ridx + 3 vs y's gap of m₀.ridx +
              -- 2); (c) therefore the named datum STANDS: the
              -- twin's TOP-shape at the cover leg's state, now
              -- with the start-pin's color case-split priced in
              -- (d-mint: no pin; family-mint: pin, no top read).
              -- THE ORIGIN-ANCHORED CRASH closes the stand (the
              -- archaeology engine's own read, mint-suit-agnostic):
              -- the d-suit hot card at the terminus's own rung was
              -- founded at the origin (strictly under the hsq1-grade
              -- anchor by the two-end squeeze) and is hot at the
              -- terminus, so `pollutesCrash_terminalHot_Below` seats
              -- it BELOW a live neighbor; the neighbor is
              -- family-colored by the seat fit's color conservation
              -- and ranked strictly under the fork's pinned family
              -- rungs, hence foundation-resident — contradicting the
              -- Below read's own face-up membership
              -- (`mem_found_unique`).  The twin premise never enters;
              -- the fork's saturation crashes the census.
              obtain ⟨o, hwfo, hsq1o, pf, hshpo⟩ := harch
              exact pollutesCrash_originCrash hwfst' hy' hd hdcol hsq2'
                hwfo hsq1o ⟨pf, hshpo⟩
      | foundToTab c b =>
          -- THE Z-ONTO-MINT PULL BURIAL (rhoOpen literal: the mid-state
          -- seat read pins z's host to the mint's seat pile): the popped
          -- card lands DIRECTLY ON z's pile.  The kit RE-MINTS TO THE
          -- POPPED CARD — the pull-bracket drops c's own suit rung to
          -- its index (landing-live), the landing fit pins c one rank
          -- under the mint (the rank bound arms), and the landing lens
          -- appends c at the guard's own pinned pile k2 — the covered
          -- mint rides under it, the seat's chop clause live.
          cases b with
          | inl a₂ =>
              exfalso
              exact Bool.noConfusion
                (hopenTF.symm.trans (rfl (a := false)))
          | inr z =>
              have hmidpot : (vp.setFound c.suit (chop (vp.found c.suit))).pileOfTop z
                  = some k2 := by
                simp only [pollutesCrash_rhoOpen] at hopenTF
                exact of_decide_eq_true hopenTF
              obtain ⟨c₀, htop0, hceq, hcp, hs⟩ := step_foundToTab_inv hstep
              rw [hceq] at htop0
              obtain ⟨k₀', hholdz, hsitz⟩ := canPlace_inr hcp
              -- the mid-state piles ride vp's board: z's vp-host IS the
              -- mint's seat pile
              have hk₀'k2 : k₀' = k2 :=
                Option.some.inj
                  ((hholdz.symm.trans
                    (pollutesCrash_pileOfTop_congr z
                      (setFound_piles vp c.suit (chop (vp.found c.suit)))).symm).trans
                    hmidpot)
              rw [hk₀'k2] at hholdz
              have hz : z = m₀ :=
                Option.some.inj ((pileOfTop_top hholdz).2.symm.trans htop2)
              -- the landing fit: c sits directly on the mint, one rank
              -- under it
              obtain ⟨hrkz, -⟩ := (canSitOn_eq c z).mp hsitz
              rw [hz] at hrkz
              have hrkb' : c.rank.toIdx + 2 ≤ y.rank.toIdx := by omega
              -- the pull-bracket: c's own suit rung lands at its own
              -- index — the popped card is next-up-live at its landing
              have hrungC : c.rank.toIdx + 1 = rungAt vp c.suit :=
                pollutesCrash_foundTop_rank hwfs htop0
              have hbran : rungAt s₁ c.suit = c.rank.toIdx :=
                pollutesCrash_pull_bracket hstep (by rw [hrungC])
              have hn1 : s₁.nextUp c = true :=
                pollutesCrash_landing_live hbran
              -- the landing lens: c appends at the guard's own pinned
              -- (mint's) seat pile
              have hlens : s₁
                  = (vp.setFound c.suit (chop (vp.found c.suit))).setPile k2
                    { vp.piles k2 with
                        faceUp := (vp.piles k2).faceUp ++ [c] } := by
                rw [hs]
                rw [show (vp.setFound c.suit (chop (vp.found c.suit))).putCard c
                      (Sum.inr z)
                    = (vp.setFound c.suit (chop (vp.found c.suit))).setPile k2
                      { (vp.setFound c.suit (chop (vp.found c.suit))).piles k2 with
                        faceUp := ((vp.setFound c.suit
                          (chop (vp.found c.suit))).piles k2).faceUp ++ [c] }
                  from by simp only [State.putCard, hmidpot]]
                rw [setFound_piles vp c.suit (chop (vp.found c.suit))]
              have hshape1 : (s₁.piles k2).faceUp
                  = (vp.piles k2).faceUp ++ [c] := by
                rw [hlens, setPile_piles_self]
              have hshape1' : (s₁.piles k2).faceUp
                  = (se2 ++ [m₀]) ++ [c] := by
                rw [hshape1, hshape2]
              have hhold1 : s₁.pileOfTop c = some k2 :=
                (pileOfTop_eq_some_iff hwfs₁).2 (by
                  show lastOf (s₁.piles k2).faceUp = some c
                  rw [hshape1']
                  exact lastOf_snoc)
              have hcond1 : chop (s₁.piles k2).faceUp ≠ [] ∨
                  ((s₁.piles k2).hidden = [] ∧ c.rank = Rank.king) := by
                refine Or.inl ?_
                show chop (s₁.piles k2).faceUp ≠ []
                rw [hshape1', chop_snoc]
                intro hcon
                have hm₀last : lastOf (se2 ++ [m₀]) = some m₀ := lastOf_snoc
                rw [hcon] at hm₀last
                exact pollutesCrash_none_ne_some m₀ hm₀last
              exact ih ⟨c, hwfs₁, hn1, hrkb', k2, se2 ++ [m₀], hshape1',
                hhold1, hcond1,
                pollutesCrash_tailDebt_pull hstep ⟨ccRA, ccPD, hdE⟩⟩
                hwfst' hy' hdcov' hlat' hnext' hsq2'
  | false =>
    cases m with
    | draw =>
        -- found and piles ride verbatim; the kit passes wholesale
        have hdw : vp.stepDraw = some s₁ := hstep
        have hfd : s₁.found = vp.found := stepDraw_found hdw
        have hpl : s₁.piles = vp.piles := stepDraw_piles hdw
        exact ih ⟨m₀, hwfs₁, (nextUp_congr m₀ hfd).trans hn, hrkb,
          k2, se2, by rw [hpl]; exact hshape2,
          (pollutesCrash_pileOfTop_congr m₀ hpl).trans hhold2,
          by rw [hpl]; exact hcond2,
          pollutesCrash_tailDebt_keep hfd ⟨ccRA, ccPD, hdE⟩⟩
          hwfst' hy' hdcov' hlat' hnext' hsq2'
    | wasteToFound c => exact absurd hwleg (journey_never_wasteToFound hstep)
    | wasteToTab c b => exact absurd hwleg (journey_never_wasteToTab hstep)
    | tabToFound c =>
        have hcwF : c ≠ m₀ := by
          intro hcon
          have htrue : pollutesCrash_rhoOpen (Move.tabToFound c) vp m₀ k2
              = true := by
            simp only [pollutesCrash_rhoOpen, decide_eq_true hcon,
              Bool.true_or]
          exact Bool.noConfusion (htrue.symm.trans hopenTF)
        exact pollutesCrash_rhoRaise hd hdcol hzrk hzcol hrk hwne hsq3 hpc1
          hpc2 hpid hwfs hn hrkb k2 se2 hshape2 hhold2 hcond2
          ⟨ccRA, ccPD, hdE⟩ hwfst' hy'
          hdcov' hlat' hnext' hsq2' hcwF hwleg hstep ih
    | tabToTab c b =>
        by_cases hcw : c = m₀
        · -- the mint alone slides: the empty-seat escape dies by the
          -- rank bound; ANY landing re-pairs the light kit (the landlord
          -- roams) — twin landing included
          obtain ⟨a, hhhold, hcp, _hfrun, hs⟩ := step_tabToTab_inv hstep
          rw [hcw] at hhhold
          -- the departure pile is the mint's seat pile itself
          have hm₀mem : m₀ ∈ (vp.piles k2).faceUp := by
            rw [hshape2]
            exact List.mem_append.mpr
              (Or.inr (List.mem_singleton.mpr rfl))
          have hak2 : a = k2 := by
            by_cases hq : a = k2
            · exact hq
            · exfalso
              exact absurd (pileHolding_mem hhhold)
                ((mem_faceUp_unique hwfs hm₀mem) a hq).1
          rw [hcw, hak2] at hs
          cases b with
          | inl a2 =>
              obtain ⟨-, hking⟩ := canPlace_inl hcp
              exfalso
              have hy12 : y.rank.toIdx < 13 := Rank.toIdx_lt y.rank
              have hk12 : Rank.king.toIdx = 12 := rfl
              rw [hcw] at hking
              rw [hking] at hrkb
              omega
          | inr z =>
              obtain ⟨k₀, hholdz, hsitz⟩ := canPlace_inr hcp
              rw [hcw] at hsitz
              -- the landing host is a stranger pile (the seat tops the
              -- mint, and the fit's rank clause bars the mint itself)
              have hk0k2 : k₀ ≠ k2 := by
                intro hcon
                rw [hcon] at hholdz
                have hzm : z = m₀ :=
                  Option.some.inj ((pileOfTop_top hholdz).2.symm.trans htop2)
                obtain ⟨hrkz, -⟩ := (canSitOn_eq m₀ z).mp hsitz
                rw [hzm] at hrkz
                omega
              have hneak2 : k2 ≠ k₀ := fun hcon => hk0k2 hcon.symm
              -- z strictly below the mint by the fit clause
              obtain ⟨hzrkz, -⟩ := (canSitOn_eq m₀ z).mp hsitz
              -- the host transplant: the mid-state top search
              have hzonly := mem_faceUp_only hwfs
                (Pile.mem_of_top (pileOfTop_top hholdz).2)
              have hneak : a ≠ k₀ :=
                fun hcon => hneak2 (by rw [← hcon]; exact hak2.symm)
              have hzfa : z ∉ (vp.piles a).faceUp := (hzonly.1 a hneak).2
              have hzha : z ∉ (vp.piles a).hidden := (hzonly.1 a hneak).1
              rw [hak2] at hzfa
              rw [hak2] at hzha
              have hmidz := pollutesCrash_slide_hostKeep (c := m₀)
                (z := z) (a := k2) (k₀ := k₀) hwfs hk0k2 hholdz hzfa hzha
              have hmidk0 : (vp.setPile k2 (Pile.afterRunRemoved (vp.piles k2)
                  (below m₀ (vp.piles k2).faceUp))).piles k₀
                  = vp.piles k₀ :=
                setPile_afterRunRemoved_piles_ne vp k2 m₀ k₀ hk0k2
              -- the moving run is the singleton [m₀] (the pile content is
              -- nodup, so the mint's occurrence is the last)
              have hnodup : (se2 ++ [m₀]).Nodup :=
                runOK_nodup (by rw [← hshape2]; exact hwfs.runOK_of k2)
              have hmne : m₀ ∉ se2 := pollutesCrash_nodup_snocNotmem hnodup
              have hsplit := pollutesCrash_below_fromCard_split (c := m₀)
                (se2 ++ [m₀])
              have hbl : below m₀ (se2 ++ [m₀]) = se2 :=
                pollutesCrash_below_lastOf se2 hmne
              rw [hbl] at hsplit
              have hmem2 : m₀ ∈ fromCard m₀ ((se2 : List Card) ++ [m₀]) := by
                have hmemw : m₀ ∈ se2 ++ [m₀] := by
                  rw [← hshape2]
                  exact hm₀mem
                rw [← hsplit] at hmemw
                rcases List.mem_append.mp hmemw with h3 | h4
                · exact absurd h3 hmne
                · exact h4
              have hL := congrArg List.length hsplit
              simp only [List.length_append, List.length_singleton] at hL
              have hlentail : (fromCard m₀ (se2 ++ [m₀])).length = 1 := by
                omega
              have hrun : fromCard m₀ (vp.piles k2).faceUp = [m₀] := by
                rw [hshape2]
                cases hr : fromCard m₀ (se2 ++ [m₀]) with
                | nil =>
                    rw [hr] at hmem2
                    exact absurd hmem2 (by simp)
                | cons u us =>
                    rw [hr] at hmem2
                    cases us with
                    | nil =>
                        rcases List.mem_cons.mp hmem2 with hcon | hcon
                        · rw [hcon]
                        · exact absurd hcon (by simp)
                    | cons v vs =>
                        exfalso
                        have hL3 := congrArg List.length hr
                        rw [List.length_cons, List.length_cons] at hL3
                        omega
              -- the landing lens
              have hlens : s₁
                  = (vp.setPile k2 (Pile.afterRunRemoved (vp.piles k2)
                      (below m₀ (vp.piles k2).faceUp))).setPile k₀
                    { vp.piles k₀ with
                        faceUp := (vp.piles k₀).faceUp
                          ++ fromCard m₀ (vp.piles k2).faceUp } := by
                rw [hs, putRun_inr_eq hmidz, hmidk0, hrun]
              -- the kit re-pairs at the landing pile (the landlord roams)
              have hfdd : s₁.found = vp.found :=
                pollutesCrash_slide_foundEq hstep
              have hn1 : s₁.nextUp m₀ = true :=
                (nextUp_congr m₀ hfdd).trans hn
              have hshape1 : (s₁.piles k₀).faceUp
                  = (vp.piles k₀).faceUp ++ [m₀] := by
                rw [hlens, setPile_piles_self, hrun]
              have hhold1 : s₁.pileOfTop m₀ = some k₀ :=
                (pileOfTop_eq_some_iff hwfs₁).2 (by
                  show lastOf (s₁.piles k₀).faceUp = some m₀
                  rw [hshape1]
                  exact lastOf_snoc)
              have hse2ne : (vp.piles k₀).faceUp ≠ [] := by
                intro hcon
                have hz2 : lastOf ((vp.piles k₀).faceUp) = some z :=
                  (pileOfTop_top hholdz).2
                rw [hcon] at hz2
                exact pollutesCrash_none_ne_some z hz2
              have hcond1 : chop (s₁.piles k₀).faceUp ≠ [] ∨
                  ((s₁.piles k₀).hidden = [] ∧ m₀.rank = Rank.king) :=
                Or.inl (by
                  show chop (s₁.piles k₀).faceUp ≠ []
                  rw [hshape1, chop_snoc]
                  exact hse2ne)
              exact ih ⟨m₀, hwfs₁, hn1, hrkb, k₀, (vp.piles k₀).faceUp,
                hshape1, hhold1, hcond1,
                pollutesCrash_tailDebt_keep hfdd ⟨ccRA, ccPD, hdE⟩⟩
                hwfst' hy' hdcov' hlat' hnext' hsq2'
        · -- a stranger's run closes at `b ≠ Sum.inr m₀` over the slide mover
          have hbwF : b ≠ Sum.inr m₀ := by
            cases b with
            | inl a2 => exact fun hcon => absurd hcon (by simp)
            | inr z =>
                intro hcon
                have hzw : z = m₀ := by injection hcon
                have htrue : pollutesCrash_rhoOpen (Move.tabToTab c (Sum.inr z))
                    vp m₀ k2 = true := by
                  show (decide (c ≠ m₀) && decide (z = m₀)) = true
                  rw [decide_eq_true hcw, Bool.true_and, decide_eq_true hzw]
                exact Bool.noConfusion (htrue.symm.trans hopenTF)
          exact pollutesCrash_rhoSlide hd hdcol hzrk hzcol hrk hwne hsq3 hpc1
            hpc2 hpid hwfs hn hrkb k2 se2 hshape2 hhold2 hcond2
            ⟨ccRA, ccPD, hdE⟩ hwfst'
            hy' hdcov' hlat' hnext' hsq2' hcw hbwF hwleg hstep ih
    | foundToTab c b =>
        by_cases hsc : c.suit = m₀.suit
        · -- THE RE-MINT: the pull pops the current top of the mint's own
          -- suit (one under the mint's own index), the popped card lands
          -- next-up-live at its own bracket index — the light kit
          -- re-seeds at the popped card's landing (the landlord roams).
          obtain ⟨c₀, htop0, hceq, hcp, hs⟩ := step_foundToTab_inv hstep
          rw [hceq] at htop0
          have hrungC : c.rank.toIdx + 1 = rungAt vp c.suit :=
            pollutesCrash_foundTop_rank hwfs htop0
          have hrungM : rungAt vp m₀.suit = m₀.rank.toIdx :=
            (show m₀.rank.toIdx = (vp.found m₀.suit).length from
              of_decide_eq_true hn).symm
          have hcidx : c.rank.toIdx + 1 = m₀.rank.toIdx := by
            rw [hrungC, hsc]
            exact hrungM
          have hrkb' : c.rank.toIdx + 2 ≤ y.rank.toIdx := by omega
          -- the landing rung is the popped card's own index (the bracket)
          have hbran : rungAt s₁ c.suit = c.rank.toIdx :=
            pollutesCrash_pull_bracket hstep (by rw [hrungC])
          have hn1 : s₁.nextUp c = true :=
            pollutesCrash_landing_live hbran
          cases b with
          | inl a₂ =>
              -- the bare king landing: chop dies but the king line holds
              obtain ⟨hemp, hking⟩ := canPlace_inl hcp
              have hlens : s₁.piles a₂ = ⟨[], [c]⟩ := by
                rw [hs, putCard_eq_inl, setPile_piles_self]
              exact ih ⟨c, hwfs₁, hn1, hrkb', a₂, [],
                by
                  rw [hlens]
                  show (⟨[], [c]⟩ : Pile).faceUp = ([] : List Card) ++ [c]
                  rfl,
                (pileOfTop_eq_some_iff hwfs₁).2 (by
                  show (s₁.piles a₂).top = some c
                  rw [hlens]
                  show (⟨[], [c]⟩ : Pile).top = some c
                  rfl),
                Or.inr (by
                  rw [hlens]
                  show (⟨[], [c]⟩ : Pile).hidden = [] ∧ c.rank = Rank.king
                  exact ⟨rfl, hking⟩),
                pollutesCrash_tailDebt_pull hstep ⟨ccRA, ccPD, hdE⟩⟩
                hwfst' hy' hdcov' hlat' hnext' hsq2'
          | inr z =>
              obtain ⟨k₀', hholdz', _hsitz'⟩ := canPlace_inr hcp
              -- the mid-state is piles-verbatim under setFound, so the
              -- host read re-anchors at the guard's own pile
              have hmidpot : (vp.setFound c.suit (chop (vp.found c.suit))).pileOfTop z
                  = some k₀' :=
                (pollutesCrash_pileOfTop_congr z
                  (setFound_piles vp c.suit (chop (vp.found c.suit)))).trans
                  hholdz'
              have hlens : s₁
                  = (vp.setFound c.suit (chop (vp.found c.suit))).setPile k₀'
                    { vp.piles k₀' with
                        faceUp := (vp.piles k₀').faceUp ++ [c] } := by
                 rw [hs]
                 rw [show (vp.setFound c.suit (chop (vp.found c.suit))).putCard c
                       (Sum.inr z)
                     = (vp.setFound c.suit (chop (vp.found c.suit))).setPile k₀'
                       { (vp.setFound c.suit (chop (vp.found c.suit))).piles k₀'
                           with
                         faceUp := ((vp.setFound c.suit
                           (chop (vp.found c.suit))).piles k₀').faceUp ++ [c] }
                   from by simp only [State.putCard, hmidpot]]
                 rw [setFound_piles vp c.suit (chop (vp.found c.suit))]
              have hshape1 : (s₁.piles k₀').faceUp
                  = (vp.piles k₀').faceUp ++ [c] := by
                rw [hlens, setPile_piles_self]
              have hhold1 : s₁.pileOfTop c = some k₀' :=
                (pileOfTop_eq_some_iff hwfs₁).2 (by
                  show lastOf (s₁.piles k₀').faceUp = some c
                  rw [hshape1]
                  exact lastOf_snoc)
              have hcond1 : chop (s₁.piles k₀').faceUp ≠ [] ∨
                  ((s₁.piles k₀').hidden = [] ∧ c.rank = Rank.king) := by
                refine Or.inl ?_
                rw [hshape1, chop_snoc]
                show (vp.piles k₀').faceUp ≠ []
                intro hcon
                have hz2 : lastOf ((vp.piles k₀').faceUp) = some z :=
                  (pileOfTop_top hholdz').2
                rw [hcon] at hz2
                exact pollutesCrash_none_ne_some z hz2
              exact ih ⟨c, hwfs₁, hn1, hrkb', k₀', (vp.piles k₀').faceUp,
                hshape1, hhold1, hcond1,
                pollutesCrash_tailDebt_pull hstep ⟨ccRA, ccPD, hdE⟩⟩
                hwfst' hy' hdcov' hlat' hnext' hsq2'
        · -- the stranger-suit fork: the self-anchor wipe, the vanished
          -- landing, and the off-seat hosts all survive (light kit passes)
          have hsc' : m₀.suit ≠ c.suit := fun hcon => hsc hcon.symm
          obtain ⟨_c₀, _htop0, _hceq, hcp, hs⟩ := step_foundToTab_inv hstep
          cases b with
          | inl a₂ =>
              -- the self-anchor wipe: the seat pile is not empty (the mint
              -- sits face-up on it), so the empty-seat guard cannot fire
              obtain ⟨hemp, -⟩ := canPlace_inl hcp
              by_cases hka : a₂ = k2
              · rw [hka] at hemp
                have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
                rw [hshape2] at hfupE
                exact absurd hfupE (by simp)
              · have hkna : k2 ≠ a₂ := fun hcon => hka hcon.symm
                have hn1 := pollutesCrash_rhoPull_nextUpKeep hstep hsc' hn
                have hshape1 := pollutesCrash_rhoPull_shapeKeep hstep hkna
                  hshape2
                have hhold1 : s₁.pileOfTop m₀ = some k2 :=
                  (pileOfTop_eq_some_iff hwfs₁).2 (by
                    show lastOf (s₁.piles k2).faceUp = some m₀
                    rw [hshape1]
                    exact lastOf_snoc)
                have hhpilk := pollutesCrash_rhoPull_pilesKeep_inl hkna hstep
                have hcond1 : chop (s₁.piles k2).faceUp ≠ [] ∨
                    ((s₁.piles k2).hidden = [] ∧ m₀.rank = Rank.king) := by
                  rw [hhpilk]
                  exact hcond2
                exact ih ⟨m₀, hwfs₁, hn1, hrkb, k2, se2, hshape1, hhold1,
                  hcond1, pollutesCrash_tailDebt_pull hstep ⟨ccRA, ccPD, hdE⟩⟩ hwfst' hy'
                  hdcov' hlat' hnext' hsq2'
          | inr z =>
              have hhostNE : (vp.setFound c.suit (chop (vp.found c.suit))).pileOfTop z
                  ≠ some k2 := by
                intro hcon
                have htrue : pollutesCrash_rhoOpen (Move.foundToTab c (Sum.inr z))
                    vp m₀ k2 = true := by
                  simp only [pollutesCrash_rhoOpen]
                  rw [decide_eq_true hcon]
                exact Bool.noConfusion (htrue.symm.trans hopenTF)
              cases hpz : (vp.setFound c.suit (chop (vp.found c.suit))).pileOfTop z
                with
              | none =>
                  -- the landing vanishes: the piles board rides wholesale
                  have hn1 := pollutesCrash_rhoPull_nextUpKeep hstep hsc' hn
                  have hpilk2 : s₁.piles k2 = vp.piles k2 := by
                    rw [hs]
                    rw [show (vp.setFound c.suit (chop (vp.found c.suit))).putCard c
                          (Sum.inr z)
                        = vp.setFound c.suit (chop (vp.found c.suit))
                      from by simp only [State.putCard, hpz]]
                    rfl
                  exact ih ⟨m₀, hwfs₁, hn1, hrkb, k2, se2,
                    by rw [hpilk2]; exact hshape2,
                    (pileOfTop_eq_some_iff hwfs₁).2 (by
                      show (s₁.piles k2).top = some m₀
                      rw [hpilk2]
                      exact htop2),
                    by rw [hpilk2]; exact hcond2,
                    pollutesCrash_tailDebt_pull hstep ⟨ccRA, ccPD, hdE⟩⟩ hwfst' hy' hdcov'
                    hlat' hnext' hsq2'
              | some k₂' =>
                  have hkn : k2 ≠ k₂' := by
                    intro hcon
                    exact hhostNE (by rw [hcon]; exact hpz)
                  have hn1 := pollutesCrash_rhoPull_nextUpKeep hstep hsc' hn
                  have hshape1 := pollutesCrash_rhoPull_shapeKeep_inr hstep hpz
                    hkn hshape2
                  have hhold1 : s₁.pileOfTop m₀ = some k2 :=
                    (pileOfTop_eq_some_iff hwfs₁).2 (by
                      show lastOf (s₁.piles k2).faceUp = some m₀
                      rw [hshape1]
                      exact lastOf_snoc)
                  have hhpilk := pollutesCrash_rhoPull_pilesKeep_inr hkn hstep hpz
                  have hcond1 : chop (s₁.piles k2).faceUp ≠ [] ∨
                      ((s₁.piles k2).hidden = [] ∧ m₀.rank = Rank.king) := by
                    rw [hhpilk]
                    exact hcond2
                  exact ih ⟨m₀, hwfs₁, hn1, hrkb, k2, se2, hshape1, hhold1,
                    hcond1, pollutesCrash_tailDebt_pull hstep ⟨ccRA, ccPD, hdE⟩⟩ hwfst' hy'
                    hdcov' hlat' hnext' hsq2'

/-- **THE MOVER DISPATCH, FOUNDED-FORM** — the widened carry's second
half: a mint riding its own suit's foundation row at its own bracket
survives every rider leg.  The stranger legs and the draw carry the
row verbatim; a same-suit RAISE grows the stack above the mint
(`pollutesCrash_foundRaise_stackGrow`); a same-suit PULL chops the
stack alone (`pollutesCrash_foundPull_stackShrink`); and when the
stack is EMPTY the pulled card IS the mint — THE RE-EXHUME:
`pollutesCrash_reseat_pop` lands it next-up-live and seat-top in the
light kit's very own shape (the switch-back constructor, the widened
mover's pure-assembly row).  The waste movers die by the journey
census as everywhere.  Ranks and the census debt ride the priced per
leg rows (`tailDebt_keep/raise/pull`).  The founded mint cannot
itself be raised or covered while it rides its row: a founded card
tops no pile and sits in none
(`pollutesCrash_foundCard_notPileTop`/`_notInPile`), so no arm needs
a guard beyond the row reads. -/
private theorem pollutesCrash_rhoMoverF {x y d w zt : Card}
    {play π : List Move}
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hdcol : d.suit.color ≠ y.suit.color)
    (hzrk : zt.rank.toIdx = w.rank.toIdx + 1)
    (hzcol : zt.suit.color = y.suit.color)
    (hrk : w.rank.toIdx + 1 ≤ d.rank.toIdx)
    (hwne : w ≠ y ∧ w ≠ y.twin)
    (hsq3 : raisesOf play d.suit + 2 ≤ pullsOf play d.suit)
    (hpc1 : raisesOf play y.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.suit)
    (hpc2 : raisesOf play y.twin.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.twin.suit)
    (hpid : raisesOf π d.suit + (d.rank.toIdx - w.rank.toIdx)
      ≤ pullsOf π d.suit)
    {vp s₁ sth : State} {m : Move} {m₀ : Card}
    (hw : w.suit = d.suit)
    (hwfs : vp.WF)
    (hrkb : m₀.rank.toIdx + 2 ≤ y.rank.toIdx)
    (PRE STOCK : List Card)
    (hrow : vp.found m₀.suit = PRE ++ [m₀] ++ STOCK)
    (hbrk : PRE.length = m₀.rank.toIdx)
    (hdebt : ∃ ccRA ccPD : Nat, rungAt vp d.suit + ccPD
      = w.rank.toIdx + ccRA)
    (hwfst' : sth.WF)
    (hy' : ForkWitness sth y)
    (hdcov' : ∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
      sth.pileOfTop d = some cc)
    (hlat' : ∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin)
    (hnext' : sth.nextUp d = false)
    (hsq2' : rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1)
    (hwleg : reversibleAtW vp m)
    (hstep : State.step vp m = some s₁)
    (harch : ∃ (o : State), o.WF ∧
      d.rank.toIdx + 1 ≤ rungAt o d.suit ∧
      ∃ (pf : List Move), ShufflePlayW o pf sth)
    (ih : ((∃ m₁ : Card, s₁.WF ∧ s₁.nextUp m₁ = true ∧
        m₁.rank.toIdx + 2 ≤ y.rank.toIdx ∧
        ∃ ke se, (s₁.piles ke).faceUp = se ++ [m₁] ∧
          s₁.pileOfTop m₁ = some ke ∧
          (chop (s₁.piles ke).faceUp ≠ [] ∨
            ((s₁.piles ke).hidden = [] ∧ m₁.rank = Rank.king)) ∧
        ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD
          = w.rank.toIdx + ccRA) ∨
       (∃ m₁ : Card, s₁.WF ∧ m₁.rank.toIdx + 2 ≤ y.rank.toIdx ∧
        ∃ PRE STOCK : List Card, s₁.found m₁.suit = PRE ++ [m₁] ++ STOCK ∧
          PRE.length = m₁.rank.toIdx ∧
        ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD
          = w.rank.toIdx + ccRA)) →
      sth.WF → ForkWitness sth y →
      (∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
        sth.pileOfTop d = some cc) →
      (∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin) →
      sth.nextUp d = false →
      rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1 →
      (∃ (o : State), o.WF ∧
        d.rank.toIdx + 1 ≤ rungAt o d.suit ∧
        ∃ (pf : List Move), ShufflePlayW o pf sth) →
      ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin) :
    ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin := by
  have hwfs₁ : s₁.WF := step_wf hwfs hstep
  cases m with
  | draw =>
      have hdw : vp.stepDraw = some s₁ := hstep
      have hfk : s₁.found = vp.found := stepDraw_found hdw
      have hrow' : s₁.found m₀.suit = PRE ++ [m₀] ++ STOCK := by
        rw [hfk]
        exact hrow
      exact ih (Or.inr ⟨m₀, hwfs₁, hrkb, PRE, STOCK, hrow', hbrk,
        pollutesCrash_tailDebt_keep hfk hdebt⟩)
        hwfst' hy' hdcov' hlat' hnext' hsq2' harch
  | wasteToFound c =>
      exact absurd hwleg (journey_never_wasteToFound hstep)
  | wasteToTab c b =>
      exact absurd hwleg (journey_never_wasteToTab hstep)
  | tabToFound c =>
      obtain ⟨_hn, _a, _hp, hs⟩ := step_tabToFound_inv hstep
      by_cases hsc : c.suit = m₀.suit
      · -- the same-suit raise: the stack grows above the mint
        have happ : s₁.found m₀.suit = vp.found m₀.suit ++ [c] := by
          rw [hs]
          rw [hsc]
          exact setFound_found_self
        have hrow' : s₁.found m₀.suit = PRE ++ [m₀] ++ (STOCK ++ [c]) :=
          pollutesCrash_foundRaise_stackGrow hrow happ
        exact ih (Or.inr ⟨m₀, hwfs₁, hrkb, PRE, STOCK ++ [c], hrow', hbrk,
          pollutesCrash_tailDebt_raise hstep hdebt⟩)
          hwfst' hy' hdcov' hlat' hnext' hsq2' harch
      · -- the stranger-suit raise: the mint's row verbatim
        have hfm : s₁.found m₀.suit = vp.found m₀.suit := by
          rw [hs]
          exact setFound_found_ne (fun hcon => hsc hcon.symm)
        exact ih (Or.inr ⟨m₀, hwfs₁, hrkb, PRE, STOCK, hfm.trans hrow,
          hbrk, pollutesCrash_tailDebt_raise hstep hdebt⟩)
          hwfst' hy' hdcov' hlat' hnext' hsq2' harch
  | tabToTab c b =>
      have hfk : s₁.found = vp.found := pollutesCrash_slide_foundEq hstep
      have hrow' : s₁.found m₀.suit = PRE ++ [m₀] ++ STOCK := by
        rw [hfk]
        exact hrow
      exact ih (Or.inr ⟨m₀, hwfs₁, hrkb, PRE, STOCK, hrow', hbrk,
        pollutesCrash_tailDebt_keep hfk hdebt⟩)
        hwfst' hy' hdcov' hlat' hnext' hsq2' harch
  | foundToTab c b =>
      obtain ⟨c₀, htop0, hceq, _hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hceq] at htop0
      by_cases hesc : c.suit = m₀.suit
      · by_cases hst : STOCK = []
        · -- the stack empty: the popped top IS the mint — the re-exhume
          rw [hesc] at htop0
          have hrowS : vp.found m₀.suit = PRE ++ [m₀] :=
            hrow.trans (by rw [hst, List.append_nil])
          obtain ⟨hft, hlen⟩ := pollutesCrash_foundTop_atOwn hrowS
          have hcm : c = m₀ :=
            Option.some.inj (htop0.symm.trans hft)
          rw [hcm] at hstep
          have hrungv : rungAt vp m₀.suit = m₀.rank.toIdx + 1 := by
            show (vp.found m₀.suit).length = m₀.rank.toIdx + 1
            rw [hlen, hbrk]
          obtain ⟨hn1, ke, se, hshape1, hhold1, hcond1⟩ :=
            pollutesCrash_reseat_pop hwfs hrungv hstep
          exact ih (Or.inl ⟨m₀, hwfs₁, hn1, hrkb, ke, se, hshape1,
            hhold1, hcond1,
            pollutesCrash_tailDebt_pull hstep hdebt⟩)
            hwfst' hy' hdcov' hlat' hnext' hsq2' harch
        · -- the stack nonempty: the pop chops the stack alone
          have hchop : s₁.found m₀.suit = chop (vp.found m₀.suit) := by
            rw [hs]
            rw [putCard_found]
            rw [hesc]
            exact setFound_found_self
          obtain ⟨STOCK', hrow'⟩ :=
            pollutesCrash_foundPull_stackShrink hst hrow hchop
          exact ih (Or.inr ⟨m₀, hwfs₁, hrkb, PRE, STOCK', hrow', hbrk,
            pollutesCrash_tailDebt_pull hstep hdebt⟩)
            hwfst' hy' hdcov' hlat' hnext' hsq2' harch
      · -- the stranger-suit pull: the mint's row verbatim
        have hfm : s₁.found m₀.suit = vp.found m₀.suit := by
          rw [hs, putCard_found]
          exact setFound_found_ne (fun hcon => hesc hcon.symm)
        exact ih (Or.inr ⟨m₀, hwfs₁, hrkb, PRE, STOCK, hfm.trans hrow,
          hbrk, pollutesCrash_tailDebt_pull hstep hdebt⟩)
          hwfst' hy' hdcov' hlat' hnext' hsq2' harch

/-- **THE CONS-STEP RESIDUE — the ρ-tail landlord iteration's single
leg** (the staircase's named terminal piece): one witnessed leg
`vp --m--> s₁`, the minted card's carry at `vp`, the fork-side
saturation bundle at the end state `sth`, and the continuation `ih`
(the rest of the_tail at the same end state).  The carry's mint is
EXISTENTIAL (the re-mint restatement): the kit rides leg by leg.  Every arm closes over the
light kit:
1. THE DRAW LEG — the boards ride verbatim; the kit passes wholesale.
2. THE RAISE LEG (`tabToFound c`) — a stranger's raise leaves the mint
   seated and `ih` runs (`pollutesCrash_rhoRaise`); a wash-back of the mint itself
   is the mover's residue (the mint founded with no pinned successor).
3. THE SLIDE LEG (`tabToTab c b`) — a stranger's run off the mint closes
   over `pollutesCrash_rhoSlide`; the mint ALONE slides to ANY landing
   (king escape excluded by the rank bound) and re-pairs the light kit
   at the landing pile; the run onto the mint is the residue.
4. THE PULL LEG (`foundToTab c b`) — the same-suit pop re-mints to the
   popped card at its own bracket index; stranger-suit pops survive
   through the five banked survival rows; the z-onto-mint pull burial
   closes in the mover's open arm (the popped card re-mints over the
   covered mint at its own bracket — the ∃-kit's mint-swap).
 5. THE WASTE LEGS die by the journey census (`journey_never_waste*`).
The residual family (two literals in `pollutesCrash_rhoOpen`): the
mint FOUNDED or COVERED with no pinned successor — the one remaining
named fork, per the HOLD audit. -/
private theorem pollutesCrash_rhoLeg {x y d w zt : Card}
    {play π : List Move}
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hdcol : d.suit.color ≠ y.suit.color)
    (hzrk : zt.rank.toIdx = w.rank.toIdx + 1)
    (hzcol : zt.suit.color = y.suit.color)
    (hrk : w.rank.toIdx + 1 ≤ d.rank.toIdx)
    (hwne : w ≠ y ∧ w ≠ y.twin)
    (hsq3 : raisesOf play d.suit + 2 ≤ pullsOf play d.suit)
    (hpc1 : raisesOf play y.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.suit)
    (hpc2 : raisesOf play y.twin.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.twin.suit)
    (hpid : raisesOf π d.suit + (d.rank.toIdx - w.rank.toIdx)
      ≤ pullsOf π d.suit)
    {vp s₁ sth : State} {m : Move}
    (hw : w.suit = d.suit)
    (hcarry : ∃ m₀ : Card, vp.WF ∧ vp.nextUp m₀ = true ∧
      m₀.rank.toIdx + 2 ≤ y.rank.toIdx ∧
      ∃ ke se, (vp.piles ke).faceUp = se ++ [m₀] ∧
        vp.pileOfTop m₀ = some ke ∧
        (chop (vp.piles ke).faceUp ≠ [] ∨
          ((vp.piles ke).hidden = [] ∧ m₀.rank = Rank.king)) ∧
      ∃ ccRA ccPD : Nat, rungAt vp d.suit + ccPD
        = w.rank.toIdx + ccRA)
    (hwfst' : sth.WF)
    (hy' : ForkWitness sth y)
    (hdcov' : ∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
      sth.pileOfTop d = some cc)
    (hlat' : ∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin)
    (hnext' : sth.nextUp d = false)
    (hsq2' : rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1)
    (hwleg : reversibleAtW vp m)
    (hstep : State.step vp m = some s₁)
    (harch : ∃ (o : State), o.WF ∧
      d.rank.toIdx + 1 ≤ rungAt o d.suit ∧
      ∃ (pf : List Move), ShufflePlayW o pf sth)
    (ihWide : ((∃ m₀ : Card, s₁.WF ∧ s₁.nextUp m₀ = true ∧
        m₀.rank.toIdx + 2 ≤ y.rank.toIdx ∧
        ∃ ke se, (s₁.piles ke).faceUp = se ++ [m₀] ∧
          s₁.pileOfTop m₀ = some ke ∧
          (chop (s₁.piles ke).faceUp ≠ [] ∨
            ((s₁.piles ke).hidden = [] ∧ m₀.rank = Rank.king)) ∧
        ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD
          = w.rank.toIdx + ccRA) ∨
       (∃ m₀ : Card, s₁.WF ∧ m₀.rank.toIdx + 2 ≤ y.rank.toIdx ∧
        ∃ PRE STOCK : List Card, s₁.found m₀.suit = PRE ++ [m₀] ++ STOCK ∧
          PRE.length = m₀.rank.toIdx ∧
        ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD
          = w.rank.toIdx + ccRA)) →
      sth.WF → ForkWitness sth y →
      (∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
        sth.pileOfTop d = some cc) →
      (∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin) →
      sth.nextUp d = false →
      rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1 →
      (∃ (o : State), o.WF ∧
        d.rank.toIdx + 1 ≤ rungAt o d.suit ∧
        ∃ (pf : List Move), ShufflePlayW o pf sth) →
      ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin) :
    ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin := by
  obtain ⟨m₀, hwfs, hn, hrkb, k2, se2, hshape2, hhold2, hcond2, hdebt⟩ :=
    hcarry
  -- the seat-grade view of the widened ih: every arm that re-pairs within
  -- the light kit's own shape consumes this wrapper; the mover rows below
  -- receive the widened ihWide itself (the wash-back emits the founded form)
  have ih : (∃ m₁ : Card, s₁.WF ∧ s₁.nextUp m₁ = true ∧
      m₁.rank.toIdx + 2 ≤ y.rank.toIdx ∧
      ∃ ke se, (s₁.piles ke).faceUp = se ++ [m₁] ∧
        s₁.pileOfTop m₁ = some ke ∧
        (chop (s₁.piles ke).faceUp ≠ [] ∨
          ((s₁.piles ke).hidden = [] ∧ m₁.rank = Rank.king)) ∧
      ∃ ccRA ccPD : Nat, rungAt s₁ d.suit + ccPD
        = w.rank.toIdx + ccRA) →
    sth.WF → ForkWitness sth y →
    (∃ cc bscc, (sth.piles cc).faceUp = bscc ++ [y.twin, d] ∧
      sth.pileOfTop d = some cc) →
    (∀ z, sth.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin) →
    sth.nextUp d = false →
    rungAt sth d.suit + 2 ≤ d.rank.toIdx + 1 →
    ∃ t, CanRaiseS sth t ∧ t ≠ y ∧ t ≠ y.twin :=
    fun hk hwfst' hy' hdcov' hlat' hnext' hsq2' =>
      ihWide (Or.inl hk) hwfst' hy' hdcov' hlat' hnext' hsq2' harch
  cases m with
  | draw =>
      have hdw : vp.stepDraw = some s₁ := hstep
      obtain ⟨hn1, ke1, se1, hshape1, hhold1, hcond1⟩ :=
        pollutesCrash_rhoDraw_now hdw hn ⟨k2, se2, hshape2, hhold2, hcond2⟩
      exact ih ⟨m₀, step_wf hwfs hstep, hn1, hrkb, ke1, se1, hshape1,
        hhold1, hcond1, pollutesCrash_tailDebt_keep (stepDraw_found hdw)
        hdebt⟩ hwfst' hy' hdcov' hlat' hnext' hsq2'
  | tabToFound _c =>
      exact pollutesCrash_rhoMover hd hdcol hzrk hzcol hrk hwne hsq3 hpc1
        hpc2 hpid hw hwfs hn hrkb k2 se2 hshape2 hhold2 hcond2 hdebt hwfst'
        hy' hdcov' hlat' hnext' hsq2' hwleg hstep harch ihWide
  | foundToTab _c _b =>
      exact pollutesCrash_rhoMover hd hdcol hzrk hzcol hrk hwne hsq3 hpc1
        hpc2 hpid hw hwfs hn hrkb k2 se2 hshape2 hhold2 hcond2 hdebt hwfst'
        hy' hdcov' hlat' hnext' hsq2' hwleg hstep harch ihWide
  | tabToTab _c _b =>
      exact pollutesCrash_rhoMover hd hdcol hzrk hzcol hrk hwne hsq3 hpc1
        hpc2 hpid hw hwfs hn hrkb k2 se2 hshape2 hhold2 hcond2 hdebt hwfst'
        hy' hdcov' hlat' hnext' hsq2' hwleg hstep harch ihWide
  | wasteToFound _c =>
      exact absurd hwleg (journey_never_wasteToFound hstep)
  | wasteToTab _c _b =>
      exact absurd hwleg (journey_never_wasteToTab hstep)

/-- **THE ρ-TAIL SKELETON** — the journey-strengthened chase: the
carry's mint rides the tail leg by leg; at the EMPTY tail the mint IS
the terminal off-pair card; the waste movers die by the journey census
(`journey_never_wasteToFound`/`journey_never_wasteToTab`); every
surviving leg defers to the cons-step residue `pollutesCrash_rhoLeg`. -/
private theorem pollutesCrash_rhoTail {x y d w zt : Card}
    {play π : List Move}
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hdcol : d.suit.color ≠ y.suit.color)
    (hzrk : zt.rank.toIdx = w.rank.toIdx + 1)
    (hzcol : zt.suit.color = y.suit.color)
    (hrk : w.rank.toIdx + 1 ≤ d.rank.toIdx)
    (hwne : w ≠ y ∧ w ≠ y.twin)
    (hsq3 : raisesOf play d.suit + 2 ≤ pullsOf play d.suit)
    (hpc1 : raisesOf play y.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.suit)
    (hpc2 : raisesOf play y.twin.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.twin.suit)
    (hpid : raisesOf π d.suit + (d.rank.toIdx - w.rank.toIdx)
      ≤ pullsOf π d.suit)
    (hw : w.suit = d.suit) :
    ∀ (s st : State) (jr : List Move), ShufflePlayW s jr st →
      ((∃ m₀ : Card, s.WF ∧ s.nextUp m₀ = true ∧
        m₀.rank.toIdx + 2 ≤ y.rank.toIdx ∧
        ∃ ke se, (s.piles ke).faceUp = se ++ [m₀] ∧
          s.pileOfTop m₀ = some ke ∧
          (chop (s.piles ke).faceUp ≠ [] ∨
            ((s.piles ke).hidden = [] ∧ m₀.rank = Rank.king)) ∧
        ∃ ccRA ccPD : Nat, rungAt s d.suit + ccPD
          = w.rank.toIdx + ccRA) ∨
       (∃ m₀ : Card, s.WF ∧ m₀.rank.toIdx + 2 ≤ y.rank.toIdx ∧
        ∃ PRE STOCK : List Card, s.found m₀.suit = PRE ++ [m₀] ++ STOCK ∧
          PRE.length = m₀.rank.toIdx ∧
        ∃ ccRA ccPD : Nat, rungAt s d.suit + ccPD
          = w.rank.toIdx + ccRA)) →
      st.WF → ForkWitness st y →
      (∃ cc bscc, (st.piles cc).faceUp = bscc ++ [y.twin, d] ∧
        st.pileOfTop d = some cc) →
      (∀ z, st.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin) →
      st.nextUp d = false →
      rungAt st d.suit + 2 ≤ d.rank.toIdx + 1 →
      (∃ (o : State), o.WF ∧
        d.rank.toIdx + 1 ≤ rungAt o d.suit ∧
        ∃ (pf : List Move), ShufflePlayW o pf st) →
      ∃ t, CanRaiseS st t ∧ t ≠ y ∧ t ≠ y.twin := by
  intro s st jr hrJ
  induction hrJ with
  | nil s₀ =>
      intro hcarry hwfst' hy' _hdcov' _hlat' _hnext' hsq2' harch
      rcases hcarry with
        ⟨m₀, _hwfs, _hn, _hrkb, _ke, _se, _hshape, _hhold, _hcond, _⟩ |
        ⟨m₀, _hwfs, _hrkb, _PRE, _STOCK, _hrow, _hbrk, _⟩
      · exact ⟨m₀, CanRaiseS.now m₀ ⟨_hn, _ke, _hhold, _hcond⟩,
          fun hcon => by
            rw [hcon] at _hrkb
            omega,
          fun hcon => by
            rw [hcon] at _hrkb
            rw [Card.twin_rank y] at _hrkb
            omega⟩
      · -- THE ORIGIN-ANCHORED CRASH — the archaeology engine's
        -- consumption, the census corner's priced landing: pack in
        -- hand, the d-suit hot card at the terminus's own rung was
        -- founded at the origin (strictly under the hsq1-grade anchor
        -- by the two-end squeeze) and is hot at the terminus, so
        -- `pollutesCrash_terminalHot_Below` seats it BELOW a live
        -- neighbor; the seat fit makes that neighbor family-colored
        -- (the seat's color conservation `lock_color_pair`) and
        -- ranked strictly under the fork's pinned family rungs (both
        -- pinned at the pair's rank by `canRaiseS_rung` off `hy'`),
        -- hence foundation-resident by the height bridge —
        -- contradicting the Below-read's own face-up membership
        -- (`mem_found_unique`).  The fork's saturation crashes the
        -- census; the mint's suit never enters (the d-suit witness
        -- rides every state).
        obtain ⟨o, hwfo, hsq1o, pf, hshpo⟩ := harch
        -- the standing terminus package + the arch are jointly
        -- crashing (pollutesCrash_originCrash): the d-suit hot card
        -- at the terminus's own rung was founded at the origin, rides
        -- the archaeology engine to a Below seat, and the fork's own
        -- family pins bar the neighbor — mem_found_unique closes.
        exact pollutesCrash_originCrash hwfst' hy' hd hdcol hsq2'
          hwfo hsq1o ⟨pf, hshpo⟩
  | @cons vp m s₁ rest sth hwleg hstep _hrest ih =>
      intro hcarry hwfst' hy' hdcov' hlat' hnext' hsq2' harch
      rcases hcarry with hseat |
        ⟨m₀, hwfs, hrkb, PRE, STOCK, hrow, hbrk, hdebt⟩
      · cases m with
      | draw =>
          exact pollutesCrash_rhoLeg hd hdcol hzrk hzcol hrk hwne hsq3 hpc1
            hpc2 hpid hw hseat hwfst' hy' hdcov' hlat' hnext' hsq2' hwleg
            hstep harch ih
      | tabToFound c =>
          exact pollutesCrash_rhoLeg hd hdcol hzrk hzcol hrk hwne hsq3 hpc1
            hpc2 hpid hw hseat hwfst' hy' hdcov' hlat' hnext' hsq2' hwleg
            hstep harch ih
      | foundToTab c b =>
          exact pollutesCrash_rhoLeg hd hdcol hzrk hzcol hrk hwne hsq3 hpc1
            hpc2 hpid hw hseat hwfst' hy' hdcov' hlat' hnext' hsq2' hwleg
            hstep harch ih
      | tabToTab c b =>
          exact pollutesCrash_rhoLeg hd hdcol hzrk hzcol hrk hwne hsq3 hpc1
            hpc2 hpid hw hseat hwfst' hy' hdcov' hlat' hnext' hsq2' hwleg
            hstep harch ih
      | wasteToFound c =>
          exact absurd hwleg (journey_never_wasteToFound hstep)
      | wasteToTab c b =>
          exact absurd hwleg (journey_never_wasteToTab hstep)
      · exact pollutesCrash_rhoMoverF hd hdcol hzrk hzcol hrk hwne hsq3 hpc1
          hpc2 hpid hw hwfs hrkb PRE STOCK hrow hbrk hdebt hwfst' hy' hdcov'
          hlat' hnext' hsq2' hwleg hstep harch ih

/-- **THE DESCENT RESIDUE — route 4's ρ-tail chase, the staircase's one
named sub-residue.**  From the minted third live card at the landing
epoch (`hmint`, with its off-pair certificates `hwne`), the ρ-tail's
witnessed journey to the lower fork manufactures the TERMINAL dragged
low card at `st₂`, still `CanRaiseS`-live and off-pair.  ROUTE (complete):

1. THE ρ-LEG RE-ARMING — every `foundToTab` leg of the tail is
   current-top LIFO (`foundToTab_pops_currentTop`), so its landing card
   is exactly the popped card, face-up over its own landlord, with the
   landing rung exactly the popped card's own index — NEXT-UP-LIVE at
   its own landing by `pollutesCrash_landing_live`, then
   `pollutesCrash_landing_canRaiseS` with the seat intact: each
   debt-servicing pull re-mints a census-visible live card.
2. THE HOST CONFINEMENT — `hlattice` reads every lawful landlord of the
   cover `d` at `st₂` as a pair member; `hdcover` seats `y.twin` directly
   under `d` and `hnext` parks `d` itself, so every mid-tail landing one
   rung up the family color (`hzcol`) must thread the pair's seats or
   the dress lattice one rung down (`dress_legalSeats_pair`), whose
   hosts are themselves foundation-resident (`pair_lowFamily_founded`
   wedges) and must be pulled first — the landlord iteration drags the
   family's low cards one rank at a time.
3. THE CENSUS PRICING — the ρ-leg pulls are priced against the π-side
   installment `hpid` and the whole-journey debts `hsq3`/`hpc1`/`hpc2`
   (the per-segment `witness_rung_census` on `hrho`, closed by the
   bracket `hsq2`): washing a dragged card back re-raises its suit's
   rung (a priced raise) while its exit is a priced pull, so the
   back-and-forth cannot ground in a finite prefix — some dragged low
   card stands FACE-UP-LIVE at `st₂` itself, `CanRaiseS`-witnessed
   (`canRaiseS_iff`), off-pair by the rank/color ledger exactly as
   `pollutesCrash_w_offPair` prices the minted card. -/
private theorem pollutesCrash_descent {st₂ v : State}
    {x y d w zt : Card} {kk : Anchor} {bs : List Card}
    {ρ play π : List Move}
    (hwf₂ : st₂.WF)
    (hy : ForkWitness st₂ y)
    (hd : d.rank.toIdx + 1 = y.rank.toIdx)
    (hdcol : d.suit.color ≠ y.suit.color)
    (hdcover : ∃ cc bscc, (st₂.piles cc).faceUp = bscc ++ [y.twin, d] ∧
      st₂.pileOfTop d = some cc)
    (hnext : st₂.nextUp d = false)
    (hlattice : ∀ z, st₂.canPlace d (Sum.inr z) = true → z = y ∨ z = y.twin)
    (hsq2 : rungAt st₂ d.suit + 2 ≤ d.rank.toIdx + 1)
    (hsq3 : raisesOf play d.suit + 2 ≤ pullsOf play d.suit)
    (hpc1 : raisesOf play y.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.suit)
    (hpc2 : raisesOf play y.twin.suit + (x.rank.toIdx - y.rank.toIdx)
      ≤ pullsOf play y.twin.suit)
    (hpid : raisesOf π d.suit + (d.rank.toIdx - w.rank.toIdx)
      ≤ pullsOf π d.suit)
    (hwfv : v.WF)
    (hrho : ShufflePlayW v ρ st₂)
    (hmint : CanRaiseS v w)
    (hwne : w ≠ y ∧ w ≠ y.twin)
    (hshape : (v.piles kk).faceUp = bs ++ [zt, w])
    (hhold : v.pileOfTop w = some kk)
    (hzrk : zt.rank.toIdx = w.rank.toIdx + 1)
    (hzcol : zt.suit.color = y.suit.color)
    (hrk : w.rank.toIdx + 1 ≤ d.rank.toIdx)
    (hw : w.suit = d.suit)
    (hv1 : rungAt v w.suit = w.rank.toIdx)
    (harch : ∃ (o : State), o.WF ∧
      d.rank.toIdx + 1 ≤ rungAt o d.suit ∧
      ∃ (pf : List Move), ShufflePlayW o pf st₂) :
    ∃ t, CanRaiseS st₂ t ∧ t ≠ y ∧ t ≠ y.twin := by
  -- the ρ-tail walks the landlord iteration; the EXISTENTIAL-MINT light
  -- kit seeds at the origin mint (off-pair by the rank ledger, its
  -- landlord one above, the census debt seeded at the landing bracket)
  exact pollutesCrash_rhoTail hd hdcol hzrk hzcol hrk hwne hsq3 hpc1 hpc2 hpid
    hw v st₂ ρ hrho (Or.inl ⟨w, hwfv, pollutesCrash_canRaiseS_nextUp hmint,
    show w.rank.toIdx + 2 ≤ y.rank.toIdx by omega,
    kk, bs ++ [zt],
    show (v.piles kk).faceUp = (bs ++ [zt]) ++ [w] from by
      rw [hshape]; simp,
    hhold,
    Or.inl (by
      show chop ((v.piles kk).faceUp) ≠ []
      rw [hshape]
      exact pollutesCrash_chop_seatTail (zt := zt) (w := w) bs),
    pollutesCrash_tailDebt_seed hw hv1⟩) hwf₂ hy hdcover hlattice
    hnext hsq2 harch

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
    lock_found_rank_lt hwf₁ hdfound
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
    have hlt := lock_found_rank_lt hwf₂ hmem
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
        exact lock_color_pair hzcol h2
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
set_option linter.unusedVariables false in
/-- **THE FOUNDED-COVER POLLUTION CRASH** — §3.5's terminal row, LANDED
ZERO-SORRY as THE ORIGIN-ANCHORED CENSUS CRASH (the nil census's landed
route, promoted to the composition head; the mint never enters).  The
d-suit HOT CARD at the terminus's own rung — `T := Card.mk d.suit
(lockRk (rungAt st₂ d.suit))`, hot by definition there
(`pollutesCrash_landing_live`: its rank index IS the terminus's d-rung),
non-king and origin-height by `omega` over `hsq2`/`hsq1`/`hd` — was
founded at the origin but is hot (never re-founded) at the terminus, so
the successor-archaeology engine `pollutesCrash_terminalHot_Below`
(the `lock_found_exit` exodus split, the fire-time bracket, the
`reseat_pop` landing kit, the `Below_stable` suffix transport) ends it
BELOW-SEATED at `st₂`; the seat fit (`lock_runOK_adjacent` +
`canSitOn_eq`) makes that below-neighbor FAMILY-colored
(`lock_color_pair` against `hdcol`) and ranked strictly under the fork
(`omega` over `hsq2`), the fork's own family rungs both pin at the pair
rank (`canRaiseS_rung` off `hy`, the twin via `Card.twin_rank`), so the
neighbor is foundation-resident (`mem_found_of_height`) while the Below
seat reads it face-up (`mem_found_unique`) — `False`, MINT-SUIT
-AGNOSTIC, no chase and no twin datum anywhere.  The seed-side premises
(`hpkg`, `hsq3`, `hpc1`, `hpc2`, the cover/lattice pack and the
origin-fork rows) stay as the frozen scaffold's documented binders —
the ρ-tail consumption they fed is retired from this crash, and the
mover chain's lone sorry (the covered-mint twin-top fork) becomes
unconsumed Stage-grade machinery, its audit profile orphaned. -/
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
  -- THE ORIGIN-ANCHORED CENSUS CRASH, at the composition head (the nil
  -- census's landed route with s₀ = st₂ and o = st₁): the d-suit hot
  -- card at the terminus's own rung rides the archaeology engine to a
  -- Below seat whose neighbor the family census has founded.  The
  -- frozen scaffold's remaining binders (the seed `hpkg`, the
  -- migration counts, the cover/lattice pack) are the set_option
  -- silenced documented package — nothing of them enters the proof's
  -- content, but the two ∃-shaped ones are DESTRUCTURED FIRST all the
  -- same: a bare `omega` facing a live ∃ premise instantiates it with
  -- `Classical.choice` (the farm's choice-noose lesson; this head's
  -- own battery caught the door once when the destructure was
  -- dropped), so every omega below runs over consumed premises only.
  obtain ⟨_w, _b, _zt, _kk, _bs, _π, _ρ, _u, _v, _hw, _hrk, _hshpi,
      _hstep, _hrev, _hrho, _htop, _hhold, _hzrk, _hzcol, _hu1,
      _hv1⟩ := hpkg
  obtain ⟨_hc, _bsC, _hshapeC, _hpodC⟩ := hdcover
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
    (canSitOn_eq T nb).mp (lock_runOK_adjacent nb T L R hok)
  have hbcol : nb.suit.color = y.suit.color :=
    lock_color_pair (a := d.suit.color)
      (by rw [← hTsuit]; exact hcolbt) hdcol
  have hyPin : rungAt st₂ y.suit = y.rank.toIdx :=
    canRaiseS_rung ((hy.1 y).mp (Or.inl rfl))
  have hytPin : rungAt st₂ y.twin.suit = y.rank.toIdx := by
    have h0 := canRaiseS_rung ((hy.1 y.twin).mp (Or.inr rfl))
    rwa [Card.twin_rank y] at h0
  have hsuit : nb.suit = y.suit ∨ nb.suit = y.twin.suit := by
    have hz : (Card.mk nb.suit y.rank) = y ∨
        (Card.mk nb.suit y.rank) = y.twin :=
      lock_rankColor_pair rfl hbcol
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
  refine ⟨by omega, forkState_sameFamily_samePair hwf₁ ((forkState_iff).mpr ⟨x, hx⟩) hcls x hx hy hfam (by omega)⟩

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
echoes NOTHING.  The retired-from-consumption ρ-tail chase
(`pollutesCrash_descent`/`rhoTail`/`rhoLeg`/`rhoMover`/`rhoMoverF`,
with its `rhoOpen` guard and the mint kit) stays in-tree as
unconsumed Stage-grade machinery: its lone literal fork (the
covered-mint twin-top datum in `rhoMover`) and its mover-local
choice leak no longer reach any audited head — the retirement deletion
is the cleanup's next pass.  The choice-noose's lesson stays banked:
`omega` instantiates a live `∃` hypothesis in its context with
`Classical.choose` — every `omega` in a census-debt context runs
only AFTER the ∃ is destructured (`rhoMover`'s head `obtain`), and
the `pollutesCrash_tailDebt_*` rows follow the same order (obtain
first, `omega` after). -/

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
#print axioms forkState_rankDrop_locked
#print axioms forkState_family_rankFloor
#print axioms forkState_family_pairClass
