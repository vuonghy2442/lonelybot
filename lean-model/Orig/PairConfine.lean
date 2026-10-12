import Orig.PairName
import Orig.BracketDecomp
import Orig.SFlatTransfer

/-!
# Orig.PairConfine — THE PAIR-CONFINEMENT CARD (the upward axis)

Within any macro class containing a `forkState`, the pair's rank
NEVER ADVANCES: the two pair-suit rungs never both exceed their
at-fork values.  The card's honest ladder:

* §1 **`pair_cover_lattice`** — THE COVER-LATTICE READ: the S-iff's
  covered branch (the orientation pin bars the twin's vanilla
  license, so the flat form pins the twin covered with its seat)
  produces the twin's DIRECT cover `d` — one rank below, opposite
  color of the pair family — and the deck census
  (`conf_rankColor_pair`, the copy of `Orig/RunOrTwin.lean`'s
  private `rankColor_pair`) reads `d`'s landing lattice: every
  legal card-directed placement of `d` tops a PAIR member, and no
  empty-seat landing exists (`d` is no king).
* §2 **`pair_cover_pins`** — the saturation reads at the fork: the
  tower above `d` is EMPTY (every γ-family card of rank index
  below the fork is already founded — a face-up occupant above `d`
  would sit on a founded card), so `d` tops the twin's pile; the
  S-saturation then forces `¬ nextUp d` (else `CanRaise st d` fires
  against the iff), and the pile discipline reads the cover suit's
  rung strictly below the fork index.
* §3 **`crossing_door_exists`** — THE CROSSING-STATE REDUCTION: if
  both pair rungs stand strictly above their at-fork values at any
  journey end, then along the forward witness shuffle some leg is
  literally `tabToFound x` (resp. `tabToFound x.twin`) fired at a
  state where the OTHER member's rung already exceeds the fork —
  the second-founding door.  Fully proved from the per-leg rung
  ledger (draw/cargo write nothing; waste legs never ride; raise
  lifts exactly its own suit; pull lowers exactly its own suit).
* §4 **`forkState_one_founding`** — THE UPWARD CONFINEMENT: the
  door never opens — consumed from `crossing_door_barred`, the
  named residue with its complete route (the cover-hop transport,
  the freeze, the pull-round-trip accounting), and the corollary
  ladder: `forkState_sameFamily_rankCeiling` (a same-family
  witness at a class member pins rank at most the fork's rank —
  the forkConsumer read) and `forkState_sameFamily_samePair` (with
  the rank pinned, the same-family witness IS the pair member, up
  to the twin flip).

House compliance: additive leaf; zero fresh `Classical.choice`;
every fresh head audited; the one named residue carries its route
in its docstring.
-/

/-! ## §0. The private kit (per-file copies, the house dedup discipline) -/

/-- Two colors that both differ from a third agree (the copy of
`Orig/RunOrTwin.lean`'s private `color_pair`). -/
private theorem conf_color_pair {a u v : Color} (h1 : a ≠ u) (h2 : a ≠ v) : u = v := by
  rcases a <;> rcases u <;> rcases v <;> simp_all

/-- **THE DECK CENSUS** — the cards of one rank and one color are
exactly the twin pair (the copy of `Orig/RunOrTwin.lean`'s private
`rankColor_pair`; `Orig/ForkStateS.lean` and `Orig/SFlatTransfer.lean`
carry identical private copies). -/
private theorem conf_rankColor_pair {c z : Card}
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
private theorem conf_runOK_adjacent (c d : Card) :
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

/-! ## §1. The cover-lattice reads -/

/-- **THE COVER-LATTICE READ**: the fork's twin-cover `d` (rank one
below the fork, opposite color of the pair family) exists as the
DIRECT card above the covered twin, with the twin's seat package, and
has EXACTLY the two pair members as its landing lattice: every legal
card-directed placement of `d` lands on a card that IS `x` or
`x.twin`, and no empty-seat placement of `d` exists (the rung
arithmetic bars the king branch). -/
theorem pair_cover_lattice {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) :
    ∃ (a : Anchor) (bs rest : List Card) (d : Card),
      (st.piles a).faceUp = bs ++ x.twin :: (d :: rest) ∧
      (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ x.twin.rank = Rank.king)) ∧
      canSitOn d x.twin = true ∧
      (∀ z : Card, st.canPlace d (Sum.inr z) = true → z = x ∨ z = x.twin) ∧
      (∀ k : Anchor, st.canPlace d (Sum.inl k) = true → False) := by
  obtain ⟨hiff, hnt⟩ := hx
  have htwinS : CanRaiseS st x.twin := (hiff x.twin).mp (Or.inr rfl)
  obtain ⟨hnextt, a, bs, run, hshape, hseat, hdisj⟩ := (canRaiseS_iff hwf).1 htwinS
  -- the covered branch: the twin cannot top (the pin's vanilla bar)
  have hrunne : run ≠ [] := by
    intro hrun
    rw [hrun] at hshape
    have htop : (st.piles a).top = some x.twin := by
      show lastOf (st.piles a).faceUp = some x.twin
      rw [hshape]
      exact lastOf_snoc
    have hseat' : chop (st.piles a).faceUp ≠ [] ∨
        ((st.piles a).hidden = [] ∧ x.twin.rank = Rank.king) := by
      rw [hshape]
      rcases hseat with hbs | hhk
      · exact Or.inl (by rw [chop_snoc]; exact hbs)
      · exact Or.inr hhk
    exact hnt ⟨hnextt, a, (pileOfTop_eq_some_iff hwf).2 htop, hseat'⟩
  obtain ⟨d, rest, hrun⟩ := list_cons_of_ne_nil hrunne
  rw [hrun] at hshape
  have hfit : canSitOn d x.twin = true :=
    conf_runOK_adjacent x.twin d bs rest (by rw [← hshape]; exact hwf.runOK_of a)
  refine ⟨a, bs, rest, d, hshape, hseat, hfit, ?_, ?_⟩
  · -- the card-directed lattice: a pair member tops every landing
    intro z hcp
    obtain ⟨k, hpo, hsit⟩ := canPlace_inr hcp
    obtain ⟨hridx, hcol⟩ := (canSitOn_eq d z).mp hsit
    obtain ⟨hridxt, hcolt⟩ := (canSitOn_eq d x.twin).mp hfit
    have hzr : z.rank.toIdx = x.rank.toIdx := by
      rw [Card.twin_rank] at hridxt
      omega
    have hu : z.suit.color = x.twin.suit.color :=
      conf_color_pair (a := d.suit.color) hcol hcolt
    have hzc : z.suit.color = x.suit.color := by
      rw [hu, Card.twin_suit, Suit.color_twin]
    exact conf_rankColor_pair hzr hzc
  · -- the empty-seat lattice: the king branch is arithmetically dead
    intro k hcp
    obtain ⟨-, hking⟩ := canPlace_inl hcp
    obtain ⟨hridxt, -⟩ := (canSitOn_eq d x.twin).mp hfit
    rw [hking, Card.twin_rank] at hridxt
    have hk12 : Rank.king.toIdx = 12 := rfl
    have hlt := Rank.toIdx_lt x.rank
    omega

/-! ## §2. The saturation pins -/

/-- An element at position `i` belongs to the first `n` entries of the
list when `i < n` (the copy of `Orig/CanV3.lean`'s private
`v3GetInTake`). -/
private theorem conf_get_in_take : ∀ {α : Type} (l : List α) (n i : Nat)
    (hl : i < l.length) (hn : i < n), l.get ⟨i, hl⟩ ∈ l.take n := by
  intro α l n i hl hn
  induction n generalizing l i hl with
  | zero => exact absurd hn (by omega)
  | succ n ih =>
      cases l with
      | nil => exact absurd hl (by simp)
      | cons a t =>
          cases i with
          | zero =>
              show a ∈ a :: t.take n
              exact List.mem_cons.2 (Or.inl rfl)
          | succ i' =>
              simp only [List.length_cons] at hl
              refine List.mem_cons_of_mem a (ih t i' (by omega) (by omega))

/-- A card sits at its own build index in its suit's foundation
order (the copy of `Orig/CanV3.lean`'s private `v3UpGet`). -/
private theorem conf_upCards_get (z : Card)
    (h : z.rank.toIdx < z.suit.upCards.length) :
    z.suit.upCards.get ⟨z.rank.toIdx, h⟩ = z := by
  rcases z with ⟨zs, zr⟩
  cases zr <;> rfl

/-- **THE FOUNDED-BRIDGE** — a suit rung strictly above a card's rank
index has already founded it (the founded-prefix read of the WF
clause, through the build-index rows). -/
private theorem conf_mem_found_of_rung {st : State} (hwf : st.WF) {c : Card}
    (hlt : c.rank.toIdx < rungAt st c.suit) : c ∈ st.found c.suit := by
  have hpre := rung_found_prefix st hwf c.suit
  have h13 : c.suit.upCards.length = 13 := Suit.upCards_length c.suit
  have hget : c.suit.upCards.get ⟨c.rank.toIdx, by
      rw [h13]; exact Rank.toIdx_lt c.rank⟩ = c :=
    conf_upCards_get c (by rw [h13]; exact Rank.toIdx_lt c.rank)
  have hmem0 : c.suit.upCards.get ⟨c.rank.toIdx, by
      rw [h13]; exact Rank.toIdx_lt c.rank⟩ ∈
      c.suit.upCards.take (rungAt st c.suit) :=
    conf_get_in_take c.suit.upCards (rungAt st c.suit) c.rank.toIdx
      (show c.rank.toIdx < c.suit.upCards.length by
        rw [h13]; exact Rank.toIdx_lt c.rank) hlt
  rw [hget] at hmem0
  have hmem : c ∈ c.suit.upCards.take (rungAt st c.suit) := hmem0
  rwa [← hpre] at hmem

/-- The last of a double snoc (the two-card top read of the
covered-twin pile shape). -/
private theorem conf_snoc2_last (bs : List Card) (u d : Card) :
    lastOf (bs ++ [u, d]) = some d := by
  have h : bs ++ [u, d] = (bs ++ [u]) ++ [d] := by
    cases bs <;> simp [List.append_assoc]
  rw [h]
  exact lastOf_snoc

/-- The chop of a double snoc (the two-card below read of the
covered-twin pile shape). -/
private theorem conf_snoc2_chop (bs : List Card) (u d : Card) :
    chop (bs ++ [u, d]) = bs ++ [u] := by
  have h : bs ++ [u, d] = (bs ++ [u]) ++ [d] := by
    cases bs <;> simp [List.append_assoc]
  rw [h]
  exact chop_snoc

/-- The color family is the twin-suit family: a same-color suit is
the suit or its twin (the census read at the suit grade). -/
private theorem conf_suit_family {s t : Suit} (h : s.color = t.color) :
    s = t ∨ s = t.twin := by
  cases s <;> cases t <;> simp_all [Suit.color, Suit.twin]

/-- **THE PILED-RUNG ROW** — a face-up card's suit rung sits weakly
below its rank index: a taller rung would have founded it (the
founded bridge) against conservation. -/
private theorem conf_piled_rung {st : State} (hwf : st.WF) {z : Card} {a : Anchor}
    (hmem : z ∈ (st.piles a).faceUp) : rungAt st z.suit ≤ z.rank.toIdx := by
  have hnot : z ∉ st.found z.suit := (mem_faceUp_only hwf hmem).2.2.2.2 z.suit
  rcases Nat.lt_trichotomy (rungAt st z.suit) (z.rank.toIdx) with h | h | h
  · exact Nat.le_of_lt h
  · exact Nat.le_of_eq h
  · exact absurd (conf_mem_found_of_rung hwf h) hnot

/-- **THE γ-FAMILY LOW ROW** — every same-family card of rank index
strictly below the fork is ALREADY FOUNDED at the fork: both suit
rungs of the pair family pin the fork index, and the founded bridge
reads the membership. -/
theorem pair_lowFamily_founded {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) {c : Card}
    (hcol : c.suit.color = x.suit.color)
    (hlt : c.rank.toIdx < x.rank.toIdx) :
    c ∈ st.found c.suit := by
  have hr : rungAt st c.suit = x.rank.toIdx := by
    rcases conf_suit_family hcol with hs | hs
    · rw [hs]
      exact canRaiseS_rung ((hx.1 x).mp (Or.inl rfl))
    · rw [hs]
      have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
      rwa [Card.twin_rank] at h2
  exact conf_mem_found_of_rung hwf (by omega)

/-- **THE SATURATION PINS** — the fork's twin-cover package at its
final shape: the cover `d` sits DIRECTLY on the twin (one below,
opposite family), the tower above it is EMPTY (every γ-family card
below the fork is already founded, so nothing can cover a cover), so
`d` tops the twin's pile — and then the S-saturation forces `d`
non-nextUp (`else CanRaise st d` fires against the iff), with the
cover suit's rung strictly below the fork index. -/
theorem pair_cover_pins {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) :
    ∃ (a : Anchor) (bs : List Card) (d : Card),
      (st.piles a).faceUp = bs ++ [x.twin, d] ∧
      (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ x.twin.rank = Rank.king)) ∧
      canSitOn d x.twin = true ∧
      st.pileOfTop d = some a ∧
      st.nextUp d = false ∧
      rungAt st d.suit + 1 ≤ x.rank.toIdx := by
  obtain ⟨a, bs, rest, d, hshape, hseat, hfit, -, -⟩ :=
    pair_cover_lattice hwf hx
  obtain ⟨hiff, hnt⟩ := id hx
  -- the fit arithmetic: the cover is one rank below, opposite family
  obtain ⟨hridx, hcol⟩ := (canSitOn_eq d x.twin).mp hfit
  rw [Card.twin_rank] at hridx
  -- THE TOWER BAR: nothing sits directly above d (any occupant is a
  -- γ-family low card — already founded — against conservation)
  have hrest : rest = [] := by
    cases rest with
    | nil => rfl
    | cons w rest' =>
        exfalso
        have hok' : runOK (bs ++ x.twin :: (d :: w :: rest')) = true := by
          rw [← hshape]
          exact hwf.runOK_of a
        have hok : runOK ((bs ++ [x.twin]) ++ (d :: w :: rest')) = true := by
          rw [List.append_assoc bs [x.twin] (d :: w :: rest')]
          exact hok'
        have hfit2 : canSitOn w d = true :=
          conf_runOK_adjacent d w (bs ++ [x.twin]) rest' hok
        obtain ⟨hridx2, hcol2⟩ := (canSitOn_eq w d).mp hfit2
        have hwcol0 : w.suit.color = x.twin.suit.color :=
          conf_color_pair (a := d.suit.color) hcol2.symm hcol
        have hwcol : w.suit.color = x.suit.color := by
          rw [hwcol0, Card.twin_suit, Suit.color_twin]
        have hwlt : w.rank.toIdx < x.rank.toIdx := by omega
        have hwfounded := pair_lowFamily_founded hwf hx hwcol hwlt
        have hwmem : w ∈ (st.piles a).faceUp := by
          rw [hshape]
          exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr
            (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
        exact (mem_faceUp_only hwf hwmem).2.2.2.2 w.suit hwfounded
  subst hrest
  -- d tops the twin's pile
  have hdtop : st.pileOfTop d = some a := by
    refine (pileOfTop_eq_some_iff hwf).2 ?_
    show lastOf (st.piles a).faceUp = some d
    rw [hshape]
    exact conf_snoc2_last bs x.twin d
  -- THE SATURATION BAR: d cannot be nextUp (it tops with seat, so
  -- nextUp would arm CanRaise st d, breaking the pair-only iff)
  have hnotnext : st.nextUp d = false := by
    cases hn : st.nextUp d with
    | true =>
        exfalso
        have hseat' : chop (st.piles a).faceUp ≠ [] ∨
            ((st.piles a).hidden = [] ∧ d.rank = Rank.king) := by
          rw [hshape, conf_snoc2_chop bs x.twin d]
          exact Or.inl (by cases bs <;> simp)
        have hcan : CanRaise st d := ⟨hn, a, hdtop, hseat'⟩
        rcases (hiff d).mpr (CanRaiseS.now d hcan) with hc | hc
        · rw [hc] at hridx
          omega
        · rw [hc, Card.twin_rank] at hridx
          omega
    | false => rfl
  -- the rung pin: the pile discipline reads the cover suit's rung
  have hdmem : d ∈ (st.piles a).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr
      (List.mem_singleton.mpr rfl))))
  have hrung : rungAt st d.suit + 1 ≤ x.rank.toIdx := by
    have h1 := conf_piled_rung hwf hdmem
    have hne : d.rank.toIdx ≠ rungAt st d.suit := by
      intro hcon
      have hn2 : st.nextUp d = true := decide_eq_true hcon
      rw [hn2] at hnotnext
      exact absurd hnotnext (by simp)
    omega
  exact ⟨a, bs, d, hshape, hseat, hfit, hdtop, hnotnext, hrung⟩

/-! ## §3. The crossing-state reduction -/

/-- A draw writes no rung (the copy of the ledger row). -/
private theorem conf_rung_draw {st st' : State}
    (hstep : st.step Move.draw = some st') :
    ∀ s, rungAt st' s = rungAt st s := by
  intro s
  show (st'.found s).length = (st.found s).length
  rw [stepDraw_found hstep]

/-- A cargo slide writes no rung (the copy of the ledger row; the
step's successor equation rewrites through `putRun_found` and
`setPile_found`). -/
private theorem conf_rung_cargo {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.tabToTab c b) = some st') :
    ∀ s, rungAt st' s = rungAt st s := by
  obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv hstep
  intro s
  show (st'.found s).length = (st.found s).length
  rw [hs, putRun_found, setPile_found]

/-- A raise writes exactly its own suit's foundation row and no other
(the banked trio's first two reads, restated for the ledger). -/
private theorem conf_raise_found {st st' : State} {c : Card}
    (hstep : State.step st (Move.tabToFound c) = some st') :
    st'.found c.suit = st.found c.suit ++ [c] ∧
      ∀ s, s ≠ c.suit → st'.found s = st.found s := by
  obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
  obtain ⟨hself, hothers, -⟩ := tabToFound_found_trio (a := a) hs
  exact ⟨hself, hothers⟩

/-- **THE RAISE LEDGER** — a raise lifts exactly its own suit's rung
by one and leaves every other rung in place. -/
private theorem conf_rung_raise {st st' : State} {c : Card}
    (hstep : State.step st (Move.tabToFound c) = some st') :
    rungAt st' c.suit = rungAt st c.suit + 1 ∧
      ∀ s, s ≠ c.suit → rungAt st' s = rungAt st s := by
  obtain ⟨hself, hothers⟩ := conf_raise_found hstep
  refine ⟨?_, ?_⟩
  · show (st'.found c.suit).length = (st.found c.suit).length + 1
    rw [hself, List.length_append]
    have h1 : ([c] : List Card).length = 1 := rfl
    omega
  · intro s hs
    show (st'.found s).length = (st.found s).length
    rw [hothers s hs]

/-- A pull writes exactly its own suit's foundation row back and no
other (the copy of the ledger row's found-half). -/
private theorem conf_pull_found {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some st') :
    st'.found c.suit = chop (st.found c.suit) ∧
      ∀ s, s ≠ c.suit → st'.found s = st.found s := by
  obtain ⟨c', htop, hc'c, -, hs⟩ := step_foundToTab_inv hstep
  refine ⟨?_, ?_⟩
  · rw [hs]
    show ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found c.suit
      = chop (st.found c.suit)
    rw [show ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found
        = (st.setFound c.suit (chop (st.found c.suit))).found from
      putCard_found _ _ _]
    exact setFound_found_self
  · intro s h
    rw [hs]
    show ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found s
      = st.found s
    rw [show ((st.setFound c.suit (chop (st.found c.suit))).putCard c b).found
        = (st.setFound c.suit (chop (st.found c.suit))).found from
      putCard_found _ _ _]
    exact setFound_found_ne h

/-- **THE PULL LEDGER** — a pull lowers exactly its own suit's rung
by one and leaves every other rung in place (the guard names the
popped card as the foundation's current top, so the row was a snoc). -/
private theorem conf_rung_pull {st st' : State} {c : Card} {b : Base}
    (hstep : State.step st (Move.foundToTab c b) = some st') :
    rungAt st c.suit = rungAt st' c.suit + 1 ∧
      ∀ s, s ≠ c.suit → rungAt st' s = rungAt st s := by
  obtain ⟨hself, hothers⟩ := conf_pull_found hstep
  obtain ⟨c', htop, hc'c, -, -⟩ := step_foundToTab_inv hstep
  rw [hc'c] at htop
  have hlast : lastOf (st.found c.suit) = some c := htop
  have hlen := congrArg (List.length) (lastOf_chop hlast)
  rw [List.length_append] at hlen
  have h1 : ([c] : List Card).length = 1 := rfl
  refine ⟨?_, ?_⟩
  · show (st.found c.suit).length = (st'.found c.suit).length + 1
    rw [hself]
    omega
  · intro s hs
    show (st'.found s).length = (st.found s).length
    rw [hothers s hs]

/-- A card is its suit-and-rank-index: the identity read behind the
crossing-card chase. -/
private theorem conf_card_of_suit_toIdx {c z : Card}
    (hs : c.suit = z.suit) (hr : c.rank.toIdx = z.rank.toIdx) : c = z := by
  rcases c with ⟨cs, cr⟩
  rcases z with ⟨zs, zr⟩
  have hsr : cr = zr := Rank.toIdx_inj hr
  simp only [Card.mk.injEq]
  exact ⟨hs, hsr⟩

/-- The pair suits are distinct: a card's twin wears the twin suit. -/
private theorem conf_twin_suit_ne (x : Card) : x.twin.suit ≠ x.suit := by
  rw [Card.twin_suit]
  exact Suit.twin_ne x.suit

/-- **THE CROSSING-STATE REDUCTION** — if both pair rungs stand
strictly above the fork index at a witness-shuffle's end (with the
start not yet elevated), then the play contains the SECOND-FOUNDING
DOOR: an interior journey state whose firing leg is literally
`tabToFound x` (resp. `tabToFound x.twin`) while the OTHER member's
rung already exceeds the fork index.  Fully proved: along a witness
journey the waste letters never ride and the draw/cargo letters write
no rung, so the leg that first makes BOTH rungs exceed the index is a
raise — it lifts one pair suit from exactly the index (the `nextUp`
guard) onto the already-elevated other (the firstness read); the
founded-prefix arithmetic names the raised card as the pair member
itself. -/
theorem crossing_door_exists {st : State} {x : Card} :
    ∀ {w : State} {play : List Move},
    ShufflePlayW st play w →
    ¬ (rungAt st x.suit > x.rank.toIdx ∧
       rungAt st x.twin.suit > x.rank.toIdx) →
    (rungAt w x.suit > x.rank.toIdx ∧
     rungAt w x.twin.suit > x.rank.toIdx) →
    ∃ (u s₁ : State) (π : List Move),
      ShufflePlayW st π u ∧
      ((State.step u (Move.tabToFound x) = some s₁ ∧
          rungAt u x.twin.suit > x.rank.toIdx) ∨
       (State.step u (Move.tabToFound x.twin) = some s₁ ∧
          rungAt u x.suit > x.rank.toIdx)) := by
  intro w play h
  induction h with
  | nil u =>
      intro hNQ hQ
      exact absurd hQ hNQ
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro hNQ hQ
      rcases Decidable.em
        (rungAt s₁ x.suit > x.rank.toIdx ∧
         rungAt s₁ x.twin.suit > x.rank.toIdx) with hQ₁ | hNQ₁
      · -- THE FIRST LEG CROSSES: the leg ledger names the crossing
        obtain ⟨hQ₁A, hQ₁B⟩ := hQ₁
        cases m with
        | draw =>
            have hA : rungAt s₁ x.suit = rungAt s₀ x.suit :=
              conf_rung_draw hstep x.suit
            have hB : rungAt s₁ x.twin.suit = rungAt s₀ x.twin.suit :=
              conf_rung_draw hstep x.twin.suit
            exact absurd ⟨by rw [← hA]; exact hQ₁A, by rw [← hB]; exact hQ₁B⟩ hNQ
        | wasteToFound c =>
            exact absurd hrev (journey_never_wasteToFound hstep)
        | wasteToTab c b =>
            exact absurd hrev (journey_never_wasteToTab hstep)
        | tabToTab c b =>
            have hA : rungAt s₁ x.suit = rungAt s₀ x.suit :=
              conf_rung_cargo hstep x.suit
            have hB : rungAt s₁ x.twin.suit = rungAt s₀ x.twin.suit :=
              conf_rung_cargo hstep x.twin.suit
            exact absurd ⟨by rw [← hA]; exact hQ₁A, by rw [← hB]; exact hQ₁B⟩ hNQ
        | tabToFound c =>
            obtain ⟨hn, a, hpo, hs⟩ := step_tabToFound_inv hstep
            obtain ⟨hrise, hothers⟩ := conf_rung_raise hstep
            have hcnext : c.rank.toIdx = rungAt s₀ c.suit :=
              of_decide_eq_true hn
            by_cases hsx : c.suit = x.suit
            · -- the raised suit is x's: the other member already stands
              -- elevated, so this leg is literally the SECOND founding
              rw [hsx] at hrise hcnext
              have hB₀eq : rungAt s₀ x.twin.suit = rungAt s₁ x.twin.suit :=
                (hothers x.twin.suit (fun hcon =>
                  conf_twin_suit_ne x (hcon.trans hsx))).symm
              have hB₀gt : rungAt s₀ x.twin.suit > x.rank.toIdx := by
                rw [hB₀eq]
                omega
              have hA₀ : rungAt s₀ x.suit = x.rank.toIdx := by
                rcases Nat.lt_trichotomy (rungAt s₀ x.suit) (x.rank.toIdx) with
                  h | h | h
                · omega
                · exact h
                · exact absurd ⟨h, hB₀gt⟩ hNQ
              have hcx : c = x :=
                conf_card_of_suit_toIdx hsx (by omega)
              rw [hcx] at hstep
              exact ⟨s₀, s₁, [], .nil s₀, Or.inl ⟨hstep, hB₀gt⟩⟩
            · by_cases hsxt : c.suit = x.twin.suit
              · -- the raised suit is the twin's: the witness already
                -- stands elevated, so this leg is literally the second
                -- founding
                rw [hsxt] at hrise hcnext
                have hA₀eq : rungAt s₀ x.suit = rungAt s₁ x.suit :=
                  (hothers x.suit (fun hcon =>
                    conf_twin_suit_ne x ((hcon.trans hsxt).symm))).symm
                have hA₀gt : rungAt s₀ x.suit > x.rank.toIdx := by
                  rw [hA₀eq]
                  omega
                have hB₀ : rungAt s₀ x.twin.suit = x.rank.toIdx := by
                  rcases Nat.lt_trichotomy (rungAt s₀ x.twin.suit)
                      (x.rank.toIdx) with h | h | h
                  · omega
                  · exact h
                  · exact absurd ⟨hA₀gt, h⟩ hNQ
                have hcxt : c = x.twin :=
                  conf_card_of_suit_toIdx hsxt (by
                    rw [Card.twin_rank, hcnext]
                    exact hB₀)
                rw [hcxt] at hstep
                exact ⟨s₀, s₁, [], .nil s₀, Or.inr ⟨hstep, hA₀gt⟩⟩
              · -- a foreign-suit raise moves neither pair rung
                have hA₀eq : rungAt s₀ x.suit = rungAt s₁ x.suit :=
                  (hothers x.suit (fun hcon => hsx hcon.symm)).symm
                have hB₀eq : rungAt s₀ x.twin.suit = rungAt s₁ x.twin.suit :=
                  (hothers x.twin.suit (fun hcon => hsxt hcon.symm)).symm
                exact absurd ⟨by rw [hA₀eq]; exact hQ₁A,
                  by rw [hB₀eq]; exact hQ₁B⟩ hNQ
        | foundToTab c b =>
            obtain ⟨hdrop, hothers⟩ := conf_rung_pull hstep
            by_cases hsx : c.suit = x.suit
            · -- a pull only lowers its own suit: the first leg cannot have
              -- crossed through a pull
              rw [hsx] at hdrop
              have hB₀eq : rungAt s₀ x.twin.suit = rungAt s₁ x.twin.suit :=
                (hothers x.twin.suit (fun hcon =>
                  conf_twin_suit_ne x (hcon.trans hsx))).symm
              have hA₀gt : rungAt s₀ x.suit > x.rank.toIdx := by omega
              have hB₀gt : rungAt s₀ x.twin.suit > x.rank.toIdx := by
                rw [hB₀eq]
                omega
              exact absurd ⟨hA₀gt, hB₀gt⟩ hNQ
            · by_cases hsxt : c.suit = x.twin.suit
              · rw [hsxt] at hdrop
                have hA₀eq : rungAt s₀ x.suit = rungAt s₁ x.suit :=
                  (hothers x.suit (fun hcon =>
                    conf_twin_suit_ne x ((hcon.trans hsxt).symm))).symm
                have hB₀gt : rungAt s₀ x.twin.suit > x.rank.toIdx := by omega
                have hA₀gt : rungAt s₀ x.suit > x.rank.toIdx := by
                  rw [hA₀eq]
                  omega
                exact absurd ⟨hA₀gt, hB₀gt⟩ hNQ
              · have hA₀eq : rungAt s₀ x.suit = rungAt s₁ x.suit :=
                  (hothers x.suit (fun hcon => hsx hcon.symm)).symm
                have hB₀eq : rungAt s₀ x.twin.suit = rungAt s₁ x.twin.suit :=
                  (hothers x.twin.suit (fun hcon => hsxt hcon.symm)).symm
                exact absurd ⟨by rw [hA₀eq]; exact hQ₁A,
                  by rw [hB₀eq]; exact hQ₁B⟩ hNQ
      · -- recurse into the tail with the interior start
        obtain ⟨u, s₂, π, hsh, hdoor⟩ := ih hNQ₁ hQ
        exact ⟨u, s₂, m :: π, .cons hrev hstep hsh, hdoor⟩

/-! ## §4. THE ONE-FOUNDING INVARIANT (the upward axis) -/

/-- **THE CROSSING-DOOR BAR** — the card's one named residue.

The premise: `u` is a witness-journey state (forward-reachable from
the fork State `st`, its prefix a `ShufflePlayW`, every leg one-move
undone) where `tabToFound x` (resp. `tabToFound x.twin`) FIRES while
the other pair member's rung already exceeds the fork index, i.e.
`x.twin` (resp. `x`) is already FOUNDED at `u`.

THE COMPLETE ROUTE (each step priced against this file's landed rows
and the banked machinery):

1. FOUNDED-BRIDGE AT `u`: `u.WF` (WF descends the prefix via
   `step_wf`), so `rungAt u x.twin.suit > x.rank.toIdx` reads
   `x.twin ∈ u.found x.twin.suit` (`conf_mem_found_of_rung`); the
   firing raise's own inversion (`step_tabToFound_inv`) reads `x`
   topping pile `a` with `nextUp` and a seat package.
2. THE ST-SIDE COVER PACKAGE: `pair_cover_pins` — the twin's direct
   cover `d` tops the twin's pile at `st` with `st.nextUp d = false`
   and `rungAt st d.suit + 1 ≤ x.rank.toIdx`.
3. THE COVER-HOP TRANSPORT over the prefix's legs: draw and cargo
   legs write no rung; cargo legs move covers only between pair
   members (the landing lattice of `pair_cover_lattice`: a cover's
   legal card-directed placement tops a PAIR member; the founded
   member is off-board by `mem_faceUp_only`, so the hop pins the
   cover to the on-board member — the `S_census_one_leg` engine,
   generalized per leg); raise/pull legs of foreign suits preserve
   every pair-side fact. The analysis reduces to: at `u`, `x` was
   exposed by a leg departing from `x`'s own direct cover `c` — a
   cover-family card (of `{d, d.twin}`, rank index `r − 1`, opposite
   family, the run-discipline fit via `conf_runOK_adjacent`).
4. THE FREEZE: the acting cover `c` can never be FOUNDED along the
   way — its suit's rung sits below `r − 1` at `st`
   (`pair_cover_pins`), and no `c.suit` raise can fire: each would
   need a face-up `c.suit`-card of rank index `< r − 1`, and every
   such card sits (run discipline) on a γ-family card of rank index
   `≤ r − 1`, all FOUNDED at `st` (`pair_lowFamily_founded`) and
   un-exposable from the stock/hidden/waste freeze (waste legs never
   ride; reveals never ride; pulls of them need γ-family tops one
   rank up — inductively frozen); the deck census then closes every
   `tabToTab` departure of a cover while one member is founded: the
   landing lattice has no on-board target.
5. THE PULL ROUND-TRIPS: pulls pop LIFO
   (`foundToTab_pops_currentTop`), so a founded member returns only by
   a pull landing on an on-board family top — barred by the same
   lattice read — and the oscillation accounting closes through the
   per-suit census (`witness_rung_census` over `raisesOf`/`pullsOf`).

Until the transport of 3–5 lands as rows, the bar is honestly open;
the main invariant below carries exactly this residue and no other. -/
private theorem crossing_door_barred {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) {u s₁ : State} (π : List Move)
    (hpre : ShufflePlayW st π u) :
    ((State.step u (Move.tabToFound x) = some s₁ ∧
        rungAt u x.twin.suit > x.rank.toIdx) ∨
     (State.step u (Move.tabToFound x.twin) = some s₁ ∧
        rungAt u x.suit > x.rank.toIdx)) →
    False := by
  sorry

/-- **THE ONE-FOUNDING INVARIANT — the upward confinement**: within
any macro class containing a `forkState`, the PAIR'S RANK NEVER
ADVANCES — the two pair-suit rungs never both exceed their at-fork
values at any journey endpoint.  The proof: the class's forward
witness play plus the fork's own pins hand the crossing-state
reduction (`crossing_door_exists`) the both-elevated end state; the
reduction pins the second-founding door leg literally as a
`tabToFound` of a pair member at a state where the other member is
already founded; the named residue `crossing_door_barred` (route
above) bars the door. -/
theorem forkState_one_founding {st st' : State} (hwf : st.WF)
    (h : forkState st) (hjourney : sameOrbitSetoid.r st st')
    (x : Card) (hx : ForkWitness st x) :
    ¬ (rungAt st' x.suit > rungAt st x.suit ∧
       rungAt st' x.twin.suit > rungAt st x.twin.suit) := by
  intro ⟨hA, hB⟩
  have _hfork := h
  obtain ⟨τ, hτ⟩ := sameOrbit_forward hjourney
  have hr0 : rungAt st x.suit = x.rank.toIdx :=
    canRaiseS_rung ((hx.1 x).mp (Or.inl rfl))
  have hr1 : rungAt st x.twin.suit = x.rank.toIdx := by
    have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
    rwa [Card.twin_rank] at h2
  have hNQst : ¬ (rungAt st x.suit > x.rank.toIdx ∧
      rungAt st x.twin.suit > x.rank.toIdx) := by
    rintro ⟨h1, h2⟩
    omega
  have hQw : rungAt st' x.suit > x.rank.toIdx ∧
      rungAt st' x.twin.suit > x.rank.toIdx :=
    ⟨by omega, by omega⟩
  obtain ⟨u, s₁, π, hpre, hdoor⟩ :=
    crossing_door_exists hτ hNQst hQw
  exact crossing_door_barred hwf hx π hpre hdoor

/-! ## §5. The forkConsumer corollaries -/

/-- **THE FORKCONSUMER RANK CEILING** — any `forkState` IN THE CLASS
witnessing the same suit family necessarily pins a rank AT MOST the
fork's rank: the same-family witness's rung pins identify both pair
rungs at `st'` with the witness's rank index, and a strictly greater
index would put BOTH pair rungs above their at-fork values against the
one-founding invariant.  (The downward half — that the index cannot be
strictly SMALLER — is the sibling probe's axis, not this card's.) -/
theorem forkState_sameFamily_rankCeiling {st st' : State} (hwf : st.WF)
    (h : forkState st) (hjourney : sameOrbitSetoid.r st st')
    (x : Card) (hx : ForkWitness st x)
    {y : Card} (hy : ForkWitness st' y)
    (hys : y.suit = x.suit ∨ y.suit = x.twin.suit) :
    y.rank.toIdx ≤ x.rank.toIdx := by
  have _hfork := h
  have hr0 : rungAt st x.suit = x.rank.toIdx :=
    canRaiseS_rung ((hx.1 x).mp (Or.inl rfl))
  have hr1 : rungAt st x.twin.suit = x.rank.toIdx := by
    have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
    rwa [Card.twin_rank] at h2
  have hyA : rungAt st' y.suit = y.rank.toIdx :=
    canRaiseS_rung ((hy.1 y).mp (Or.inl rfl))
  have hyB : rungAt st' y.twin.suit = y.rank.toIdx :=
    canRaiseS_rung ((hy.1 y.twin).mp (Or.inr rfl))
  rcases hys with hs | hs
  · -- the witness names x's own suit: both pins identify the pair rungs
    have hs2 : y.twin.suit = x.twin.suit := by
      simp only [Card.twin_suit, hs]
    have heq1 : rungAt st' x.suit = y.rank.toIdx := by
      rw [hs] at hyA
      exact hyA
    have heq2 : rungAt st' x.twin.suit = y.rank.toIdx := by
      rw [hs2] at hyB
      exact hyB
    rcases Nat.lt_trichotomy (y.rank.toIdx) (x.rank.toIdx) with hlt | heq | hgt
    · exact Nat.le_of_lt hlt
    · exact Nat.le_of_eq heq
    · exact absurd ⟨by omega, by omega⟩
        (forkState_one_founding hwf h hjourney x hx)
  · -- the witness names the twin's suit: the pins identify, mirrored
    have hs2 : y.twin.suit = x.suit := by
      simp only [Card.twin_suit, hs, Suit.twin_twin]
    have heqB : rungAt st' x.twin.suit = y.rank.toIdx := by
      rw [hs] at hyA
      exact hyA
    have heqA : rungAt st' x.suit = y.rank.toIdx := by
      rw [hs2] at hyB
      exact hyB
    rcases Nat.lt_trichotomy (y.rank.toIdx) (x.rank.toIdx) with hlt | heq | hgt
    · exact Nat.le_of_lt hlt
    · exact Nat.le_of_eq heq
    · exact absurd ⟨by omega, by omega⟩
        (forkState_one_founding hwf h hjourney x hx)

/-- **THE SAME-NEXT-UP READ** — with the rank index pinned (the
ceiling row's equality case), a same-family witness at a class member
IS a pair member, up to the twin flip: suit and rank-index together
name the card (`conf_card_of_suit_toIdx`).  Together with
`forkState_sameFamily_rankCeiling` this is the forkConsumer
corollary: any forkState in the class witnessing the same suit pair
and family pins the same next-ups. -/
theorem forkState_sameFamily_samePair {st st' : State} (hwf : st.WF)
    (h : forkState st) (hjourney : sameOrbitSetoid.r st st')
    (x : Card) (hx : ForkWitness st x)
    {y : Card} (hy : ForkWitness st' y)
    (hys : y.suit = x.suit ∨ y.suit = x.twin.suit)
    (hrank : y.rank.toIdx = x.rank.toIdx) :
    y = x ∨ y = x.twin := by
  rcases hys with hs | hs
  · exact Or.inl (conf_card_of_suit_toIdx hs hrank)
  · refine Or.inr (conf_card_of_suit_toIdx hs ?_)
    rwa [Card.twin_rank]

/-- WF travels a witness shuffle (the leg-step induction over
`step_wf`). -/
private theorem conf_shuffle_wf {st : State} : ∀ {play : List Move} {v : State},
    ShufflePlayW st play v → st.WF → v.WF := by
  intro play v h
  induction h with
  | nil u => intro hwf; exact hwf
  | @cons s₀ m s₁ rest v₀ hrev hstep hrest ih =>
      intro hwf
      exact ih (step_wf hwf hstep)

/-- **THE DOOR-STATE READ** — the residue's step 1, closed as rows: at
a crossing-door state the already-elevated member is LITERALLY in its
suit's foundation and the firing member tops its pile with the seat
package.  The follow-up card that lands the cover-hop transport and
the freeze consumes exactly this read as its starting geometry. -/
theorem crossing_door_read {st u u' : State} (hwf : st.WF)
    (π : List Move) (hpre : ShufflePlayW st π u)
    {x : Card}
    (hstep : State.step u (Move.tabToFound x) = some u')
    (helev : rungAt u x.twin.suit > x.twin.rank.toIdx) :
    x.twin ∈ u.found x.twin.suit ∧
      (∃ a, u.pileOfTop x = some a) ∧ u.nextUp x = true := by
  have hwfu : u.WF := conf_shuffle_wf hpre hwf
  have hindb : x.twin ∈ u.found x.twin.suit := by
    refine conf_mem_found_of_rung hwfu ?_
    rwa [Card.twin_rank] at helev
  obtain ⟨hnext, a, hpo, -⟩ := step_tabToFound_inv hstep
  exact ⟨hindb, ⟨a, hpo⟩, hnext⟩

/-! ## The audit battery -/

#print axioms crossing_door_exists
#print axioms crossing_door_read
#print axioms crossing_door_barred
#print axioms forkState_one_founding
#print axioms forkState_sameFamily_rankCeiling
#print axioms forkState_sameFamily_samePair
#print axioms pair_lowFamily_founded
#print axioms pair_cover_lattice
#print axioms pair_cover_pins
