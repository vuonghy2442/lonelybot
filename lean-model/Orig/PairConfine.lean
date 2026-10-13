import Orig.PairName
import Orig.BracketDecomp
import Orig.FoundKit
import Orig.SFlatTransfer
import Orig.OrphanSeat

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
  (`SeedKit.rankColor_pair`, the copy of `Orig/RunOrTwin.lean`'s
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
* §4 **The backward-orphan kill** — THE DOOR BAR: `crossing_door_barred`
  runs both door orders through `conf_door_orphan`.  Every witness
  journey rides back (`conf_playback` — the same-orbit setoid's own
  second play, spliced by `ShufflePlayW_append`); on the backward
  read the door's founding forces the two-below twin's seat into
  the open, where the imported residue `cross_orphan_seat`
  (`Orig/OrphanSeat.lean`) plants its below-neighbor and the fork
  census (`pair_lowFamily_founded` + `mem_faceUp_only`) kills it.
  The forward-end split runs by `conf_orphan_roam` (the banked
  `Below_stable`): a surviving seat dies on the top clash
  (`conf_orphan_topclash`) or the found/face-up exclusivity, and the
  nowhere-face-up end dies at the endpoint triage, its draw-cycle
  arms through the never-gain union (`conf_orphan_union`).  The
  corollary ladder: `forkState_one_founding` (THE UPWARD
  CONFINEMENT), `forkState_sameFamily_rankCeiling` (a same-family
  witness at a class member pins rank at most the fork's rank — the
  forkConsumer read) and `forkState_sameFamily_samePair` (with the
  rank pinned, the same-family witness IS the pair member, up to
  the twin flip).

House compliance: additive leaf; zero fresh `Classical.choice`; the
card is fully proved — zero named residues; the audit battery reads
[propext] or [propext, Quot.sound] on every row.
-/

/-! ## §0. The private kit (per-file copies, the house dedup discipline) -/

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
    SeedKit.runOK_adjacent_fit x.twin d bs rest (by rw [← hshape]; exact hwf.runOK_of a)
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
      SeedKit.color_pair (a := d.suit.color) hcol hcolt
    have hzc : z.suit.color = x.suit.color := by
      rw [hu, Card.twin_suit, Suit.color_twin]
    exact SeedKit.rankColor_pair hzr hzc
  · -- the empty-seat lattice: the king branch is arithmetically dead
    intro k hcp
    obtain ⟨-, hking⟩ := canPlace_inl hcp
    obtain ⟨hridxt, -⟩ := (canSitOn_eq d x.twin).mp hfit
    rw [hking, Card.twin_rank] at hridxt
    have hk12 : Rank.king.toIdx = 12 := rfl
    have hlt := Rank.toIdx_lt x.rank
    omega

/-! ## §2. The saturation pins -/

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

/-- **THE PILED-RUNG ROW** — a face-up card's suit rung sits weakly
below its rank index: a taller rung would have founded it (the
founded bridge) against conservation. -/
private theorem conf_piled_rung {st : State} (hwf : st.WF) {z : Card} {a : Anchor}
    (hmem : z ∈ (st.piles a).faceUp) : rungAt st z.suit ≤ z.rank.toIdx := by
  have hnot : z ∉ st.found z.suit := (mem_faceUp_only hwf hmem).2.2.2.2 z.suit
  rcases Nat.lt_trichotomy (rungAt st z.suit) (z.rank.toIdx) with h | h | h
  · exact Nat.le_of_lt h
  · exact Nat.le_of_eq h
  · exact absurd (FoundKit.mem_found_of_rung hwf h) hnot

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
    rcases SeedKit.suit_family hcol with hs | hs
    · rw [hs]
      exact canRaiseS_rung ((hx.1 x).mp (Or.inl rfl))
    · rw [hs]
      have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
      rwa [Card.twin_rank] at h2
  exact FoundKit.mem_found_of_rung hwf (by
    have hrw : st.foundHeight c.suit = rungAt st c.suit := rfl
    omega)

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
          SeedKit.runOK_adjacent_fit d w (bs ++ [x.twin]) rest' hok
        obtain ⟨hridx2, hcol2⟩ := (canSitOn_eq w d).mp hfit2
        have hwcol0 : w.suit.color = x.twin.suit.color :=
          SeedKit.color_pair (a := d.suit.color) hcol2.symm hcol
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

/-- **THE CROSSING LETTER** — the elevated member's OWN founding leg
literally rides the play (the proved waypoint row of the door bar's
route items 1 and 5): if a member suit's rung rises strictly past its
at-fork value somewhere along a witness journey, the play splits at a
`Move.tabToFound m` leg.  The per-leg rung ledger prices it (draws and
cargo legs write nothing, `journey_never_wasteToFound` and
`journey_never_wasteToTab` bar the waste letters, a pull only lowers
its own suit, a foreign raise only lifts its own), so the first leg
whose end crosses the index is a same-suit raise from exactly the
member's index (the firstness read), and suit-and-index name the card
(`conf_card_of_suit_toIdx`). -/
private theorem conf_founding_crosses {st : State} {m : Card} :
    ∀ {u : State} {play : List Move},
    ShufflePlayW st play u →
    ¬ (rungAt st m.suit > m.rank.toIdx) →
    rungAt u m.suit > m.rank.toIdx →
    ∃ (ρ : List Move) (v s₂ : State) (rest : List Move),
      play = ρ ++ (Move.tabToFound m :: rest) ∧
      ShufflePlayW st ρ v ∧
      State.step v (Move.tabToFound m) = some s₂ := by
  intro play u h
  induction h with
  | nil u =>
      intro hle hgt
      exact absurd hgt hle
  | @cons s₀ mv s₁ rest w₀ hrev hstep hrest ih =>
      intro hle hgt
      rcases Decidable.em (rungAt s₁ m.suit > m.rank.toIdx) with hQ₁ | hNQ₁
      · -- the crossing happens at this very leg: only a same-suit
        -- raise can write it (the ledger)
        cases mv with
        | draw =>
            have hA : rungAt s₁ m.suit = rungAt s₀ m.suit :=
              conf_rung_draw hstep m.suit
            exact absurd (show rungAt s₀ m.suit > m.rank.toIdx by
                rw [← hA]; exact hQ₁) hle
        | wasteToFound c =>
            exact absurd hrev (journey_never_wasteToFound hstep)
        | wasteToTab c b =>
            exact absurd hrev (journey_never_wasteToTab hstep)
        | tabToTab c b =>
            have hA : rungAt s₁ m.suit = rungAt s₀ m.suit :=
              conf_rung_cargo hstep m.suit
            exact absurd (show rungAt s₀ m.suit > m.rank.toIdx by
                rw [← hA]; exact hQ₁) hle
        | tabToFound c =>
            obtain ⟨hn, -, -, -⟩ := step_tabToFound_inv hstep
            obtain ⟨hrise, hothers⟩ := conf_rung_raise hstep
            have hcnext : c.rank.toIdx = rungAt s₀ c.suit :=
              of_decide_eq_true hn
            rcases Decidable.em (c.suit = m.suit) with hcs | hcs
            · -- THE founding raise: the pre-rung pins the member's
              -- index, so the raised card IS the member
              rw [hcs] at hrise hcnext
              have hpreQ : m.rank.toIdx < rungAt s₀ m.suit + 1 := by
                rw [← hrise]; exact hQ₁
              have hpre : rungAt s₀ m.suit = m.rank.toIdx :=
                Nat.le_antisymm (Nat.not_lt.mp hle) (Nat.lt_succ_iff.mp hpreQ)
              have hcm : c = m :=
                conf_card_of_suit_toIdx hcs (hcnext.trans hpre)
              rw [hcm] at hstep
              exact ⟨[], s₀, s₁, rest, by rw [hcm]; rfl, .nil s₀, hstep⟩
            · -- a foreign raise moves neither pair rung
              have hA : rungAt s₁ m.suit = rungAt s₀ m.suit :=
                hothers m.suit (fun hcon => hcs hcon.symm)
              exact absurd (show rungAt s₀ m.suit > m.rank.toIdx by
                  rw [← hA]; exact hQ₁) hle
        | foundToTab c b =>
            obtain ⟨hdrop, hothers⟩ := conf_rung_pull hstep
            rcases Decidable.em (c.suit = m.suit) with hcs | hcs
            · -- a pull only lowers its own suit: the crossing cannot
              -- have crossed through a pull
              rw [hcs] at hdrop
              have hgt0 : m.rank.toIdx < rungAt s₀ m.suit := by
                rw [hdrop]
                exact Nat.lt_trans hQ₁ (Nat.lt_succ_self _)
              exact absurd (show rungAt s₀ m.suit > m.rank.toIdx from hgt0)
                hle
            · have hA : rungAt s₁ m.suit = rungAt s₀ m.suit :=
                hothers m.suit (fun hcon => hcs hcon.symm)
              exact absurd (show rungAt s₀ m.suit > m.rank.toIdx by
                  rw [← hA]; exact hQ₁) hle
      · -- recurse into the tail with the interior start
        obtain ⟨ρ, v, s₂, rest', hsplit, hsh, hfstep⟩ := ih hNQ₁ hgt
        exact ⟨mv :: ρ, v, s₂, rest', by rw [hsplit]; rfl,
          .cons hrev hstep hsh, hfstep⟩

/-- The top search respects pile equality (the copy of the
`pileHolding_congr` idiom, at the pile-of-top search). -/
private theorem conf_pileOfTop_congr {s s' : State}
    (h : s'.piles = s.piles) (z : Card) :
    s'.pileOfTop z = s.pileOfTop z := by
  unfold State.pileOfTop State.topOf
  rw [h]

/-- The last of an append with a nonempty tail is the tail's last. -/
private theorem conf_lastOf_append (l₁ : List Card) :
    ∀ (l₂ : List Card), l₂ ≠ [] → lastOf (l₁ ++ l₂) = lastOf l₂ := by
  induction l₁ with
  | nil => intro l₂ _; rfl
  | cons x xs ih =>
      intro l₂ hne
      cases l₂ with
      | nil => exact absurd rfl hne
      | cons y l' =>
          cases xs with
          | nil => exact rfl
          | cons v vs =>
              exact ih (y :: l') hne

/-- The face-up run splits at the from-card: the below-prefix and the
moving run (the copy of the in-tree private row). -/
private theorem conf_below_fromCard (t : Card) : ∀ (l : List Card),
    l = below t l ++ fromCard t l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases hxt : x = t
      · rw [hxt, below_cons_self, fromCard_cons_self, List.nil_append]
      · rw [below_cons_ne xs hxt, fromCard_cons_ne xs hxt, List.cons_append]
        exact congrArg (x :: ·) ih

/-- The emptied-pile reads, one per hidden shape: with an empty
below-prefix the run removal leaves no face-up card over an empty
hidden deck, or the single revealed hidden head. -/
private theorem conf_arr_nil_top_none {p : Pile} (h : p.hidden = []) :
    (Pile.afterRunRemoved p []).top = none := by
  rcases p with ⟨hs, fs⟩
  rw [show (⟨hs, fs⟩ : Pile).hidden = hs from rfl] at h
  subst h
  rfl

private theorem conf_arr_nil_top_some {p : Pile} {g : Card} {gs : List Card}
    (h : p.hidden = g :: gs) :
    (Pile.afterRunRemoved p []).top = some g := by
  rcases p with ⟨hs, fs⟩
  rw [show (⟨hs, fs⟩ : Pile).hidden = hs from rfl] at h
  subst h
  rfl

/-- A pile-of-top that reads `none` admits no `some` reading (the
negation bridge for the flip's contrapositions). -/
private theorem conf_pileOfTop_none_ne {s : State} {t : Card} {A : Anchor}
    (hNT : s.pileOfTop t = none) :
    ¬ (s.pileOfTop t = some A) := by
  rw [hNT]
  simp

/-- **THE SLIDE-PROFILE WORKBENCH** — a firing run move at a WF state
has the two-pile write profile: the departure pile keeps (or reveals
over) its below-prefix, the landing pile (never the departure pile,
by the self-safety census) takes the run appended above its own
face-up run, and every other pile is untouched. -/
private theorem conf_slide_shape {s s' : State} {c : Card} {b : Base}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToTab c b) = some s') :
    ∃ (a k : Anchor) (run : List Card),
      s.pileHolding c = some a ∧
      run = fromCard c (s.piles a).faceUp ∧
      run ≠ [] ∧
      k ≠ a ∧
      (s'.piles a = Pile.afterRunRemoved (s.piles a)
          (below c (s.piles a).faceUp)) ∧
      (∀ y, y ≠ a → y ≠ k → s'.piles y = s.piles y) ∧
      ((s'.piles k).hidden = (s.piles k).hidden ∧
          (s'.piles k).faceUp = (s.piles k).faceUp ++ run) := by
  obtain ⟨a₀, hh, hcp, hrne, hs⟩ := step_tabToTab_inv hstep
  have hcmem : c ∈ (s.piles a₀).faceUp := pileHolding_mem hh
  cases b with
  | inl e =>
      obtain ⟨hemp, -⟩ := canPlace_inl hcp
      obtain ⟨hhde, hhfe⟩ := (Pile.isEmpty_eq _).mp hemp
      have hne : e ≠ a₀ := canPlace_inl_target_pile_ne hcp hcmem
      rw [hs, putRun_eq_inl]
      refine ⟨a₀, e, fromCard c (s.piles a₀).faceUp, hh, rfl, hrne, hne,
        ?_, ?_, ?_⟩
      · rw [setPile_piles_ne (Ne.symm hne), setPile_piles_self]
      · intro y hy hye
        rw [setPile_piles_ne hye, setPile_piles_ne hy]
      · rw [setPile_piles_self, hhde, hhfe]
        exact ⟨rfl, rfl⟩
  | inr z =>
      obtain ⟨k₀, hk₀, -⟩ := canPlace_inr hcp
      have hne : k₀ ≠ a₀ := fun hcon =>
        canPlace_inr_target_pile_ne hwf hcp hcmem (hcon ▸ hk₀)
      have hzmem : z ∈ (s.piles k₀).faceUp :=
        Pile.mem_of_top (pileOfTop_top hk₀).2
      have hzNotA : z ∉ (s.piles a₀).faceUp :=
        (mem_faceUp_unique hwf hzmem a₀ (Ne.symm hne)).1
      have hzNotH : z ∉ (s.piles a₀).hidden :=
        (mem_faceUp_unique hwf hzmem a₀ (Ne.symm hne)).2.1
      -- the mid state rewrites only the departure pile
      have hmidk : (s.setPile a₀ (Pile.afterRunRemoved (s.piles a₀)
          (below c (s.piles a₀).faceUp))).piles k₀
          = s.piles k₀ := setPile_piles_ne hne
      -- the base-card search answers as before: its own pile is untouched
      have hmidx : (s.setPile a₀ (Pile.afterRunRemoved (s.piles a₀)
          (below c (s.piles a₀).faceUp))).pileOfTop z = some k₀ := by
        unfold State.pileOfTop
        refine firstWhere_find (Anchor.mem_all k₀) ?_ ?_
        · show decide ((s.setPile a₀ (Pile.afterRunRemoved (s.piles a₀)
              (below c (s.piles a₀).faceUp))).topOf k₀
            = some z) = true
          rw [setPile_topOf_ne hne]
          exact decide_eq_true (pileOfTop_top hk₀).2
        · intro y _hy hyne'
          show decide ((s.setPile a₀ (Pile.afterRunRemoved (s.piles a₀)
              (below c (s.piles a₀).faceUp))).topOf y
            = some z) = false
          by_cases hya : y = a₀
          · have hXz : (Pile.afterRunRemoved (s.piles a₀)
                (below c (s.piles a₀).faceUp)).top ≠ some z := by
              intro hcon
              by_cases hpre : (below c (s.piles a₀).faceUp) = []
              · rw [hpre] at hcon
                cases hhid : (s.piles a₀).hidden with
                | nil =>
                    rw [conf_arr_nil_top_none hhid] at hcon
                    exact absurd hcon (by simp)
                | cons g gs =>
                    rw [conf_arr_nil_top_some hhid] at hcon
                    have hgt : g = z := Option.some.inj hcon
                    exact hzNotH
                      (by rw [← hgt, hhid]; exact List.mem_cons_self ..)
              · rw [afterRunRemoved_ne hpre] at hcon
                have hL : lastOf (below c (s.piles a₀).faceUp) = some z :=
                  hcon
                exact hzNotA
                  (mem_below ((s.piles a₀).faceUp) (lastOf_mem hL))
            rw [hya]
            unfold State.topOf
            rw [setPile_piles_self]
            exact decide_false_of_not hXz
          · rw [setPile_topOf_ne hya]
            exact decide_false_of_not (fun hcon =>
              (mem_faceUp_unique hwf hzmem y hyne').1 (Pile.mem_of_top hcon))
      rw [hs, putRun_inr_eq hmidx]
      refine ⟨a₀, k₀, fromCard c (s.piles a₀).faceUp, hh, rfl, hrne, hne,
        ?_, ?_, ?_⟩
      · rw [setPile_piles_ne (Ne.symm hne), setPile_piles_self]
      · intro y hy hyk
        rw [setPile_piles_ne hyk, setPile_piles_ne hy]
      · rw [setPile_piles_self, hmidk]
        exact ⟨rfl, rfl⟩

/-- **THE FACE-UP-INVARIANT CARRY** — at a witness leg whose start
holds the target `t` face-up on a pile and does not top it, the
successor still holds it face-up on some pile; founding `t` would
require it to top first, and every other leg preserves face-up
membership pile-wise. -/
private theorem conf_hop_Fkeep {s s' : State} {m : Move} {t : Card}
    (hwf : s.WF) (hstep : State.step s m = some s')
    (hrev : reversibleAtW s m)
    (hNT : s.pileOfTop t = none)
    (hF : ∃ a, t ∈ (s.piles a).faceUp) :
    ∃ a, t ∈ (s'.piles a).faceUp := by
  obtain ⟨W, hW⟩ := hF
  cases m with
  | draw =>
      have hp : s'.piles = s.piles := stepDraw_piles hstep
      exact ⟨W, by rw [hp]; exact hW⟩
  | wasteToFound c => exact absurd hrev (journey_never_wasteToFound hstep)
  | wasteToTab c b => exact absurd hrev (journey_never_wasteToTab hstep)
  | tabToFound c =>
      obtain ⟨hn, a₀, hpo, hs⟩ := step_tabToFound_inv hstep
      have hsnoc : (s.piles a₀).faceUp =
          chop (s.piles a₀).faceUp ++ [c] :=
        lastOf_chop (pileOfTop_top hpo).2
      have hct : c ≠ t := by
        intro hcon
        rw [hcon] at hpo
        rw [hNT] at hpo
        exact absurd hpo (by simp)
      have hpy : ∀ y, s'.piles y = if y = a₀ then
          Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp)
          else s.piles y := fun y => by rw [hs]
      by_cases hWa : W = a₀
      · have htchop : t ∈ chop (s.piles a₀).faceUp := by
          rw [hWa, hsnoc] at hW
          rcases List.mem_append.mp hW with hchop | hlast
          · exact hchop
          · rw [List.mem_singleton] at hlast
            exact absurd hlast.symm hct
        have hchopne : chop (s.piles a₀).faceUp ≠ [] :=
          fun hcon => by rw [hcon] at htchop; exact absurd htchop (by simp)
        refine ⟨a₀, ?_⟩
        rw [hpy a₀, if_pos rfl, afterRunRemoved_ne hchopne]
        exact htchop
      · refine ⟨W, ?_⟩
        rw [hpy W, ite_eq_right hWa]
        exact hW
  | foundToTab c b =>
      obtain ⟨c₀, htop, hc₀c, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hc₀c] at htop
      have hcne : c ≠ t := by
        intro hcon
        have hmemF : t ∈ s.found t.suit := by
          rw [← hcon]; exact lastOf_mem htop
        exact (mem_faceUp_only hwf hW).2.2.2.2 t.suit hmemF
      cases b with
      | inl e =>
          obtain ⟨hemp, -⟩ := canPlace_inl hcp
          obtain ⟨-, hhfe⟩ := (Pile.isEmpty_eq _).mp hemp
          have hpy : ∀ y, s'.piles y =
              if y = e then ⟨[], [c]⟩ else s.piles y := by
            intro y
            rw [hs, putCard_piles_inl, setFound_piles]
          by_cases hWe : W = e
          · exfalso
            rw [hWe, hhfe] at hW
            exact absurd hW (by simp)
          · refine ⟨W, ?_⟩
            rw [hpy W, ite_eq_right hWe]
            exact hW
      | inr z =>
          obtain ⟨k₀, hk₀, -⟩ := canPlace_inr hcp
          have hk₀' : (s.setFound c.suit (chop (s.found c.suit))).pileOfTop z
              = some k₀ :=
            (conf_pileOfTop_congr (setFound_piles s c.suit
              (chop (s.found c.suit))) z).trans hk₀
          have hpy : ∀ y, s'.piles y = if y = k₀ then
              { s.piles k₀ with faceUp := (s.piles k₀).faceUp ++ [c] }
              else s.piles y := by
            intro y
            rw [hs, putCard_piles_inr _ _ _ _ hk₀', setFound_piles]
          by_cases hWk : W = k₀
          · rw [hWk] at hW
            refine ⟨W, ?_⟩
            rw [hWk, hpy k₀, ite_eq_left rfl]
            exact List.mem_append.mpr (Or.inl hW)
          · refine ⟨W, ?_⟩
            rw [hpy W, ite_eq_right hWk]
            exact hW
  | tabToTab c b =>
      obtain ⟨a₀, k, run, hh, hrun, hrne, hne, hpa, hothers, hpair⟩ :=
        conf_slide_shape hwf hstep
      have hsplit : (s.piles a₀).faceUp =
          below c (s.piles a₀).faceUp ++ run := by
        have h := conf_below_fromCard c (s.piles a₀).faceUp
        rw [hrun]
        exact h
      by_cases hWa : W = a₀
      · rw [hWa] at hW
        rw [hsplit] at hW
        rcases List.mem_append.mp hW with hmem | hmem
        · have hprene : below c (s.piles a₀).faceUp ≠ [] :=
            fun hcon => by rw [hcon] at hmem; exact absurd hmem (by simp)
          refine ⟨a₀, ?_⟩
          rw [hpa, afterRunRemoved_ne hprene]
          exact hmem
        · have hfeq : (s'.piles k).faceUp = (s.piles k).faceUp ++ run :=
            hpair.2
          refine ⟨k, ?_⟩
          rw [hfeq]
          exact List.mem_append.mpr (Or.inr hmem)
      · by_cases hWk : W = k
        · rw [hWk] at hW
          refine ⟨W, ?_⟩
          rw [hWk, hpair.2]
          exact List.mem_append.mpr (Or.inl hW)
        · refine ⟨W, ?_⟩
          rw [hothers W hWa hWk]
          exact hW

/-- **THE FIRST-TOPPING FLIP** — the leg whose post-state first tops
the target names its move: a `tabToTab` whose head sits directly on
the target at the departure seat, or a `tabToFound` of the card
directly covering it — in both cases the run-discipline fit
`canSitOn c t` holds.  Every other leg either writes no pile (draw),
never rides (waste letters), or cannot produce a first top (pulls
place cards on top, relocations keep within-run positions, and the
target cannot be the pulled/founded card while it is face-up and not
topping). -/
private theorem conf_hop_flip {s s' : State} (hwf : s.WF) {m : Move}
    (hstep : State.step s m = some s') (hrev : reversibleAtW s m)
    {t : Card}
    (hF : ∃ a, t ∈ (s.piles a).faceUp)
    (hNT : s.pileOfTop t = none)
    (hT' : s'.pileOfTop t ≠ none) :
    (∃ c b, m = Move.tabToTab c b ∧ canSitOn c t = true) ∨
      (∃ c, m = Move.tabToFound c ∧ canSitOn c t = true) := by
  obtain ⟨W, hW⟩ := hF
  have htnoH : ∀ a', t ∉ (s.piles a').hidden := by
    intro a'
    by_cases hWa : a' = W
    · rw [hWa]; exact (mem_faceUp_only hwf hW).2.1
    · exact (mem_faceUp_unique hwf hW a' hWa).2.1
  cases m with
  | draw =>
      exact absurd ((conf_pileOfTop_congr (stepDraw_piles hstep) t).trans hNT)
        hT'
  | wasteToFound c => exact absurd hrev (journey_never_wasteToFound hstep)
  | wasteToTab c b => exact absurd hrev (journey_never_wasteToTab hstep)
  | tabToFound c =>
      obtain ⟨hn, a₀, hpo, hs⟩ := step_tabToFound_inv hstep
      have hcTop : lastOf (s.piles a₀).faceUp = some c := (pileOfTop_top hpo).2
      have hsnoc : (s.piles a₀).faceUp =
          chop (s.piles a₀).faceUp ++ [c] := lastOf_chop hcTop
      have hpy : ∀ y, s'.piles y = if y = a₀ then
          Pile.afterRunRemoved (s.piles a₀) (chop (s.piles a₀).faceUp)
          else s.piles y := fun y => by rw [hs]
      obtain ⟨A, hA⟩ := option_some_of_ne_none hT'
      obtain ⟨-, hlastA⟩ := pileOfTop_top hA
      by_cases hAa : A = a₀
      · have hTop' : (Pile.afterRunRemoved (s.piles a₀)
            (chop (s.piles a₀).faceUp)).top = some t := by
          rw [hpy A, ite_eq_left hAa] at hlastA
          exact hlastA
        by_cases hchop : chop (s.piles a₀).faceUp = []
        · exfalso
          rw [hchop] at hTop'
          cases hhid : (s.piles a₀).hidden with
          | nil =>
              rw [conf_arr_nil_top_none hhid] at hTop'
              exact absurd hTop' (by simp)
          | cons g gs =>
              rw [conf_arr_nil_top_some hhid] at hTop'
              have hgt : g = t := Option.some.inj hTop'
              exact htnoH a₀
                (by rw [← hgt, hhid]; exact List.mem_cons_self ..)
        · rw [afterRunRemoved_ne hchop] at hTop'
          obtain ⟨front, hfront⟩ := lastOf_eq_snoc
            (show lastOf (chop (s.piles a₀).faceUp) = some t from hTop')
          have hshape : (s.piles a₀).faceUp = front ++ [t, c] := by
            rw [hsnoc, hfront, List.append_assoc]; rfl
          exact Or.inr ⟨c, rfl, SeedKit.runOK_adjacent_fit t c front [] (by
              rw [← hshape]; exact hwf.2.1 a₀)⟩
      · exfalso
        rw [hpy A, ite_eq_right hAa] at hlastA
        exact absurd ((pileOfTop_eq_some_iff hwf).2
          (show (s.piles A).top = some t from hlastA))
          (conf_pileOfTop_none_ne hNT)
  | foundToTab c b =>
      obtain ⟨c₀, htop, hc₀c, hcp, hs⟩ := step_foundToTab_inv hstep
      rw [hc₀c] at htop
      have hcne : c ≠ t := by
        intro hcon
        have hmemF : t ∈ s.found t.suit := by
          rw [← hcon]; exact lastOf_mem htop
        exact (mem_faceUp_only hwf hW).2.2.2.2 t.suit hmemF
      cases b with
      | inl e =>
          have hpy : ∀ y, s'.piles y =
              if y = e then ⟨[], [c]⟩ else s.piles y := by
            intro y
            rw [hs, putCard_piles_inl, setFound_piles]
          obtain ⟨A, hA⟩ := option_some_of_ne_none hT'
          obtain ⟨-, hlastA⟩ := pileOfTop_top hA
          by_cases hAe : A = e
          · rw [hpy A, ite_eq_left hAe] at hlastA
            exact absurd (Option.some.inj hlastA) hcne
          · exfalso
            rw [hpy A, ite_eq_right hAe] at hlastA
            exact absurd ((pileOfTop_eq_some_iff hwf).2
              (show (s.piles A).top = some t from hlastA))
              (conf_pileOfTop_none_ne hNT)
      | inr z =>
          obtain ⟨k₀, hk₀, -⟩ := canPlace_inr hcp
          have hk₀' : (s.setFound c.suit (chop (s.found c.suit))).pileOfTop z
              = some k₀ :=
            (conf_pileOfTop_congr (setFound_piles s c.suit
              (chop (s.found c.suit))) z).trans hk₀
          have hpy : ∀ y, s'.piles y = if y = k₀ then
              { s.piles k₀ with faceUp := (s.piles k₀).faceUp ++ [c] }
              else s.piles y := by
            intro y
            rw [hs, putCard_piles_inr _ _ _ _ hk₀', setFound_piles]
          obtain ⟨A, hA⟩ := option_some_of_ne_none hT'
          obtain ⟨-, hlastA⟩ := pileOfTop_top hA
          by_cases hAk : A = k₀
          · exfalso
            rw [hpy A, ite_eq_left hAk] at hlastA
            have hTop' : lastOf ((s.piles k₀).faceUp ++ [c]) = some t :=
              hlastA
            exact absurd
              (Option.some.inj (lastOf_snoc.symm.trans hTop')) hcne
          · exfalso
            rw [hpy A, ite_eq_right hAk] at hlastA
            exact absurd ((pileOfTop_eq_some_iff hwf).2
              (show (s.piles A).top = some t from hlastA))
              (conf_pileOfTop_none_ne hNT)
  | tabToTab c b =>
      obtain ⟨a₀, k, run, hh, hrun, hrne, hne, hpa, hothers, hpair⟩ :=
        conf_slide_shape hwf hstep
      have hsplit : (s.piles a₀).faceUp =
          below c (s.piles a₀).faceUp ++ run := by
        have h := conf_below_fromCard c (s.piles a₀).faceUp
        rw [hrun]
        exact h
      obtain ⟨A, hA⟩ := option_some_of_ne_none hT'
      obtain ⟨-, hlastA⟩ := pileOfTop_top hA
      by_cases hAa : A = a₀
      · have hTop' : (Pile.afterRunRemoved (s.piles a₀)
            (below c (s.piles a₀).faceUp)).top = some t := by
          rw [hAa, hpa] at hlastA
          exact hlastA
        by_cases hprene : below c (s.piles a₀).faceUp = []
        · exfalso
          rw [hprene] at hTop'
          cases hhid : (s.piles a₀).hidden with
          | nil =>
              rw [conf_arr_nil_top_none hhid] at hTop'
              exact absurd hTop' (by simp)
          | cons g gs =>
              rw [conf_arr_nil_top_some hhid] at hTop'
              have hgt : g = t := Option.some.inj hTop'
              exact htnoH a₀
                (by rw [← hgt, hhid]; exact List.mem_cons_self ..)
        · rw [afterRunRemoved_ne hprene] at hTop'
          have hL : lastOf (below c (s.piles a₀).faceUp) = some t :=
            hTop'
          obtain ⟨front, hfront⟩ := lastOf_eq_snoc hL
          have hruncons : ∃ tail, run = c :: tail := by
            rw [hrun, fromCard_eq_of_mem (pileHolding_mem hh)]
            exact ⟨_, rfl⟩
          obtain ⟨tail, hrunT⟩ := hruncons
          have hshape : (s.piles a₀).faceUp = front ++ t :: c :: tail := by
            rw [hsplit, hfront, hrunT, List.append_assoc, List.cons_append]
            rfl
          refine Or.inl ⟨c, b, rfl, SeedKit.runOK_adjacent_fit t c front tail ?_⟩
          rw [← hshape]
          exact hwf.2.1 a₀
      · by_cases hAk : A = k
        · exfalso
          rw [hAk] at hlastA
          rw [hpair.2, conf_lastOf_append _ run hrne] at hlastA
          have hLU : lastOf (s.piles a₀).faceUp = some t := by
            rw [hsplit, conf_lastOf_append _ run hrne]
            exact hlastA
          exact absurd ((pileOfTop_eq_some_iff hwf).2
            (show (s.piles a₀).top = some t from hLU))
            (conf_pileOfTop_none_ne hNT)
        · exfalso
          rw [hothers A hAa hAk] at hlastA
          exact absurd ((pileOfTop_eq_some_iff hwf).2
            (show (s.piles A).top = some t from hlastA))
            (conf_pileOfTop_none_ne hNT)

/-- **THE FIRSTNESS CLIMB** — if the target is face-up and not
topping at a journey start, and tops at the journey end, then some
interior leg of the play is literally a `tabToTab c b` or a
`tabToFound c` leg with `canSitOn c t = true`.  Until the first
topping leg the face-up carry holds, so the flip lemma names the
first leg that changes the top status. -/
private theorem conf_hop_aux {t : Card} {s : State} :
    ∀ {w : State} {π : List Move},
    ShufflePlayW s π w → s.WF →
    (∃ a, t ∈ (s.piles a).faceUp) → s.pileOfTop t = none →
    (∃ a, w.pileOfTop t = some a) →
    (∃ (ρ₁ ρ₂ : List Move) (c : Card) (b : Base) (s₃ s₄ : State),
        π = ρ₁ ++ Move.tabToTab c b :: ρ₂ ∧
        ShufflePlayW s ρ₁ s₃ ∧
        State.step s₃ (Move.tabToTab c b) = some s₄ ∧
        canSitOn c t = true) ∨
    (∃ (ρ₁ ρ₂ : List Move) (c : Card) (s₃ s₄ : State),
        π = ρ₁ ++ Move.tabToFound c :: ρ₂ ∧
        ShufflePlayW s ρ₁ s₃ ∧
        State.step s₃ (Move.tabToFound c) = some s₄ ∧
        canSitOn c t = true) := by
  intro w π h
  induction h with
  | nil u =>
      intro hwf hF hNT hT
      obtain ⟨A, hA⟩ := hT
      rw [hNT] at hA
      exact absurd hA (by simp)
  | @cons s₀ mv s₁ rest w₀ hrev hstep hrest ih =>
      intro hwf hF hNT hT
      cases hpt : s₁.pileOfTop t with
      | none =>
          rcases ih (step_wf hwf hstep)
            (conf_hop_Fkeep hwf hstep hrev hNT hF) hpt hT with
            hcargo | hfounded
          · obtain ⟨ρ₁, ρ₂, c, b, s₃, s₄, hsplit, hsh₁, hstep₁, hfit⟩ :=
              hcargo
            exact Or.inl ⟨mv :: ρ₁, ρ₂, c, b, s₃, s₄,
              by rw [List.cons_append, hsplit],
              .cons hrev hstep hsh₁, hstep₁, hfit⟩
          · obtain ⟨ρ₁, ρ₂, c, s₃, s₄, hsplit, hsh₁, hstep₁, hfit⟩ :=
              hfounded
            exact Or.inr ⟨mv :: ρ₁, ρ₂, c, s₃, s₄,
              by rw [List.cons_append, hsplit],
              .cons hrev hstep hsh₁, hstep₁, hfit⟩
      | some A₁ =>
          rcases conf_hop_flip hwf hstep hrev hF hNT
            (by rw [hpt]; exact Option.some_ne_none A₁) with
            hcargo | hfounded
          · obtain ⟨c, b, hm, hfit⟩ := hcargo
            have hπ : mv :: rest = [] ++ Move.tabToTab c b :: rest := by
              rw [hm]; rfl
            rw [hm] at hstep
            exact Or.inl ⟨[], rest, c, b, s₀, s₁, hπ, .nil s₀, hstep,
              hfit⟩
          · obtain ⟨c, hm, hfit⟩ := hfounded
            have hπ : mv :: rest = [] ++ Move.tabToFound c :: rest := by
              rw [hm]; rfl
            rw [hm] at hstep
            exact Or.inr ⟨[], rest, c, s₀, s₁, hπ, .nil s₀, hstep, hfit⟩

/-- **THE COVER-HOP TRANSPORT CHAIN** — route step 3, the first of the
three named sub-residues of the door bar.  Premise grade: the twin was
covered DIRECTLY at the fork (`pair_cover_pins`, applied from `hx`:
the cover one rank below, opposite family, topping the twin's pile
with the tower above it empty); at the reachable state `w` the twin
now TOPS a pile.  Conclusion: some interior leg of the prefix moved
the twin's direct cover by hand — either a cargo leg whose head is a
cover-family card (rank index `r − 1`, opposite color family — the
run-discipline fit at the departure), or the founding of such a card
(the freeze's target below).  Route to close: the per-leg
direct-cover position language (`below`/`aboveIn` over the pile
lists), the lastness identification of the uncovering leg (the last
change to the twin's above-run), the `SeedKit.runOK_adjacent_fit` fit at the
departure seat. -/
private theorem crossing_door_hop {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) {w : State} {π : List Move}
    (hpre : ShufflePlayW st π w)
    (htop : ∃ a, w.pileOfTop x.twin = some a) :
    (∃ (ρ₁ ρ₂ : List Move) (c : Card) (b : Base) (s₃ s₄ : State),
       π = ρ₁ ++ Move.tabToTab c b :: ρ₂ ∧
       ShufflePlayW st ρ₁ s₃ ∧
       State.step s₃ (Move.tabToTab c b) = some s₄ ∧
       c.rank.toIdx + 1 = x.rank.toIdx ∧
       c.suit.color ≠ x.suit.color) ∨
    (∃ (ρ₁ ρ₂ : List Move) (c : Card) (s₃ s₄ : State),
       π = ρ₁ ++ Move.tabToFound c :: ρ₂ ∧
       ShufflePlayW st ρ₁ s₃ ∧
       State.step s₃ (Move.tabToFound c) = some s₄ ∧
       c.rank.toIdx + 1 = x.rank.toIdx ∧
        c.suit.color ≠ x.suit.color) := by
  -- the fork's twin-cover package: the twin sits face-up under d
  obtain ⟨a, bs, d, hshape, -, hfit, -, -, -⟩ := pair_cover_pins hwf hx
  have hFmem : x.twin ∈ (st.piles a).faceUp := by
    rw [hshape]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  -- and cannot top anywhere: d tops its own pile, the twin is
  -- nowhere else face-up
  have hNT : st.pileOfTop x.twin = none := by
    cases hPot : st.pileOfTop x.twin with
    | none => rfl
    | some A =>
        exfalso
        obtain ⟨-, hlast⟩ := pileOfTop_top hPot
        by_cases hA : A = a
        · rw [hA, hshape, conf_snoc2_last] at hlast
          exact ne_of_canSitOn hfit (Option.some.inj hlast)
        · exact (mem_faceUp_unique hwf hFmem A hA).1
            (lastOf_mem hlast)
  -- the firstness climb: within the witness prefix the twin stays
  -- face-up until the first topping leg, which the flip names
  rcases conf_hop_aux hpre hwf ⟨a, hFmem⟩ hNT htop with hcargo | hfounded
  · obtain ⟨ρ₁, ρ₂, c, b, s₃, s₄, hsplit, hsh₁, hstep₁, hfit⟩ := hcargo
    obtain ⟨hrank, hcol⟩ := (canSitOn_eq c x.twin).mp hfit
    rw [Card.twin_rank] at hrank
    have hxcol : x.suit.color = x.twin.suit.color := by
      rw [Card.twin_suit x, Suit.color_twin]
    exact Or.inl ⟨ρ₁, ρ₂, c, b, s₃, s₄, hsplit, hsh₁, hstep₁, hrank,
      by rw [hxcol]; exact hcol⟩
  · obtain ⟨ρ₁, ρ₂, c, s₃, s₄, hsplit, hsh₁, hstep₁, hfit⟩ := hfounded
    obtain ⟨hrank, hcol⟩ := (canSitOn_eq c x.twin).mp hfit
    rw [Card.twin_rank] at hrank
    have hxcol : x.suit.color = x.twin.suit.color := by
      rw [Card.twin_suit x, Suit.color_twin]
    exact Or.inr ⟨ρ₁, ρ₂, c, s₃, s₄, hsplit, hsh₁, hstep₁, hrank,
      by rw [hxcol]; exact hcol⟩

/-- **THE RUNG-CROSSING RAISE CENSUS** — if a suit's rung starts at
most `R` at a witness-journey start and ends strictly above `R`, the
play contains a literal `tabToFound e` leg whose card is exactly
`(σ, R)` — the first-exceeding raise: the per-leg rung ledger
(draw/cargo write nothing, waste letters never ride, a raise lifts
exactly its own suit, a pull only lowers its own) forces the leg that
first carries the rung past `R` to be a same-suit raise from exactly
`R`, and the `nextUp` guard plus suit-and-index name the card. -/
private theorem conf_raise_crossing {st : State} {σ : Suit} {R : Nat} :
    ∀ {w : State} {π : List Move},
    ShufflePlayW st π w →
    ¬ (rungAt st σ > R) → rungAt w σ > R →
    ∃ (ρ₁ ρ₂ : List Move) (e : Card) (t₃ t₄ : State),
      π = ρ₁ ++ Move.tabToFound e :: ρ₂ ∧
      ShufflePlayW st ρ₁ t₃ ∧
      State.step t₃ (Move.tabToFound e) = some t₄ ∧
      e.suit = σ ∧ e.rank.toIdx = R := by
  intro w π h
  induction h with
  | nil u =>
      intro hle hgt
      exact absurd hgt hle
  | @cons s₀ mv s₁ rest w₀ hrev hstep hrest ih =>
      intro hle hgt
      rcases Nat.lt_or_ge (rungAt s₁ σ) (R + 1) with hQ | hQ
      · -- still at-or-below: the crossing is later in the tail
        obtain ⟨ρ₁, ρ₂, e, t₃, t₄, hsplit, hsh₁, hstep₁, hes, her⟩ :=
          ih (by omega) hgt
        exact ⟨mv :: ρ₁, ρ₂, e, t₃, t₄, by rw [hsplit]; rfl,
          .cons hrev hstep hsh₁, hstep₁, hes, her⟩
      · -- this leg carries the crossing: the rung ledger names it
        cases mv with
        | draw =>
            have hA : rungAt s₁ σ = rungAt s₀ σ := conf_rung_draw hstep σ
            exfalso
            omega
        | wasteToFound c =>
            exact absurd hrev (journey_never_wasteToFound hstep)
        | wasteToTab c b =>
            exact absurd hrev (journey_never_wasteToTab hstep)
        | tabToTab c b =>
            have hA : rungAt s₁ σ = rungAt s₀ σ := conf_rung_cargo hstep σ
            exfalso
            omega
        | tabToFound c =>
            obtain ⟨hn, -, -, -⟩ := step_tabToFound_inv hstep
            obtain ⟨hrise, hothers⟩ := conf_rung_raise hstep
            have hcnext : c.rank.toIdx = rungAt s₀ c.suit :=
              of_decide_eq_true hn
            by_cases hcs : c.suit = σ
            · rw [hcs] at hrise hcnext
              exact ⟨[], rest, c, s₀, s₁, rfl, .nil s₀, hstep, hcs, by omega⟩
            · have hB : rungAt s₁ σ = rungAt s₀ σ :=
                hothers σ (fun hcon => hcs hcon.symm)
              exfalso
              omega
        | foundToTab c b =>
            obtain ⟨hdrop, hothers⟩ := conf_rung_pull hstep
            by_cases hcs : c.suit = σ
            · rw [hcs] at hdrop
              exfalso
              omega
            · have hB : rungAt s₁ σ = rungAt s₀ σ :=
                hothers σ (fun hcon => hcs hcon.symm)
              exfalso
              omega

/-- The WF carry along a witness shuffle (per-leg `step_wf`). -/
private theorem conf_wf_along {st : State} : ∀ {w : State} {play : List Move},
    ShufflePlayW st play w → st.WF → w.WF := by
  intro w play h
  induction h with
  | nil u => intro hwf; exact hwf
  | @cons s₀ mv s₁ rest w₀ hrev hstep hrest ih =>
      intro hwf
      exact ih (step_wf hwf hstep)

private theorem conf_dealUpTo_mem (d : Card) :
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

/-- **THE DRAW-CYCLE CLOSURE** — along a witness journey the stock and
the waste are a closed two-zone world for their residents (the copy
of the in-tree public-but-downstream row; the only stock/waste
writers are the draw's own recycle and deal; the waste letters never
ride). -/
private theorem conf_stockWaste_closed (d : Card) :
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
            · cases hss : s₀.stock with
              | nil => rw [hss] at hst; exact absurd hst (by simp)
              | cons x xs =>
                  have hrt : r = s₀ := by
                    rw [← hrEq]
                    exact recycle_keep s₀ (by rw [hss]; simp)
                  have hin : d ∈ r.stock := by rw [hrt]; exact hst
                  have hspl := conf_dealUpTo_mem d r.drawStep r.stock hin
                  rcases hspl with hD | hR
                  · exact Or.inr
                      (List.mem_append.mpr (Or.inl (List.mem_reverse.mpr hD)))
                  · exact Or.inl hR
            · cases hss : s₀.stock with
              | nil =>
                  cases hws : s₀.waste with
                  | nil => rw [hws] at hwst; exact absurd hwst (by simp)
                  | cons v vs =>
                      have hrt : r = { s₀ with
                          stock := s₀.waste.reverse,
                          waste := ([] : List Card) } := by
                        rw [← hrEq]
                        exact recycle_nil s₀ hss (by rw [hws]; simp)
                      have hin : d ∈ r.stock := by
                        rw [hrt]
                        exact List.mem_reverse.mpr hwst
                      have hspl := conf_dealUpTo_mem d r.drawStep r.stock hin
                      rcases hspl with hD | hR
                      · exact Or.inr
                          (List.mem_append.mpr
                            (Or.inl (List.mem_reverse.mpr hD)))
                      · exact Or.inl hR
              | cons x xs =>
                  have hrt : r = s₀ := by
                    rw [← hrEq]
                    exact recycle_keep s₀ (by rw [hss]; simp)
                  exact Or.inr
                    (List.mem_append.mpr (Or.inr (by rw [hrt]; exact hwst)))
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
              putCard_keep (st := s₀.setFound walt.suit
                (chop (s₀.found walt.suit))) (c := walt) (b := balt)
            rw [hP1, hP2]
            exact hcyc
        | tabToTab walt balt =>
            obtain ⟨Asrc, -, -, -, hs⟩ := step_tabToTab_inv hstep
            rw [hs]
            obtain ⟨-, hP1, hP2, -⟩ :=
              putRun_keep (st := s₀.setPile Asrc
                (Pile.afterRunRemoved (s₀.piles Asrc)
                  (below walt ((s₀.piles Asrc).faceUp))))
                (run := fromCard walt ((s₀.piles Asrc).faceUp)) (b := balt)
            rw [hP1, hP2]
            exact hcyc
      exact ih hmid

/-- A zone-prefix member's suit is the zone's suit. -/
private theorem conf_mem_upCards_suit {σ : Suit} {c : Card}
    (h : c ∈ σ.upCards) : c.suit = σ := by
  rw [Suit.upCards] at h
  obtain ⟨r, -, hrc⟩ := List.mem_map.mp h
  rcases c with ⟨cs, cr⟩
  have : Card.mk σ r = Card.mk cs cr := hrc
  injection this with h1 h2
  exact h1.symm

/-- **INTERIOR-LEG REVERSIBILITY** — every leg of a witness shuffle is
reversible at its own pre-state; with the prefix-shuffle certificate
(`ShufflePlayW st ρ₁ s₃`) locating the pre-state, any certified
interior leg `(π = ρ₁ ++ m :: ρ₂)` carries `reversibleAtW s₃ m`.
This is the extractor the reveal-bar and pillar-bar consumptions in
the residues (`conf_charlie_bareCell`'s hidden ≠ [] case and the
founded-cell/pull-escape re-boarding epochs) need. -/
private theorem conf_interior_rev {st : State} :
    ∀ {w : State} {π : List Move}, ShufflePlayW st π w →
    ∀ (ρ₁ ρ₂ : List Move) (m : Move) (s₃ : State),
      π = ρ₁ ++ m :: ρ₂ →
      ShufflePlayW st ρ₁ s₃ →
      reversibleAtW s₃ m := by
  intro w π h
  induction h with
  | nil u =>
      intro ρ₁ ρ₂ m s₃ hπ hsh
      cases ρ₁ with
      | nil =>
          rw [List.nil_append] at hπ
          cases hπ
      | cons v vs =>
          rw [List.cons_append] at hπ
          cases hπ
  | @cons s₀ mvh s₁ rest w₀ hrev hstep hrest ih =>
      intro ρ₁ ρ₂ m s₃ hπ hsh
      cases ρ₁ with
      | nil =>
          rw [List.nil_append] at hπ
          have hm : mvh = m := (List.cons_eq_cons.mp hπ).1
          rw [hm] at hrev
          cases hsh
          exact hrev
      | cons v vs =>
          rw [List.cons_append] at hπ
          obtain ⟨hmv, hrestEq⟩ := List.cons_eq_cons.mp hπ
          rw [← hmv] at hsh
          cases hsh with
          | @cons s₂ mvv s₂' restv wv' hrevv hstepv hrestv =>
              have hs₂ : s₁ = s₂' := Option.some.inj (hstep.symm.trans hstepv)
              rw [← hs₂] at hrestv
              exact ih vs ρ₂ m s₃ hrestEq hrestv

/-- The bare removal: over an empty hidden deck the emptied run leaves
the fully-empty pile (the per-file private copy). -/
private theorem conf_arr_bare {p : Pile} (hh : p.hidden = []) :
    Pile.afterRunRemoved p ([] : List Card) = (⟨[], []⟩ : Pile) := by
  show Pile.revealTop { p with faceUp := [] } = _
  rcases p with ⟨hl, fl⟩
  cases hl with
  | nil => rfl
  | cons g gs => exact absurd hh (by simp)

private theorem conf_inl_king {s : State} {w : Card} {k : Anchor}
    (h : s.canPlace w (Sum.inl k) = true) : w.rank = Rank.king := by
  rw [State.canPlace, Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

private theorem conf_fromCard_run_head (e : Card) :
    ∀ (l : List Card), fromCard e l ≠ [] → ∃ tr, fromCard e l = e :: tr := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [fromCard])
  | cons z zs ih =>
      intro h
      by_cases hze : z = e
      · exact ⟨zs, by rw [hze, fromCard_cons_self]⟩
      · obtain ⟨tr, htr⟩ := ih (by
          intro hcon
          rw [fromCard_cons_ne zs hze] at h
          exact h hcon)
        exact ⟨tr, by rw [fromCard_cons_ne zs hze]; exact htr⟩

/-- The afterRunRemoved Q-read: a member card keeps the removal in the
empty-or-king-headed family (the per-file private copy). -/
private theorem conf_arr_Q {P : Pile} {e : Card}
    (hmemE : e ∈ P.faceUp)
    (hQ : (P.faceUp = [] ∧ P.hidden = []) ∨
      ∃ K t, P.faceUp = K :: t ∧ K.rank = Rank.king ∧ P.hidden = []) :
    (Pile.afterRunRemoved P (below e P.faceUp)).faceUp = [] ∧
      (Pile.afterRunRemoved P (below e P.faceUp)).hidden = [] ∨
      ∃ K t, (Pile.afterRunRemoved P (below e P.faceUp)).faceUp = K :: t ∧
        K.rank = Rank.king ∧
        (Pile.afterRunRemoved P (below e P.faceUp)).hidden = [] := by
  by_cases hpre : below e P.faceUp = []
  · have hhQ : P.hidden = [] := by
      rcases hQ with ⟨-, hh⟩ | ⟨-, -, -, -, hh⟩
      · exact hh
      · exact hh
    rw [hpre, conf_arr_bare hhQ]
    exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨w, ws, hpc⟩ := list_cons_of_ne_nil hpre
    rcases hQ with ⟨hfup, hhA⟩ | ⟨K, t, hfup, hK, hhA⟩
    · exact absurd hmemE (by rw [hfup] at hmemE; simp at hmemE)
    · -- below e (K :: t) is king-headed: the member cannot be the head
      have hKe : K ≠ e := by
        intro hcon
        rw [hfup] at hpc
        rw [hcon, below_cons_self] at hpc
        exact absurd hpc.symm (by simp)
      have hne : below e P.faceUp ≠ [] := by rw [hpc]; simp
      have hcf : (Pile.afterRunRemoved P (below e P.faceUp)).faceUp
          = below e P.faceUp := by
        rw [afterRunRemoved_ne hne]
      refine Or.inr ⟨K, below e t, ?_, hK, ?_⟩
      · rw [hcf, hfup, below_cons_ne t hKe]
      · rw [afterRunRemoved_ne hne]
        exact hhA

/-- **THE PILLAR'S ONE-STEP ENGINE** — every firing move keeps the
empty-or-king-headed family of a pile (the per-file private copy). -/
private theorem conf_eok_oneStep {A : Anchor} {s s' : State} {m : Move}
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
      have hp : (({s.setFound w.suit (s.found w.suit ++ [w]) with
          waste := xs} : State).piles A) = s.piles A := rfl
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
            · exact Or.inr ⟨w, [], rfl, conf_inl_king hg.2, rfl⟩
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
        have hself : (if A = k then
            Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
            else s.piles A)
            = Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp) :=
          ite_eq_left hAk
        rw [hself]
        rcases hQ with ⟨hfup, hhA⟩ | ⟨K, t, hfup, hK, hhA⟩
        · have hch : chop (s.piles k).faceUp = [] := by rw [hfup]; rfl
          rw [hch, conf_arr_bare hhA]
          exact Or.inl ⟨rfl, rfl⟩
        · cases t with
          | nil =>
              have hch : chop (s.piles k).faceUp = [] := by rw [hfup]; rfl
              rw [hch, conf_arr_bare hhA]
              exact Or.inl ⟨rfl, rfl⟩
          | cons u us =>
              have hch : chop (s.piles k).faceUp = K :: chop (u :: us) := by
                rw [hfup]; rfl
              rw [hch, afterRunRemoved_ne (by
                intro hcon; exact absurd hcon (by simp))]
              exact Or.inr ⟨K, chop (u :: us), rfl, hK, hhA⟩
      · have helse : (if A = k then
          Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
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
          have hp : (((s.setFound w.suit (chop (s.found w.suit))).putCard w
              (Sum.inl k)).piles A)
              = (if A = k then (⟨[], [w]⟩ : Pile) else s.piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨w, [], rfl, conf_inl_king hg, rfl⟩
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
          have hmidpin :
              (s.setFound w.suit (chop (s.found w.suit))).pileOfTop z
              = some kk := by
            rw [conf_pileOfTop_congr hmidp z]
            exact hpin
          have hp : (((s.setFound w.suit (chop (s.found w.suit))).putCard w
              (Sum.inr z)).piles A)
              = (if A = kk then
                  { s.piles kk with faceUp := (s.piles kk).faceUp ++ [w] }
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
              = (if A = k then
                  (⟨[], fromCard e ((s.piles Asrc).faceUp)⟩ : Pile)
                 else (s.setPile Asrc (Pile.afterRunRemoved (s.piles Asrc)
                   (below e ((s.piles Asrc).faceUp)))).piles A) := rfl
          rw [hp]
          by_cases hAk : A = k
          · rw [ite_eq_left hAk]
            obtain ⟨tr, hrun⟩ :=
              conf_fromCard_run_head e ((s.piles Asrc).faceUp) hfr
            rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, -, hhA⟩
            · exact Or.inr ⟨e, tr, by rw [hrun], conf_inl_king hcp, rfl⟩
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
              exact conf_arr_Q hmemE hQ
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
                exact conf_arr_Q hmemE hQ
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
                  rcases conf_arr_Q hmemE hQ with ⟨h1, h2⟩ | ⟨K, tm, h1, hK, h2⟩
                  · exact absurd h1 hneMid
                  · refine Or.inr ⟨K,
                      tm ++ fromCard e ((s.piles Asrc).faceUp), ?_, hK, h2⟩
                    rw [h1, List.cons_append]
                · have hmidA : (s.setPile Asrc (Pile.afterRunRemoved
                        (s.piles Asrc)
                        (below e ((s.piles Asrc).faceUp)))).piles kk
                      = s.piles A := by
                    rw [← hAk]
                    exact setPile_afterRunRemoved_piles_ne s Asrc e A hAs
                  rw [hmidA] at hneMid ⊢
                  rcases hQ with ⟨hfup, -⟩ | ⟨K, t, hfup, hK, hhA⟩
                  · exfalso
                    rw [hfup] at hneMid
                    exact absurd hneMid (by simp)
                  · refine Or.inr ⟨K,
                      t ++ fromCard e ((s.piles Asrc).faceUp), ?_, hK, hhA⟩
                    rw [hfup, List.cons_append]
              · rw [setPile_piles_ne hAk]
                by_cases hAs : A = Asrc
                · rw [hAs] at hQ
                  rw [hAs, setPile_afterRunRemoved_piles_self s Asrc e]
                  exact conf_arr_Q hmemE hQ
                · rw [setPile_afterRunRemoved_piles_ne s Asrc e A hAs]
                  exact hQ

/-- **THE PILLAR, PLAY-LIFTED** — from a fully-empty pile, every play
leaves it fully empty or king-headed (the copy of the in-tree private
row). -/
private theorem conf_emptyOrKingHead_play {A : Anchor} :
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
      exact ih s₁ s' (conf_eok_oneStep hstep hQ) hrest

/-- **THE BARE-RAISE BAR** — raising a non-king off a bare seat over no
hidden deck empties its pile fully, so no return play can restore the
pre-state (the pillar: a fully-emptied pile rebuilds only to a king
head; the sole face-up card of the pre-state is no king). -/
private theorem conf_bareRaise_irr {s : State} {c : Card} {a : Anchor}
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
    rw [hpileEq, ite_eq_left hak, ← hak, hchop, conf_arr_bare hhid]
  have hQend := conf_emptyOrKingHead_play (A := a) s₁ pl s
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

/-- **THE BARE-DEPARTURE BAR** — a non-king heading its whole run out
of a pile with no face-up content below and no hidden deck leaves the
pile FULLY EMPTY, and no play can ever restore a NON-KING bottom
there (the pillar, tabToTab flavor; the per-file private copy). -/
private theorem conf_bareDeparture_irr {s : State} {c : Card} {b : Base}
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
      conf_arr_bare hhid, setPile_piles_self]
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
  have hQend := conf_emptyOrKingHead_play (A := a) s₁ pl s
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

private theorem conf_king12 : (Rank.king : Rank).toIdx = 12 := by decide

/-- Every rank index sits at most at the king's. -/
private theorem conf_toIdx_le (r : Rank) : r.toIdx ≤ 12 := by
  cases r <;> decide

/-- **STAGE 2.2, PART 1 — THE PER-LEG LEDGER ROWS** (the farm copies of
BracketDecomp's private per-leg readers; the raise few facts the LIFO
walk needs, projected from the proved per-leg rung moves). -/
private theorem conf_ledger_raiseStep {s s' : State} {c : Card}
    (hstep : State.step s (Move.tabToFound c) = some s') :
    rungAt s' c.suit = rungAt s c.suit + 1 :=
  (conf_rung_raise hstep).1

/-- A pull leg lowers its own suit's rung by exactly one (the farm
copy's pull half: the popped card's index bracket rides the prefix
reading `rung_found_prefix`-style in the walk). -/
private theorem conf_ledger_pullStep {s s' : State} {c : Card} {b : Base}
    (hstep : State.step s (Move.foundToTab c b) = some s') :
    rungAt s c.suit = rungAt s' c.suit + 1 :=
  (conf_rung_pull hstep).1

/-- **STAGE 2.2, PART 2 — THE APPEND-COUNTING ROWS** (the farm copies:
the ledger functionals count per-leg, so they split over appends and
read a located literal leg as +1 on its own suit). -/
private theorem conf_raises_append (ρ₁ ρ₂ : List Move) (σ : Suit) :
    raisesOf (ρ₁ ++ ρ₂) σ = raisesOf ρ₁ σ + raisesOf ρ₂ σ := by
  induction ρ₁ with
  | nil => simp [raisesOf]
  | cons m rest ih =>
      cases m <;> simp_all [raisesOf, ih] <;> omega

private theorem conf_pulls_append (ρ₁ ρ₂ : List Move) (σ : Suit) :
    pullsOf (ρ₁ ++ ρ₂) σ = pullsOf ρ₁ σ + pullsOf ρ₂ σ := by
  induction ρ₁ with
  | nil => simp [pullsOf]
  | cons m rest ih =>
      cases m <;> simp_all [pullsOf, ih] <;> omega

/-- **THE TWO-HEAD OVERLAP LEMMA** — the fold-order surgery priced in
the seat-cycle route: when one list admits two head-anchored
decompositions with DISTINCT heads, one region sits inside the
other's prefix.  (Pure core-list combinatorics; the Move-level
fold-order row is its instance with the constructor-clash heads.) -/
private theorem conf_oscil_foldOrder {α : Type} (x y : α) (hxy : x ≠ y) :
    ∀ (ρ₁ ρ₂ ρ₃ ρ₄ : List α),
      ρ₁ ++ x :: ρ₂ = ρ₃ ++ y :: ρ₄ →
      ∃ ws, ρ₃ = ρ₁ ++ x :: ws ∨ ρ₁ = ρ₃ ++ y :: ws := by
  intro ρ₁
  induction ρ₁ with
  | nil =>
      intro ρ₂ ρ₃ ρ₄ h
      cases ρ₃ with
      | nil =>
          injection h with h1 h2
          exact absurd h1 hxy
      | cons w ws =>
          have hxw : x = w := by
            injection h with h1 h2
          exact ⟨ws, Or.inl (by
            rw [hxw, List.nil_append])⟩
  | cons v vs ih =>
      intro ρ₂ ρ₃ ρ₄ h
      cases ρ₃ with
      | nil =>
          have hvy : v = y := by
            rw [List.cons_append] at h
            injection h with h1 h2
          exact ⟨vs, Or.inr (by
            rw [← hvy, List.nil_append])⟩
      | cons w ws =>
          rw [List.cons_append, List.cons_append] at h
          injection h with hvw hrest
          obtain ⟨ws', hdisj⟩ := ih ρ₂ ws ρ₄ hrest
          rw [← hvw]
          rcases hdisj with hL | hR
          · exact ⟨ws', Or.inl (by
              rw [hL, List.cons_append])⟩
          · exact ⟨ws', Or.inr (by
              rw [hR, List.cons_append])⟩

/-- LAYER 1, arm 1/6 — the draw leg's zone carry (found by the
record-level `stepDraw_found` congruence; piles by `stepDraw_piles`). -/
private theorem conf_carry_draw {s s' : State} {γ : Card}
    (hstep : State.step s Move.draw = some s')
    (hc : γ ∈ s.found γ.suit ∨ ∃ a, γ ∈ (s.piles a).faceUp) :
    γ ∈ s'.found γ.suit ∨ ∃ a, γ ∈ (s'.piles a).faceUp := by
  have hd : s.stepDraw = some s' := hstep
  rcases hc with hF | ⟨a, hFa⟩
  · rw [congrFun (stepDraw_found hd) γ.suit]
    exact Or.inl hF
  · rw [stepDraw_piles hd]
    exact Or.inr ⟨a, hFa⟩

/-- LAYER 1, arms 2 & 3/6 — the waste legs never ride a witness
journey (the carry is vacuous at them). -/
private theorem conf_carry_wasteFound {s s' : State} {γ w : Card}
    (hstep : State.step s (Move.wasteToFound w) = some s')
    (hrev : reversibleAtW s (Move.wasteToFound w)) :
    γ ∈ s'.found γ.suit ∨ ∃ a, γ ∈ (s'.piles a).faceUp := by
  exact absurd hrev (journey_never_wasteToFound hstep)

private theorem conf_carry_wasteTab {s s' : State} {γ w : Card} {b : Base}
    (hstep : State.step s (Move.wasteToTab w b) = some s')
    (hrev : reversibleAtW s (Move.wasteToTab w b)) :
    γ ∈ s'.found γ.suit ∨ ∃ a, γ ∈ (s'.piles a).faceUp := by
  exact absurd hrev (journey_never_wasteToTab hstep)

-- LAYER 1, arm 4/6 - the tabToFound leg's carry, priced:
-- FOUNDED side: γ ≠ e first (e is face-up atop its pile; a founded γ
-- would contradict `mem_faceUp_only`'s `.2.2.2.2`-conjugate), then the
-- per-suit split: γ.suit = e.suit ⇒ γ ∈ s.found γ.suit ⊆
-- take (rungAt+1) (`rung_found_prefix` both ways + `conf_rung_raise`'s
-- +1, `List.take_subset`); γ.suit ≠ e.suit ⇒ the same-take transport
-- (`conf_rung_raise`'s others-preserved limb + both prefixes' rw).
-- FACE-UP side: the piles-splice `if_neg/if_pos` per pile; the
-- same-pile case decomposes `faceUp = front ++ [e]` (`lastOf_eq_snoc`
-- on the inv's `pileOfTop_top`), γ ∈ front survives the removal (the
-- chop/`chop_snoc`-lookup is the one missing piece to price next
-- run), γ ≠ e kills the tail; γ ∈ run is impossible (nothing sits
-- above the top).
-- (row lands after the chop_snoc lookup; arms 1-3 are proved above)

/-- LAYER 1, arm 6/6 — the tabToTab leg's carry (founded stays — the
slide record writes only piles; face-up rides the slide shape's
below/landing limbs). -/
private theorem conf_carry_tabToTab {s s' : State} {γ e : Card} {b : Base}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToTab e b) = some s')
    (hc : γ ∈ s.found γ.suit ∨ ∃ a, γ ∈ (s.piles a).faceUp) :
    γ ∈ s'.found γ.suit ∨ ∃ a, γ ∈ (s'.piles a).faceUp := by
  obtain ⟨A, k, run, hh, hrun, hrne, hne, hpa, hothers, hpair⟩ :=
    conf_slide_shape hwf hstep
  rcases hc with hF | ⟨a, hFa⟩
  · -- FOUNDED: the slide's two records preserve foundations —
    -- peel them off the record equation, then the read is untouched
    obtain ⟨Ax, -, -, -, hrec⟩ := step_tabToTab_inv hstep
    rw [hrec, putRun_found, setPile_found]
    exact Or.inl hF
  · -- face-up: three limbs — the landing append, the departure
    -- split (below-part keeps, run-part lands), others untouched
    by_cases hak : a = k
    · rw [hak] at hFa
      refine Or.inr ⟨k, ?_⟩
      rw [hpair.right]
      exact List.mem_append.mpr (Or.inl hFa)
    · by_cases haA : a = A
      · rw [haA] at hFa
        have hsplit : (s.piles A).faceUp =
            below e ((s.piles A).faceUp) ++ run := by
          rw [hrun]
          exact conf_below_fromCard e ((s.piles A).faceUp)
        rw [hsplit] at hFa
        rcases List.mem_append.mp hFa with hbl | hrunm
        · refine Or.inr ⟨A, ?_⟩
          rw [hpa, afterRunRemoved_ne (by
              intro hcon
              rw [hcon] at hbl
              exact absurd hbl (by simp))]
          exact hbl
        · refine Or.inr ⟨k, ?_⟩
          rw [hpair.right]
          exact List.mem_append.mpr (Or.inr hrunm)
      · refine Or.inr ⟨a, ?_⟩
        rw [hothers a (fun hcon => haA hcon)
          (fun hcon => hak hcon)]
        exact hFa

/-- LAYER 1 helper — the take's monotone membership (the same-suit
founded transport of the raising/pop arms). -/
private theorem conf_take_mono {c : Card} : ∀ (R : Nat) (l : List Card),
    c ∈ List.take R l → c ∈ List.take (R+1) l := by
  intro R
  induction R with
  | zero => intro l h; cases h
  | succ r ih =>
      intro l
      cases l with
      | nil => intro h; cases h
      | cons x xs =>
          intro h
          rw [List.take_succ_cons] at h
          rw [List.take_succ_cons]
          rcases List.mem_cons.mp h with rfl | htl
          · exact List.mem_cons_self ..
          · exact List.mem_cons.mpr (Or.inr (ih xs htl))

/-- LAYER 1, arm 4's FOUNDED side — a founded card stays founded under
a tabToFound leg (other suits' takes identical by the rung-raise's
others-limb; the raised suit's take grows by one — the mono). -/
private theorem conf_carry_tabToFound_founded {s s' : State} {γ e : Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound e) = some s')
    (hF : γ ∈ s.found γ.suit) :
    γ ∈ s'.found γ.suit := by
  obtain ⟨hrise, hothers⟩ := conf_rung_raise hstep
  have hwf' : s'.WF := step_wf hwf hstep
  have hp0 := rung_found_prefix s hwf γ.suit
  have hp1 := rung_found_prefix s' hwf' γ.suit
  rw [hp0] at hF
  rw [hp1]
  by_cases hes : γ.suit = e.suit
  · rw [← hes] at hrise
    rw [hrise]
    exact conf_take_mono _ _ hF
  · rw [hothers γ.suit (fun hcon => hes hcon)]
    exact hF

/-- LAYER 1, arm 4/6 (full) — the tabToFound leg's carry: founded by
the banked founded-side row; face-up through the piles splice, the
same-pile front kept by `chop_snoc`+`afterRunRemoved_ne`, the raised
tail itself exiting into the foundation's append. -/
private theorem conf_carry_tabToFound {s s' : State} {γ e : Card}
    (hwf : s.WF)
    (hstep : State.step s (Move.tabToFound e) = some s')
    (hc : γ ∈ s.found γ.suit ∨ ∃ a, γ ∈ (s.piles a).faceUp) :
    γ ∈ s'.found γ.suit ∨ ∃ a, γ ∈ (s'.piles a).faceUp := by
  rcases hc with hF | ⟨a, hFa⟩
  · exact Or.inl (conf_carry_tabToFound_founded hwf hstep hF)
  · obtain ⟨-, k, hpod, hs'⟩ := step_tabToFound_inv hstep
    have hpileEq : ∀ y, s'.piles y = (if y = k then
        Pile.afterRunRemoved (s.piles k) (chop (s.piles k).faceUp)
        else s.piles y) := by
      intro y
      rw [hs']
    by_cases hak : a = k
    · have hlast := (pileOfTop_top hpod).2
      rw [hak] at hFa
      obtain ⟨front, hfront⟩ := lastOf_eq_snoc hlast
      rw [hfront] at hFa
      rcases List.mem_append.mp hFa with hbl | hlastm
      · refine Or.inr ⟨k, ?_⟩
        rw [hpileEq k, ite_eq_left rfl]
        rw [show chop ((s.piles k).faceUp) = front from by
            rw [hfront]
            exact chop_snoc]
        rw [afterRunRemoved_ne (by
            intro hcon
            rw [hcon] at hbl
            exact absurd hbl (by simp))]
        exact hbl
      · rw [List.mem_singleton] at hlastm
        rw [hlastm, hs']
        refine Or.inl ?_
        simp only [State.setFound, if_pos]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    · refine Or.inr ⟨a, ?_⟩
      rw [hpileEq a, ite_eq_right hak]
      exact hFa

/-- LAYER 1, arm 5/6 — the foundToTab leg's carry (the pull): a
founded γ in the pulled suit rides the front (`lastOf_eq_snoc` +
`chop_snoc` — the popped tail alone leaves) or IS the popped card
(γ = w exits face-up through the landing profiles); face-up side by
the putCard profiles. -/
private theorem conf_carry_foundToTab {s s' : State} {γ w : Card} {b : Base}
    (hstep : State.step s (Move.foundToTab w b) = some s')
    (hc : γ ∈ s.found γ.suit ∨ ∃ a, γ ∈ (s.piles a).faceUp) :
    γ ∈ s'.found γ.suit ∨ ∃ a, γ ∈ (s'.piles a).faceUp := by
  obtain ⟨c', ht, heqw, hcp, hs'⟩ := step_foundToTab_inv hstep
  rcases hc with hF | ⟨a, hFa⟩
  · -- FOUNDED: the record's setFound rewrite; split on the suit
    by_cases hγw : γ.suit = w.suit
    · -- same suit: the list's front survives by chop_snoc; the
      -- popped card IS its last (foundTop reads lastOf)
      rw [hγw] at hF
      have hlastw : lastOf (s.found w.suit) = some w := by
        rw [show s.foundTop w.suit = lastOf (s.found w.suit) from rfl,
          heqw] at ht
        exact ht
      obtain ⟨front, hfront⟩ := lastOf_eq_snoc hlastw
      rw [hfront] at hF
      by_cases hgw : γ = w
      · -- the popped card exits face-up: the landing profiles
        rw [hgw, hs']
        cases b with
        | inl e =>
            refine Or.inr ⟨e, ?_⟩
            simp only [putCard_piles_inl, ite_eq_left]
            exact List.mem_cons_self ..
        | inr z =>
            obtain ⟨k, hpin, -⟩ := canPlace_inr hcp
            have hmidpin :
                (s.setFound w.suit (chop (s.found w.suit))).pileOfTop z
                = some k := by
              rw [conf_pileOfTop_congr
                (setFound_piles s w.suit (chop (s.found w.suit))) z]
              exact hpin
            refine Or.inr ⟨k, ?_⟩
            simp only [putCard_piles_inr _ _ _ _ hmidpin, ite_eq_left]
            exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      · refine Or.inl ?_
        rw [hs', putCard_found]
        simp only [State.setFound, hfront, chop_snoc, if_pos hγw]
        rcases List.mem_append.mp hF with hbl | hlastm
        · exact hbl
        · rw [List.mem_singleton] at hlastm
          exact absurd hlastm hgw
    · -- other suit: the else-branch keeps s's list
      refine Or.inl ?_
      rw [hs', putCard_found]
      simp only [State.setFound, if_neg hγw]
      exact hF
  · -- FACE-UP: the putCard profiles on the pre-pull setFound state
    rw [hs']
    have hmid : (s.setFound w.suit (chop (s.found w.suit))).piles
        = s.piles :=
      setFound_piles s w.suit (chop (s.found w.suit))
    cases b with
    | inl e =>
        have hp : ((s.setFound w.suit (chop (s.found w.suit))).putCard w
            (Sum.inl e)).piles a
            = (if a = e then (⟨[], [w]⟩ : Pile)
               else (s.setFound w.suit (chop (s.found w.suit))).piles a) := rfl
        refine Or.inr ⟨a, ?_⟩
        rw [hp]
        by_cases hae : a = e
        · exfalso
          obtain ⟨hemp, -⟩ := canPlace_inl hcp
          rw [← hae] at hemp
          have hfupE := ((Pile.isEmpty_eq _).mp hemp).2
          exact absurd hFa (by rw [hfupE]; simp)
        · rw [ite_eq_right hae, hmid]
          exact hFa
    | inr z =>
        obtain ⟨k, hpin, -⟩ := canPlace_inr hcp
        have hmidpin :
            (s.setFound w.suit (chop (s.found w.suit))).pileOfTop z
            = some k := by
          rw [conf_pileOfTop_congr hmid z]
          exact hpin
        have hp : ((s.setFound w.suit (chop (s.found w.suit))).putCard w
            (Sum.inr z)).piles a
            = (if a = k then
                { s.piles k with faceUp := (s.piles k).faceUp ++ [w] }
               else (s.setFound w.suit (chop (s.found w.suit))).piles a) := by
          simp only [putCard_piles_inr _ _ _ _ hmidpin]
          rw [congrFun hmid]
        refine Or.inr ⟨a, ?_⟩
        rw [hp]
        by_cases hak : a = k
        · rw [hak] at hFa
          rw [hak, ite_eq_left rfl]
          show γ ∈ (s.piles k).faceUp ++ [w]
          exact List.mem_append.mpr (Or.inl hFa)
        · rw [ite_eq_right hak, hmid]
          exact hFa

/-- **LAYER 1 — THE ZONE CARRY, GLUED** — along any witness journey a
card founded-or-face-up at the start stays founded-or-face-up at
the end (the six per-leg rows composed by the shuffle induction).
The shared infrastructure: the census folds (seatCycle,
familyCarry) and the orphan-seat interlock's step-2 closures all
consume this row at grade. -/
private theorem conf_foundedCarry {st : State} {γ : Card} :
    ∀ {w : State} {π : List Move},
    ShufflePlayW st π w → st.WF →
    (γ ∈ st.found γ.suit ∨ ∃ a, γ ∈ (st.piles a).faceUp) →
    (γ ∈ w.found γ.suit ∨ ∃ a, γ ∈ (w.piles a).faceUp) := by
  intro w π h
  induction h with
  | nil u => intro hwf hc; exact hc
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro hwf hc
      have hwf₁ : s₁.WF := step_wf hwf hstep
      cases m with
      | draw => exact ih hwf₁ (conf_carry_draw hstep hc)
      | wasteToFound w' =>
          exact ih hwf₁ (conf_carry_wasteFound hstep hrev)
      | wasteToTab w' b =>
          exact ih hwf₁ (conf_carry_wasteTab hstep hrev)      | tabToFound w' =>
          exact ih hwf₁ (conf_carry_tabToFound hwf hstep hc)
      | foundToTab w' b =>
          exact ih hwf₁ (conf_carry_foundToTab hstep hc)
      | tabToTab w' b =>
          exact ih hwf₁ (conf_carry_tabToTab hwf hstep hc)

/-- The rank of a given index (the 13-cell enumeration; the exfalso
keeps `omega` off non-arithmetic goals, staying `Classical.choice`-free). -/
private theorem conf_rank_of_idx {n : Nat} (hn : n < 13) :
    ∃ r : Rank, r.toIdx = n := by
  cases n with
  | zero => exact ⟨Rank.ace, rfl⟩
  | succ n1 =>
    cases n1 with
    | zero => exact ⟨Rank.two, rfl⟩
    | succ n2 =>
      cases n2 with
      | zero => exact ⟨Rank.three, rfl⟩
      | succ n3 =>
        cases n3 with
        | zero => exact ⟨Rank.four, rfl⟩
        | succ n4 =>
          cases n4 with
          | zero => exact ⟨Rank.five, rfl⟩
          | succ n5 =>
            cases n5 with
            | zero => exact ⟨Rank.six, rfl⟩
            | succ n6 =>
              cases n6 with
              | zero => exact ⟨Rank.seven, rfl⟩
              | succ n7 =>
                cases n7 with
                | zero => exact ⟨Rank.eight, rfl⟩
                | succ n8 =>
                  cases n8 with
                  | zero => exact ⟨Rank.nine, rfl⟩
                  | succ n9 =>
                    cases n9 with
                    | zero => exact ⟨Rank.ten, rfl⟩
                    | succ n10 =>
                      cases n10 with
                      | zero => exact ⟨Rank.jack, rfl⟩
                      | succ n11 =>
                        cases n11 with
                        | zero => exact ⟨Rank.queen, rfl⟩
                        | succ n12 =>
                          cases n12 with
                          | zero => exact ⟨Rank.king, rfl⟩
                          | succ mm => exfalso; omega

/-- Membership in a bounded take is membership in the list (the
probe's kit copy). -/
private theorem conf_take_sub : ∀ {α : Type} (n : Nat) (l : List α)
    (x : α), x ∈ l.take n → x ∈ l := by
  intro α n
  induction n with
  | zero =>
      intro l x hmem
      simp [List.take] at hmem
  | succ n ih =>
      intro l x hmem
      cases l with
      | nil => simp [List.take] at hmem
      | cons y t =>
          rw [List.take_succ_cons] at hmem
          rcases List.mem_cons.1 hmem with rfl | hrest
          · exact List.mem_cons.2 (Or.inl rfl)
          · exact List.mem_cons.2 (Or.inr (ih t x hrest))

/-- **THE DEAL NEVER INVENTS (the shrink lanes)** — each deal lane's
residents came from the stock: the dealt lane and the remnant lane
both only ever hold cards of the source list (the k-induction
mirroring the banked forward membership row `conf_dealUpTo_mem`; the
succ-cons case's dealt lane is cons-headed, the remnant lane drops
the dealt head). -/
private theorem conf_deal_shrink (d : Card) : ∀ (k : Nat) (l : List Card),
    (d ∈ (State.dealUpTo k l).1 → d ∈ l) ∧
      (d ∈ (State.dealUpTo k l).2 → d ∈ l) := by
  intro k
  induction k with
  | zero =>
      intro l
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [State.dealUpTo] at hmem
        exact absurd hmem (by simp)
      · intro hmem
        simp only [State.dealUpTo] at hmem
        exact hmem
  | succ k ih =>
      intro l
      cases l with
      | nil =>
          refine ⟨?_, ?_⟩
          all_goals
            intro hmem
            simp only [State.dealUpTo] at hmem
            exact absurd hmem (by simp)
      | cons x xs =>
          obtain ⟨ih1, ih2⟩ := ih xs
          refine ⟨?_, ?_⟩
          · intro hmem
            simp only [State.dealUpTo] at hmem
            rcases List.mem_cons.mp hmem with heq | hrest
            · rw [heq]
              exact List.mem_cons_self ..
            · exact List.mem_cons.2 (Or.inr (ih1 hrest))
          · intro hmem
            simp only [State.dealUpTo] at hmem
            exact List.mem_cons.2 (Or.inr (ih2 hmem))

/-- **THE UNION NEVER GAINS (closed)** — the stock/waste world never
gains along a witness play: the tail carries the induction backward,
and each single leg is inverted arm by arm (the waste letters never
ride; the tab/found/cargo writers keep the union verbatim through
`putCard_keep`/`putRun_keep`; the draw's zone-flip reads back through
the deal shrink — the remnant lane stays stock, the dealt lane
re-reverses into it, and the recycle lanes (`recycle_keep`,
`recycle_nil`, `recycle_allEmpty`) map the deal's source onto the
start union). -/
private theorem conf_orphan_union {st : State} : ∀ {u : State}
    {τ : List Move},
    ShufflePlayW st τ u →
    (∀ d : Card, d ∈ u.stock ∨ d ∈ u.waste → d ∈ st.stock ∨ d ∈ st.waste) := by
  intro u τ h
  induction h with
  | nil s =>
      intro d hcyc
      exact hcyc
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro d h1
      have hmid : d ∈ s₁.stock ∨ d ∈ s₁.waste := ih d h1
      cases m with
      | draw =>
          have hd : s₀.stepDraw = some s₁ := hstep
          obtain ⟨r, hrEq, -, hyEq⟩ := draw_unfold hd
          rw [hyEq] at hmid
          rcases hmid with hst | hwst
          · have hmem : d ∈ r.stock :=
              (conf_deal_shrink d r.drawStep r.stock).2 hst
            cases hss : s₀.stock with
            | nil =>
                cases hws : s₀.waste with
                | nil =>
                    have hall : r = s₀ := by
                      rw [← hrEq]
                      exact recycle_allEmpty s₀ hss hws
                    rw [hall, hss] at hmem
                    exact absurd hmem (by simp)
                | cons v vs =>
                    have hrt : r = { s₀ with
                        stock := s₀.waste.reverse,
                        waste := ([] : List Card) } := by
                      rw [← hrEq]
                      exact recycle_nil s₀ hss (by rw [hws]; simp)
                    rw [hrt, hws] at hmem
                    exact Or.inr (List.mem_reverse.mp hmem)
            | cons x xs =>
                have hrt : r = s₀ := by
                  rw [← hrEq]
                  exact recycle_keep s₀ (by rw [hss]; simp)
                rw [hrt, hss] at hmem
                exact Or.inl hmem
          · cases hss : s₀.stock with
            | nil =>
                cases hws : s₀.waste with
                | nil =>
                    have hall : r = s₀ := by
                      rw [← hrEq]
                      exact recycle_allEmpty s₀ hss hws
                    rcases List.mem_append.mp hwst with hD | hR
                    · have hmem : d ∈ r.stock :=
                        (conf_deal_shrink d r.drawStep r.stock).1
                          (List.mem_reverse.mp hD)
                      rw [hall, hss] at hmem
                      exact absurd hmem (by simp)
                    · rw [hall, hws] at hR
                      exact absurd hR (by simp)
                | cons v vs =>
                    have hrt : r = { s₀ with
                        stock := s₀.waste.reverse,
                        waste := ([] : List Card) } := by
                      rw [← hrEq]
                      exact recycle_nil s₀ hss (by rw [hws]; simp)
                    rcases List.mem_append.mp hwst with hD | hR
                    · have hmem : d ∈ r.stock :=
                        (conf_deal_shrink d r.drawStep r.stock).1
                          (List.mem_reverse.mp hD)
                      rw [hrt, hws] at hmem
                      exact Or.inr (List.mem_reverse.mp hmem)
                    · rw [hrt] at hR
                      exact absurd hR (by simp)
            | cons x xs =>
                have hrt : r = s₀ := by
                  rw [← hrEq]
                  exact recycle_keep s₀ (by rw [hss]; simp)
                rcases List.mem_append.mp hwst with hD | hR
                · have hmem : d ∈ r.stock :=
                    (conf_deal_shrink d r.drawStep r.stock).1
                      (List.mem_reverse.mp hD)
                  rw [hrt, hss] at hmem
                  exact Or.inl hmem
                · rw [hrt] at hR
                  exact Or.inr hR
      | wasteToFound walt =>
          exact absurd hrev (journey_never_wasteToFound hstep)
      | wasteToTab walt balt =>
          exact absurd hrev (journey_never_wasteToTab hstep)
      | tabToFound walt =>
          obtain ⟨-, k, -, hs⟩ := step_tabToFound_inv hstep
          rw [hs] at hmid
          exact hmid
      | foundToTab walt balt =>
          obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv hstep
          rw [hs] at hmid
          obtain ⟨-, hP1, hP2, -⟩ :=
            putCard_keep (st := s₀.setFound walt.suit
              (chop (s₀.found walt.suit))) (c := walt) (b := balt)
          rw [hP1, hP2] at hmid
          exact hmid
      | tabToTab walt balt =>
          obtain ⟨Asrc, -, -, -, hs⟩ := step_tabToTab_inv hstep
          rw [hs] at hmid
          obtain ⟨-, hP1, hP2, -⟩ :=
            putRun_keep (st := s₀.setPile Asrc
              (Pile.afterRunRemoved (s₀.piles Asrc)
                (below walt ((s₀.piles Asrc).faceUp))))
              (run := fromCard walt ((s₀.piles Asrc).faceUp)) (b := balt)
          rw [hP1, hP2] at hmid
          exact hmid

/-- **THE ROAMING SEAT (closed)** — a non-king card that starts the
journey seated on a fitting face-up below-neighbor is, at the end,
either founded (hence nowhere face-up, by `mem_found_unique` on the
WF end state carried by `conf_wf_along`) or still seated on a
below-neighbor: the seat itself comes off the banked `Below_stable`
(the seed IS a `Below`-shape instantiation at the start state), and
the end-fit off the run discipline (`SeedKit.runOK_adjacent_fit` on the
end state's pile). -/
private theorem conf_orphan_roam {st u : State} (hwf : st.WF)
    {τ : List Move}
    (hτ : ShufflePlayW st τ u) {d : Card} (hnk : d.rank ≠ Rank.king)
    (hseed : ∃ a bs z, (st.piles a).faceUp = bs ++ [z, d] ∧
      canSitOn d z = true) :
    (∃ a L z R, (u.piles a).faceUp = L ++ z :: d :: R ∧
      canSitOn d z = true) ∨
      (∀ a, d ∉ (u.piles a).faceUp) := by
  obtain ⟨a, bs, z, hshape, hfit⟩ := hseed
  have hwfu : u.WF := conf_wf_along hτ hwf
  rcases Below_stable hwf hτ hnk (Or.inr ⟨z, a, bs, [], hshape⟩) with
    hF | ⟨z', a', L, R, hs'⟩
  · exact Or.inr (fun a₂ => ((mem_found_unique hwfu hF).1 a₂).2)
  · refine Or.inl ⟨a', L, z', R, hs', ?_⟩
    exact SeedKit.runOK_adjacent_fit z' d L R
      (by rw [← hs']; exact hwfu.2.1 a')

/-- The nodup slice: a seated card's below-tail cannot contain it
(the face-up pile lists are nodup). -/
private theorem conf_nodup_slice {z d : Card} :
    ∀ (L : List Card) (R : List Card),
      (L ++ z :: d :: R).Nodup → z ∉ d :: R := by
  intro L
  induction L with
  | nil =>
      intro R hn
      exact (List.nodup_cons.1 hn).1
  | cons y ys ih =>
      intro R hn
      exact ih R ((List.nodup_cons.1 hn).2)

/-- **SEAM — THE TOP CLASH (closed)**: a pile TOP cannot have a card
seated directly above it — the top read and the seating shape
contradict on the nodup pile list. -/
private theorem conf_orphan_topclash {u : State} (hwfu : u.WF)
    {z d : Card}
    (hpo : ∃ Q, u.pileOfTop z = some Q)
    (hpkg : ∃ a L R, (u.piles a).faceUp = L ++ z :: d :: R) :
    False := by
  obtain ⟨Q, hpoQ⟩ := hpo
  obtain ⟨A, L, R, hpkg⟩ := hpkg
  obtain ⟨-, hQlast⟩ := pileOfTop_top hpoQ
  have hzA : z ∈ (u.piles A).faceUp := by
    rw [hpkg]
    exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
  have hn : ((u.piles Q).faceUp).Nodup := runOK_nodup (hwfu.2.1 Q)
  by_cases hAQ : A = Q
  · rw [hAQ] at hzA hpkg
    rw [hpkg] at hQlast hn
    rw [conf_lastOf_append _ _ (by
        intro hcon
        cases hcon)] at hQlast
    cases R with
    | nil =>
        have h : some d = some z := hQlast
        have hzd : z = d := (Option.some.inj h).symm
        subst hzd
        exact absurd (List.mem_cons.2 (Or.inl rfl))
          (conf_nodup_slice L [] hn)
    | cons r rs =>
        have hzR : z ∈ r :: rs :=
          lastOf_mem (show lastOf (r :: rs) = some z from by
            have := hQlast
            exact this)
        exact absurd (show z ∈ d :: r :: rs from
            List.mem_cons.2 (Or.inr hzR))
          (conf_nodup_slice L (r :: rs) hn)
  · exact (mem_faceUp_unique hwfu hzA Q (fun hcon => hAQ hcon.symm)).1
      (lastOf_mem hQlast)

/-- **THE BACKWARD-ORPHAN KILL OF THE CROSSING DOOR** — the full
upward-door circumvention, proved modulo the two seams above and
`Orig.OrphanSeat.lean`'s orphan-seat residue.  The door package is
exactly the banked `crossing_door_exists` output shape; `hdcover` is
the fork's `pair_cover_pins` twin-cover package; `hback` is the
class-return journey from the door state to the fork. -/
private theorem conf_door_orphan {st u s₁ : State} (hwf : st.WF)
    (hwfu : u.WF) {π ρ : List Move}
    (hjourney : ShufflePlayW st π u) (hback : ShufflePlayW u ρ st)
    {x d m m' : Card}
    (hx : ForkWitness st x)
    (hpair : (m = x ∧ m' = x.twin) ∨ (m = x.twin ∧ m' = x))
    (hfire : State.step u (Move.tabToFound m') = some s₁)
    (helev : rungAt u m.suit > x.rank.toIdx)
    (hdcover : ∃ a bs, (st.piles a).faceUp = bs ++ [x.twin, d] ∧
      canSitOn d x.twin = true)
    (hdcol : d.suit.color ≠ x.suit.color)
    (hdnext : st.nextUp d = false)
    (hdpin : rungAt st d.suit + 1 ≤ x.rank.toIdx) :
    False := by
  obtain ⟨A, bsA, hshape, hfit⟩ := hdcover
  obtain ⟨hdrankT, hdcolT⟩ := (canSitOn_eq d x.twin).mp hfit
  rw [Card.twin_rank] at hdrankT
  have hxtc : x.twin.suit.color = x.suit.color := by
    rw [Card.twin_suit, Suit.color_twin]
  rw [hxtc] at hdcolT
  have hdmemST : d ∈ (st.piles A).faceUp := by
    rw [hshape]
    exact List.mem_append.2 (Or.inr (List.mem_cons.2
      (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
  have hdred := Rank.toIdx_lt x.rank
  have hdnk : d.rank ≠ Rank.king := by
    intro hcon
    have hk12 : Rank.king.toIdx = 12 := rfl
    rw [hcon] at hdrankT
    omega
  have hbridge : rungAt st d.suit = st.foundHeight d.suit := rfl
  have hneR : d.rank.toIdx ≠ rungAt st d.suit := by
    intro hc0
    have htrue : st.nextUp d = true := by
      show decide (d.rank.toIdx = st.foundHeight d.suit) = true
      rw [hc0, hbridge]
      exact decide_eq_true rfl
    rw [htrue] at hdnext
    simp at hdnext
  have hdeepst : rungAt st d.suit + 2 ≤ x.rank.toIdx := by omega
  have hnothid : ∀ k, d ∉ (u.piles k).hidden := by
    intro k hcon
    have hp := shuffle_hiddenPinned hjourney k
    rw [hp] at hcon
    by_cases hk : k = A
    · rw [hk] at hcon
      exact (mem_faceUp_only hwf hdmemST).2.1 hcon
    · exact ((mem_faceUp_only hwf hdmemST).1 k hk).1 hcon
  rcases hpair with ⟨hm, hm'⟩ | ⟨hm, hm'⟩
  · have hms : x = m := hm.symm
    subst hms
    have hms' : x.twin = m' := hm'.symm
    subst hms'
    have hmFound : x ∈ u.found x.suit :=
      FoundKit.mem_found_of_rung hwfu (by
        have hrw : u.foundHeight x.suit = rungAt u x.suit := rfl
        omega)
    rcases conf_orphan_roam hwf hjourney hdnk ⟨A, bsA, x.twin, hshape, hfit⟩ with
      ⟨a₂, L, b, R, hpkg, hbfit⟩ | haway
    · obtain ⟨hbr, hbc⟩ := (canSitOn_eq d b).mp hbfit
      have hbx : b.suit.color = x.suit.color := SeedKit.color_pair hbc hdcolT
      have hbCell : b = x ∨ b = x.twin :=
        SeedKit.rankColor_pair (by omega) hbx
      have hbmem : b ∈ (u.piles a₂).faceUp := by
        rw [hpkg]
        exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      rcases hbCell with hb1 | hb1
      · have hxmem : x ∈ (u.piles a₂).faceUp := hb1 ▸ hbmem
        exact ((mem_found_unique hwfu hmFound).1 a₂).2 hxmem
      · subst hb1
        obtain ⟨-, Q, hpoQ, -⟩ := step_tabToFound_inv hfire
        exact conf_orphan_topclash hwfu ⟨Q, hpoQ⟩ ⟨a₂, L, R, hpkg⟩
    · rcases FoundKit.zone_residency u hwfu d with ⟨s, hdFu⟩ | ⟨k, hh⟩ |
        ⟨k, hfa⟩ | hstock | hwaste
      · have hsub := rung_found_prefix u hwfu s
        have htake : d ∈ s.upCards.take (rungAt u s) := by
          rw [← hsub]
          exact hdFu
        have hdlist : d ∈ s.upCards := conf_take_sub _ _ _ htake
        have hsuit : s = d.suit := by
          rcases d with ⟨ds, dr⟩
          obtain ⟨r', -, hEq⟩ := List.mem_map.mp hdlist
          injection hEq with h1 _
        have hdF2 : d ∈ u.found d.suit := hsuit ▸ hdFu
        have hRungUp : d.rank.toIdx < rungAt u d.suit :=
          FoundKit.mem_found_rank_lt hwfu hdF2
        have hx13 := Rank.toIdx_lt x.rank
        have heidx : x.rank.toIdx - 2 < 13 := by omega
        obtain ⟨rk, hrk⟩ := conf_rank_of_idx heidx
        have hefound : rk.toIdx + 2 = x.rank.toIdx := by omega
        have heF : Card.mk d.suit rk ∈ u.found d.suit := by
          refine FoundKit.mem_found_of_rung hwfu ?_
          show rk.toIdx < rungAt u d.suit
          omega
        have heN : Card.mk d.suit rk ∉ st.found d.suit := by
          intro hcon
          have hlt := FoundKit.mem_found_rank_lt hwf hcon
          have hlt2 : rk.toIdx < rungAt st d.suit :=
            show rk.toIdx < rungAt st d.suit from hlt
          omega
        obtain ⟨P, b₂, hemem2, hb₂mem, hfit2⟩ :=
          cross_orphan_seat hwfu hback (e := Card.mk d.suit rk)
            (by
              show (Card.mk d.suit rk).rank ≠ Rank.king
              intro hcon
              have hc2 : rk = Rank.king := hcon
              rw [hc2] at hrk
              have hk12 : Rank.king.toIdx = 12 := rfl
              omega) heF heN
        obtain ⟨hbr2, hbc2⟩ :=
          (canSitOn_eq (Card.mk d.suit rk) b₂).mp hfit2
        have hbr3 : rk.toIdx + 1 = b₂.rank.toIdx :=
          show rk.toIdx + 1 = b₂.rank.toIdx from hbr2
        have hbx2 : b₂.suit.color = x.suit.color :=
          SeedKit.color_pair hbc2 hdcolT
        have hb₂F : b₂ ∈ st.found b₂.suit :=
          pair_lowFamily_founded hwf hx hbx2 (by omega)
        exact (mem_faceUp_only hwf hb₂mem).2.2.2.2 b₂.suit hb₂F
      · exact hnothid k hh
      · exact haway k hfa
      · rcases conf_orphan_union hjourney d (Or.inl hstock) with hS | hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.1 hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.2.1 hS
      · rcases conf_orphan_union hjourney d (Or.inr hwaste) with hS | hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.1 hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.2.1 hS
  · have hms : x.twin = m := hm.symm
    subst hms
    have hms' : x = m' := hm'.symm
    subst hms'
    have htwinr : x.twin.rank.toIdx = x.rank.toIdx :=
      congrArg Rank.toIdx (Card.twin_rank x)
    have hmFound : x.twin ∈ u.found x.twin.suit :=
      FoundKit.mem_found_of_rung hwfu (by
        have hrw : u.foundHeight x.twin.suit = rungAt u x.twin.suit := rfl
        omega)
    rcases conf_orphan_roam hwf hjourney hdnk ⟨A, bsA, x.twin, hshape, hfit⟩ with
      ⟨a₂, L, b, R, hpkg, hbfit⟩ | haway
    · obtain ⟨hbr, hbc⟩ := (canSitOn_eq d b).mp hbfit
      have hbx : b.suit.color = x.suit.color := SeedKit.color_pair hbc hdcolT
      have hbCell : b = x ∨ b = x.twin :=
        SeedKit.rankColor_pair (by omega) hbx
      have hbmem : b ∈ (u.piles a₂).faceUp := by
        rw [hpkg]
        exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      rcases hbCell with hb1 | hb1
      · subst hb1
        obtain ⟨-, Q, hpoQ, -⟩ := step_tabToFound_inv hfire
        exact conf_orphan_topclash hwfu ⟨Q, hpoQ⟩ ⟨a₂, L, R, hpkg⟩
      · have hxmem : x.twin ∈ (u.piles a₂).faceUp := hb1 ▸ hbmem
        exact ((mem_found_unique hwfu hmFound).1 a₂).2 hxmem
    · rcases FoundKit.zone_residency u hwfu d with ⟨s, hdFu⟩ | ⟨k, hh⟩ |
        ⟨k, hfa⟩ | hstock | hwaste
      · have hsub := rung_found_prefix u hwfu s
        have htake : d ∈ s.upCards.take (rungAt u s) := by
          rw [← hsub]
          exact hdFu
        have hdlist : d ∈ s.upCards := conf_take_sub _ _ _ htake
        have hsuit : s = d.suit := by
          rcases d with ⟨ds, dr⟩
          obtain ⟨r', -, hEq⟩ := List.mem_map.mp hdlist
          injection hEq with h1 _
        have hdF2 : d ∈ u.found d.suit := hsuit ▸ hdFu
        have hRungUp : d.rank.toIdx < rungAt u d.suit :=
          FoundKit.mem_found_rank_lt hwfu hdF2
        have hx13 := Rank.toIdx_lt x.rank
        have heidx : x.rank.toIdx - 2 < 13 := by omega
        obtain ⟨rk, hrk⟩ := conf_rank_of_idx heidx
        have hefound : rk.toIdx + 2 = x.rank.toIdx := by omega
        have heF : Card.mk d.suit rk ∈ u.found d.suit := by
          refine FoundKit.mem_found_of_rung hwfu ?_
          show rk.toIdx < rungAt u d.suit
          omega
        have heN : Card.mk d.suit rk ∉ st.found d.suit := by
          intro hcon
          have hlt := FoundKit.mem_found_rank_lt hwf hcon
          have hlt2 : rk.toIdx < rungAt st d.suit :=
            show rk.toIdx < rungAt st d.suit from hlt
          omega
        obtain ⟨P, b₂, hemem2, hb₂mem, hfit2⟩ :=
          cross_orphan_seat hwfu hback (e := Card.mk d.suit rk)
            (by
              show (Card.mk d.suit rk).rank ≠ Rank.king
              intro hcon
              have hc2 : rk = Rank.king := hcon
              rw [hc2] at hrk
              have hk12 : Rank.king.toIdx = 12 := rfl
              omega) heF heN
        obtain ⟨hbr2, hbc2⟩ :=
          (canSitOn_eq (Card.mk d.suit rk) b₂).mp hfit2
        have hbr3 : rk.toIdx + 1 = b₂.rank.toIdx :=
          show rk.toIdx + 1 = b₂.rank.toIdx from hbr2
        have hbx2 : b₂.suit.color = x.suit.color :=
          SeedKit.color_pair hbc2 hdcolT
        have hb₂F : b₂ ∈ st.found b₂.suit :=
          pair_lowFamily_founded hwf hx hbx2 (by omega)
        exact (mem_faceUp_only hwf hb₂mem).2.2.2.2 b₂.suit hb₂F
      · exact hnothid k hh
      · exact haway k hfa
      · rcases conf_orphan_union hjourney d (Or.inl hstock) with hS | hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.1 hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.2.1 hS
      · rcases conf_orphan_union hjourney d (Or.inr hwaste) with hS | hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.1 hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.2.1 hS

/-- **THE LOOP-CLOSURE ENGINE (per-file copy)** — a play from `x`
landing at `w`, spliced with ANY play back from `w` to `x`, is a
witness shuffle `x → w` (the copy of `Orig/MacroInternal.lean`'s
private `shuffleW_of_round`; for every interior leg the loop
remainder is an explicit returning play, so each leg carries its own
`reversibleAtW`). -/
private theorem conf_shuffleW_of_round : ∀ (σ : List Move) (x w : State),
    x.run σ = some w → ∀ ρ : List Move, w.run ρ = some x →
      ShufflePlayW x σ w := by
  intro σ
  induction σ with
  | nil =>
      intro x w hσ ρ hρ
      have hxw : some x = some w := hσ
      injection hxw with hx
      rw [hx]
      exact .nil w
  | cons p rest ih =>
      intro x w hσ ρ hρ
      obtain ⟨y, hp, hrest⟩ := State.run_cons hσ
      refine .cons ⟨y, rest ++ ρ, hp, run_split rest y w ρ x hrest hρ⟩ hp ?_
      exact ih y w hrest (ρ ++ [p]) (run_split ρ w x [p] y hρ (run_one hp))

/-- **ONE REVERSIBLE LEG STAYS IN CLASS (per-file copy)** — the
firing's own witness gives the both-directions shuffle pair (the
copy of `Orig/MacroInternal.lean`'s private `class_leg`; the σ side
is the loop-closed return play, the τ side is the single-move
witness play, and the setoid's `r` IS that pair). -/
private theorem conf_class_leg {st s₁ : State} {m : Move}
    (hrev : reversibleAtW st m) (hstep : State.step st m = some s₁) :
    sameOrbitSetoid.r st s₁ := by
  obtain ⟨s₁', play, hstep', hrun⟩ := hrev
  have hs : s₁' = s₁ := Option.some.inj (hstep'.symm.trans hstep)
  rw [hs] at hrun
  show RevEqW s₁ st
  exact ⟨play, conf_shuffleW_of_round play s₁ st hrun [m] (run_one hstep),
    [m], .cons ⟨s₁, play, hstep, hrun⟩ hstep (.nil s₁)⟩

/-- **THE WITNESS PLAYBACK (closed)** — every witness journey rides
backwards: each leg's class row carries the loop-closed return as
the both-directions pair's own σ side (the setoid's definition, not
the leg's run-play in disguise), and the tail's return splices on
by `ShufflePlayW_append`. -/
private theorem conf_playback {st : State} : ∀ {u : State} {π : List Move},
    ShufflePlayW st π u → ∃ ρ, ShufflePlayW u ρ st := by
  intro u π h
  induction h with
  | nil s =>
      exact ⟨[], ShufflePlayW.nil s⟩
  | @cons s₀ m s₁ rest u₀ hrev hstep hrest ih =>
      obtain ⟨ρleg, hρleg, -⟩ : RevEqW s₁ s₀ := conf_class_leg hrev hstep
      obtain ⟨ρ₁, hρ₁⟩ := ih
      exact ⟨ρ₁ ++ ρleg, ShufflePlayW_append hρ₁ hρleg⟩

/-- **THE DOOR BAR** — the crossing door cannot fire in any macro
class containing a fork: at the door state one pair member would
found while the other's suit rung already stands past the fork
index.  The backward-orphan kill (the two door orders, the hidden
bar, the orphan construction, the backward seat application, and
the fork-saturation census) — mounted on the imported
`cross_orphan_seat` residue, the three named seams, and the
`pair_cover_pins` twin-cover package. -/
private theorem crossing_door_barred {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) {u s₁ : State} (π : List Move)
    (hpre : ShufflePlayW st π u) :
    ((State.step u (Move.tabToFound x) = some s₁ ∧
        rungAt u x.twin.suit > x.rank.toIdx) ∨
     (State.step u (Move.tabToFound x.twin) = some s₁ ∧
        rungAt u x.suit > x.rank.toIdx)) →
    False := by
  rintro (⟨hstep, helev⟩ | ⟨hstep, helev⟩)
  all_goals
    obtain ⟨a, bs, d, hshape, -, hfit, -, hdnext, hdpin⟩ :=
      pair_cover_pins hwf hx
    obtain ⟨-, hdcolT⟩ := (canSitOn_eq d x.twin).mp hfit
    have hxtc : x.twin.suit.color = x.suit.color := by
      rw [Card.twin_suit, Suit.color_twin]
    rw [hxtc] at hdcolT
    obtain ⟨ρ, hback⟩ := conf_playback hpre
  · -- the door raises x: the twin side stands past the fork index
    exact conf_door_orphan hwf (conf_wf_along hpre hwf) hpre hback hx
      (Or.inr ⟨rfl, rfl⟩) hstep helev ⟨a, bs, hshape, hfit⟩
      hdcolT hdnext hdpin
  · -- the door raises the twin: the witness side stands past
    exact conf_door_orphan hwf (conf_wf_along hpre hwf) hpre hback hx
      (Or.inl ⟨rfl, rfl⟩) hstep helev ⟨a, bs, hshape, hfit⟩
      hdcolT hdnext hdpin

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

/-- **THE SAME-NEXT-UP READ (the strengthened card-naming row)** — a
same-family card of the pinned rank IS a pair member, up to the twin
flip: the suit family and the rank index together name the card
(`conf_card_of_suit_toIdx`).  The fork/journey premise pack of the
original statement retired with the hypothesis cleanup — the row
rides the suit disjunction and the rank pin alone, and the
forkConsumer corollary reads it at the fork context (with
`forkState_sameFamily_rankCeiling` supplying the pin upstream). -/
theorem forkState_sameFamily_samePair {x y : Card}
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
    refine FoundKit.mem_found_of_rung hwfu ?_
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
#print axioms FoundKit.mem_found_iff_height
