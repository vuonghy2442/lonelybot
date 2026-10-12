import Orig.PairConfine

/-!
# Orig.CrossFamily — THE CROSS-FAMILY LOCK (the last axis)

Within one macro class, a fork cannot witness a fork of the OTHER
color family: any same-class `forkState` fork witnesses the SAME
family.  The card's honest ladder:

* §1 **`cross_census_dead`** — THE TWO-CENSUS COLLISION: at the first
  fork both members of any other-family pair are already CanRaiseS
  DEAD (the saturation iff names the only S-live set, and the color
  census — twins share the suit family — bars both members of a
  differently-colored pair from it).
* §2 **`cross_cover_residency`** — THE EQUAL-RANK COVER RESIDENCY: at
  equal ranks the second fork's twin-cover is a rank-`(r−1)` card of
  the FIRST fork's family — foundation-resident at the first fork
  (`pair_lowFamily_founded`), face-up on the tableau at the second
  (`pair_cover_pins`).
* §3 **`cross_cover_rung_drop`** — THE RUNG-DROP ROW: the cover's
  home suit drops at least TWO rungs between the two forks (the
  at-first pin `r`, the cover pin `r − 1`, the `nextUp = false` read).
* §4 **`cross_anchor_climb`** — THE REVERSE CLIMB ROW: the FIRST
  fork's cover (a rank-`(r−1)` card of the SECOND family) sits
  weakly below `r − 1` at the first fork and is foundation-resident —
  hence strictly above `r − 1` — at the second (the
  founded-membership bridge, `xfam_mem_found_rank_lt`).
* §5 **`cross_cover_pull_pressure`** — THE JOURNEY CENSUS READ: the
  cover's home suit owes at least TWO MORE PULLS THAN RAISES along
  the class's forward witness shuffle (the banked `witness_rung_census`
  consumed against §3's drop).
* §6 `cross_family_interlock` — the card's ONE NAMED RESIDUE with
  its complete route; `forkState_familyRigid` — the card's main row,
  consumed from the residue.

House compliance: additive leaf; fresh private kit copies per the
dedup discipline; every fresh head audited.
-/

/-! ## §0. The private kit (per-file copies, the house dedup discipline) -/

/-- The pair-form color flip: a card's family rides the twin suits —
`Card.twin_suit` and `Suit.color_twin` private copies inlined. The
statement form used throughout this file: a same-color relation is
twin-invariant on the right; the twin-flipped membership form: the
color of a pair member's twin keeps the family. -/
private theorem xfam_twin_color (c : Card) :
    c.twin.suit.color = c.suit.color := by
  rw [Card.twin_suit, Suit.color_twin]

/-! ## §1. The two-census collision -/

/-- **THE TWO-CENSUS COLLISION** — at a fork witnessing `{x, x.twin}`,
BOTH members of any other-family pair are already S-DEAD: the fork's
saturation iff names the only S-live cards, and the color census
(twins share the suit family, so both members of `{y, y.twin}` carry
`y`'s color) bars each of them from the named set.  This is the st₁
end of the collision; the st₂ end reads the same after swapping the
two witness parcels. -/
theorem cross_census_dead {st : State} {x y : Card}
    (hx : ForkWitness st x) (hcol : y.suit.color ≠ x.suit.color) :
    ¬ CanRaiseS st y ∧ ¬ CanRaiseS st y.twin := by
  obtain ⟨hiff, -⟩ := hx
  constructor
  · intro hcan
    rcases (hiff y).mpr hcan with hc | hc
    · exact hcol (by rw [hc])
    · exact hcol (by rw [hc]; exact xfam_twin_color x)
  · intro hcan
    rcases (hiff y.twin).mpr hcan with hc | hc
    · have hyx : y = x.twin := Card.twin_inj (hc.trans (Card.twin_twin x).symm)
      exact hcol (by rw [hyx]; exact xfam_twin_color x)
    · exact hcol (by rw [Card.twin_inj hc])

/-- Two colors that both differ from a third agree (the copy of
`Orig/RunOrTwin.lean`'s private `color_pair`). -/
private theorem xfam_color_pair {a u v : Color} (h1 : a ≠ u) (h2 : a ≠ v) : u = v := by
  rcases a <;> rcases u <;> rcases v <;> simp_all

/-! ## §2. The equal-rank cover residency -/

/-- **THE EQUAL-RANK COVER RESIDENCY** — at equal pair ranks the
second fork's twin-cover `d₂` (the direct cover of `y.twin`, from the
`st₂` saturation pins) is a rank-`(r−1)` card of the FIRST fork's
family: its color is `x`'s (the two-color census against the opposite
family), its rank index is exactly one below the common fork index,
and — the residency read — it sits FOUNDATION-RESIDENT at the first
fork (`pair_lowFamily_founded`: every first-family card below the
fork rank is already founded) while covering `y.twin` FACE-UP on the
`st₂` tableau (`pair_cover_pins`).  The cross-family journey must
therefore pull this card out of the foundation. -/
theorem cross_cover_residency {st₁ st₂ : State} (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hrank : y.rank.toIdx = x.rank.toIdx) :
    ∃ (a : Anchor) (bs : List Card) (d₂ : Card),
      (st₂.piles a).faceUp = bs ++ [y.twin, d₂] ∧
      canSitOn d₂ y.twin = true ∧
      st₂.pileOfTop d₂ = some a ∧
      st₂.nextUp d₂ = false ∧
      d₂.suit.color = x.suit.color ∧
      d₂.rank.toIdx + 1 = x.rank.toIdx ∧
      d₂ ∈ st₁.found d₂.suit ∧
      rungAt st₂ d₂.suit + 1 ≤ y.rank.toIdx := by
  obtain ⟨a, bs, d₂, hshape, -, hfit, htop, hnext, hrung⟩ := pair_cover_pins hwf₂ hy
  obtain ⟨hridx, hcne⟩ := (canSitOn_eq d₂ y.twin).mp hfit
  rw [Card.twin_rank] at hridx
  -- the two-color census: d₂'s family is the first fork's family
  have hyt : y.twin.suit.color = y.suit.color := xfam_twin_color y
  rw [hyt] at hcne
  have hdcol : d₂.suit.color = x.suit.color :=
    xfam_color_pair (Ne.symm hcne) hcol
  -- the residency: first-family, strictly below the fork rank
  have hres : d₂ ∈ st₁.found d₂.suit :=
    pair_lowFamily_founded hwf₁ hx hdcol (by omega)
  exact ⟨a, bs, d₂, hshape, hfit, htop, hnext, hdcol, (by omega), hres, hrung⟩

/-- A same-color suit is the suit or its twin (the copy of
`Orig/PairConfine.lean`'s private `conf_suit_family`). -/
private theorem xfam_suit_family {s t : Suit} (h : s.color = t.color) :
    s = t ∨ s = t.twin := by
  cases s <;> cases t <;> simp_all [Suit.color, Suit.twin]

/-- The family rung pin at a fork: every same-family suit's rung
reads the fork rank (the copy of the internal `hr` row inside
`Orig/PairConfine.lean`'s `pair_lowFamily_founded`). -/
private theorem xfam_family_rung {st : State} {x : Card}
    (hx : ForkWitness st x) {s : Suit}
    (hcol : s.color = x.suit.color) :
    rungAt st s = x.rank.toIdx := by
  rcases xfam_suit_family hcol with hs | hs
  · rw [hs]
    exact canRaiseS_rung ((hx.1 x).mp (Or.inl rfl))
  · rw [hs]
    have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
    rwa [Card.twin_rank] at h2

/-! ## §3. The rung-drop row -/

/-- **THE RUNG-DROP ROW** — at equal ranks the cover `d₂`'s home suit
drops at least TWO rungs on the cross-family journey: at the first
fork the family pin reads exactly the fork index `r` (both
same-family suits are pinned by the fork's own witnesses), while at
the second fork the saturation bars read `rungAt st₂ d₂.suit + 1 ≤
r` together with `nextUp d₂ = false` — and `nextUp` reads exactly
`decide (d₂.rank.toIdx = rungAt st₂ d₂.suit)`, so the rung cannot
sit at `d₂`'s own index `r − 1`: it lands at `r − 2` or below.  This
is the net-drop accounting's seed: the finisher's census of pulls can
read at least TWO LIFO pops of this suit (the first of which pops
`d₂` itself, the then-current foundation top). -/
theorem cross_cover_rung_drop {st₁ st₂ : State} (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hrank : y.rank.toIdx = x.rank.toIdx) :
    ∃ (d₂ : Card),
      d₂.suit.color = x.suit.color ∧
      d₂.rank.toIdx + 1 = x.rank.toIdx ∧
      rungAt st₁ d₂.suit = x.rank.toIdx ∧
      rungAt st₂ d₂.suit + 2 ≤ x.rank.toIdx := by
  obtain ⟨-, -, d₂, -, -, -, hnext, hdcol, hridx, -, hrung⟩ :=
    cross_cover_residency hwf₁ hwf₂ hx hy hcol hrank
  have hrung₁ : rungAt st₁ d₂.suit = x.rank.toIdx :=
    xfam_family_rung hx hdcol
  -- the nextUp=false read: the cover's rung is not its own rank index
  have hne : d₂.rank.toIdx ≠ rungAt st₂ d₂.suit := by
    intro hcon
    have hn2 : st₂.nextUp d₂ = true := decide_eq_true hcon
    rw [hn2] at hnext
    exact absurd hnext (by simp)
  exact ⟨d₂, hdcol, hridx, hrung₁, by omega⟩

/-! ## §4. The founded-membership bridge, and the reverse climb -/

/-! The take-position kit (the copies of `Orig/Dominance.lean`'s
private self-rolled helper and the converse of its `mem_take_of_pos`
— the same induction, read the other way). -/

/-- The position of `x` in `l` (its first-occurrence index; the copy
of `Orig/Dominance.lean`'s private helper). -/
private def xfam_posOf {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: t => if y = x then 0 else xfam_posOf x t + 1

/-- Membership in a bounded take bounds the first-occurrence position
(the converse of `Orig/Dominance.lean`'s private `mem_take_of_pos`,
the same induction mirrored). -/
private theorem xfam_mem_take_pos {α : Type} [DecidableEq α] :
    ∀ (n : Nat) (l : List α) (x : α), x ∈ l.take n → xfam_posOf x l < n := by
  intro n
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
          by_cases hyx : y = x
          · have hp : xfam_posOf x (y :: t) = 0 := by
              show (if y = x then 0 else xfam_posOf x t + 1) = 0
              rw [if_pos hyx]
            omega
          · have hp : xfam_posOf x (y :: t) = xfam_posOf x t + 1 := by
              show (if y = x then 0 else xfam_posOf x t + 1) = _
              rw [if_neg hyx]
            have hmem' : x ∈ t.take n := by
              rcases List.mem_cons.1 hmem with he | hrest
              · exact absurd he.symm hyx
              · exact hrest
            have hlt := ih t x hmem'
            omega

/-- The build order is the rank order (the copy of
`Orig/Dominance.lean`'s private `posOf_upCards`). -/
private theorem xfam_posOf_upCards (σ : Suit) (r : Rank) :
    xfam_posOf (Card.mk σ r) (Suit.upCards σ) = r.toIdx := by
  cases σ <;> cases r <;> rfl

/-- **THE FOUNDED-MEMBERSHIP BRIDGE** — a card on its own suit's
foundation sits strictly below the foundation's top: the founded
prefix is the build order's take, so the card's build position (its
rank index) is bounded by the take length (`xfam_mem_take_pos`), and
the build position IS the rank index (`xfam_posOf_upCards`).  This
is the converse-half of the founded bridge that
`Orig/PairConfine.lean` carried as its own private copy of the
membership direction. -/
private theorem xfam_mem_found_rank_lt {st : State} (hwf : st.WF) {d : Card}
    (hmem : d ∈ st.found d.suit) :
    d.rank.toIdx < rungAt st d.suit := by
  rcases d with ⟨s, r⟩
  have hmem' : Card.mk s r ∈ st.found s := hmem
  have hpre := rung_found_prefix st hwf s
  rw [hpre] at hmem'
  have hpos : xfam_posOf (Card.mk s r) (Suit.upCards s) < rungAt st s :=
    xfam_mem_take_pos _ _ _ hmem'
  have hidx := xfam_posOf_upCards s r
  show r.toIdx < rungAt st s
  omega

/-- **THE REVERSE CLIMB ROW** — the first fork's twin-cover `d₁`
(the direct cover of `x.twin`, from the `st₁` saturation pins) is a
rank-`(r−1)` card of the SECOND fork's family, and the residency
reads the OTHER way: `d₁` covers `x.twin` FACE-UP on the `st₁`
tableau while sitting FOUNDATION-RESIDENT at the second fork (the
second fork's `pair_lowFamily_founded`), so its home suit must have
CLIMBED past the common fork index: at `st₁` the cover pin holds the
suit weakly below `r − 1`, while the founded-membership bridge at
`st₂` holds it strictly past `d₁`'s own index `r − 1`, i.e. at `r`
or above.  Together with §2–§3 this is the interlocked lattice's
two-end read: each family's `(r−1)`-cover material is resident at the
OTHER fork's foundation, and no cover suit ends where it started. -/
theorem cross_anchor_climb {st₁ st₂ : State} (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hrank : y.rank.toIdx = x.rank.toIdx) :
    ∃ (a : Anchor) (bs : List Card) (d₁ : Card),
      (st₁.piles a).faceUp = bs ++ [x.twin, d₁] ∧
      canSitOn d₁ x.twin = true ∧
      st₁.pileOfTop d₁ = some a ∧
      st₁.nextUp d₁ = false ∧
      rungAt st₁ d₁.suit + 1 ≤ x.rank.toIdx ∧
      d₁.suit.color = y.suit.color ∧
      d₁.rank.toIdx + 1 = x.rank.toIdx ∧
      d₁ ∈ st₂.found d₁.suit ∧
      x.rank.toIdx ≤ rungAt st₂ d₁.suit := by
  obtain ⟨a, bs, d₁, hshape, -, hfit, htop, hnext, hrung₁⟩ := pair_cover_pins hwf₁ hx
  obtain ⟨hridx, hcne⟩ := (canSitOn_eq d₁ x.twin).mp hfit
  rw [Card.twin_rank] at hridx
  -- the two-color census: the cover's family is the SECOND fork's
  have hxt : x.twin.suit.color = x.suit.color := xfam_twin_color x
  rw [hxt] at hcne
  have hdcol : d₁.suit.color = y.suit.color :=
    xfam_color_pair (Ne.symm hcne) (Ne.symm hcol)
  -- the residency at the second fork: second family, strictly below the ring rank
  have hres : d₁ ∈ st₂.found d₁.suit :=
    pair_lowFamily_founded hwf₂ hy hdcol (by omega)
  -- the climb: founded at st₂ strictly past d₁'s own index
  have hlt := xfam_mem_found_rank_lt hwf₂ hres
  exact ⟨a, bs, d₁, hshape, hfit, htop, hnext, hrung₁, hdcol, hridx, hres, by omega⟩

/-! ## §5. The journey census read -/

/-- **THE PULL-PRESSURE ROW** — the net-drop accounting's seed: along
the class's own forward witness shuffle (`sameOrbit_forward`), the
banked journey census (`witness_rung_census`: `rungAt end + pulls =
rungAt start + raises` per suit) reads §3's two-rung drop as a
PULL DEBT — the cover's home suit owes at least TWO more LIFO pops
than it ever gained, and (consuming the census at the moment of the
first such pop) the earliest pop of this suit departs with the
foundation's then-current top.  The first popped `x`-family card of
rank index `r − 1` is the cover `d₂` itself whenever no raise of the
suit intervenes — the finisher's per-leg ladder pins exactly that
intervention. -/
theorem cross_cover_pull_pressure {st₁ st₂ : State} (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hrank : y.rank.toIdx = x.rank.toIdx) :
    ∃ (d₂ : Card) (τ : List Move),
      d₂.suit.color = x.suit.color ∧
      d₂.rank.toIdx + 1 = x.rank.toIdx ∧
      ShufflePlayW st₁ τ st₂ ∧
      2 + raisesOf τ d₂.suit ≤ pullsOf τ d₂.suit := by
  obtain ⟨d₂, hdcol, hridx, hrung₁, hrung₂⟩ :=
    cross_cover_rung_drop hwf₁ hwf₂ hx hy hcol hrank
  obtain ⟨τ, hτ⟩ := sameOrbit_forward hcls
  have hcen := witness_rung_census hτ d₂.suit
  exact ⟨d₂, τ, hdcol, hridx, hτ, by omega⟩

/-! ## §6. The assembly: the named residue and the main row -/

/-- **THE CROSS-FAMILY INTERLOCK — the card's one named residue.**

PREMISE: two fork states of the same macro class witnessing
DIFFERENT color families (`hcol`), with both witness parcels, both
well-formedness rows, and the class witness.

THE COMPLETE ROUTE (each step priced against landed rows — this
file's §1–§5, plus the banked chain):

1. THE RANK CASE LADDER. `rcases` the trichotomy of `y.rank.toIdx`
   against `x.rank.toIdx`.  The EQUAL case is the worst corner: the
   material competition at `(r − 1)` — and it consumes this file's
   rows LITERALLY:
   * `cross_cover_residency`: the second fork's twin-cover `d₂` (an
     `x`-family rank-`(r−1)` card) is foundation-resident at `st₁`
     yet face-up covering `y.twin` at `st₂` with `nextUp = false`.
   * `cross_cover_rung_drop`: `rungAt st₁ d₂.suit = r` (the family
     pin) against `rungAt st₂ d₂.suit + 2 ≤ r` — a net two-rung
     drop of `d₂`'s suit along the class's own shuffle.
   * `cross_cover_pull_pressure`: the shuffle owes at least
     `raisesOf + 2` LIFO pops of that suit; the first popped card is
     the then-current top — `d₂` itself if no raise of the suit
     intervened (the finisher's first per-leg pin).
   * `cross_anchor_climb`: the MIRROR package for `d₁` — the first
     fork's cover is resident at `st₂`'s foundation, its suit
     weakly below `r − 1` at `st₁`, at `r` or above at `st₂`.
   * `cross_census_dead`: the collision envelope — at each endpoint
     fork, both members of the OTHER family's pair are S-DEAD.
2. THE EQUAL-RANK FINISH (the remaining ladder): the per-leg
   analysis between `st₁` and `st₂` on the shuffle from
   `sameOrbit_forward`.  The engine is the banked one-leg transfer
   (`S_census_one_leg`, `Orig/SFlatTransfer.lean`): an S-DEAD
   `z`-card can only GAIN structured liveness by a cargo leg
   exposing it with its seat intact, by a pull landing a fitting
   cover on it, or by a raise lowering the family rung read —
   and the census at both bars every member of the foreign pair.
   Track `x`'s pair members along the shuffle: at `st₁` both are
   S-live (`x` topping with license, `x.twin` covered by `d₁`); at
   `st₂` both are dead.  The kill analysis (§2 of the card brief):
   (i) a founding raise of a member puts it on a foundation whose
   rung then reads past `r` — barred at `st₂` for `d₂`'s suit by the
   drop row (the founding would have to be pulled back through the
   LIFO debt); (ii) seat destruction rides a cargo leg — its
   landing target is pinned by the `pair_cover_lattice`-grade
   census (every legal card-directed placement of the moved cover
   tops a pair member); (iii) the pull-down direction needs the
   popped cards re-landed on anchors — the deck census pins the
   anchor cards as exactly the foreign pair, forcing the
   material-competition contradiction: both families' `(r−1)`
   covers are each other's foundation-resident material, and the
   LIFO debts of the two suits cannot both be serviced without a
   leg that seats a foreign cover on a live pair member at a
   census-barred moment.  The oscillation accounting per suit
   consumes `witness_rung_census` over `raisesOf`/`pullsOf` exactly
   as in the pressure row, and the pops are LIFO
   (`foundToTab_pops_currentTop`, `Orig/BracketDecomp.lean`).
3. THE UNEQUAL-RANK CASES: for `r₂ < r₁` the whole `y`-rank stratum
   sits strictly below the `x`-family founded prefix at `st₁` (via
   `pair_lowFamily_founded` at `st₁`), and both `y`-pair covers
   are foundation-resident there — the same pull-debt analysis with
   the anchor census shifted one stratum; for `r₂ > r₁` the mirror
   reads against `st₂` with the class symmetry
   (`sameOrbitSetoid`'s own symmetry hands the reversed shuffle).

Until steps 2–3 land as rows, the bar stays honestly open; the
main theorem below carries exactly this residue and no other. -/
theorem cross_family_interlock {st₁ st₂ : State} (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color) :
    False := by
  sorry

/-- **THE CROSS-FAMILY LOCK** — within one class, the fork pair
cannot CHANGE color family: any same-class fork that would witness
the other family trips the interlock above.  (The statement is the
`¬ ≠` form: the family flips never happens; `not_not` recovers the
positive form `y.suit.color = x.suit.color`.) -/
theorem forkState_familyRigid (st₁ st₂ : State) (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (h₁ : forkState st₁) (h₂ : forkState st₂)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y) :
    ¬ (y.suit.color ≠ x.suit.color) := by
  have _f₁ := h₁
  have _f₂ := h₂
  intro hcol
  exact cross_family_interlock hwf₁ hwf₂ hcls hx hy hcol

/-! ## The audit battery

`#print axioms` per fresh head — the four row rows and the pressure
row read `[propext, Quot.sound]`-grade (banked chain only); the
residue and the main row carry exactly the one fresh `sorryAx`
(`cross_family_interlock`'s; `forkState_familyRigid` inherits it
and NOTHING else). -/

#print axioms cross_census_dead
#print axioms cross_cover_residency
#print axioms cross_cover_rung_drop
#print axioms cross_anchor_climb
#print axioms cross_cover_pull_pressure
#print axioms cross_family_interlock
#print axioms forkState_familyRigid
