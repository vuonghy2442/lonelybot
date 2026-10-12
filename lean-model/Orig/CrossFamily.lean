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
* §5b **`cross_drop_general`/`cross_climb_general`** — THE RANK-FREE
  COVER-SHIFT ROWS: the drop and the climb re-run WITHOUT the
  equal-rank premise — the x-family cover suit pinned at the first
  fork yet two below the second fork's rank (founded-resident at
  the first whenever `r₂ ≤ r₁`); the y-family cover suit two below
  the first fork's rank yet pinned exactly at the second's.
* §6 `cross_family_interlock` — the RANK-TRICHOTOMY ASSEMBLY
  (proved), consuming two named sub-residues —
  `cross_equal_rank_kill` (the equal-rank material competition) and
  `cross_unequal_rank_strata` (the unequal-rank stratification, the
  reversed order by the class symmetry); `forkState_familyRigid` —
  the card's main row, consumed from the assembly.

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

/-! ## §5b. The rank-free cover-shift rows

§3's drop and §4's climb both premised EQUAL pair ranks, but the
load-bearing reads inside them — the two-color cover census, the
family rung pins, the `nextUp = false` refinement of the piled-rung
read — never consult the OTHER fork's rank.  Re-running the
machinery without the rank premise lands the honest general rows
the unequal-rank stratification consumes: the x-family cover suit
is pinned at the first fork's `r₁` while reading at least two
below `r₂` at the second fork — a net drop of `(r₁ − r₂) + 2`,
strictly worse the lower the second rank sits — and is
foundation-resident at the first fork whenever `r₂ ≤ r₁`; the
y-family cover suit reads at most `r₁ − 2` at the first fork while
PINNED exactly at `r₂` at the second, and is foundation-resident at
the second fork whenever `r₁ ≤ r₂`.  At equal ranks each row
sharpens its banked §3/§4 counterpart by one rung. -/

/-- **THE RANK-FREE DROP ROW** — the second fork's twin-cover `d₂`
(an x-family card of rank index `r₂ − 1`) has its home suit pinned
at the first fork's family rung `r₁` yet reading at least TWO below
the second fork's rank `r₂` (the `nextUp = false` refinement of the
piled-rung read); whenever `r₂ ≤ r₁` the cover is moreover
foundation-resident at `st₁` (the low-family founded row, one
stratum read). -/
theorem cross_drop_general {st₁ st₂ : State} (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color) :
    ∃ (d₂ : Card),
      d₂.suit.color = x.suit.color ∧
      d₂.rank.toIdx + 1 = y.rank.toIdx ∧
      rungAt st₁ d₂.suit = x.rank.toIdx ∧
      rungAt st₂ d₂.suit + 2 ≤ y.rank.toIdx ∧
      (y.rank.toIdx ≤ x.rank.toIdx → d₂ ∈ st₁.found d₂.suit) := by
  obtain ⟨-, -, d₂, -, -, hfit, -, hnext, hrung⟩ :=
    pair_cover_pins hwf₂ hy
  obtain ⟨hridx, hcne⟩ := (canSitOn_eq d₂ y.twin).mp hfit
  rw [Card.twin_rank] at hridx
  have hyt : y.twin.suit.color = y.suit.color := xfam_twin_color y
  rw [hyt] at hcne
  have hdcol : d₂.suit.color = x.suit.color :=
    xfam_color_pair (Ne.symm hcne) hcol
  have hrung₁ : rungAt st₁ d₂.suit = x.rank.toIdx :=
    xfam_family_rung hx hdcol
  have hne : d₂.rank.toIdx ≠ rungAt st₂ d₂.suit := by
    intro hcon
    have hn2 : st₂.nextUp d₂ = true := decide_eq_true hcon
    rw [hn2] at hnext
    exact absurd hnext (by simp)
  refine ⟨d₂, hdcol, hridx, hrung₁, ?_, ?_⟩
  · have h1 : rungAt st₂ d₂.suit + 1 ≤ y.rank.toIdx := hrung
    omega
  · intro hle
    exact pair_lowFamily_founded hwf₁ hx hdcol (by omega)

/-- **THE RANK-FREE CLIMB ROW** — the first fork's twin-cover `d₁`
(a y-family card of rank index `r₁ − 1`) tops the `st₁` tableau with
`nextUp d₁ = false`, so its suit reads at least two below the first
fork's rank `r₁` there — while PINNED at the second fork's witness
rank `r₂` (both witnesses' `canRaiseS_rung` reads through the family
pin); whenever `r₁ ≤ r₂` the cover is foundation-resident at `st₂`.
The climb row §4 restated without its rank premise, sharpened: the
`st₂` end is an EQUALITY. -/
theorem cross_climb_general {st₁ st₂ : State} (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color) :
    ∃ (d₁ : Card) (a : Anchor),
      d₁.suit.color = y.suit.color ∧
      d₁.rank.toIdx + 1 = x.rank.toIdx ∧
      st₁.pileOfTop d₁ = some a ∧
      st₁.nextUp d₁ = false ∧
      rungAt st₁ d₁.suit + 2 ≤ x.rank.toIdx ∧
      rungAt st₂ d₁.suit = y.rank.toIdx ∧
      (x.rank.toIdx ≤ y.rank.toIdx → d₁ ∈ st₂.found d₁.suit) := by
  obtain ⟨a, -, d₁, -, -, hfit, htop, hnext, hrung₁⟩ :=
    pair_cover_pins hwf₁ hx
  obtain ⟨hridx, hcne⟩ := (canSitOn_eq d₁ x.twin).mp hfit
  rw [Card.twin_rank] at hridx
  have hxt : x.twin.suit.color = x.suit.color := xfam_twin_color x
  rw [hxt] at hcne
  have hdcol : d₁.suit.color = y.suit.color :=
    xfam_color_pair (Ne.symm hcne) (Ne.symm hcol)
  have hne : d₁.rank.toIdx ≠ rungAt st₁ d₁.suit := by
    intro hcon
    have hn2 : st₁.nextUp d₁ = true := decide_eq_true hcon
    rw [hn2] at hnext
    exact absurd hnext (by simp)
  have hrung₂ : rungAt st₂ d₁.suit = y.rank.toIdx :=
    xfam_family_rung hy hdcol
  refine ⟨d₁, a, hdcol, hridx, htop, hnext, ?_, hrung₂, ?_⟩
  · have h1 : rungAt st₁ d₁.suit + 1 ≤ x.rank.toIdx := hrung₁
    omega
  · intro hle
    exact pair_lowFamily_founded hwf₂ hy hdcol (by omega)

/-! ## §6. The assembly: the two named sub-residues and the main row -/

/-- The class relation's symmetry: `sameOrbitSetoid.r u v` is
definitionally `RevEqW v u` (the witness shuffles run both ways),
so the two journeys swap (`RevEqW_symm`) — the reversed-order
hand-off the assembly's third branch consumes. -/
private theorem cross_class_symm {u v : State}
    (h : sameOrbitSetoid.r u v) : sameOrbitSetoid.r v u :=
  RevEqW_symm h

/-- **THE EQUAL-RANK MATERIAL COMPETITION — the first named
sub-residue.**  Premise: two same-class forks of DIFFERENT color
families at EQUAL pair ranks (`hrank`).  Route (each step priced
against landed rows — this file's §1–§5 and §5b, plus the bank):

1. THE RESIDENCIES (banked, equal-rank grade): `cross_cover_residency`
   — the second fork's twin-cover `d₂` is an x-family rank-`(r−1)`
   card, foundation-resident at `st₁`, face-up covering `y.twin` at
   `st₂` with `nextUp = false`; `cross_anchor_climb` — the mirror
   package for `d₁` (a y-family rank-`(r−1)` card, tableau at `st₁`,
   resident at `st₂`, its suit pinned EXACTLY at `r` at `st₂` by
   §5b's sharpened climb read).
2. THE TWO OPPOSITE SHIFTS (banked): `cross_cover_rung_drop` — the
   x-family cover suit drops `r → r−2-or-below`, and
   `cross_cover_pull_pressure` reads its census as a LIFO pull debt
   (`2 + raisesOf ≤ pullsOf`, the pops current-top by
   `foundToTab_pops_currentTop`); the same journey census
   (`witness_rung_census`) on `d₁`'s y-family suit reads the mirror
   debt (`pullsOf + 2 ≤ raisesOf`) — the two cover suits shift in
   OPPOSITE directions along the one class shuffle.
3. THE MATERIAL COMPETITION at the `(r−1)` stratum (the residue's
   core, still to price): each popped x-family cover card needs a
   legal card-directed landing (a tableau top one rank up, opposite
   color; empty-anchor landings are king-only), and the rankColor
   census (one rank + one color = exactly the twin pair) names the
   only fitting hosts — at the debt-servicing epochs, the live
   y-pair members themselves.  The banked one-leg transfer
   (`S_census_one_leg`, `Orig/SFlatTransfer.lean`) pins the epochs
   at which a foreign member can first GAIN structured S-liveness
   (a cargo leg exposing it with its seat intact, a pull landing a
   fitting cover on it, or a raise lowering the family rung read);
   the flat/bracket factor rows (`quiet_flat`, `pull_factor`,
   `raise_factor` over the draw-free board component of
   `sameOrbit_factor_full`) price each intervening segment; the
   landing lattice (`pair_cover_lattice`-grade census) pins each
   cargo cover's legal card-directed landings to pair-member tops;
   and the two-census collision (`cross_census_dead`) bars both
   ends' exits.  Servicing both opposite debts forces a leg that
   seats a foreign cover on a live pair member at a census-barred
   moment — the material competition, the only possible mechanism;
   its per-leg LIFO chase (the oscillation accounting per suit over
   `raisesOf`/`pullsOf`, exactly as in the pressure row) is the
   pricing still to land.

Until that ladder lands, the equal-rank corner stays honestly
open; the assembly consumes exactly this residue. -/
private theorem cross_equal_rank_kill {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hrank : y.rank.toIdx = x.rank.toIdx) :
    False := by
  sorry

/-- **THE UNEQUAL-RANK STRATIFICATION — the second named
sub-residue.**  Premise: the same-class cross-family forks with the
second fork's pair rank STRICTLY below the first's (`hle`, `hne`).
Route (the §5b rank-free rows carry the load-bearing reads):

1. THE STRATIFIED SHIFTS (banked, §5b): the x-family cover suit
   drops from the `st₁` family pin `r₁` to at most `r₂ − 2` at
   `st₂` — a net drop of `(r₁ − r₂) + 2 ≥ 3`, strictly worse than
   the equal-rank corner — and its cover `d₂` is
   foundation-resident at `st₁` (rank `r₂ − 1 < r₁`,
   `pair_lowFamily_founded`); the y-family cover suit reads at
   most `r₁ − 2` at `st₁` while PINNED exactly at `r₂` at `st₂` —
   and its cover `d₁` is resident at `st₂` only in the OTHER rank
   order, which the hypothesis bars.  The two covers occupy
   different foundation strata, one at each end: the LIFO pops
   servicing the deep x-suit debt surface x-family cards of rank
   index below `r₂`, a full stratum beneath the y-pair's fork
   material — the stratification: the covers do not compete.
2. THE SHIFTED KILL-LADDER (still to price, one stratum down from
   the equal corner): each popped x-family card's only fitting
   hosts are y-family tops one rank up; the second fork's own
   `pair_cover_pins` saturation holds that stratum covered or
   founded at `st₂`, the residency census holds the non-pair
   members sunk, and the two-census collision
   (`cross_census_dead`) bars the survivors; the one-leg transfer
   (`S_census_one_leg`) and the flat/bracket factor rows
   (`quiet_flat`, `pull_factor`, `raise_factor` over the board
   component) price the epochs, the per-suit journey census
   (`witness_rung_census` over `raisesOf`/`pullsOf`) closes the
   oscillation exactly as in the equal corner.
3. THE MIRRORED ORDER (`r₂ > r₁`) never enters this residue: the
   assembly hands that branch here with the forks SWAPPED (the
   class symmetry `cross_class_symm`), so the residue itself only
   ever carries the y-below-x order.

Until that shifted ladder lands, the unequal strata stay honestly
open; the assembly consumes exactly this residue. -/
private theorem cross_unequal_rank_strata {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hle : y.rank.toIdx ≤ x.rank.toIdx)
    (hne : y.rank.toIdx ≠ x.rank.toIdx) :
    False := by
  sorry

/-- **THE CROSS-FAMILY INTERLOCK — the trichotomy assembly (proved).**

PREMISE: two fork states of the same macro class witnessing
DIFFERENT color families (`hcol`), with both witness parcels, both
well-formedness rows, and the class witness.

THE COMPLETE ROUTE, as landed:

1. THE RANK TRICHOTOMY (proved, below): `Nat.lt_trichotomy` on
   `y.rank.toIdx` against `x.rank.toIdx` splits the interlock into
   the EQUAL-RANK corner and the two UNEQUAL-RANK orders — and the
   class symmetry (`cross_class_symm`: the two `RevEqW` witness
   shuffles swap) hands the `r₂ > r₁` order back with the forks
   swapped, so the assembly only ever argues the order it names.
2. THE EQUAL-RANK corner closes through the named residue
   `cross_equal_rank_kill` (route in its docstring): the two cover
   suits' OPPOSITE rung shifts, the LIFO pull debt
   (`cross_cover_pull_pressure`), and the `(r−1)`-stratum material
   competition as the only mechanism.
3. THE UNEQUAL-RANK strata close through the named residue
   `cross_unequal_rank_strata` (route in its docstring), built on
   the rank-free §5b shift rows: the deepened drop, the stratified
   residencies, and the one-stratum-down per-leg chase.

The interlock therefore rests on exactly the two named
sub-residues and no other leaf; the main theorem below inherits
precisely that residue from here. -/
theorem cross_family_interlock {st₁ st₂ : State} (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color) :
    False := by
  rcases Nat.lt_trichotomy (y.rank.toIdx) (x.rank.toIdx) with hlt | h | hgt
  · exact cross_unequal_rank_strata hwf₁ hwf₂ hcls hx hy hcol
      (Nat.le_of_lt hlt) (Nat.ne_of_lt hlt)
  · exact cross_equal_rank_kill hwf₁ hwf₂ hcls hx hy hcol h
  · exact cross_unequal_rank_strata hwf₂ hwf₁ (cross_class_symm hcls) hy hx
      (Ne.symm hcol) (Nat.le_of_lt hgt) (Nat.ne_of_lt hgt)

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

`#print axioms` per fresh head — the four row rows, the pressure
row, and the two §5b rank-free shift rows read
`[propext, Quot.sound]`-grade (banked chain only); the assembly and
the main row carry exactly the two fresh `sorryAx`es of the named
sub-residues (`cross_equal_rank_kill`, `cross_unequal_rank_strata`;
`forkState_familyRigid` inherits exactly those and NOTHING else). -/

#print axioms cross_census_dead
#print axioms cross_cover_residency
#print axioms cross_cover_rung_drop
#print axioms cross_anchor_climb
#print axioms cross_cover_pull_pressure
#print axioms cross_drop_general
#print axioms cross_climb_general
#print axioms cross_equal_rank_kill
#print axioms cross_unequal_rank_strata
#print axioms cross_family_interlock
#print axioms forkState_familyRigid
