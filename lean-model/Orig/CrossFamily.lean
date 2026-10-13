import Orig.PairConfine
import Orig.CrossFamilyStatic

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
  founded-membership bridge, `FoundKit.mem_found_rank_lt`).
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
  `cross_unequal_rank_strata` (the unequal-rank stratification, now
  assembly-grade: its per-leg chase is split one level into the named
  nothing `cross_strata_chase`, the reversed order barred by the
  class symmetry `cross_class_symm`); `forkState_familyRigid` —
  the card's main row, consumed from the assembly.  THE CLOSURE
  (2026-10-12): the three former corner residues
  (`cross_equal_rank_kick`, `cross_strata_consec`, `cross_strata_gap`)
  are each closed by one call of `Orig/CrossFamilyStatic.lean`'s
  STATIC ORPHAN-SEAT kill `cross_orphan_kill` — the axis's one
  remaining leaf residue is that file's named `cross_orphan_seat`.

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
    SeedKit.color_pair (Ne.symm hcne) hcol
  -- the residency: first-family, strictly below the fork rank
  have hres : d₂ ∈ st₁.found d₂.suit :=
    pair_lowFamily_founded hwf₁ hx hdcol (by omega)
  exact ⟨a, bs, d₂, hshape, hfit, htop, hnext, hdcol, (by omega), hres, hrung⟩

/-- The family rung pin at a fork: every same-family suit's rung
reads the fork rank (the copy of the internal `hr` row inside
`Orig/PairConfine.lean`'s `pair_lowFamily_founded`). -/
private theorem xfam_family_rung {st : State} {x : Card}
    (hx : ForkWitness st x) {s : Suit}
    (hcol : s.color = x.suit.color) :
    rungAt st s = x.rank.toIdx := by
  rcases SeedKit.suit_family hcol with hs | hs
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

/-! ## §4. The reverse climb (the founding bridge via `FoundKit`) -/

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
    SeedKit.color_pair (Ne.symm hcne) (Ne.symm hcol)
  -- the residency at the second fork: second family, strictly below the ring rank
  have hres : d₁ ∈ st₂.found d₁.suit :=
    pair_lowFamily_founded hwf₂ hy hdcol (by omega)
  -- the climb: founded at st₂ strictly past d₁'s own index
  have hlt := FoundKit.mem_found_rank_lt hwf₂ hres
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
    SeedKit.color_pair (Ne.symm hcne) hcol
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
    SeedKit.color_pair (Ne.symm hcne) (Ne.symm hcol)
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

/-- **THE LEG EXTRACTORS — step zero of the per-leg chase.**  A
nonzero suit ledger names a literal leg OF THAT SUIT inside the
play: a counted `tabToFound` raise (resp. `foundToTab` pull) of the
suit occurs as a member of the play itself.  Self-contained rows
over the counters' equations — the census debts' first concrete
leg, the anchor every future LIFO read pins its epoch to. -/
private theorem cross_raise_leg : ∀ (τ : List Move) (σ : Suit),
    0 < raisesOf τ σ → ∃ c : Card, Move.tabToFound c ∈ τ ∧ c.suit = σ := by
  intro τ
  induction τ with
  | nil => intro σ h; simp [raisesOf] at h
  | cons m t ih =>
      intro σ h
      cases m with
      | tabToFound c =>
          by_cases hcs : c.suit = σ
          · exact ⟨c, List.mem_cons.2 (Or.inl rfl), hcs⟩
          · have h' : 0 < raisesOf t σ := by
              rw [show raisesOf (Move.tabToFound c :: t) σ
                  = (if c.suit = σ then 1 else 0) + raisesOf t σ from rfl,
                ite_eq_right hcs] at h
              omega
            obtain ⟨c', hmem, hsuit⟩ := ih σ h'
            exact ⟨c', List.mem_cons.2 (Or.inr hmem), hsuit⟩
      | draw =>
          have h' : 0 < raisesOf t σ := by
            rw [show raisesOf (Move.draw :: t) σ = raisesOf t σ from rfl] at h
            exact h
          obtain ⟨c', hmem, hsuit⟩ := ih σ h'
          exact ⟨c', List.mem_cons.2 (Or.inr hmem), hsuit⟩
      | wasteToFound c =>
          have h' : 0 < raisesOf t σ := by
            rw [show raisesOf (Move.wasteToFound c :: t) σ = raisesOf t σ
              from rfl] at h
            exact h
          obtain ⟨c', hmem, hsuit⟩ := ih σ h'
          exact ⟨c', List.mem_cons.2 (Or.inr hmem), hsuit⟩
      | wasteToTab c b =>
          have h' : 0 < raisesOf t σ := by
            rw [show raisesOf (Move.wasteToTab c b :: t) σ = raisesOf t σ
              from rfl] at h
            exact h
          obtain ⟨c', hmem, hsuit⟩ := ih σ h'
          exact ⟨c', List.mem_cons.2 (Or.inr hmem), hsuit⟩
      | foundToTab c b =>
          have h' : 0 < raisesOf t σ := by
            rw [show raisesOf (Move.foundToTab c b :: t) σ = raisesOf t σ
              from rfl] at h
            exact h
          obtain ⟨c', hmem, hsuit⟩ := ih σ h'
          exact ⟨c', List.mem_cons.2 (Or.inr hmem), hsuit⟩
      | tabToTab c b =>
          have h' : 0 < raisesOf t σ := by
            rw [show raisesOf (Move.tabToTab c b :: t) σ = raisesOf t σ
              from rfl] at h
            exact h
          obtain ⟨c', hmem, hsuit⟩ := ih σ h'
          exact ⟨c', List.mem_cons.2 (Or.inr hmem), hsuit⟩

private theorem cross_pull_leg : ∀ (τ : List Move) (σ : Suit),
    0 < pullsOf τ σ → ∃ c b, Move.foundToTab c b ∈ τ ∧ c.suit = σ := by
  intro τ
  induction τ with
  | nil => intro σ h; simp [pullsOf] at h
  | cons m t ih =>
      intro σ h
      cases m with
      | foundToTab c b =>
          by_cases hcs : c.suit = σ
          · exact ⟨c, b, List.mem_cons.2 (Or.inl rfl), hcs⟩
          · have h' : 0 < pullsOf t σ := by
              rw [show pullsOf (Move.foundToTab c b :: t) σ
                  = (if c.suit = σ then 1 else 0) + pullsOf t σ from rfl,
                ite_eq_right hcs] at h
              omega
            obtain ⟨c', b', hmem, hsuit⟩ := ih σ h'
            exact ⟨c', b', List.mem_cons.2 (Or.inr hmem), hsuit⟩
      | draw =>
          have h' : 0 < pullsOf t σ := by
            rw [show pullsOf (Move.draw :: t) σ = pullsOf t σ from rfl] at h
            exact h
          obtain ⟨c', b', hmem, hsuit⟩ := ih σ h'
          exact ⟨c', b', List.mem_cons.2 (Or.inr hmem), hsuit⟩
      | wasteToFound c =>
          have h' : 0 < pullsOf t σ := by
            rw [show pullsOf (Move.wasteToFound c :: t) σ = pullsOf t σ
              from rfl] at h
            exact h
          obtain ⟨c', b', hmem, hsuit⟩ := ih σ h'
          exact ⟨c', b', List.mem_cons.2 (Or.inr hmem), hsuit⟩
      | wasteToTab c b =>
          have h' : 0 < pullsOf t σ := by
            rw [show pullsOf (Move.wasteToTab c b :: t) σ = pullsOf t σ
              from rfl] at h
            exact h
          obtain ⟨c', b', hmem, hsuit⟩ := ih σ h'
          exact ⟨c', b', List.mem_cons.2 (Or.inr hmem), hsuit⟩
      | tabToFound c =>
          have h' : 0 < pullsOf t σ := by
            rw [show pullsOf (Move.tabToFound c :: t) σ = pullsOf t σ
              from rfl] at h
            exact h
          obtain ⟨c', b', hmem, hsuit⟩ := ih σ h'
          exact ⟨c', b', List.mem_cons.2 (Or.inr hmem), hsuit⟩
      | tabToTab c b =>
          have h' : 0 < pullsOf t σ := by
            rw [show pullsOf (Move.tabToTab c b :: t) σ = pullsOf t σ
              from rfl] at h
            exact h
          obtain ⟨c', b', hmem, hsuit⟩ := ih σ h'
          exact ⟨c', b', List.mem_cons.2 (Or.inr hmem), hsuit⟩

/-- **THE COVER'S EXILE** — a twin-cover `d₂`, foundation-resident
at the first fork, is GONE from its home suit's foundation at the
second fork: its rank index sits a full two above the suit's end read,
and the founded-membership bridge bars any at-or-above member.  The
chase's and the kill's splits both consume this row. -/
private theorem cross_strata_exile {st₂ : State} (hwf₂ : st₂.WF) {y d₂ : Card}
    (hdrank : d₂.rank.toIdx + 1 = y.rank.toIdx)
    (hrung₂ : rungAt st₂ d₂.suit + 2 ≤ y.rank.toIdx) :
    ¬ d₂ ∈ st₂.found d₂.suit := by
  intro hmem
  have hlt := FoundKit.mem_found_rank_lt hwf₂ hmem
  omega

set_option linter.unusedVariables false in
/-! ### The exodus wheel

The shifted ladder's tail-induction engine (the per-file copy of the
sibling roTail architecture, scoped to the residency mint): a card
that rides its suit's foundation at the journey's start yet misses
it at the end must have passed through its OWN pull leg —
`foundToTab` is the only exit from a foundation.  The residency
carry washes through each leg's found-semantics: pulls chop the
suit row (the LIFO law `foundToTab_pops_currentTop` + `lastOf_chop`
pinned to the popped card), raises and waste-founds only extend it
(`setFound_found_self`/`_ne` through the step inversions), draws
(`stepDraw_found`) and slides (`setPile_found`/`putRun_found`/
`putCard_found`) hold it fixed; the nil leg closes by the two
memberships facing each other.  Each corner's step-0 anchor. -/

/-- **THE LIFO EXODUS LAW** — a card foundation-resident at the
journey's start yet absent at the end has passed a literal
`foundToTab` leg of its own along the witness shuffle: the residency
mint survives every raise, waste-founding, draw and slide, and only
the card's own pop spends it. -/
private theorem cross_found_exodus : ∀ {u : State} {τ : List Move} {w : State},
    ShufflePlayW u τ w → ∀ (d : Card),
    d ∈ u.found d.suit → d ∉ w.found d.suit →
    ∃ b, Move.foundToTab d b ∈ τ := by
  intro u τ w h
  induction h with
  | nil => intro d hmem hno; exact absurd hmem hno
  | @cons s m s₁ rest w' hrev hstep hrest ih =>
      intro d hmem hno
      cases m with
      | draw =>
          have hsurv : d ∈ s₁.found d.suit := by
            rw [stepDraw_found (show s.stepDraw = some s₁ from hstep)]
            exact hmem
          obtain ⟨b', hl⟩ := ih d hsurv hno
          exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩
      | wasteToFound c =>
          obtain ⟨-, x, xs, -, hs⟩ := step_wasteToFound_inv hstep
          have hsurv : d ∈ s₁.found d.suit := by
            rw [hs]
            show d ∈ (s.setFound c.suit (s.found c.suit ++ [c])).found d.suit
            by_cases hsc : d.suit = c.suit
            · rw [hsc, setFound_found_self]
              rw [hsc] at hmem
              exact List.mem_append.2 (Or.inl hmem)
            · rw [setFound_found_ne hsc]
              exact hmem
          obtain ⟨b', hl⟩ := ih d hsurv hno
          exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩
      | wasteToTab c b =>
          obtain ⟨-, x, xs, -, hs⟩ := step_wasteToTab_inv hstep
          have hsurv : d ∈ s₁.found d.suit := by
            rw [hs]
            show d ∈ (s.putCard c b).found d.suit
            rw [putCard_found]
            exact hmem
          obtain ⟨b', hl⟩ := ih d hsurv hno
          exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩
      | tabToFound c =>
          obtain ⟨-, a, -, hs⟩ := step_tabToFound_inv hstep
          have hsurv : d ∈ s₁.found d.suit := by
            rw [hs]
            show d ∈ (s.setFound c.suit (s.found c.suit ++ [c])).found d.suit
            by_cases hsc : d.suit = c.suit
            · rw [hsc, setFound_found_self]
              rw [hsc] at hmem
              exact List.mem_append.2 (Or.inl hmem)
            · rw [setFound_found_ne hsc]
              exact hmem
          obtain ⟨b', hl⟩ := ih d hsurv hno
          exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩
      | foundToTab c b =>
          by_cases hdc : d = c
          · exact ⟨b, List.mem_cons.2 (Or.inl (by rw [hdc]))⟩
          · obtain ⟨-, -, -, -, hs⟩ := step_foundToTab_inv hstep
            have hsurv : d ∈ s₁.found d.suit := by
              by_cases hsc : d.suit = c.suit
              · have hchop : s.found c.suit = chop (s.found c.suit) ++ [c] :=
                  lastOf_chop (foundToTab_pops_currentTop hstep)
                rw [hsc] at hmem
                rw [hchop] at hmem
                rw [hs, putCard_found, hsc, setFound_found_self]
                rcases List.mem_append.1 hmem with h | h
                · exact h
                · rcases List.mem_cons.1 h with he | hn
                  · exact absurd he hdc
                  · exact absurd hn (by simp)
              · rw [hs, putCard_found, setFound_found_ne hsc]
                exact hmem
            obtain ⟨b', hl⟩ := ih d hsurv hno
            exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩
      | tabToTab c b =>
          obtain ⟨a, -, -, -, hs⟩ := step_tabToTab_inv hstep
          have hsurv : d ∈ s₁.found d.suit := by
            rw [hs, putRun_found, setPile_found]
            exact hmem
          obtain ⟨b', hl⟩ := ih d hsurv hno
          exact ⟨b', List.mem_cons.2 (Or.inr hl)⟩

set_option linter.unusedVariables false in
/-- **THE EQUAL-RANK CORNER of the shifted kill-ladder — the
equal-rank residue (`cross_equal_rank_kill`'s split child).**  The
kill's PROVED preprocessing is carried as hypotheses: the equal-rank
premise `hrank` (`r₂ = r₁`); the second fork's twin-cover `d₂` —
x-family (`hd₂col`), one below the common fork rank (`hd₂rank`),
foundation-resident at the first fork (`hd₂res`) yet EXILED from its
home foundation at the second (`hd₂out`), face-up covering `y.twin`
on the `st₂` tableau as a legal card-directed landing (`hd₂top`,
`hd₂fit`); the first fork's own cover `d₁` — y-family (`hd₁col`),
one below the common rank (`hd₁rank`), riding a tableau top at
`st₁` (`hd₁top`), FOUNDATION-RESIDENT at the second fork (`hd₁res`),
its home suit pinned EXACTLY at `r` at `st₂` (`hd₁rung₂`) and at
least two below `r` at `st₁` (`hd₁rung₁`); and the two OPPOSITE
census debts along the one class shuffle — `hdebt₂` (the x-family
suit owes at least two net LIFO pops) vs `hdebt₁` (the y-family suit
owes at least two net raises, the census equation `hd₁cen` closing
the per-suit oscillation together with `witness_rung_census` on
`d₂.suit`).  ROUTE (complete, the residue's own):
1. THE SURFACING — the `hdebt₂` pops are current-top LIFO
   (`foundToTab_pops_currentTop`), surfacing x-family cards of rank
   index `r − 1` down (`d₂` itself must pass through a pop, `hd₂res`
   vs `hd₂out`), none reaching the king, so each lands on a fitting
   top one rank up, opposite color (`canSitOn`), or nowhere
   (empty-anchor landings are king-only).
2. THE HOST CENSUS — the rank/color census (`SeedKit.rankColor_pair`)
   names the only fitting hosts for the top of the surfaced stratum:
   the live y-pair members themselves; the founded-at-`st₂` `d₁`
   (`hd₁res`, the `cross_anchor_climb` residency) is one, and the
   two-census collision (`cross_census_dead`) bars either member
   from ever gaining S-liveness at the wrong end.
3. THE MATERIAL COMPETITION (the core, still to price): the banked
   one-leg transfer (`S_census_one_leg`, `Orig/SFlatTransfer.lean`)
   pins the epochs at which a foreign member can first GAIN
   structured S-liveness (a cargo leg exposing it with its seat
   intact, a pull landing a fitting cover on it, or a raise lowering
   the family rung read); the flat/bracket factor rows (`quiet_flat`,
   `pull_factor`, `raise_factor` over the draw-free board component
   of `sameOrbit_factor_full`) price each intervening segment; the
   landing lattice (`pair_cover_lattice`-grade census) pins each
   cargo cover's legal card-directed landings to pair-member tops;
    servicing both OPPOSITE debts forces a leg that seats a cover on
    a pair member at a census-barred moment — the per-leg LIFO chase
    (`raisesOf`/`pullsOf`, exactly as in the pressure row) has no
    legal leg, `False`.

CLOSED (2026-10-12) via `Orig.CrossFamilyStatic.lean`'s
`cross_orphan_kill` — the STATIC ORPHAN-SEAT route: none of the
census-debt machinery above is consulted; the whole package reduces
to the kill's four pins (families separated, `r₂ ≤ r₁`, the cover
suit's color, the deep `hd₂rung₂` read).  The single residue the
closure rides is that file's named `cross_orphan_seat` (the
below-riding seat row), whose `sorryAx` flows here alone.  The
remaining hypothesis package documents the banked static facts the
assembly hands the corner; the static route consumes only the four
pins, so the linter is silenced for the named binders below. -/
private theorem cross_equal_rank_kick {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {x y d₁ d₂ : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hrank : y.rank.toIdx = x.rank.toIdx)
    {τ : List Move} (hτ : ShufflePlayW st₁ τ st₂)
    (hd₂col : d₂.suit.color = x.suit.color)
    (hd₂rank : d₂.rank.toIdx + 1 = x.rank.toIdx)
    (hd₂res : d₂ ∈ st₁.found d₂.suit)
    (hd₂rung₁ : rungAt st₁ d₂.suit = x.rank.toIdx)
    (hd₂rung₂ : rungAt st₂ d₂.suit + 2 ≤ y.rank.toIdx)
    (hd₂top : ∃ a bs, (st₂.piles a).faceUp = bs ++ [y.twin, d₂] ∧
      st₂.pileOfTop d₂ = some a ∧ st₂.nextUp d₂ = false)
    (hd₂fit : canSitOn d₂ y.twin = true)
    (hd₂out : ¬ d₂ ∈ st₂.found d₂.suit)
    (hd₁col : d₁.suit.color = y.suit.color)
    (hd₁rank : d₁.rank.toIdx + 1 = x.rank.toIdx)
    (hd₁res : d₁ ∈ st₂.found d₁.suit)
    (hd₁top : ∃ a, st₁.pileOfTop d₁ = some a ∧ st₁.nextUp d₁ = false)
    (hd₁rung₁ : rungAt st₁ d₁.suit + 2 ≤ x.rank.toIdx)
    (hd₁rung₂ : rungAt st₂ d₁.suit = y.rank.toIdx)
    (hdebt₂ : x.rank.toIdx + 2 + raisesOf τ d₂.suit
      ≤ y.rank.toIdx + pullsOf τ d₂.suit)
    (hdebt₁ : pullsOf τ d₁.suit + 2 ≤ raisesOf τ d₁.suit)
    (hd₁cen : y.rank.toIdx + pullsOf τ d₁.suit
      = rungAt st₁ d₁.suit + raisesOf τ d₁.suit) :
    False := by
  exact cross_orphan_kill hwf₁ hwf₂ hτ hx hy hcol (by omega) d₂.suit
    hd₂col hd₂rung₂

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

LANDED as the SPLIT: the body is PROVED — the banked rows
(`cross_cover_residency`, `cross_climb_general`, `xfam_family_rung`,
the fit/exile preprocessing rows, `witness_rung_census` read into
the two opposite census debts) assemble the full package and hand
it to the corner `cross_equal_rank_kick` directly above — and the
    kick is now itself closed by the STATIC ORPHAN-SEAT kill
    (`Orig/CrossFamilyStatic.lean`'s `cross_orphan_kill`, reached through
    the landed orphan-seat row `cross_orphan_seat`, proved
    `[propext, Quot.sound]`), which needs none
of the census debt. -/
private theorem cross_equal_rank_kill {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hrank : y.rank.toIdx = x.rank.toIdx) :
    False := by
  -- THE FORWARD WITNESS SHUFFLE (the class's own play)
  obtain ⟨τ, hτ⟩ := sameOrbit_forward hcls
  -- THE SECOND FORK'S TWIN-COVER (the residency package, banked):
  -- x-family, one below the common rank, resident at st₁, covering
  -- y.twin face-up on the st₂ tableau, its suit pinned r at st₁ yet
  -- reading two below r at st₂ (the nextUp-dead refinement)
  obtain ⟨a₂, bs₂, d₂, hshape₂, hfit₂, htop₂, hnext₂, hd₂col, hd₂rank,
      hd₂res, hd₂rung₂le⟩ :=
    cross_cover_residency hwf₁ hwf₂ hx hy hcol hrank
  have hd₂rung₁ : rungAt st₁ d₂.suit = x.rank.toIdx :=
    xfam_family_rung hx hd₂col
  have hd₂rung₂ : rungAt st₂ d₂.suit + 2 ≤ y.rank.toIdx := by
    have hne : d₂.rank.toIdx ≠ rungAt st₂ d₂.suit := by
      intro hcon
      have hn2 : st₂.nextUp d₂ = true := decide_eq_true hcon
      rw [hn2] at hnext₂
      exact absurd hnext₂ (by simp)
    have h1 : rungAt st₂ d₂.suit + 1 ≤ y.rank.toIdx := hd₂rung₂le
    omega
  -- the exile: d₂ left its home foundation by the second fork
  have hd₂out : ¬ d₂ ∈ st₂.found d₂.suit :=
    cross_strata_exile hwf₂ (by omega) hd₂rung₂
  -- THE FIRST FORK'S OWN COVER (the rank-free climb row, the
  -- equal-rank residency engaged): y-family, one below, topping at
  -- st₁ with nextUp dead, resident at st₂, pinned exactly r at st₂
  obtain ⟨d₁, a₁, hd₁col, hd₁rank, htop₁, hnext₁, hd₁rung₁, hd₁rung₂,
      hd₁res⟩ :=
    cross_climb_general hwf₁ hwf₂ hx hy hcol
  have hd₁res : d₁ ∈ st₂.found d₁.suit := hd₁res (by omega)
  -- THE TWO OPPOSITE CENSUS DEBTS along the one class shuffle
  have hcen₂ := witness_rung_census hτ d₂.suit
  have hdebt₂ : x.rank.toIdx + 2 + raisesOf τ d₂.suit
      ≤ y.rank.toIdx + pullsOf τ d₂.suit := by omega
  have hd₁cen : y.rank.toIdx + pullsOf τ d₁.suit
      = rungAt st₁ d₁.suit + raisesOf τ d₁.suit := by
    have hc := witness_rung_census hτ d₁.suit
    omega
  have hdebt₁ : pullsOf τ d₁.suit + 2 ≤ raisesOf τ d₁.suit := by omega
  exact cross_equal_rank_kick hwf₁ hwf₂ hx hy hcol hrank hτ hd₂col
    hd₂rank hd₂res hd₂rung₁ hd₂rung₂
    ⟨a₂, bs₂, hshape₂, htop₂, hnext₂⟩ hfit₂ hd₂out hd₁col hd₁rank
    hd₁res ⟨a₁, htop₁, hnext₁⟩ hd₁rung₁ hd₁rung₂ hdebt₂ hdebt₁ hd₁cen

/-! ### The stratified chase's proved preprocessing

The rows the chase's split consumes: the deck-census copy (the house
per-file dedup of the `rankColor_pair` family), the twin-cover FIT
(the chase's `d₂`-over-`y.twin` seat re-priced as a legal
card-directed landing off the chase's own rank/color premises), the
cover EXILE (the resident-at-`st₁` cover is gone from its home
foundation at `st₂`, off the deep end read through the
founded-membership bridge), and the MIRROR CENSUS read of `d₁`'s
pinned suit. -/

/-- **THE TWIN-COVER FIT** — the chase's `d₂`-over-`y.twin` tableau
seat is a legal card-directed landing: the twin keeps the rank (the
chase's rank premise IS the fit), and the twin keeps the color family
(the two forks' color separation IS the color half). -/
private theorem xfam_canSitOn_twinCover {x y d : Card}
    (hcol : y.suit.color ≠ x.suit.color)
    (hdcol : d.suit.color = x.suit.color)
    (hdrank : d.rank.toIdx + 1 = y.rank.toIdx) :
    canSitOn d y.twin = true := by
  rw [canSitOn_eq]
  refine ⟨?_, ?_⟩
  · rw [Card.twin_rank]; exact hdrank
  · have hyt : y.twin.suit.color = y.suit.color := xfam_twin_color y
    rw [hyt, hdcol]
    exact Ne.symm hcol

/-! ### The corner dichotomy rows

The complete cover/pair census across the three corner regimes: at
the first fork the twin-cover `d` of `x.twin` (one below `x`, of the
opposite family) confronts the second fork's pair `{w, w.twin}` — a
MEMBER exactly in the consecutive regime (shift 1), a NON-member in
the gap regime (shift ≥ 2) and in the equal regime (shift 0) by the
rank arithmetic alone; and in EVERY regime the second fork's own low
cover `d₂` (one below `w`) sits strictly beneath the first fork's
pair.  Pure card arithmetic over the deck census — the corner
residues' step-0 tools, landed ahead of the per-leg chase. -/

/-- **THE PAIR-MEMBERSHIP CENSUS (the shift-one read)** — a cover of
`x.twin` (one below `x`) is literally a member of `w`'s pair exactly
when `w` also sits exactly one below `x`: equal ranks and matching
colors name the deck census's twin pair. -/
private theorem cross_cover_member_shift {d x w : Card}
    (hdx : d.rank.toIdx + 1 = x.rank.toIdx)
    (hwx : w.rank.toIdx + 1 = x.rank.toIdx)
    (hcol : d.suit.color = w.suit.color) :
    d = w ∨ d = w.twin :=
  SeedKit.rankColor_pair (by omega) hcol

/-- **THE PAIR-NONMEMBERSHIP CENSUS (the gap read)** — a cover of
`x.twin` cannot be a member of `w`'s pair when `w`'s pair sits two or
more below `x`: the rank arithmetic alone separates the strata. -/
private theorem cross_cover_nonmember_gap {d x w : Card}
    (hdx : d.rank.toIdx + 1 = x.rank.toIdx)
    (hgap : w.rank.toIdx + 2 ≤ x.rank.toIdx) :
    d ≠ w ∧ d ≠ w.twin := by
  refine ⟨?_, ?_⟩ <;> intro heq
  · rw [heq] at hdx; omega
  · rw [heq, Card.twin_rank] at hdx; omega

/-- **THE PAIR-NONMEMBERSHIP CENSUS (the equal read)** — a cover of
`x.twin` (one below `x`) cannot be a member of `w`'s pair when the
pair sits AT `x`'s rank: the cover is a full stratum below. -/
private theorem cross_cover_nonmember_eq {d x w : Card}
    (hdx : d.rank.toIdx + 1 = x.rank.toIdx)
    (hwxeq : w.rank.toIdx = x.rank.toIdx) :
    d ≠ w ∧ d ≠ w.twin := by
  refine ⟨?_, ?_⟩ <;> intro heq
  · rw [heq] at hdx; omega
  · rw [heq, Card.twin_rank] at hdx; omega

/-- **THE LOW-COVER SEPARATION** — a card one below `w` is never a
member of `x`'s pair whenever `w` sits at or below `x`: the second
fork's own low cover stays a full stratum beneath the first fork's
pair, in every rank regime. -/
private theorem cross_lowcover_notpair {d x w : Card}
    (hdw : d.rank.toIdx + 1 = w.rank.toIdx)
    (hwle : w.rank.toIdx ≤ x.rank.toIdx) :
    d ≠ x ∧ d ≠ x.twin := by
  refine ⟨?_, ?_⟩ <;> intro heq
  · rw [heq] at hdw; omega
  · rw [heq, Card.twin_rank] at hdw; omega

/-- **THE TWIN-COVER CENSUS** — the fork's own twin-cover package
re-read through the deck census: the direct cover `d` of `x.twin`
tops its pile with `nextUp` dead, its color is the OTHER fork's
family, and its rank sits exactly one below the fork's own witness
rank. -/
private theorem cross_twincover_census {st : State} (hwf : st.WF)
    {x w : Card} (hx : ForkWitness st x) (hcolw : w.suit.color ≠ x.suit.color) :
    ∃ (a : Anchor) (bs : List Card) (d : Card),
      (st.piles a).faceUp = bs ++ [x.twin, d] ∧
      canSitOn d x.twin = true ∧
      st.pileOfTop d = some a ∧
      st.nextUp d = false ∧
      d.suit.color = w.suit.color ∧
      d.rank.toIdx + 1 = x.rank.toIdx := by
  obtain ⟨a, bs, d, hshape, -, hfit, htop, hnext, -⟩ :=
    pair_cover_pins hwf hx
  obtain ⟨hridx, hcne⟩ := (canSitOn_eq d x.twin).mp hfit
  rw [Card.twin_rank] at hridx
  have hxt : x.twin.suit.color = x.suit.color := xfam_twin_color x
  rw [hxt] at hcne
  refine ⟨a, bs, d, hshape, hfit, htop, hnext, ?_, hridx⟩
  exact SeedKit.color_pair (Ne.symm hcne) (Ne.symm hcolw)

/-- **THE COVER/PAIR DICHOTOMY, ASSEMBLED (the consecutive read)** —
in the shift-one regime the first fork's twin-cover IS a member of
the second fork's pair: `cross_twincover_census` plus the
membership shift read. -/
private theorem cross_twincover_member_pkg {st : State} (hwf : st.WF)
    {x w : Card} (hx : ForkWitness st x) (hcolw : w.suit.color ≠ x.suit.color)
    (hshift : w.rank.toIdx + 1 = x.rank.toIdx) :
    ∃ (a : Anchor) (bs : List Card) (d : Card),
      (st.piles a).faceUp = bs ++ [x.twin, d] ∧
      canSitOn d x.twin = true ∧
      st.pileOfTop d = some a ∧
      st.nextUp d = false ∧
      (d = w ∨ d = w.twin) := by
  obtain ⟨a, bs, d, hshape, hfit, htop, hnext, hdcolw, hridx⟩ :=
    cross_twincover_census hwf hx hcolw
  exact ⟨a, bs, d, hshape, hfit, htop, hnext,
    cross_cover_member_shift hridx hshift hdcolw⟩

/-- **THE COVER/PAIR DICHOTOMY, ASSEMBLED (the gap read)** — in the
gap regime the first fork's twin-cover is a NON-member of the
second fork's pair: the census package plus the stratum
separation. -/
private theorem cross_twincover_nonpair_pkg {st : State} (hwf : st.WF)
    {x w : Card} (hx : ForkWitness st x) (hcolw : w.suit.color ≠ x.suit.color)
    (hgap : w.rank.toIdx + 2 ≤ x.rank.toIdx) :
    ∃ (a : Anchor) (bs : List Card) (d : Card),
      (st.piles a).faceUp = bs ++ [x.twin, d] ∧
      canSitOn d x.twin = true ∧
      st.pileOfTop d = some a ∧
      st.nextUp d = false ∧
      (d ≠ w ∧ d ≠ w.twin) := by
  obtain ⟨a, bs, d, hshape, hfit, htop, hnext, -, hridx⟩ :=
    cross_twincover_census hwf hx hcolw
  exact ⟨a, bs, d, hshape, hfit, htop, hnext,
    cross_cover_nonmember_gap hridx hgap⟩

/-- **THE COVER/PAIR DICHOTOMY, ASSEMBLED (the equal read)** — in the
equal-rank regime the first fork's twin-cover is a NON-member of
the second fork's pair: it tops a full stratum below the pair. -/
private theorem cross_twincover_nonpair_eq_pkg {st : State} (hwf : st.WF)
    {x w : Card} (hx : ForkWitness st x) (hcolw : w.suit.color ≠ x.suit.color)
    (hwxeq : w.rank.toIdx = x.rank.toIdx) :
    ∃ (a : Anchor) (bs : List Card) (d : Card),
      (st.piles a).faceUp = bs ++ [x.twin, d] ∧
      canSitOn d x.twin = true ∧
      st.pileOfTop d = some a ∧
      st.nextUp d = false ∧
      (d ≠ w ∧ d ≠ w.twin) := by
  obtain ⟨a, bs, d, hshape, hfit, htop, hnext, -, hridx⟩ :=
    cross_twincover_census hwf hx hcolw
  exact ⟨a, bs, d, hshape, hfit, htop, hnext,
    cross_cover_nonmember_eq hridx hwxeq⟩

set_option linter.unusedVariables false in
/-- **THE CONSECUTIVE CORNER of the shifted kill-ladder — the
stratified chase's residue in the tight regime `r₁ = r₂ + 1`
(`cross_strata_chase`'s first named corner).**  The chase's PROVED
preprocessing is carried as hypotheses: the cover `d₂` is x-family,
one below the second fork's rank, resident at the first fork
(`hd₂res`) yet EXILED from its home foundation at the second
(`hd₂out`), covering `y.twin` as a legal card-directed landing
(`hd₂fit`); the cover `d₁` is y-family, one below the first fork's
rank, riding a tableau TOP at the first fork with `nextUp` dead
(`hd₁top`) — and in this regime the deck census (`SeedKit.rankColor_pair`)
proves it a literal PAIR MEMBER of the second fork (`hd₁pair`:
`d₁ = y` or `d₁ = y.twin`), its home suit pinned EXACTLY at `r₂` at
the second fork while reading at most `r₂ − 1` at the first
(`hd₁cen`: the mirror census — `d₁`'s suit owes at least one net
RAISE along the journey); and `d₂`'s home suit owes at least THREE
net LIFO pops (`hdebt₂`, the census `hd₂rung₁`/`hd₂rung₂` read
tight to `r₁ − r₂ = 1`).  ROUTE (complete, the residue's own):
1. THE SURFACING — each pop of the debt is current-top LIFO
   (`foundToTab_pops_currentTop`), so the pops first surface the
   x-family cards stacked above `d₂` (rank indices `r₂..r₁−1`, none
   a king, so no empty-anchor landing exists), each landing on a
   fitting top one rank up, opposite color (`canSitOn`), or nowhere.
2. THE HOST CENSUS — by the deck census the only fitting hosts at
   the top of the surfaced stratum are the pair members `{y, y.twin}`
   themselves; the saturations bar both ends — at the first fork
   `cross_census_dead` holds both members S-dead while `hd₁top`
   seats one ON TOP of a pile, and `pair_cover_pins` seats the
   st₁-end twin-cover — so a pair-member host must have LEFT its
   pile, and its own exit is a pull onto an x-family top one rank
   further up at that epoch.
3. THE OSCILLATION PRICED — each such exit's landing needs its own
   fitting host one rank up in the x family (rank indices `r₂..r₁`),
   all of which the second fork holds FOUNDED beneath its pins
    (`pair_lowFamily_founded` + `FoundKit.mem_found_rank_lt`, the census
   `hd₂rung₂`/`hd₂rung₁` bounding the survivors); the two OPPOSITE
   census debts (`hdebt₂`'s net pulls vs `hd₁cen`'s net raises on the
   two cover suits, `witness_rung_census` closing the per-suit
   oscillation) cannot both service through the same capped strata —
    the per-leg accounting forces an epoch whose every legal seat is
    census-barred: the material competition has no legal leg, `False`.

CLOSED (2026-10-12) via `Orig.CrossFamilyStatic.lean`'s
`cross_orphan_kill` — the STATIC ORPHAN-SEAT route (the orphan one
stratum below `d₂`, its below-neighbor's cell saturated by the second
fork; no census hypothesis consulted); the single residue the
closure rides is that file's named `cross_orphan_seat`, whose
`sorryAx` flows here alone.  The remaining hypothesis package
documents the banked static facts the assembly hands the corner; the
static route consumes only the four pins, so the linter is silenced
for the named binders below. -/
private theorem cross_strata_consec {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {x y d₁ d₂ : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    {τ : List Move} (hτ : ShufflePlayW st₁ τ st₂)
    (hne : y.rank.toIdx + 1 = x.rank.toIdx)
    (hd₂col : d₂.suit.color = x.suit.color)
    (hd₂rank : d₂.rank.toIdx + 1 = y.rank.toIdx)
    (hd₂res : d₂ ∈ st₁.found d₂.suit)
    (hd₂rung₁ : rungAt st₁ d₂.suit = x.rank.toIdx)
    (hd₂rung₂ : rungAt st₂ d₂.suit + 2 ≤ y.rank.toIdx)
    (hd₂top : ∃ a bs, (st₂.piles a).faceUp = bs ++ [y.twin, d₂] ∧
      st₂.pileOfTop d₂ = some a ∧ st₂.nextUp d₂ = false)
    (hd₂fit : canSitOn d₂ y.twin = true)
    (hd₂out : ¬ d₂ ∈ st₂.found d₂.suit)
    (hd₁col : d₁.suit.color = y.suit.color)
    (hd₁rank : d₁.rank.toIdx + 1 = x.rank.toIdx)
    (hd₁pair : d₁ = y ∨ d₁ = y.twin)
    (hd₁top : ∃ a, st₁.pileOfTop d₁ = some a ∧ st₁.nextUp d₁ = false)
    (hd₁rung₁ : rungAt st₁ d₁.suit + 2 ≤ x.rank.toIdx)
    (hd₁rung₂ : rungAt st₂ d₁.suit = y.rank.toIdx)
    (hdebt₂ : x.rank.toIdx + 2 + raisesOf τ d₂.suit
      ≤ y.rank.toIdx + pullsOf τ d₂.suit)
    (hd₁cen : y.rank.toIdx + pullsOf τ d₁.suit
      = rungAt st₁ d₁.suit + raisesOf τ d₁.suit) :
    False := by
  exact cross_orphan_kill hwf₁ hwf₂ hτ hx hy hcol (by omega) d₂.suit
    hd₂col hd₂rung₂

set_option linter.unusedVariables false in
/-- **THE GAP CORNER of the shifted kill-ladder — the stratified
chase's residue in the deep regime `r₂ + 2 ≤ r₁` (`cross_strata_chase`'s
second named corner).**  The chase's PROVED preprocessing is carried
as hypotheses (fit `hd₂fit`, exile `hd₂out`, mirror census `hd₁cen`,
the deep debt `hdebt₂` reading here as at least FOUR net LIFO pops),
plus the corner's own PROVED stratum separation: `hstrat` — `d₁`
tops rank `r₁ − 1`, a full stratum (at least two) ABOVE everything
the debt can surface (the surfaced x-family cards sit at or below
`d₂`'s rank `r₂ − 1`, all beneath the second fork's pinnings).  ROUTE
(complete, the residue's own): 1. THE SURFACING — as in the
consecutive corner, the debt's pops are current-top LIFO
(`foundToTab_pops_currentTop`), surfacing x-family cards of rank
index at most `r₂ − 1`, none a king; their only fitting hosts
(`canSitOn` + the deck census `SeedKit.rankColor_pair`) are y-family
tops one rank up — the stratum the second fork holds FOUNDED
(`pair_lowFamily_founded`), below its pins (`hd₂rung₂`), so each
surfaced card's host is itself founded and must be pulled first.
2. THE HOST EXITS — each such host's pull lands on an x-family top
one rank further up at that epoch; `hstrat` places that host-stratum
a full stratum beneath `d₁`'s own top seat, and `hd₁top` (with the
st₁-end `pair_cover_pins` saturation and `cross_census_dead` at both
ends) bars the y-family exits the chain needs on the tableau.
3. THE OSCILLATION PRICED — the two OPPOSITE census debts on the two
cover suits (`hdebt₂`'s deep net pulls vs `hd₁cen`'s net raises,
`witness_rung_census` closing the per-suit oscillation) stretch the
chain across the gap `r₁ − r₂ ≥ 2`, one stratum more than the
consecutive corner; the capped founded strata (`hd₂rung₁`,
`hd₂rung₂`, `hd₁rung₁`, `hd₁rung₂`) cannot service both directions —
    an epoch arrives whose every legal seat is census-barred, `False`.

CLOSED (2026-10-12) via `Orig/CrossFamilyStatic.lean`'s
`cross_orphan_kill` — the STATIC ORPHAN-SEAT route (identical to the
consecutive corner: the orphan card has no seatable below-neighbor at
the second fork regardless of the gap's depth); the single residue
the closure rides is that file's named `cross_orphan_seat`, whose
`sorryAx` flows here alone.  The remaining hypothesis package
documents the banked static facts the assembly hands the corner; the
static route consumes only the four pins, so the linter is silenced
for the named binders below. -/
private theorem cross_strata_gap {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {x y d₁ d₂ : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    {τ : List Move} (hτ : ShufflePlayW st₁ τ st₂)
    (hg : y.rank.toIdx + 2 ≤ x.rank.toIdx)
    (hd₂col : d₂.suit.color = x.suit.color)
    (hd₂rank : d₂.rank.toIdx + 1 = y.rank.toIdx)
    (hd₂res : d₂ ∈ st₁.found d₂.suit)
    (hd₂rung₁ : rungAt st₁ d₂.suit = x.rank.toIdx)
    (hd₂rung₂ : rungAt st₂ d₂.suit + 2 ≤ y.rank.toIdx)
    (hd₂top : ∃ a bs, (st₂.piles a).faceUp = bs ++ [y.twin, d₂] ∧
      st₂.pileOfTop d₂ = some a ∧ st₂.nextUp d₂ = false)
    (hd₂fit : canSitOn d₂ y.twin = true)
    (hd₂out : ¬ d₂ ∈ st₂.found d₂.suit)
    (hd₁col : d₁.suit.color = y.suit.color)
    (hd₁rank : d₁.rank.toIdx + 1 = x.rank.toIdx)
    (hstrat : d₂.rank.toIdx + 2 ≤ d₁.rank.toIdx)
    (hd₁top : ∃ a, st₁.pileOfTop d₁ = some a ∧ st₁.nextUp d₁ = false)
    (hd₁rung₁ : rungAt st₁ d₁.suit + 2 ≤ x.rank.toIdx)
    (hd₁rung₂ : rungAt st₂ d₁.suit = y.rank.toIdx)
    (hdebt₂ : x.rank.toIdx + 2 + raisesOf τ d₂.suit
      ≤ y.rank.toIdx + pullsOf τ d₂.suit)
    (hd₁cen : y.rank.toIdx + pullsOf τ d₁.suit
      = rungAt st₁ d₁.suit + raisesOf τ d₁.suit) :
    False := by
  exact cross_orphan_kill hwf₁ hwf₂ hτ hx hy hcol (by omega) d₂.suit
    hd₂col hd₂rung₂

/-- **THE SHIFTED KILL-LADDER — the stratification's named nothing.**
The unequal-rank corner's per-leg chase, route-shrunk one level
below `cross_unequal_rank_strata` (whose body assembles exactly this
premise package from the §5b rows and consumes this residue; the
equal-rank sibling keeps its own corner).  PREMISE, THE STRATIFIED
COVER PACKAGE (freed of the assembly's derivation work): the second
fork's twin-cover `d₂` — x-family (`hd₂col`), one below the second
fork's rank (`hd₂rank`), foundation-RESIDENT at the first fork
(`hd₂res`), its home suit pinned at `r₁` there (`hd₂rung₁`) yet
reading at least two below `r₂` at the second (`hd₂rung₂`), face-up
covering `y.twin` at `st₂` (`hd₂top`) — together with the first
fork's own cover `d₁` — y-family (`hd₁col`), one below the FIRST
fork's rank (`hd₁rank`), topping at `st₁` with `nextUp` = false
(`hd₁top`), its suit reading at least two below `r₁` there
(`hd₁rung₁`) while pinned EXACTLY at `r₂` at the second fork
(`hd₁rung₂`) — and the forward class shuffle `τ` carrying the deep
pull debt (`hdebt₂`: `(r₁ − r₂) + 2` more LIFO pops of `d₂`'s home
suit than raises along it, read `≥ 3` at the strict corner by
`hlo`).  ROUTE (still to price): the debt's pops are LIFO
(`foundToTab_pops_currentTop`) and each lands its surfaced x-family
card on a fitting top one rank up or not at all (empty-anchor
landings are king-only and the surfaced ranks never reach the
king); the low end of the surfaced stratum sits beneath everything
the second fork pins, so the fitting hosts there are y-family cards
the second fork holds FOUNDED (`pair_lowFamily_founded` iterated;
the founded wedges `FoundKit.mem_found_rank_lt` both directions) — each
host must itself be pulled first, whose landing needs an x-family
top one rank further up at that epoch; the two forks' saturations
(`cross_census_dead`) and the one-leg transfer (`S_census_one_leg`,
with `quiet_flat` / `pull_factor` / `raise_factor` pricing the
intervening segments and `witness_rung_census` closing the per-suit
oscillation) bar every epoch at which any link of the chain seats a
cover: the deeper stratum's material cannot mirror into the
shallower fork's own foundation.  The CONSECUTIVE corner
(`r₁ = r₂ + 1`: the cover `d₁` IS a y-pair member, the rank/color
census) and the GAP corner (`r₁ ≥ r₂ + 2`: `d₁` tops a full stratum
above the second fork's pinnings) split inside; the reversed order
never enters (`hlo`).

LANDED as the SPLIT: the body below is PROVED — the deck-census copy
(`SeedKit.rankColor_pair`) prices the twin-cover fit
(`xfam_canSitOn_twinCover`) and the exile (`cross_strata_exile`), the
per-suit census (`witness_rung_census`) is read once into the mirror
`hd₁cen`, and the chase forks into the two corners directly above:
the CONSECUTIVE corner `cross_strata_consec` (where `d₁` is proved
literally a y-pair member, `hd₁pair`) and the GAP corner
`cross_strata_gap` (where the stratum separation `hstrat` is priced
in) — and both corners are now themselves closed by the STATIC
ORPHAN-SEAT kill (`Orig/CrossFamilyStatic.lean`'s
`cross_orphan_kill`, through that file's one named residue
`cross_orphan_seat`). -/
private theorem cross_strata_chase {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {x y d₁ d₂ : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hlo : y.rank.toIdx < x.rank.toIdx)
    {τ : List Move} (hτ : ShufflePlayW st₁ τ st₂)
    (hd₂col : d₂.suit.color = x.suit.color)
    (hd₂rank : d₂.rank.toIdx + 1 = y.rank.toIdx)
    (hd₂res : d₂ ∈ st₁.found d₂.suit)
    (hd₂rung₁ : rungAt st₁ d₂.suit = x.rank.toIdx)
    (hd₂rung₂ : rungAt st₂ d₂.suit + 2 ≤ y.rank.toIdx)
    (hd₂top : ∃ a bs, (st₂.piles a).faceUp = bs ++ [y.twin, d₂] ∧
      st₂.pileOfTop d₂ = some a ∧ st₂.nextUp d₂ = false)
    (hd₁col : d₁.suit.color = y.suit.color)
    (hd₁rank : d₁.rank.toIdx + 1 = x.rank.toIdx)
    (hd₁top : ∃ a, st₁.pileOfTop d₁ = some a ∧ st₁.nextUp d₁ = false)
    (hd₁rung₁ : rungAt st₁ d₁.suit + 2 ≤ x.rank.toIdx)
    (hd₁rung₂ : rungAt st₂ d₁.suit = y.rank.toIdx)
    (hdebt₂ : x.rank.toIdx + 2 + raisesOf τ d₂.suit
      ≤ y.rank.toIdx + pullsOf τ d₂.suit) :
    False := by
  -- the proved preprocessing, handed to both corners:
  -- the twin-cover seat is a legal card-directed landing
  have hd₂fit : canSitOn d₂ y.twin = true :=
    xfam_canSitOn_twinCover hcol hd₂col hd₂rank
  -- the cover left its home foundation by the second fork
  have hd₂out : ¬ d₂ ∈ st₂.found d₂.suit :=
    cross_strata_exile hwf₂ hd₂rank hd₂rung₂
  -- the mirror census read off d₁'s pinned suit
  have hd₁cen : y.rank.toIdx + pullsOf τ d₁.suit
      = rungAt st₁ d₁.suit + raisesOf τ d₁.suit := by
    have hc := witness_rung_census hτ d₁.suit
    omega
  -- the regime fork: CONSECUTIVE vs GAP
  rcases Nat.lt_or_ge x.rank.toIdx (y.rank.toIdx + 2) with h | h
  · exact cross_strata_consec hwf₁ hwf₂ hx hy hcol hτ (by omega) hd₂col
      hd₂rank hd₂res hd₂rung₁ hd₂rung₂ hd₂top hd₂fit hd₂out hd₁col
      hd₁rank (SeedKit.rankColor_pair (by omega) hd₁col) hd₁top hd₁rung₁
      hd₁rung₂ hdebt₂ hd₁cen
  · exact cross_strata_gap hwf₁ hwf₂ hx hy hcol hτ h hd₂col hd₂rank
      hd₂res hd₂rung₁ hd₂rung₂ hd₂top hd₂fit hd₂out hd₁col hd₁rank
      (by omega) hd₁top hd₁rung₁ hd₁rung₂ hdebt₂ hd₁cen

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

LANDED as the assembly: step 1's stratified shifts and residencies
are PROVED in the body — off the §5b rank-free rows, the second
fork's own `pair_cover_pins` saturation pins, the low-family
founding row, and the journey census read into the deep pull debt —
step 3's mirrored order is barred outright by the strict
`hle`/`hne`, and step 2's per-leg chase is split one level into the
named nothing `cross_strata_chase` directly above (route in its own
docstring); the assembly consumes exactly that residue. -/
private theorem cross_unequal_rank_strata {st₁ st₂ : State}
    (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    (hcls : sameOrbitSetoid.r st₁ st₂)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hle : y.rank.toIdx ≤ x.rank.toIdx)
    (hne : y.rank.toIdx ≠ x.rank.toIdx) :
    False := by
  -- THE FORWARD WITNESS SHUFFLE (the class's own play)
  obtain ⟨τ, hτ⟩ := sameOrbit_forward hcls
  -- THE SECOND FORK'S TWIN-COVER, read off its own saturation pins:
  -- x-family, one below the second fork's rank, foundation-RESIDENT
  -- at the first fork, its home suit pinned at `r₁` there yet
  -- reading at least two below `r₂` at the second
  obtain ⟨a₂, bs₂, d₂, hshape₂, -, hfit₂, htop₂, hnext₂, hd₂rung₂le⟩ :=
    pair_cover_pins hwf₂ hy
  obtain ⟨hd₂rank, hcne₂⟩ := (canSitOn_eq d₂ y.twin).mp hfit₂
  rw [Card.twin_rank] at hd₂rank
  have hyt : y.twin.suit.color = y.suit.color := xfam_twin_color y
  rw [hyt] at hcne₂
  have hd₂col : d₂.suit.color = x.suit.color :=
    SeedKit.color_pair (Ne.symm hcne₂) hcol
  have hd₂res : d₂ ∈ st₁.found d₂.suit :=
    pair_lowFamily_founded hwf₁ hx hd₂col (by omega)
  have hd₂rung₁ : rungAt st₁ d₂.suit = x.rank.toIdx :=
    xfam_family_rung hx hd₂col
  have hne₂ : d₂.rank.toIdx ≠ rungAt st₂ d₂.suit := by
    intro hcon
    have hn2 : st₂.nextUp d₂ = true := decide_eq_true hcon
    rw [hn2] at hnext₂
    exact absurd hnext₂ (by simp)
  have hd₂rung₂ : rungAt st₂ d₂.suit + 2 ≤ y.rank.toIdx := by
    have hle2 : rungAt st₂ d₂.suit + 1 ≤ y.rank.toIdx := hd₂rung₂le
    omega
  -- THE FIRST FORK'S OWN COVER, off the rank-free climb row:
  -- y-family, one below the first fork's rank, topping at `st₁`
  -- with `nextUp` dead, its suit pinned exactly at `r₂` at the
  -- second fork
  obtain ⟨d₁, a₁, hd₁col, hd₁rank, htop₁, hnext₁, hd₁rung₁, hd₁rung₂, -⟩ :=
    cross_climb_general hwf₁ hwf₂ hx hy hcol
  -- THE DEEP PULL DEBT: `(r₁ − r₂) + 2 ≥ 3` more LIFO pops of `d₂`'s
  -- home suit than raises along the one class shuffle (the §2-§3
  -- census read, §5b-strengthened)
  have hcen := witness_rung_census hτ d₂.suit
  refine cross_strata_chase hwf₁ hwf₂ hx hy hcol (by omega) hτ
    hd₂col hd₂rank hd₂res hd₂rung₁ hd₂rung₂
    ⟨a₂, bs₂, hshape₂, htop₂, hnext₂⟩
    hd₁col hd₁rank ⟨a₁, htop₁, hnext₁⟩ hd₁rung₁ hd₁rung₂ ?_
  omega

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

The interlock therefore rests on exactly ONE fresh leaf residue —
`Orig/CrossFamilyStatic.lean`'s named `cross_orphan_seat` (reached
through the two former sub-residues, each now closed by the static
orphan-seat kill); the main theorem below inherits precisely that
residue from here. -/
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
`[propext, Quot.sound]`-grade (banked chain only); the two rank
drivers (`cross_equal_rank_kill`, `cross_strata_chase`) and the three
former corner residues (`cross_equal_rank_kick`,
`cross_strata_consec`, `cross_strata_gap`) are now PROVED — each
closed by one call of `Orig/CrossFamilyStatic.lean`'s
`cross_orphan_kill` (the static orphan-seat route), so the assembly
and the main row carry exactly ONE fresh `sorryAx`: that file's named
residue `cross_orphan_seat` (the below-riding seat row), and NOTHING
else — `forkState_familyRigid` inherits exactly that.  The
preprocessing rows (deck census, twin-cover fit, leg extractors,
exile, cover/pair dichotomy) are zero-sorry and read banked-chain
grade, as is the LIFO exodus wheel `cross_found_exodus` below — the
tail-induction engine (all six mover cases proved) whose residency
mint pins a resident-then-exiled card's own `foundToTab` leg, the
first step of the seat row's own route, landed as the per-file copy
ready for the upstream consumption. -/

#print axioms cross_census_dead
#print axioms cross_cover_residency
#print axioms cross_cover_rung_drop
#print axioms cross_anchor_climb
#print axioms cross_cover_pull_pressure
#print axioms cross_drop_general
#print axioms cross_climb_general
#print axioms SeedKit.rankColor_pair
#print axioms xfam_canSitOn_twinCover
#print axioms cross_raise_leg
#print axioms cross_pull_leg
#print axioms cross_strata_exile
#print axioms cross_found_exodus
#print axioms cross_cover_member_shift
#print axioms cross_cover_nonmember_gap
#print axioms cross_cover_nonmember_eq
#print axioms cross_lowcover_notpair
#print axioms cross_twincover_census
#print axioms cross_twincover_member_pkg
#print axioms cross_twincover_nonpair_pkg
#print axioms cross_twincover_nonpair_eq_pkg
#print axioms cross_equal_rank_kill
#print axioms cross_equal_rank_kick
#print axioms cross_strata_consec
#print axioms cross_strata_gap
#print axioms cross_unequal_rank_strata
#print axioms cross_strata_chase
#print axioms cross_family_interlock
#print axioms forkState_familyRigid
