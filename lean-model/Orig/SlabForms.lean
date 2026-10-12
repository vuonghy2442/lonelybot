import Orig.LowSlab
import Orig.PairConfine

/-!
# Orig.SlabForms — THE SLAB-FORMS EQUIVALENCE (the halved slab vs. both suits)

Two forms of "below the fork point" — for a fork with witness `x`,
fork point the rank index `r := x.rank.toIdx` — are compared and,
within the fork's macro class, IDENTIFIED up to an explicitly named
difference set:

* **THE TWIN-SIDE FORM** — `familyBelowFrontier w x` (`Orig.LowSlab`,
  the current post-refinement def):
  `rungAt w x.twin.suit ≤ x.rank.toIdx`.  This is the CLASS-REGIME
  slab, DELIBERATELY HALVED (the owner's 2026-10-12 refinement): within
  a fork's macro class the one-funding rows plus the zone seals make
  the x-lifted members benign, so the twin side alone carries the
  content; at WF endpoints joined by a witness journey the read is an
  ARRANGEMENT fact — the covered twin still physically resides in
  `w`'s tableau (`Orig.SlabEquiv.twin_slab_tableau`).
* **THE BOTH-SUITS FORM** — `xyBelowBoth w x` (defined locally in §0
  below): each family suit's rung at or below the fork point — the
  historically first draft of the slab.

THE ROWS:

* §1 **`slabForms_split`** [E] — **THE DEFINITIONAL SPLIT**: the
  both-suits form is exactly its two conjuncts, order-free (proved
  zero-sorry; pure constructor pairs).
* §2 **`slabForms_inclass`** [M] — **THE IN-CLASS COMPOSITE IFF**,
  the mission's main row: within the fork's macro class, the twin-side
  slab holds exactly at the BOTH-SUITS members and at the difference
  set — the X-LIFTED members, named disjunct-wise: x founded at `w`
  (the x-side rung strictly past the fork point) while the twin still
  sits in `w`'s tableau.  Landed ZERO-SORRY: every arm is assembly over
  the sealed zone machinery (`twin_slab_tableau`'s two arms close both
  directions; the origin-side tableau pin rides `pair_cover_pins`' seat
  shape — the twin rides face-up under the cover `d`).  The composite
  iff needs NO content of `forkState_one_founding`: the both-founded
  case falsifies BOTH sides of the iff simultaneously, so no
  confinement enters the equivalence.
* §3 **`slabForms_bothFounded_barred`** [M] — **THE BOTH-FOUNDED BAR**,
  the difference-shape completeness corollary: the x-lifted shape is
  not just a superset of the in-class difference set but EXACTLY it —
  the both-founded fourth case (x-lifted with the twin consumed too)
  is BARRED in-class by `forkState_one_founding`
  (`Orig.PairConfine`), instantiated here through the at-fork rung
  equalities (`canRaiseS_rung` on both live members, the
  `fork_self_low` pattern).

DOC MAP:

* The TWIN-SIDE form is `familyBelowFrontier` — the class-regime slab,
  deliberately halved; one-funding plus the zone seals make the
  x-lifted members benign inside a class, and §§2–3 make that
  benignity exact (§2 names the difference set; §3 bars the fourth
  case).
* THE DIFFERENCE SET of the iff is exactly the x-lifted members —
  x founded at `w` (its suit's rung past the fork point), the twin
  still in `w`'s tableau (`twin_slab_tableau`'s witness-journey
  arrangement read at WF endpoints).
* §3 is why the difference set's shape is COMPLETE: the both-founded
  fourth case is barred in-class, so the halving may ignore it.
* TREE-REGIME NOTE: OUTSIDE the class regime neither the halving nor
  §3's bar applies — a tree of journeys through arbitrary states must
  hypothesize both conjuncts inline, precisely the shape
  `Orig/ForkAscent.lean`'s `hbelow` premise carries (both family suits
  at-or-below the fork's rank, plus the start-mobility reads).  A
  cross-reference note only — no import, no content consumed.

House compliance: additive leaf (`import Orig.LowSlab` — which itself
brings `Orig.SlabEquiv` and the `familyBelowFrontier` NAME to consume —
plus `import Orig.PairConfine` for the one-funding row and the fork
vocabulary; the two chains already share `Orig.PairName` and
`Orig.BracketDecomp`, so no cycle arises and nothing below imports this
leaf); every consumed row is PUBLIC (no per-file kit copies were
needed: `twin_slab_tableau`, `pair_cover_pins`, `sameOrbit_forward`,
`canRaiseS_rung`, `forkState_one_founding`); the one fresh definition
(`xyBelowBoth`) is statement-facing; each fresh head is audited in the
battery below; zero `Classical.choice` (no classical tactics anywhere;
the single numeric dichotomy closes by `Nat.lt_or_ge` with defeq
reads — no `omega` on a non-arithmetic goal was ever needed).-/

/-! ## §0. The both-suits form (local, statement-facing) -/

/-- **THE BOTH-SUITS FORM** — the pre-refinement draft of the fork's
slab, kept here as the comparison pole of the equivalence rows: EACH
family suit's rung sits at or below the fork point `x.rank.toIdx` —
the x-side read conjoined with the twin-side slab
(`familyBelowFrontier`).  The in-class iff of §2 says the halved
(twin-side) slab carries exactly these members PLUS the x-lifted
difference set, and §3's bar is what makes that sum exhaustive. -/
def xyBelowBoth (w : State) (x : Card) : Prop :=
  rungAt w x.suit ≤ x.rank.toIdx ∧ familyBelowFrontier w x

/-! ## §1. The definitional split -/

/-- **THE DEFINITIONAL SPLIT** — `slabForms_split` [E]: the both-suits
form is exactly its two (order-free) halves — the twin-side slab
`familyBelowFrontier w x` conjoined with the x-side rung bound
`rungAt w x.suit ≤ x.rank.toIdx`.  Pure definition unfolding: two
constructor swaps, zero content; the row exists so downstream
statements may cite the split by name instead of re-unfolding the
local def. -/
theorem slabForms_split {w : State} {x : Card} :
    xyBelowBoth w x ↔
      familyBelowFrontier w x ∧ rungAt w x.suit ≤ x.rank.toIdx := by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

/-! ## §2. The in-class composite iff (the mission's main row) -/

/-- **THE IN-CLASS COMPOSITE IFF** — `slabForms_inclass` [M, landed
zero-sorry]: within the fork's macro class (the fork `st` with
witness `x`; `hcls : sameOrbitSetoid.r st w`; both endpoints WF), the
TWIN-SIDE slab `familyBelowFrontier w x` holds exactly at the
BOTH-SUITS members and at the X-LIFTED difference set — the members
where x is already founded (its suit's rung strictly past the fork
point) while the covered twin still sits in `w`'s tableau.

ROUTE (assembly over the sealed zone machinery; no new mathematics —
as the analysis predicted, every arm closes on the banked rows):

1. THE WITNESS JOURNEY: `sameOrbit_forward hcls` hands the forward
   shuffle `ShufflePlayW st τ w`.
2. THE ORIGIN TABLEAU PIN: `pair_cover_pins hwfst hx` seats the twin
   FACE-UP at the fork, directly under the cover `d`
   (`faceUp = bs ++ [x.twin, d]`) — the membership row that feeds the
   zone equivalence's origin premise.
3. THE SEALED EQUIVALENCE: `twin_slab_tableau hwfst hwfw hτ htwinst` —
   at the witness journey's WF endpoints, the twin's tableau residency
   at `w` EQUIVALENTS the twin-side slab read.  (⇒) splits
   `Nat.lt_or_ge` on the x-side rung: the ≤-case is the both-suits
   projection (`Or.inl` of the case hypothesis with the given
   twin-side fact); the >-case IS the rung conjunct of the lifted
   disjunct (no founded-bridge needed — the dichotomy hypothesis is
   the disjunct, modulo `>`/`<` defeq), with the tableau conjunct read
   off the equivalence's rung→tableau arm (`Iff.mpr` on the
   twin-side hypothesis).  (⇐) the both-arm projects its second
   conjunct; the lifted-arm reads the rung off the tableau by the
   equivalence's tableau→rung arm (`Iff.mp`).

HONESTY NOTES: the `hfork : forkState st` spear is NOT consumed —
`ForkWitness` plus the two WF's suffice (the statement keeps the
spear for uniformity with the class rows); the iff consults NO
content of `forkState_one_founding` — the both-founded case would
falsify both sides at once, so the equivalence stays inside the zone
machinery, and the confinement enters only at §3's completeness
corollary below. -/
theorem slabForms_inclass {st w : State} (hwfst : st.WF) (hwfw : w.WF)
    (hfork : forkState st) {x : Card} (hx : ForkWitness st x)
    (hcls : sameOrbitSetoid.r st w) :
    familyBelowFrontier w x ↔
      xyBelowBoth w x ∨
        (rungAt w x.suit > x.rank.toIdx ∧
          (∃ a, x.twin ∈ (w.piles a).faceUp ∨ x.twin ∈ (w.piles a).hidden)) := by
  have _hfork := hfork
  -- the origin-side tableau pin: the twin rides face-up under the cover
  obtain ⟨a₀, bs, d, hshape, -, -, -, -, -⟩ := pair_cover_pins hwfst hx
  have htwinst : ∃ a, x.twin ∈ (st.piles a).faceUp ∨ x.twin ∈ (st.piles a).hidden :=
    ⟨a₀, Or.inl (by
      rw [hshape]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))⟩
  -- the witness journey and the sealed zone equivalence
  obtain ⟨τ, hτ⟩ := sameOrbit_forward hcls
  have htab := twin_slab_tableau hwfst hwfw hτ htwinst
  constructor
  · intro hfam
    unfold familyBelowFrontier at hfam
    rcases Nat.lt_or_ge (x.rank.toIdx) (rungAt w x.suit) with h | h
    · exact Or.inr ⟨h, htab.mpr hfam⟩
    · exact Or.inl ⟨h, hfam⟩
  · rintro (⟨-, hfam⟩ | ⟨-, htabw⟩)
    · exact hfam
    · unfold familyBelowFrontier
      exact htab.mp htabw

/-! ## §3. The both-founded bar (the completeness corollary) -/

/-- **THE BOTH-FOUNDED BAR** — `slabForms_bothFounded_barred` [M,
landed at the imported invariant's grade]: within the fork's macro
class the pair's two rungs NEVER both stand strictly past the fork
point — so the x-lifted difference members of `slabForms_inclass` are
not just a superset of the in-class difference set but exactly it
(the both-founded fourth case, x-lifted with the twin consumed too, is
BARRED in-class; the halving may ignore it).

ROUTE (the one-founding instantiation; zero fresh content): the at-fork
rung equalities read off `canRaiseS_rung` on both live pair members
(the `Orig.LowSlab` `fork_self_low` pattern — the twin's read via
`Card.twin_rank`), then `forkState_one_founding hwfst hfork hcls x hx`
with both equalities rewritten in is exactly the barred pair.

GRADE — THE SORRYAX FLOW, EXPLICITLY: this row carries ONE-FUNDING's
`sorryAx` transitively through `Orig.PairConfine`'s landing seams —
the roaming-seat seam `conf_orphan_roam` (the door bar's open seam)
→ `conf_door_orphan` → `crossing_door_barred` →
`forkState_one_founding` — and NOTHING ELSE: the row's own proof adds
no fresh `sorry`; the compiled battery below documents the exact
profile. -/
theorem slabForms_bothFounded_barred {st w : State} (hwfst : st.WF)
    (hfork : forkState st) {x : Card} (hx : ForkWitness st x)
    (hcls : sameOrbitSetoid.r st w) :
    ¬ (rungAt w x.suit > x.rank.toIdx ∧
       rungAt w x.twin.suit > x.rank.toIdx) := by
  have hr0 : rungAt st x.suit = x.rank.toIdx :=
    canRaiseS_rung ((hx.1 x).mp (Or.inl rfl))
  have hr1 : rungAt st x.twin.suit = x.rank.toIdx := by
    have h2 := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
    rwa [Card.twin_rank] at h2
  rintro ⟨hA, hB⟩
  have hban := forkState_one_founding hwfst hfork hcls x hx
  rw [hr0, hr1] at hban
  exact hban ⟨hA, hB⟩

/-! ## The audit battery

`#print axioms` per fresh head (the three rows; the §0 def is
statement-facing): **`slabForms_split`** is a pure constructor swap;
**`slabForms_inclass`** is assembly over the sealed zone machinery
(`twin_slab_tableau`, `pair_cover_pins`, `sameOrbit_forward`) and was
landed WITH ZERO `sorry` — it must read banked-chain grade
(`[propext]` / `[propext, Quot.sound]`) with NO `sorryAx`;
**`slabForms_bothFounded_barred`** carries EXACTLY the one-funding
`sorryAx` flow through `Orig.PairConfine`'s landing seams (no fresh
inflow of its own) alongside the banked-chain axioms.  The empirical
profiles are the compiled battery below. -/

#print axioms slabForms_split
#print axioms slabForms_inclass
#print axioms slabForms_bothFounded_barred
