import Orig2.Fork.Cover
import Orig2.Substrate.PairClassSeed
import Orig2.Fiber.ArmFiber

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Orig2.ForkClass — the class-level fork theorem, reduced to two residues

`fork_label_class` (the frozen `Orig/ForkCensus.lean:520`) says a macro
class carries at most ONE fork pair: any two `ForkWitness` states in one
`sameOrbitSetoid` class have witnesses equal up to the twin flip.

This card assembles the theorem at the Orig2 seam from exactly two named
residues:

* `CoverToken` — at a fork, the cover of the blocked twin stays seated
  on one of the two twins along every witness play;
* `OneFounding` — the two pair-suit rungs never both exceed their
  at-fork values along a witness journey.

The assembly is the `FrozenCoverRung` route.  Both residues are
DISCHARGED in `Orig2/Fiber/LockRung.lean` (`CoverToken_holds`,
`OneFounding_holds`), which makes `fork_label_class` and
`twinPair_founds` unconditional.  This card keeps the conditional
assembly so the two inputs stay visible as named rows.

House compliance: additive leaf (`Orig2.Cover` for the cover pin,
`Orig2.PairClassSeed` for the seed kit, `Orig2.ArmFiber` for the fiber
vocabulary); the assembly is `[propext, Quot.sound]`; zero `sorry`.
-/

/-- A card with an `.inr` seat is face-up in that pile. -/
theorem faceUp_of_seat {st : State} {d u : Card}
    (h : seatOf st d = some (Sum.inr u)) :
    ∃ a, d ∈ (st.piles a).faceUp := by
  obtain ⟨a, hhold, -, -⟩ := tfc_seatOf_of_inr h
  exact ⟨a, pileHolding_mem hhold⟩

/-- **CoverToken** — the mutual-lock invariant: at a fork, the cover of
the blocked twin is seated on one of the two twins at every witness
descendant. -/
def CoverToken : Prop :=
  ∀ (F Z : State) (x y d : Card) (ρ : List Move),
    F.WF → y = x.twin → TwinLivePair F x →
    seatOf F d = some (Sum.inr y) →
    ShufflePlayW F ρ Z →
    seatOf Z d = some (Sum.inr x) ∨ seatOf Z d = some (Sum.inr y)

/-- **CROSS-FAMILY RIGIDITY FROM THE TOKEN.** -/
theorem crossFamily_rigid_of_token (htok : CoverToken)
    {F G : State} (hwfF : F.WF) (hwfG : G.WF)
    (hcls : sameOrbitSetoid.r F G)
    {x y : Card} (hx : ForkWitness F x) (hy : ForkWitness G y)
    (hcol : y.suit.color ≠ x.suit.color) : False := by
  -- the class's plays, both ways
  obtain ⟨σ, hσ, τ, hτ⟩ := hcls
  -- both live pairs
  have hliveF : TwinLivePair F x := ((forkWitness_iff F x).mp hx).1
  have hliveG : TwinLivePair G y := ((forkWitness_iff G y).mp hy).1
  -- the first fork's cover
  have hcovF : CoveredAt F x.twin :=
    (forkWitness_iff_covered hwfF rfl hliveF
      ((hliveF x.twin).mpr (Or.inr rfl))).mp hx
  obtain ⟨d, hd⟩ := hcovF
  -- the second fork's cover
  have hcovG : CoveredAt G y.twin :=
    (forkWitness_iff_covered hwfG rfl hliveG
      ((hliveG y.twin).mpr (Or.inr rfl))).mp hy
  obtain ⟨e, he⟩ := hcovG
  -- cover pins: rank and colour
  obtain ⟨-, -, -, -, -, hdcolx, hdrank, -⟩ :=
    cover_pins_of_fork hwfF hx rfl hd
  obtain ⟨-, -, -, -, -, hecoly, herank, -⟩ :=
    cover_pins_of_fork hwfG hy rfl he
  -- d has the second family's colour; e has the first's
  have hdcolY : d.suit.color = y.suit.color :=
    SeedKit.color_pair (Ne.symm hdcolx) (Ne.symm hcol)
  have hecolX : e.suit.color = x.suit.color :=
    SeedKit.color_pair (Ne.symm hecoly) hcol
  -- the token at G and at F
  have htokG : seatOf G d = some (Sum.inr x) ∨ seatOf G d = some (Sum.inr x.twin) :=
    htok F G x x.twin d τ hwfF rfl hliveF hd hτ
  have htokF : seatOf F e = some (Sum.inr y) ∨ seatOf F e = some (Sum.inr y.twin) :=
    htok G F y y.twin e σ hwfG rfl hliveG he hσ
  -- the rank squeeze, first side: s < r
  have hsr : y.rank.toIdx < x.rank.toIdx := by
    rcases htokG with hG | hG
    · obtain ⟨a, hmem⟩ := faceUp_of_seat hG
      by_cases hlt : d.rank.toIdx < y.rank.toIdx
      · have hfound := pair_lowFamily_founded hwfG hy hdcolY hlt
        exfalso
        exact ((mem_found_unique hwfG hfound).1 a).2 hmem
      · omega
    · obtain ⟨a, hmem⟩ := faceUp_of_seat hG
      by_cases hlt : d.rank.toIdx < y.rank.toIdx
      · have hfound := pair_lowFamily_founded hwfG hy hdcolY hlt
        exfalso
        exact ((mem_found_unique hwfG hfound).1 a).2 hmem
      · omega
  -- the rank squeeze, second side: r < s
  have hrs : x.rank.toIdx < y.rank.toIdx := by
    rcases htokF with hF | hF
    · obtain ⟨a, hmem⟩ := faceUp_of_seat hF
      by_cases hlt : e.rank.toIdx < x.rank.toIdx
      · have hfound := pair_lowFamily_founded hwfF hx hecolX hlt
        exfalso
        exact ((mem_found_unique hwfF hfound).1 a).2 hmem
      · omega
    · obtain ⟨a, hmem⟩ := faceUp_of_seat hF
      by_cases hlt : e.rank.toIdx < x.rank.toIdx
      · have hfound := pair_lowFamily_founded hwfF hx hecolX hlt
        exfalso
        exact ((mem_found_unique hwfF hfound).1 a).2 hmem
      · omega
  omega


set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Temp/ForkClass_SameFamily — the same-family half and the assembled class theorem

SCRATCH.  `Temp/ForkClass_CrossFamily` proved the cross-family half
conditional on `CoverToken`.  This file proves the same-family half
conditional on `OneFounding` (the mutual-lock invariant), and assembles
the full class theorem:

```
fork_label_class :
  ForkWitness F w → ForkWitness G v → sameOrbit F G → v = w ∨ v = w.twin
```

from `CoverToken + OneFounding`.  The two missing inputs are exactly the
two pieces of the `FrozenCoverRung` route.
-/


/-- **OneFounding** — the mutual-lock invariant at the class grade:
along a witness journey from a fork, the two pair-suit rungs never both
exceed their at-fork values. -/
def OneFounding : Prop :=
  ∀ (st st' : State) (x : Card),
    st.WF → forkState st → sameOrbitSetoid.r st st' → ForkWitness st x →
    ¬ (rungAt st' x.suit > rungAt st x.suit ∧
       rungAt st' x.twin.suit > rungAt st x.twin.suit)

/-- Same-family cards of equal rank are the pair, up to the twin flip. -/
theorem sameFamily_samePair {x y : Card}
    (hys : y.suit = x.suit ∨ y.suit = x.twin.suit)
    (hrank : y.rank.toIdx = x.rank.toIdx) :
    y = x ∨ y = x.twin := by
  have hcol : y.suit.color = x.suit.color := by
    rcases hys with h | h
    · rw [h]
    · rw [h, Card.twin_suit, Suit.color_twin]
  exact SeedKit.rankColor_pair hrank hcol

/-- **THE RANK CEILING** — a same-family fork at a later class-mate has
rank at most the origin fork's rank.  If it were strictly greater, both
origin pair-suit rungs would exceed their at-fork values, against
`OneFounding`. -/
theorem rankCeiling_of_oneFounding (hone : OneFounding)
    {st st' : State} (hwf : st.WF) (hwf' : st'.WF)
    (h : forkState st) (hcls : sameOrbitSetoid.r st st')
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness st' y)
    (hys : y.suit = x.suit ∨ y.suit = x.twin.suit) :
    y.rank.toIdx ≤ x.rank.toIdx := by
  obtain ⟨hx1, hx2⟩ := forkState_witness_rungs hx
  obtain ⟨hy1, hy2⟩ := forkState_witness_rungs hy
  rcases Nat.lt_trichotomy y.rank.toIdx x.rank.toIdx with hlt | heq | hgt
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq
  · exfalso
    have hgtA : rungAt st' x.suit > rungAt st x.suit := by
      rcases hys with hs | hs
      · have h1 : rungAt st' x.suit = rungAt st' y.suit := by rw [← hs]
        rw [h1, hy1, hx1]
        exact hgt
      · have hyb : y.twin.suit = x.suit := by
          rw [Card.twin_suit, hs]
          exact Suit.twin_twin x.suit
        have h1 : rungAt st' x.suit = rungAt st' y.twin.suit := by rw [← hyb]
        rw [h1, hy2, hx1]
        exact hgt
    have hgtB : rungAt st' x.twin.suit > rungAt st x.twin.suit := by
      rcases hys with hs | hs
      · have hyt : y.twin.suit = x.twin.suit := by
          rw [Card.twin_suit, hs]
          rfl
        have h1 : rungAt st' x.twin.suit = rungAt st' y.twin.suit := by rw [← hyt]
        rw [h1, hy2, hx2]
        exact hgt
      · have h1 : rungAt st' x.twin.suit = rungAt st' y.suit := by rw [← hs]
        rw [h1, hy1, hx2]
        exact hgt
    exact hone st st' x hwf h hcls hx ⟨hgtA, hgtB⟩

/-- **THE RANK FLOOR** — by symmetry of the class relation, the ceiling
applied with the endpoints swapped. -/
theorem rankFloor_of_oneFounding (hone : OneFounding)
    {st st' : State} (hwf : st.WF) (hwf' : st'.WF)
    (h : forkState st) (hcls : sameOrbitSetoid.r st st')
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness st' y)
    (hys : y.suit = x.suit ∨ y.suit = x.twin.suit) :
    x.rank.toIdx ≤ y.rank.toIdx := by
  have h2 : forkState st' := forkState_iff.mpr ⟨y, hy⟩
  have hcls' : sameOrbitSetoid.r st' st := sameOrbitSetoid.iseqv.symm hcls
  have hys' : x.suit = y.suit ∨ x.suit = y.twin.suit := by
    rcases hys with hs | hs
    · exact Or.inl hs.symm
    · refine Or.inr ?_
      rw [Card.twin_suit] at hs
      have htwin : y.suit.twin = (x.suit.twin).twin := congrArg Suit.twin hs
      rw [Suit.twin_twin] at htwin
      rw [show y.twin.suit = y.suit.twin from Card.twin_suit y]
      exact htwin.symm
  exact rankCeiling_of_oneFounding (hone := hone) (st := st') (st' := st)
    (hwf := hwf') (hwf' := hwf) (h := h2) (hcls := hcls')
    (x := y) (hx := hy) (y := x) (hy := hx) (hys := hys')

/-- **SAME-FAMILY FORK PAIRS AGREE.** -/
theorem family_pairClass_of_oneFounding (hone : OneFounding)
    {st st' : State} (hwf : st.WF) (hwf' : st'.WF)
    (h : forkState st) (hcls : sameOrbitSetoid.r st st')
    (x : Card) (hx : ForkWitness st x) {y : Card} (hy : ForkWitness st' y)
    (hys : y.suit = x.suit ∨ y.suit = x.twin.suit) :
    y.rank.toIdx = x.rank.toIdx ∧ (y = x ∨ y = x.twin) := by
  have hle := rankCeiling_of_oneFounding hone hwf hwf' h hcls x hx hy hys
  have hge := rankFloor_of_oneFounding hone hwf hwf' h hcls x hx hy hys
  have hrank : y.rank.toIdx = x.rank.toIdx := by omega
  exact ⟨hrank, sameFamily_samePair hys hrank⟩

/-- **THE CLASS THEOREM, ASSEMBLED.**  Cross-family from `CoverToken`,
same-family from `OneFounding`. -/
theorem fork_label_class_of_token_and_oneFounding
    (htok : CoverToken) (hone : OneFounding)
    {F G : State} (hwfF : F.WF) (hwfG : G.WF)
    (hcls : sameOrbitSetoid.r F G) {w v : Card}
    (hw : ForkWitness F w) (hv : ForkWitness G v) :
    v = w ∨ v = w.twin := by
  by_cases hcol : v.suit.color = w.suit.color
  · have hfam : v.suit = w.suit ∨ v.suit = w.twin.suit :=
      SeedKit.suit_family hcol
    exact (family_pairClass_of_oneFounding hone hwfF hwfG
      (forkState_iff.mpr ⟨w, hw⟩) hcls w hw hv hfam).2
  · exfalso
    exact crossFamily_rigid_of_token htok hwfF hwfG hcls hw hv hcol

/-- **THE TWIN-PAIR FOUNDS AGREE.**  The class theorem pins the witness
pair; the rung pins then force the two pair-suit foundation rows to agree
card-for-card.  This is two of the four foundation rows — the two suits
of the twin pair itself — NOT the full `found` vector.  The other two
suits are the third-suit residue `hthird`
(`Orig/PairClassZones.lean:124`); they are not covered here. -/
theorem twinPair_founds_of_token_and_oneFounding
    (htok : CoverToken) (hone : OneFounding)
    {F G : State} (hwfF : F.WF) (hwfG : G.WF)
    (hcls : sameOrbitSetoid.r F G) {w v : Card}
    (hw : ForkWitness F w) (hv : ForkWitness G v) :
    F.found w.suit = G.found w.suit ∧
      F.found w.twin.suit = G.found w.twin.suit := by
  have hpair :=
    fork_label_class_of_token_and_oneFounding htok hone hwfF hwfG hcls hw hv
  obtain ⟨hw1, hw2⟩ := forkState_witness_rungs hw
  obtain ⟨hv1, hv2⟩ := forkState_witness_rungs hv
  have hGs : rungAt G w.suit = w.rank.toIdx := by
    rcases hpair with h | h
    · rw [h] at hv1; exact hv1
    · rw [h] at hv2
      rw [tfc_card_twin_twin, Card.twin_rank] at hv2
      exact hv2
  have hGt : rungAt G w.twin.suit = w.rank.toIdx := by
    rcases hpair with h | h
    · rw [h] at hv2; exact hv2
    · rw [h] at hv1
      rw [Card.twin_rank] at hv1
      exact hv1
  exact ⟨found_congr_of_rungs hwfF hwfG (hw1.trans hGs.symm),
    found_congr_of_rungs hwfF hwfG (hw2.trans hGt.symm)⟩

/-! ## The battery -/

#print axioms sameFamily_samePair
#print axioms crossFamily_rigid_of_token
#print axioms rankCeiling_of_oneFounding
#print axioms rankFloor_of_oneFounding
#print axioms family_pairClass_of_oneFounding
#print axioms fork_label_class_of_token_and_oneFounding
#print axioms twinPair_founds_of_token_and_oneFounding