import Orig2.FloatOrbit
import Orig2.StepWF

/-!
# Orig2.AnchorRelabel — anchor symmetry

The tableau anchors are labels: relabeling them is an automorphism of the
move relation, not a legal play.  This card lands the relabeling action and
the search/placement equivariance rows (`pileOfTop`, `pileHolding`,
`canPlace`, pile/foundation updates, and the draw), which is the API a
quotient by anchor permutations rides.

The step equivariance and the `sameOrbit`/`RevEqW` transport are the next
rows of this card; the search rows below are already WF-exact.
-/

/-- A permutation of the seven tableau anchors, with an explicit inverse. -/
structure AnchorPerm where
  toFun : Anchor → Anchor
  invFun : Anchor → Anchor
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ a, toFun (invFun a) = a

namespace State

/-- Relabel the tableau anchors by `σ`. -/
def permute (σ : AnchorPerm) (st : State) : State :=
  { st with piles := fun a => st.piles (σ.invFun a) }

@[simp] theorem permute_piles (σ : AnchorPerm) (st : State) (a : Anchor) :
    (st.permute σ).piles (σ.toFun a) = st.piles a := by
  simp [State.permute, σ.left_inv]

end State

namespace Base

/-- Relabel the anchor face of a base. -/
def permute (σ : AnchorPerm) : Base → Base
  | Sum.inl a => Sum.inl (σ.toFun a)
  | Sum.inr z => Sum.inr z

end Base

namespace Move

/-- Relabel the anchor face of a move. -/
def permute (σ : AnchorPerm) : Move → Move
  | .draw => .draw
  | .wasteToFound c => .wasteToFound c
  | .wasteToTab c b => .wasteToTab c (b.permute σ)
  | .tabToFound c => .tabToFound c
  | .foundToTab c b => .foundToTab c (b.permute σ)
  | .tabToTab c b => .tabToTab c (b.permute σ)

end Move

/-- The top search is equivariant at WF states. -/
theorem State.pileOfTop_permute {σ : AnchorPerm} {st : State} (hwf : st.WF)
    {z : Card} {a : Anchor} :
    (st.permute σ).pileOfTop z = some (σ.toFun a) ↔ st.pileOfTop z = some a := by
  constructor
  · intro h
    have htop_a : (st.piles a).top = some z := by
      have h' : (st.permute σ).topOf (σ.toFun a) = some z :=
        of_decide_eq_true
          (firstWhere_sound (fun a' => decide ((st.permute σ).topOf a' = some z)) h)
      simpa [State.topOf, State.permute, σ.left_inv] using h'
    have hmem_a : z ∈ (st.piles a).faceUp := Pile.mem_of_top htop_a
    refine firstWhere_find (Anchor.mem_all a) (decide_eq_true (by simpa [State.topOf] using htop_a)) ?_
    · intro y _ hyne
      apply decide_false_of_not
      intro hy
      have hmem_y : z ∈ (st.piles y).faceUp := Pile.mem_of_top hy
      exact (mem_faceUp_unique hwf hmem_a y hyne).1 hmem_y
  · intro h
    have htop_a : (st.piles a).top = some z :=
      (pileOfTop_eq_some_iff hwf).mp h
    have hmem_a : z ∈ (st.piles a).faceUp := Pile.mem_of_top htop_a
    refine firstWhere_find (Anchor.mem_all (σ.toFun a))
      (decide_eq_true (by simpa [State.topOf, State.permute, σ.left_inv] using htop_a)) ?_
    · intro y _ hyne
      apply decide_false_of_not
      intro hy
      have htop_y : (st.piles (σ.invFun y)).top = some z := by
        simpa [State.topOf, State.permute] using hy
      have hyne' : σ.invFun y ≠ a := by
        intro hcon
        apply hyne
        calc y = σ.toFun (σ.invFun y) := (σ.right_inv y).symm
          _ = σ.toFun a := by rw [hcon]
      have hmem_y : z ∈ (st.piles (σ.invFun y)).faceUp := Pile.mem_of_top htop_y
      exact (mem_faceUp_unique hwf hmem_a (σ.invFun y) hyne').1 hmem_y

/-- The holding search is equivariant at WF states. -/
theorem State.pileHolding_permute {σ : AnchorPerm} {st : State} (hwf : st.WF)
    {c : Card} {a : Anchor} :
    (st.permute σ).pileHolding c = some (σ.toFun a) ↔ st.pileHolding c = some a := by
  constructor
  · intro h
    have hmem : c ∈ (st.piles a).faceUp := by
      have h' : c ∈ ((st.permute σ).piles (σ.toFun a)).faceUp := pileHolding_mem h
      simpa [State.permute, σ.left_inv] using h'
    exact (pileHolding_eq_some_iff hwf).mpr hmem
  · intro h
    have hmem : c ∈ (st.piles a).faceUp := pileHolding_mem h
    refine firstWhere_find (Anchor.mem_all (σ.toFun a))
      (decide_eq_true (by simpa [State.permute, σ.left_inv] using hmem)) ?_
    · intro y _ hyne
      apply decide_false_of_not
      intro hy
      have hy' : c ∈ (st.piles (σ.invFun y)).faceUp := by
        simpa [State.permute] using hy
      have hyne' : σ.invFun y ≠ a := by
        intro hcon
        apply hyne
        calc y = σ.toFun (σ.invFun y) := (σ.right_inv y).symm
          _ = σ.toFun a := by rw [hcon]
      exact (mem_faceUp_unique hwf hmem (σ.invFun y) hyne').1 hy'

/-- The top search maps through the anchor permutation. -/
theorem State.pileOfTop_permute_option {σ : AnchorPerm} {st : State} (hwf : st.WF)
    {z : Card} :
    (st.permute σ).pileOfTop z = (st.pileOfTop z).map (fun a => σ.toFun a) := by
  cases h : st.pileOfTop z with
  | none =>
      have h' : (st.permute σ).pileOfTop z = none := by
        cases hp : (st.permute σ).pileOfTop z with
        | none => rfl
        | some y =>
            have hy : st.pileOfTop z = some (σ.invFun y) := by
              have hsome : (st.permute σ).pileOfTop z = some (σ.toFun (σ.invFun y)) := by
                simpa [σ.right_inv] using hp
              exact (State.pileOfTop_permute (σ := σ) (z := z) hwf
                (a := σ.invFun y)).mp hsome
            rw [h] at hy
            exact absurd hy (by simp)
      simp [h']
  | some a =>
      have h' : (st.permute σ).pileOfTop z = some (σ.toFun a) :=
        (State.pileOfTop_permute (σ := σ) (z := z) hwf (a := a)).mpr h
      simp [h']

/-- The holding search maps through the anchor permutation. -/
theorem State.pileHolding_permute_option {σ : AnchorPerm} {st : State} (hwf : st.WF)
    {c : Card} :
    (st.permute σ).pileHolding c = (st.pileHolding c).map (fun a => σ.toFun a) := by
  cases h : st.pileHolding c with
  | none =>
      have h' : (st.permute σ).pileHolding c = none := by
        cases hp : (st.permute σ).pileHolding c with
        | none => rfl
        | some y =>
            have hy : st.pileHolding c = some (σ.invFun y) := by
              have hsome : (st.permute σ).pileHolding c = some (σ.toFun (σ.invFun y)) := by
                simpa [σ.right_inv] using hp
              exact (State.pileHolding_permute (σ := σ) (c := c) hwf
                (a := σ.invFun y)).mp hsome
            rw [h] at hy
            exact absurd hy (by simp)
      simp [h']
  | some a =>
      have h' : (st.permute σ).pileHolding c = some (σ.toFun a) :=
        (State.pileHolding_permute (σ := σ) (c := c) hwf (a := a)).mpr h
      simp [h']

/-- Pile updates commute with anchor relabeling. -/
theorem State.permute_setPile (σ : AnchorPerm) (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).permute σ = (st.permute σ).setPile (σ.toFun a) p := by
  apply State.ext
  · simp [State.permute, State.setPile]
  · funext b
    by_cases hb : b = σ.toFun a
    · subst hb; simp [State.permute, State.setPile, σ.left_inv]
    · have hb' : σ.invFun b ≠ a := by
        intro hcon
        apply hb
        calc b = σ.toFun (σ.invFun b) := (σ.right_inv b).symm
          _ = σ.toFun a := by rw [hcon]
      simp [State.permute, State.setPile, hb, hb']
  · simp [State.permute, State.setPile]
  · simp [State.permute, State.setPile]
  · simp [State.permute, State.setPile]

/-- Foundation updates commute with anchor relabeling. -/
theorem State.permute_setFound (σ : AnchorPerm) (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).permute σ = (st.permute σ).setFound s l := by
  ext <;> simp [State.permute, State.setFound]

/-- Placing a card commutes with anchor relabeling. -/
theorem State.permute_putCard {σ : AnchorPerm} {st : State} (hwf : st.WF)
    (c : Card) (b : Base) :
    (st.putCard c b).permute σ = (st.permute σ).putCard c (b.permute σ) := by
  cases b with
  | inl a =>
      simp [State.putCard, Base.permute, State.permute_setPile]
  | inr z =>
      have hmap := State.pileOfTop_permute_option (σ := σ) hwf (z := z)
      cases h : st.pileOfTop z with
      | none =>
          simp [State.putCard, Base.permute, h, hmap]
      | some a =>
          simp [State.putCard, Base.permute, h, hmap, State.permute_setPile]

/-- Placing a run commutes with anchor relabeling. -/
theorem State.permute_putRun {σ : AnchorPerm} {st : State} (hwf : st.WF)
    (run : List Card) (b : Base) :
    (st.putRun run b).permute σ = (st.permute σ).putRun run (b.permute σ) := by
  cases b with
  | inl a =>
      simp [State.putRun, Base.permute, State.permute_setPile]
  | inr z =>
      have hmap := State.pileOfTop_permute_option (σ := σ) hwf (z := z)
      cases h : st.pileOfTop z with
      | none =>
          simp [State.putRun, Base.permute, h, hmap]
      | some a =>
          simp [State.putRun, Base.permute, h, hmap, State.permute_setPile]

/-- Placement legality is equivariant. -/
theorem State.canPlace_permute {σ : AnchorPerm} {st : State} (hwf : st.WF)
    {c : Card} {b : Base} :
    (st.permute σ).canPlace c (b.permute σ) ↔ st.canPlace c b := by
  cases b with
  | inl a =>
      simp [State.canPlace, Base.permute, State.permute, σ.left_inv]
  | inr z =>
      have hmap := State.pileOfTop_permute_option (σ := σ) hwf (z := z)
      cases h : st.pileOfTop z with
      | none => simp [State.canPlace, Base.permute, h, hmap]
      | some a => simp [State.canPlace, Base.permute, h, hmap]

namespace AnchorPerm

/-- The identity anchor permutation. -/
def id : AnchorPerm where
  toFun := fun a => a
  invFun := fun a => a
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The inverse anchor permutation. -/
def symm (σ : AnchorPerm) : AnchorPerm where
  toFun := σ.invFun
  invFun := σ.toFun
  left_inv := σ.right_inv
  right_inv := σ.left_inv

/-- Composition: first `σ`, then `τ`. -/
def comp (τ σ : AnchorPerm) : AnchorPerm where
  toFun := fun a => τ.toFun (σ.toFun a)
  invFun := fun a => σ.invFun (τ.invFun a)
  left_inv := by
    intro a
    rw [τ.left_inv, σ.left_inv]
  right_inv := by
    intro a
    rw [σ.right_inv, τ.right_inv]

end AnchorPerm

@[simp] theorem State.permute_id (st : State) : st.permute AnchorPerm.id = st := by
  apply State.ext <;> simp [State.permute, AnchorPerm.id]

theorem State.permute_comp (τ σ : AnchorPerm) (st : State) :
    (st.permute σ).permute τ = st.permute (τ.comp σ) := by
  apply State.ext <;> simp [State.permute, AnchorPerm.comp]

theorem State.permute_symm_permute (σ : AnchorPerm) (st : State) :
    (st.permute σ).permute (AnchorPerm.symm σ) = st := by
  apply State.ext
  · simp [State.permute, AnchorPerm.symm]
  · funext a
    simp [State.permute, AnchorPerm.symm, σ.left_inv]
  · simp [State.permute, AnchorPerm.symm]
  · simp [State.permute, AnchorPerm.symm]
  · simp [State.permute, AnchorPerm.symm]

theorem State.permute_injective (σ : AnchorPerm) : Function.Injective (State.permute σ) := by
  intro a b h
  have h' := congrArg (State.permute (AnchorPerm.symm σ)) h
  simpa [State.permute_symm_permute] using h'

/-- Recycling commutes with anchor relabeling. -/
theorem State.permute_recycle (σ : AnchorPerm) (st : State) :
    st.recycle.permute σ = (st.permute σ).recycle := by
  unfold State.recycle
  cases hstock : st.stock <;> cases hwaste : st.waste <;>
    simp [State.permute, hstock, hwaste]

/-- Dealing from the stock commutes with anchor relabeling. -/
theorem State.permute_dealStock (σ : AnchorPerm) (st : State) :
    st.dealStock.map (fun s => s.permute σ) = (st.permute σ).dealStock := by
  unfold State.dealStock
  cases hstock : st.stock <;> simp [State.permute, hstock]

/-- The draw commutes with anchor relabeling. -/
theorem State.permute_stepDraw (σ : AnchorPerm) (st : State) :
    st.stepDraw.map (fun s => s.permute σ) = (st.permute σ).stepDraw := by
  unfold State.stepDraw
  rw [State.permute_dealStock σ st.recycle]
  rw [State.permute_recycle]


/-- The foundation-advance guard is anchor-blind. -/
theorem State.nextUp_permute (σ : AnchorPerm) (st : State) (c : Card) :
    (st.permute σ).nextUp c = st.nextUp c := rfl

/-- The waste-top guard is anchor-blind. -/
theorem State.wasteIs_permute (σ : AnchorPerm) (st : State) (c : Card) :
    (st.permute σ).wasteIs c = st.wasteIs c := rfl

/-- Placement legality transports as a Boolean equality. -/
theorem State.canPlace_permute_eq {σ : AnchorPerm} {st : State} (hwf : st.WF)
    (c : Card) (b : Base) :
    (st.permute σ).canPlace c (b.permute σ) = st.canPlace c b := by
  cases h : st.canPlace c b with
  | false =>
      have h' : ¬ ((st.permute σ).canPlace c (b.permute σ) = true) := by
        intro hc
        exact absurd ((State.canPlace_permute (σ := σ) hwf (c := c) (b := b)).mp hc)
          (by rw [h]; simp)
      cases hc : (st.permute σ).canPlace c (b.permute σ) with
      | false => rfl
      | true => exact absurd hc h'
  | true =>
      have h' := (State.canPlace_permute (σ := σ) hwf (c := c) (b := b)).mpr h
      cases hc : (st.permute σ).canPlace c (b.permute σ) with
      | false => rw [h'] at hc; exact absurd hc (by simp)
      | true => rfl


#print axioms State.pileOfTop_permute
#print axioms State.pileHolding_permute
#print axioms State.pileOfTop_permute_option
#print axioms State.pileHolding_permute_option
#print axioms State.permute_setPile
#print axioms State.permute_setFound
#print axioms State.permute_putCard
#print axioms State.permute_putRun
#print axioms State.canPlace_permute
#print axioms State.canPlace_permute_eq
#print axioms State.nextUp_permute
#print axioms State.wasteIs_permute
#print axioms State.permute_recycle
#print axioms State.permute_dealStock
#print axioms State.permute_stepDraw
#print axioms State.permute_symm_permute
#print axioms State.permute_injective

/-- The anchor-relabeling relation: states are identified when they differ by
an anchor permutation.  This is the relation the quotient rides; the
`sameOrbitSetoid` compatibility row is the next lemma of the card. -/
def AnchorRelabelSetoid : Setoid State where
  r st w := ∃ σ : AnchorPerm, w = st.permute σ
  iseqv := by
    constructor
    · intro st
      exact ⟨AnchorPerm.id, by simp⟩
    · intro st w h
      obtain ⟨σ, rfl⟩ := h
      refine ⟨AnchorPerm.symm σ, ?_⟩
      exact (State.permute_symm_permute σ st).symm
    · intro st w z h1 h2
      obtain ⟨σ, rfl⟩ := h1
      obtain ⟨τ, rfl⟩ := h2
      refine ⟨τ.comp σ, ?_⟩
      exact (State.permute_comp τ σ st).symm

/-- The state space modulo anchor relabeling. -/
def AnchorQuot : Type := Quotient AnchorRelabelSetoid

#print axioms AnchorRelabelSetoid

@[simp] theorem State.permute_found (σ : AnchorPerm) (st : State) :
    (st.permute σ).found = st.found := rfl

@[simp] theorem State.permute_stock (σ : AnchorPerm) (st : State) :
    (st.permute σ).stock = st.stock := rfl

@[simp] theorem State.permute_waste (σ : AnchorPerm) (st : State) :
    (st.permute σ).waste = st.waste := rfl

@[simp] theorem State.permute_drawStep (σ : AnchorPerm) (st : State) :
    (st.permute σ).drawStep = st.drawStep := rfl

@[simp] theorem State.permute_with_waste (σ : AnchorPerm) (st : State) (ws : List Card) :
    ({ st with waste := ws } : State).permute σ = { st.permute σ with waste := ws } := rfl

theorem State.permute_putCard_waste {σ : AnchorPerm} {st : State} (hwf : st.WF)
    (c : Card) (b : Base) (ws : List Card) :
    ({ st.putCard c b with waste := ws } : State).permute σ =
      { (st.permute σ).putCard c (b.permute σ) with waste := ws } := by
  rw [State.permute_with_waste]
  rw [State.permute_putCard (σ := σ) (st := st) hwf c b]
theorem step_wasteToFound_permute_option (σ : AnchorPerm) (st : State) (c : Card) :
    (st.permute σ).step (.wasteToFound c) =
      (st.step (.wasteToFound c)).map (fun s => s.permute σ) := by
  rw [State.step.eq_2, State.step.eq_2]
  cases hw : st.waste with
  | nil =>
      rw [State.permute_waste, hw]
      simp
  | cons head ws =>
      by_cases hg : (st.wasteIs c && st.nextUp c) = true
      · have hg' : ((st.permute σ).wasteIs c && (st.permute σ).nextUp c) = true := by
          simpa [State.wasteIs_permute, State.nextUp_permute] using hg
        rw [ite_eq_left hg, ite_eq_left hg']
        rw [State.permute_waste, hw]
        simp only [Option.map_some]
        congr 1
      · have hg' : ((st.permute σ).wasteIs c && (st.permute σ).nextUp c) = false := by
          simpa [State.wasteIs_permute, State.nextUp_permute] using hg
        rw [ite_eq_right hg]
        rw [hg']
        simp


theorem step_wasteToTab_permute_option {σ : AnchorPerm} {st : State} (hwf : st.WF)
    (c : Card) (b : Base) :
    (st.permute σ).step (.wasteToTab c (b.permute σ)) =
      (st.step (.wasteToTab c b)).map (fun s => s.permute σ) := by
  rw [State.step.eq_3, State.step.eq_3]
  cases hw : st.waste with
  | nil =>
      rw [State.permute_waste, hw]
      simp
  | cons head ws =>
      by_cases hg : (st.wasteIs c && st.canPlace c b) = true
      · have hcp : (st.permute σ).canPlace c (b.permute σ) = st.canPlace c b :=
          State.canPlace_permute_eq hwf c b
        have hg' : ((st.permute σ).wasteIs c &&
            (st.permute σ).canPlace c (b.permute σ)) = true := by
          simpa [State.wasteIs_permute, hcp] using hg
        rw [ite_eq_left hg, ite_eq_left hg']
        rw [State.permute_waste, hw]
        simp only [Option.map_some]
        congr 1
        exact (State.permute_putCard_waste (σ := σ) (st := st) hwf c b ws).symm
      · have hcp : (st.permute σ).canPlace c (b.permute σ) = st.canPlace c b :=
          State.canPlace_permute_eq hwf c b
        have hg' : ((st.permute σ).wasteIs c &&
            (st.permute σ).canPlace c (b.permute σ)) = false := by
          simpa [State.wasteIs_permute, hcp] using hg
        rw [ite_eq_right hg]
        rw [hg']
        simp


theorem State.permute_tabToFound_update (σ : AnchorPerm) (st : State) (a : Anchor)
    (p : Pile) (s : Suit) (l : List Card) :
    ({ st.setFound s l with
        piles := fun a' => if a' = a then p else st.piles a' } : State).permute σ =
      { (st.permute σ).setFound s l with
        piles := fun a' => if a' = σ.toFun a then p else (st.permute σ).piles a' } := by
  have h1 : ({ st.setFound s l with
        piles := fun a' => if a' = a then p else st.piles a' } : State) =
      (st.setPile a p).setFound s l := rfl
  rw [h1, State.permute_setFound, State.permute_setPile]
  rfl

theorem step_tabToFound_permute_option {σ : AnchorPerm} {st : State} (hwf : st.WF)
    (c : Card) :
    (st.permute σ).step (.tabToFound c) =
      (st.step (.tabToFound c)).map (fun s => s.permute σ) := by
  rw [State.step.eq_4, State.step.eq_4]
  by_cases hg : st.nextUp c = true
  · have hg' : (st.permute σ).nextUp c = true := by
      simpa [State.nextUp_permute] using hg
    rw [ite_eq_left hg, ite_eq_left hg']
    cases hp : st.pileOfTop c with
    | none =>
        have hp' : (st.permute σ).pileOfTop c = none := by
          rw [State.pileOfTop_permute_option (σ := σ) hwf, hp]
          rfl
        rw [hp']
        simp
    | some a =>
        have hp' : (st.permute σ).pileOfTop c = some (σ.toFun a) := by
          rw [State.pileOfTop_permute_option (σ := σ) hwf, hp]
          rfl
        rw [hp']
        simp only [Option.map_some, State.permute_piles]
        congr 1
        exact (State.permute_tabToFound_update σ st a
          ((st.piles a).afterRunRemoved (chop (st.piles a).faceUp))
          c.suit (st.found c.suit ++ [c])).symm
  · have hg' : (st.permute σ).nextUp c = false := by
      simpa [State.nextUp_permute] using hg
    rw [ite_eq_right hg]
    rw [hg']
    simp



@[simp] theorem State.setFound_pileOfTop (st : State) (s : Suit) (l : List Card) (z : Card) :
    (st.setFound s l).pileOfTop z = st.pileOfTop z := rfl

@[simp] theorem State.setFound_pileHolding (st : State) (s : Suit) (l : List Card) (c : Card) :
    (st.setFound s l).pileHolding c = st.pileHolding c := rfl

theorem State.setFound_putCard (st : State) (s : Suit) (l : List Card) (c : Card) (b : Base) :
    (st.setFound s l).putCard c b = (st.putCard c b).setFound s l := by
  cases b with
  | inl a => simp [State.putCard, State.setPile, State.setFound]
  | inr z =>
      simp only [State.putCard, State.setPile, State.setFound_pileOfTop]
      cases st.pileOfTop z <;> simp [State.setFound]
theorem step_foundToTab_permute_option {σ : AnchorPerm} {st : State} (hwf : st.WF)
    (c : Card) (b : Base) :
    (st.permute σ).step (.foundToTab c (b.permute σ)) =
      (st.step (.foundToTab c b)).map (fun s => s.permute σ) := by
  rw [State.step.eq_5, State.step.eq_5]
  have hf : (st.permute σ).foundTop c.suit = st.foundTop c.suit := rfl
  rw [hf]
  cases hft : st.foundTop c.suit with
  | none =>
      simp
  | some c' =>
      dsimp only
      by_cases hg : (decide (c' = c) && st.canPlace c b) = true
      · have hcp : (st.permute σ).canPlace c (b.permute σ) = st.canPlace c b :=
          State.canPlace_permute_eq hwf c b
        have hg' : (decide (c' = c) &&
            (st.permute σ).canPlace c (b.permute σ)) = true := by
          simpa [hcp] using hg
        rw [ite_eq_left hg, ite_eq_left hg']
        simp only [Option.map_some]
        congr 1
        rw [State.setFound_putCard]
        rw [State.setFound_putCard]
        rw [State.permute_setFound, State.permute_putCard (σ := σ) (st := st) hwf c b]
        rfl
      · have hcp : (st.permute σ).canPlace c (b.permute σ) = st.canPlace c b :=
          State.canPlace_permute_eq hwf c b
        have hg' : (decide (c' = c) &&
            (st.permute σ).canPlace c (b.permute σ)) = false := by
          simpa [hcp] using hg
        rw [ite_eq_right hg]
        rw [hg']
        simp




#print axioms step_wasteToFound_permute_option
#print axioms step_wasteToTab_permute_option
#print axioms step_tabToFound_permute_option
#print axioms step_foundToTab_permute_option

/-- `firstWhere` respects pointwise-equal predicates. -/
theorem firstWhere_congr_local {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ a, p a = q a) : firstWhere p l = firstWhere q l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [firstWhere, h x, ih]

/-- Editing a pile leaves the `pileOfTop` search for a card that is in neither
the old nor the new pile untouched. -/
theorem State.setPile_pileOfTop_of_not_mem {st : State} {a : Anchor} {p : Pile}
    {z : Card} (hnew : z ∉ p.faceUp) (hold : z ∉ (st.piles a).faceUp) :
    (st.setPile a p).pileOfTop z = st.pileOfTop z := by
  unfold State.pileOfTop
  apply firstWhere_congr_local
  intro j
  by_cases hja : j = a
  · rw [hja]
    have hp : p.top ≠ some z := fun h => hnew (Pile.mem_of_top h)
    have hq : (st.piles a).top ≠ some z := fun h => hold (Pile.mem_of_top h)
    simp [State.setPile, State.topOf, hp, hq]
  · change decide ((if j = a then p else st.piles j).top = some z) =
      decide ((st.piles j).top = some z)
    simp [hja]

theorem State.putRun_inr_eq_setPile {st : State} {run : List Card} {z : Card} {k : Anchor}
    (hk : st.pileOfTop z = some k) :
    st.putRun run (Sum.inr z) = st.setPile k
      { hidden := (st.piles k).hidden, faceUp := (st.piles k).faceUp ++ run } := by
  rw [State.putRun.eq_2, hk]

theorem State.permute_tabToTab_final {σ : AnchorPerm} {st : State} (_hwf : st.WF)
    {a : Anchor} {p : Pile} {run : List Card} {z : Card} {k : Anchor}
    (_hk : st.pileOfTop z = some k) (_hka : k ≠ a)
    (_hnew : z ∉ p.faceUp) (_hold : z ∉ (st.piles a).faceUp) :
    ((st.setPile a p).setPile k
        { hidden := (st.piles k).hidden, faceUp := (st.piles k).faceUp ++ run }).permute σ =
      ((st.permute σ).setPile (σ.toFun a) p).setPile (σ.toFun k)
        { hidden := ((st.permute σ).piles (σ.toFun k)).hidden,
          faceUp := ((st.permute σ).piles (σ.toFun k)).faceUp ++ run } := by
  rw [State.permute_setPile]
  rw [State.permute_setPile]
  simp [State.permute_piles]
theorem State.permute_tabToTab_final_inl (σ : AnchorPerm) (st : State) (a : Anchor)
    (p : Pile) (run : List Card) (a' : Anchor) :
    ((st.setPile a p).setPile a' { hidden := [], faceUp := run }).permute σ =
      ((st.permute σ).setPile (σ.toFun a) p).setPile (σ.toFun a')
        { hidden := [], faceUp := run } := by
  rw [State.permute_setPile, State.permute_setPile]

theorem step_tabToTab_permute_option {σ : AnchorPerm} {st : State} (hwf : st.WF)
    (c : Card) (b : Base) :
    (st.permute σ).step (.tabToTab c (b.permute σ)) =
      (st.step (.tabToTab c b)).map (fun s => s.permute σ) := by
  rw [State.step.eq_6, State.step.eq_6]
  cases hp : st.pileHolding c with
  | none =>
      have hp' : (st.permute σ).pileHolding c = none := by
        rw [State.pileHolding_permute_option (σ := σ) hwf, hp]
        rfl
      rw [hp']
      simp
  | some a =>
      have hp' : (st.permute σ).pileHolding c = some (σ.toFun a) := by
        rw [State.pileHolding_permute_option (σ := σ) hwf, hp]
        rfl
      rw [hp']
      dsimp only
      by_cases hcp : st.canPlace c b = true
      · have hcp' : (st.permute σ).canPlace c (b.permute σ) = true := by
          rw [State.canPlace_permute_eq hwf c b]
          exact hcp
        rw [hcp, hcp']
        rw [State.permute_piles]
        cases hr : fromCard c (st.piles a).faceUp with
        | nil => simp
        | cons r rs =>
            simp only [ite_true, Option.map_some, Base.permute]
            congr 1
            cases b with
            | inl a' =>
                rw [State.putRun.eq_1]
                rw [State.putRun.eq_1]
                exact (State.permute_tabToTab_final_inl σ st a
                  ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))
                  (r :: rs) a').symm
            | inr z =>
                obtain ⟨k, hk, _⟩ := canPlace_inr hcp
                have hka : k ≠ a := by
                  intro hka
                  have hk' : st.pileOfTop z = some a := by
                    rw [← hka]
                    exact hk
                  exact (canPlace_inr_target_pile_ne hwf hcp (pileHolding_mem hp)) hk'
                have hz_face : z ∈ (st.piles k).faceUp :=
                  Pile.mem_of_top (pileOfTop_top hk).2
                have hold : z ∉ (st.piles a).faceUp :=
                  ((mem_faceUp_only hwf hz_face).1 a hka.symm).2
                have hnew : z ∉ ((st.piles a).afterRunRemoved
                    (below c (st.piles a).faceUp)).faceUp := by
                  intro hz
                  have hmem : z ∈ (st.piles a).hidden ++ (st.piles a).faceUp :=
                    tfc_mem_afterRunRemoved_below_zone (x := z) (c := c)
                      (p := st.piles a) (List.mem_append.mpr (Or.inr hz))
                  rcases List.mem_append.mp hmem with hzH | hzF
                  · exact ((mem_faceUp_only hwf hz_face).1 a hka.symm).1 hzH
                  · exact hold hzF
                have hsearchR : (st.setPile a
                    ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).pileOfTop z
                    = some k := by
                  rw [State.setPile_pileOfTop_of_not_mem hnew hold]
                  exact hk
                have hnotperm : z ∉ ((st.permute σ).piles (σ.toFun a)).faceUp := by
                  rw [State.permute_piles]
                  exact hold
                have hsearchL : ((st.permute σ).setPile (σ.toFun a)
                    ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).pileOfTop z
                    = some (σ.toFun k) := by
                  rw [State.setPile_pileOfTop_of_not_mem hnew hnotperm]
                  rw [State.pileOfTop_permute_option (σ := σ) hwf, hk]
                  rfl
                rw [State.putRun_inr_eq_setPile hsearchL]
                rw [State.putRun_inr_eq_setPile hsearchR]
                have hpile_k : (st.setPile a
                    ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles k
                    = st.piles k := by
                  simp [State.setPile, hka]
                have hsig : σ.toFun k ≠ σ.toFun a := by
                  intro h
                  apply hka
                  calc k = σ.invFun (σ.toFun k) := (σ.left_inv k).symm
                    _ = σ.invFun (σ.toFun a) := by rw [h]
                    _ = a := σ.left_inv a
                have hpile_sk : ((st.permute σ).setPile (σ.toFun a)
                    ((st.piles a).afterRunRemoved (below c (st.piles a).faceUp))).piles
                    (σ.toFun k) = (st.permute σ).piles (σ.toFun k) := by
                  simp [State.setPile, hsig]
                rw [hpile_k, hpile_sk]
                exact (State.permute_tabToTab_final (σ := σ) (st := st) (a := a)
                  (p := (st.piles a).afterRunRemoved (below c (st.piles a).faceUp))
                  (run := r :: rs) (z := z) (k := k) hwf hk hka hnew hold).symm
      · have hcf : st.canPlace c b = false := by
          cases h : st.canPlace c b <;> simp_all
        have hcf' : (st.permute σ).canPlace c (b.permute σ) = false := by
          rw [State.canPlace_permute_eq hwf c b]
          exact hcf
        rw [hcf, hcf']
        simp



#print axioms State.permute_tabToTab_final_inl
#print axioms State.permute_tabToTab_final
#print axioms State.putRun_inr_eq_setPile
#print axioms step_tabToTab_permute_option

/-- The full step commutes with anchor relabeling (all six letters). -/
theorem State.step_permute_option {σ : AnchorPerm} {st : State} (hwf : st.WF)
    (m : Move) :
    (st.permute σ).step (m.permute σ) = (st.step m).map (fun s => s.permute σ) := by
  cases m with
  | draw => exact (State.permute_stepDraw σ st).symm
  | wasteToFound c => exact step_wasteToFound_permute_option σ st c
  | wasteToTab c b => exact step_wasteToTab_permute_option hwf c b
  | tabToFound c => exact step_tabToFound_permute_option hwf c
  | foundToTab c b => exact step_foundToTab_permute_option hwf c b
  | tabToTab c b => exact step_tabToTab_permute_option hwf c b

/-- The step relation is equivariant as an iff. -/
theorem State.step_permute_iff {σ : AnchorPerm} {st : State} (hwf : st.WF)
    (m : Move) {st' : State} :
    (st.permute σ).step (m.permute σ) = some (st'.permute σ) ↔
      st.step m = some st' := by
  rw [State.step_permute_option hwf m]
  cases h : st.step m with
  | none => simp
  | some s =>
      simp only [Option.map_some, Option.some.injEq]
      exact ⟨fun hh => State.permute_injective σ hh, fun hh => by rw [hh]⟩

/-- Running a relabeled play is the relabeled run. -/
theorem State.run_permute_map {st : State} (hwf : st.WF) (σ : AnchorPerm)
    (ρ : List Move) :
    (st.permute σ).run (ρ.map (Move.permute σ)) =
      (st.run ρ).map (fun s => s.permute σ) := by
  induction ρ generalizing st with
  | nil => rfl
  | cons m ρ ih =>
      simp only [List.map_cons, State.run]
      cases hstep : st.step m with
      | none =>
          have hstep' : (st.permute σ).step (m.permute σ) = none := by
            rw [State.step_permute_option hwf m, hstep]
            rfl
          simp [hstep']
      | some s1 =>
          have hwf1 : s1.WF := step_wf hwf hstep
          have hstep' : (st.permute σ).step (m.permute σ) = some (s1.permute σ) := by
            rw [State.step_permute_option hwf m, hstep]
            rfl
          simp only [hstep']
          exact ih hwf1


/-- A reversible step relabels to a reversible step. -/
theorem reversibleAtW_permute {σ : AnchorPerm} {st : State} {m : Move}
    (hwf : st.WF) (hrev : reversibleAtW st m) :
    reversibleAtW (st.permute σ) (m.permute σ) := by
  obtain ⟨s1, play, hstep, hrun⟩ := hrev
  have hwf1 : s1.WF := step_wf hwf hstep
  refine ⟨s1.permute σ, play.map (Move.permute σ), ?_, ?_⟩
  · rw [State.step_permute_option hwf m, hstep]
    rfl
  · rw [State.run_permute_map hwf1 σ play, hrun]
    rfl

/-- A witness walk relabels to a witness walk. -/
theorem Walk_permute {P Q : State → Move → Prop} {σ : AnchorPerm}
    (hP : ∀ st m, st.WF → P st m → Q (st.permute σ) (m.permute σ))
    {st : State} {ρ : List Move} {W : State} (h : Walk P st ρ W) (hwf : st.WF) :
    Walk Q (st.permute σ) (ρ.map (Move.permute σ)) (W.permute σ) := by
  induction h with
  | nil s => exact Walk.nil (s.permute σ)
  | @cons st0 s1 W0 m0 ρ0 hlet hstep hrest ih =>
      have hlet' := hP st0 m0 hwf hlet
      have hstep' : (st0.permute σ).step (m0.permute σ) = some (s1.permute σ) := by
        rw [State.step_permute_option hwf m0, hstep]
        rfl
      have hwf1 : s1.WF := step_wf hwf hstep
      exact Walk.cons hlet' hstep' (ih hwf1)

/-- A witness shuffle relabels to a witness shuffle. -/
theorem ShufflePlayW_permute {σ : AnchorPerm} {st : State} {ρ : List Move} {W : State}
    (h : ShufflePlayW st ρ W) (hwf : st.WF) :
    ShufflePlayW (st.permute σ) (ρ.map (Move.permute σ)) (W.permute σ) :=
  Walk_permute (fun _ _ hwf hrev => reversibleAtW_permute hwf hrev) h hwf

/-- The witness-reversible pair relation is anchor-equivariant. -/
theorem RevEqW_permute {σ : AnchorPerm} {a b : State} (h : RevEqW a b) (hwf : a.WF) :
    RevEqW (a.permute σ) (b.permute σ) := by
  obtain ⟨ρ, hρ, τ, hτ⟩ := h
  have hbwf : b.WF := run_wf hwf
    (Walk_run (P := fun st m => reversibleAtW st m) (st := a) (W := b) hρ)
  exact ⟨ρ.map (Move.permute σ), ShufflePlayW_permute hρ hwf,
    τ.map (Move.permute σ), ShufflePlayW_permute hτ hbwf⟩

/-- The `sameOrbitSetoid` class relation is anchor-equivariant. -/
theorem sameOrbit_permute {σ : AnchorPerm} {a b : State}
    (h : sameOrbitSetoid.r a b) (hwf : a.WF) :
    sameOrbitSetoid.r (a.permute σ) (b.permute σ) := by
  show RevEqW (b.permute σ) (a.permute σ)
  obtain ⟨ρ, hρ, τ, hτ⟩ := h
  have hbwf : b.WF := run_wf hwf
    (Walk_run (P := fun st m => reversibleAtW st m) (st := a) (W := b) hτ)
  exact RevEqW_permute ⟨ρ, hρ, τ, hτ⟩ hbwf


/-- The diagonal anchor action on state pairs: both endpoints are relabeled by
the same permutation.  (Independent relabeling of the two endpoints does NOT
preserve `sameOrbit`; the diagonal action is the one that does.) -/
def AnchorRelabelPairSetoid : Setoid (State × State) where
  r p q := ∃ σ : AnchorPerm, q.1 = p.1.permute σ ∧ q.2 = p.2.permute σ
  iseqv := by
    constructor
    · intro p
      exact ⟨AnchorPerm.id, by simp, by simp⟩
    · intro p q h
      obtain ⟨σ, h1, h2⟩ := h
      refine ⟨AnchorPerm.symm σ, ?_, ?_⟩
      · rw [h1, State.permute_symm_permute]
      · rw [h2, State.permute_symm_permute]
    · intro p q r h1 h2
      obtain ⟨σ, hpq1, hpq2⟩ := h1
      obtain ⟨τ, hqr1, hqr2⟩ := h2
      refine ⟨τ.comp σ, ?_, ?_⟩
      · rw [hqr1, hpq1, State.permute_comp]
      · rw [hqr2, hpq2, State.permute_comp]

#print axioms State.step_permute_option
#print axioms State.step_permute_iff
#print axioms State.run_permute_map
#print axioms reversibleAtW_permute
#print axioms Walk_permute
#print axioms ShufflePlayW_permute
#print axioms RevEqW_permute
#print axioms sameOrbit_permute
#print axioms AnchorRelabelPairSetoid
