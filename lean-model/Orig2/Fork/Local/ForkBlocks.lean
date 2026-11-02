import Orig2.Fork.Class.ForkCanon
import Orig2.Fork.Local.ForkChain
import Orig2.Fork.CrossSuit.ForkFibreCorridor
import Orig2.Fork.Split.ForkBridge
import Orig2.Fork.Split.ForkTailHead

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2/ForkBlocks — excluding the three shapes of `Canon.canonical_obstruction`

Scratch card.  READ-ONLY on `Orig2/`; no source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `native_decide`; axiom battery at the tail.

## The target

`Canon.canonical_obstruction` (`Orig2/Fork/Class/ForkCanon.lean:563`) says that in a
canonical (shortest, min-`inv`) play an adjacent cross-suit pair
`raise c ; pull d b` (`c` topping pile `a` at the raise's origin `A`) has its
pull's landing site on the raise's own origin structure:

```text
b = inl a                                -- the raise emptied pile `a`
∨ b = inr c                              -- the pull lands on the raised card
∨ ∃ z, b = inr z ∧ A.pileOfTop z = none  -- the raise exposed `z` from pile `a`
```

This card excludes shape 2 outright and sharpens shapes 1 and 3 to exact
structural facts, showing they are the **seat-mate** (`SeatMate c d`) pairs:

* shape 1 ⟹ `A.piles a = ⟨[], [c]⟩` and BOTH `c`, `d` are kings;
* shape 3 ⟹ `d = c.twin` (and `z` is exposed *from pile `a`*, directly below
  `c` in the run).
-/

namespace Blocks

/-! ## §0. Pile helpers -/

/-- A pile is empty exactly when it holds nothing. -/
theorem isEmpty_eq_true_iff (p : Pile) :
    p.isEmpty = true ↔ p.hidden = [] ∧ p.faceUp = [] := by
  rcases p with ⟨hd, fu⟩
  cases hd <;> cases fu <;> simp [Pile.isEmpty]

/-- A pile with a nonempty face-up run is not empty. -/
theorem isEmpty_false_of_faceUp_ne {p : Pile} (h : p.faceUp ≠ []) :
    p.isEmpty = false := by
  cases hb : p.isEmpty with
  | false => rfl
  | true => exact absurd ((isEmpty_eq_true_iff p).mp hb).2 h

/-- The raise's pile is empty only when the origin pile was bare and empty. -/
theorem isEmpty_afterRunRemoved {p : Pile} {pre : List Card}
    (h : (Pile.afterRunRemoved p pre).isEmpty = true) : p.hidden = [] ∧ pre = [] := by
  rcases p with ⟨hd, fu⟩
  cases pre with
  | nil =>
      cases hd with
      | nil => exact ⟨rfl, rfl⟩
      | cons x xs =>
          simp [Pile.afterRunRemoved, Pile.revealTop, Pile.isEmpty] at h
  | cons w ws =>
      simp [Pile.afterRunRemoved, Pile.isEmpty] at h

/-- A pile whose face-up run is a singleton ending at `c` and whose hidden deck
is empty IS the bare seat `⟨[], [c]⟩`. -/
theorem pile_eq_bare_of_chop_nil {p : Pile} {c : Card}
    (hhid : p.hidden = []) (hchop : chop p.faceUp = [])
    (htop : lastOf p.faceUp = some c) : p = ⟨[], [c]⟩ := by
  have hface : p.faceUp = [c] := by
    calc p.faceUp = chop p.faceUp ++ [c] := lastOf_chop htop
      _ = [c] := by rw [hchop]; rfl
  exact Pile.ext hhid hface

/-- **The raise cell at a bare seat.**  If `c` tops pile `a` at `WF` with
`chop = []` (a bare exercise of `tabToFoundR`), then the hidden deck is empty
and `c` is a king. -/
theorem bare_cell_of_chop_nil {A : State} {c : Card} {a : Anchor}
    (hAwf : A.WF) (hnext : A.nextUp c = true) (hca : A.pileOfTop c = some a)
    (hrevR : reversibleAtW A (Move.tabToFound c))
    (hchop : chop (A.piles a).faceUp = []) :
    (A.piles a).hidden = [] ∧ c.rank = Rank.king := by
  have hR : tabToFoundR A c = true :=
    (tabToFoundR_iff_reversibleAtW hAwf c).mpr hrevR
  cases hh : (A.piles a).hidden with
  | nil =>
      simp only [tabToFoundR, hnext, hca, hchop, hh] at hR
      exact ⟨rfl, of_decide_eq_true hR⟩
  | cons x xs =>
      simp only [tabToFoundR, hnext, hca, hchop, hh] at hR
      exact absurd hR (by simp)

/-- **`B = raiseSt A c a` from the step.** -/
theorem eq_raiseSt_of_step {A B : State} {c : Card} {a : Anchor}
    (hnext : A.nextUp c = true) (hca : A.pileOfTop c = some a)
    (hstep : State.step A (Move.tabToFound c) = some B) : B = raiseSt A c a := by
  have h := step_tabToFound_splice hnext hca
  exact Option.some.inj (hstep.symm.trans h)

/-- The raise image's pile `a`. -/
theorem raiseSt_pile_a (A : State) (c : Card) (a : Anchor) :
    (raiseSt A c a).piles a =
      Pile.afterRunRemoved (A.piles a) (chop (A.piles a).faceUp) := by
  rw [raiseSt_piles_apply, ite_eq_left rfl]

/-- Two colours both different from a third are equal. -/
theorem color_eq_of_ne_ne {a b z : Color} (h1 : a ≠ z) (h2 : b ≠ z) : a = b := by
  cases a <;> cases b <;> cases z <;> simp_all

/-- Two different suits of the same colour are twins. -/
theorem eq_twin_of_color_eq_ne {s t : Suit} (hcol : s.color = t.color) (hne : s ≠ t) :
    t = s.twin := by
  cases s <;> cases t <;> simp_all [Suit.color, Suit.twin]

/-- **Shape 2 is EMPTY.**  A pull landing on the raised card itself is
impossible: at the raise's image that card is the foundation top, hence not a
pile top, hence no legal `inr` base. -/
theorem ne_inr_raised {A B : State} {c d : Card} {b : Base}
    (hAwf : A.WF) (hstepR : State.step A (Move.tabToFound c) = some B)
    (hcp : B.canPlace d b = true) : b ≠ Sum.inr c := by
  intro hb
  obtain ⟨hnext, a, hca, -⟩ := step_tabToFound_inv hstepR
  have hB : B = raiseSt A c a := eq_raiseSt_of_step hnext hca hstepR
  have hBwf : B.WF := step_wf hAwf hstepR
  have hft : B.foundTop c.suit = some c := by
    rw [hB]; exact BaseEn.foundTop_raiseSt_self A c a
  have hnone : B.pileOfTop c = none := Canon.pileOfTop_none_of_found hBwf hft
  have hfalse : B.canPlace d (Sum.inr c) = false := by
    rw [canPlace_inr_eq, hnone]
  rw [hb] at hcp
  rw [hfalse] at hcp
  exact absurd hcp (by simp)

/-- **SHAPE 1, STRUCTURE.**  If the pull lands on the raise's own (now empty)
pile `a`, then that pile was the bare seat `⟨[], [c]⟩` and BOTH cards are kings. -/
theorem inl_shape {A B : State} {c d : Card} {a : Anchor}
    (hAwf : A.WF) (hrevR : reversibleAtW A (Move.tabToFound c))
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hca : A.pileOfTop c = some a)
    (hcp : B.canPlace d (Sum.inl a) = true) :
    A.piles a = ⟨[], [c]⟩ ∧ c.rank = Rank.king ∧ d.rank = Rank.king := by
  obtain ⟨hnext, a', hpo, -⟩ := step_tabToFound_inv hstepR
  have haa : a' = a := Option.some.inj (hpo.symm.trans hca)
  subst a'
  have hB : B = raiseSt A c a := eq_raiseSt_of_step hnext hca hstepR
  have hb := hcp
  rw [hB, canPlace_inl_unfold, Bool.and_eq_true] at hb
  obtain ⟨hemp, hdking⟩ := hb
  have hdking' : d.rank = Rank.king := of_decide_eq_true hdking
  rw [raiseSt_pile_a] at hemp
  obtain ⟨hhid, hchop⟩ := isEmpty_afterRunRemoved hemp
  have htop : lastOf (A.piles a).faceUp = some c := (pileOfTop_top hca).2
  have hbare : A.piles a = ⟨[], [c]⟩ := pile_eq_bare_of_chop_nil hhid hchop htop
  obtain ⟨-, hcking⟩ := bare_cell_of_chop_nil hAwf hnext hca hrevR hchop
  exact ⟨hbare, hcking, hdking'⟩

/-- **SHAPE 3, STRUCTURE.**  If the pull lands on a card `z` that the raise
exposed from pile `a`, then (a) `z` is indeed exposed *from pile `a`*, directly
below `c` in the face-up run, and (b) the two cards are twins. -/
theorem inr_expose_shape {A B : State} {c d z : Card} {a : Anchor}
    (hAwf : A.WF) (hrevR : reversibleAtW A (Move.tabToFound c))
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hca : A.pileOfTop c = some a) (hz : A.pileOfTop z = none)
    (hsu : c.suit ≠ d.suit)
    (hcp : B.canPlace d (Sum.inr z) = true) :
    B.pileOfTop z = some a ∧ d = c.twin ∧
      ∃ front : List Card, (A.piles a).faceUp = front ++ [z, c] := by
  obtain ⟨hnext, a', hpo, -⟩ := step_tabToFound_inv hstepR
  have haa : a' = a := Option.some.inj (hpo.symm.trans hca)
  subst a'
  have hB : B = raiseSt A c a := eq_raiseSt_of_step hnext hca hstepR
  have hBwf : B.WF := step_wf hAwf hstepR
  -- `z` is a pile top at the image
  obtain ⟨k, hk⟩ : ∃ k, B.pileOfTop z = some k := by
    cases h : B.pileOfTop z with
    | none =>
        rw [canPlace_inr_eq, h] at hcp
        exact absurd hcp (by simp)
    | some k => exact ⟨k, rfl⟩
  have hfitd : canSitOn d z = true := by
    rw [← canPlace_inr_located (st := B) (c := d) (z := z) hk]
    exact hcp
  -- and it is pile `a`
  have hka : k = a := by
    by_cases hne : k = a
    · exact hne
    · exfalso
      have hpiles : B.piles k = A.piles k := by
        rw [hB, raiseSt_piles_apply, ite_eq_right hne]
      have htopk : (B.piles k).top = some z := (pileOfTop_eq_some_iff hBwf).mp hk
      rw [hpiles] at htopk
      have hAtop : A.pileOfTop z = some k := (pileOfTop_eq_some_iff hAwf).mpr htopk
      rw [hz] at hAtop
      exact absurd hAtop (by simp)
  rw [hka] at hk
  have htopB : lastOf (B.piles a).faceUp = some z := (pileOfTop_top hk).2
  have hpile : B.piles a =
      Pile.afterRunRemoved (A.piles a) (chop (A.piles a).faceUp) := by
    rw [hB]; exact raiseSt_pile_a A c a
  rw [hpile] at htopB
  have htopC : lastOf (A.piles a).faceUp = some c := (pileOfTop_top hca).2
  have hface : (A.piles a).faceUp = chop (A.piles a).faceUp ++ [c] :=
    lastOf_chop htopC
  cases hchop : chop (A.piles a).faceUp with
  | nil =>
      exfalso
      obtain ⟨hhid, -⟩ := bare_cell_of_chop_nil hAwf hnext hca hrevR hchop
      rw [hchop, Pile.afterRunRemoved_bare hhid] at htopB
      simp [lastOf] at htopB
  | cons w ws =>
      have hchne : chop (A.piles a).faceUp ≠ [] := by rw [hchop]; simp
      rw [afterRunRemoved_ne hchne] at htopB
      have htopChop : lastOf (chop (A.piles a).faceUp) = some z := htopB
      obtain ⟨front, hfront⟩ := lastOf_eq_snoc htopChop
      have hfA : (A.piles a).faceUp = front ++ z :: c :: [] := by
        rw [hface, hfront]
        simp
      have hrun : runOK (A.piles a).faceUp = true := hAwf.2.1 a
      rw [hfA] at hrun
      have hcz : canSitOn c z = true := SeedKit.runOK_adjacent_fit z c front [] hrun
      -- two cards fitting on `z`, cross-suit, are twins
      obtain ⟨h1, h2⟩ := (canSitOn_eq c z).mp hcz
      obtain ⟨h3, h4⟩ := (canSitOn_eq d z).mp hfitd
      have hrank : d.rank = c.rank := by
        have hd : d.rank.toIdx = c.rank.toIdx := by omega
        exact Rank.toIdx_inj hd
      have hcol : c.suit.color = d.suit.color := color_eq_of_ne_ne h2 h4
      have hsuitt : d.suit = c.suit.twin := eq_twin_of_color_eq_ne hcol hsu
      have hdt : d = c.twin := by
        cases c with
        | mk cs cr =>
            cases d with
            | mk ds dr =>
                simp only [Card.twin, Card.mk.injEq]
                exact ⟨hsuitt, hrank⟩
      exact ⟨hk, hdt, front, hfA⟩

/-! ## §1. The seat-mate dichotomy at the raise's image -/

/-- **THE CORE DICHOTOMY.**  If the pull is illegal at the raise's origin (`A`)
but legal at the raise's image (`B = raiseSt A c a`), then the two cards are
**seat-mates**: either both are kings (the pull lands on the emptied pile `a`)
or the pull lands on a twin the raise exposed. -/
theorem seatMate_of_raise_image {A B : State} {c d : Card} {b : Base} {a : Anchor}
    (hAwf : A.WF) (hrevR : reversibleAtW A (Move.tabToFound c))
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hca : A.pileOfTop c = some a)
    (hno : A.canPlace d b = false)
    (hyes : B.canPlace d b = true)
    (hsu : c.suit ≠ d.suit) : SeatMate c d := by
  obtain ⟨hnext, a', hpo, -⟩ := step_tabToFound_inv hstepR
  have haa : a' = a := Option.some.inj (hpo.symm.trans hca)
  subst a'
  have hB : B = raiseSt A c a := eq_raiseSt_of_step hnext hca hstepR
  cases b with
  | inl j =>
      have hj : j = a := Canon.canPlace_inl_raise_true hno (by rw [← hB]; exact hyes)
      subst j
      obtain ⟨-, hck, hdk⟩ := inl_shape hAwf hrevR hstepR hca hyes
      exact Or.inl ⟨hck, hdk⟩
  | inr z =>
      rcases Canon.canPlace_inr_raise_true hno (by rw [← hB]; exact hyes) with hzc | hzn
      · exact absurd (by rw [hzc]) (ne_inr_raised hAwf hstepR hyes)
      · obtain ⟨-, hdt, -⟩ := inr_expose_shape hAwf hrevR hstepR hca hzn hsu hyes
        by_cases hk : c.rank = Rank.king
        · exact Or.inl ⟨hk, by rw [hdt, Card.twin_rank]; exact hk⟩
        · exact Or.inr ⟨hk, Or.inr hdt⟩

/-- **THE EXACT DICHOTOMY.**  The surviving cross-suit obstruction is exactly:
the pull lands on the raise's own (emptied) origin pile with both cards kings, or
it lands on a twin the raise exposed from that pile. -/
theorem raise_image_dichotomy {A B : State} {c d : Card} {b : Base} {a : Anchor}
    (hAwf : A.WF) (hrevR : reversibleAtW A (Move.tabToFound c))
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hca : A.pileOfTop c = some a)
    (hno : A.canPlace d b = false)
    (hyes : B.canPlace d b = true)
    (hsu : c.suit ≠ d.suit) :
    (∃ j, b = Sum.inl j ∧ A.piles j = ⟨[], [c]⟩ ∧ c.rank = Rank.king ∧
        d.rank = Rank.king)
      ∨ (∃ z, b = Sum.inr z ∧ A.pileOfTop z = none ∧ d = c.twin) := by
  obtain ⟨hnext, a', hpo, -⟩ := step_tabToFound_inv hstepR
  have haa : a' = a := Option.some.inj (hpo.symm.trans hca)
  subst a'
  have hB : B = raiseSt A c a := eq_raiseSt_of_step hnext hca hstepR
  cases b with
  | inl j =>
      have hj : j = a := Canon.canPlace_inl_raise_true hno (by rw [← hB]; exact hyes)
      subst j
      obtain ⟨hbare, hck, hdk⟩ := inl_shape hAwf hrevR hstepR hca hyes
      exact Or.inl ⟨a, rfl, hbare, hck, hdk⟩
  | inr z =>
      rcases Canon.canPlace_inr_raise_true hno (by rw [← hB]; exact hyes) with hzc | hzn
      · exact absurd (by rw [hzc]) (ne_inr_raised hAwf hstepR hyes)
      · obtain ⟨-, hdt, -⟩ := inr_expose_shape hAwf hrevR hstepR hca hzn hsu hyes
        exact Or.inr ⟨z, rfl, hzn, hdt⟩

/-! ## §2. The corridor form: the canonical geodesic's cross-suit corridors -/

/-- The raise letter's reversibility, read off the corridor play. -/
theorem rev_raise_of_corridor {u v A : State} {pre rest : List Move} {c : Card}
    (hplay : ShufflePlayW u (pre ++ (Move.tabToFound c :: rest)) v)
    (hpre : ShufflePlayW u pre A) : reversibleAtW A (Move.tabToFound c) := by
  obtain ⟨A', hpre', hrest⟩ :=
    ValleyElim.ShufflePlayW_split hplay pre (Move.tabToFound c :: rest) rfl
  have hAA : A' = A := by
    have h1 := Walk_run (fun st m => reversibleAtW st m) hpre'
    have h2 := Walk_run (fun st m => reversibleAtW st m) hpre
    exact Option.some.inj (h1.symm.trans h2)
  rw [hAA] at hrest
  cases hrest with
  | cons hrev _ _ => exact hrev

/-- **SHAPE 1's TAIL CANNOT START WITH `raise d`.**  A pull immediately followed
by a raise of the pulled card is a two-letter loop, deleted by
`Bridge.adjacent_same_turn_shortens` (`ValleyStep.valley_cancel_same`). -/
theorem shape1_not_followed_by_raise {u v B : State} {pre post : List Move}
    {d : Card} {a : Anchor}
    (huwf : u.WF)
    (hplay : ShufflePlayW u
      (pre ++ (Move.foundToTab d (Sum.inl a) :: Move.tabToFound d :: post)) v)
    (hpre : ShufflePlayW u pre B)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v →
      (pre ++ (Move.foundToTab d (Sum.inl a) :: Move.tabToFound d :: post)).length
        ≤ ρ'.length) : False := by
  obtain ⟨ρ', hρ', hlen⟩ := Bridge.adjacent_same_turn_shortens huwf hpre hplay
  exact absurd (hmin ρ' hρ') (Nat.not_le.mpr hlen)

/-- **SHAPE 1's TAIL MUST COVER `d`.**  At the pull's landing the pulled card `d`
is raisable (`ValleyStep.pull_card_canRaise`), while the saturated endpoint
blocks it, so the tail carries a *first blocking letter* for `d` — one of the
four cover-obligation shapes of `Chain.blocking_letter_shape`: a raise of `d`, a
pull in `d`'s suit, a pull landing on `d`, or a slide landing on `d`. -/
theorem corridor_tail_cover_obligation
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base}
    (huwf : u.WF) (hv : SSaturated v) (hplay : ShufflePlayW u ρ v)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) :
    ∃ (B : State) (s1 s2 : List Move) (A Z : State) (m : Move),
      ShufflePlayW B tail v ∧ B.WF ∧ CanRaise B d ∧
      tail = s1 ++ m :: s2 ∧ ShufflePlayW B s1 A ∧ CanRaise A d ∧
      reversibleAtW A m ∧ State.step A m = some Z ∧ ¬ CanRaise Z d ∧
      (m = Move.tabToFound d ∨
        (∃ (c' : Card) (b' : Base), m = Move.foundToTab c' b' ∧
          (c'.suit = d.suit ∨ b' = Sum.inr d)) ∨
        (∃ x : Card, m = Move.tabToTab x (Sum.inr d))) := by
  have hp : ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) v := heq ▸ hplay
  have hp' : ShufflePlayW u
      ((pre ++ Move.tabToFound c :: γ) ++ Move.foundToTab d b :: tail) v := by
    simpa only [List.append_assoc, List.cons_append] using hp
  exact Chain.corridor_tail_blocker hp' huwf hv

/-- **THE CANONICAL CORRIDOR DICHOTOMY.**  In a canonical (shortest, min-`inv`)
play, a cross-suit free corridor's pull has shape 1 or shape 3 — and never
shape 2. -/
theorem canonical_corridor_dichotomy
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base} {A B : State}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
    (hpre : ShufflePlayW u pre A)
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hpullB : PullKit.Pullable B d b)
    (hfree : Canon.FreeOnly γ) (hsu : c.suit ≠ d.suit)
    (hread : ∀ q ∈ γ, SlideFwd.ReadSafe d q)
    (hseat : ∀ q ∈ γ, MtnPr.SeatInert b q)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v →
      ρ'.length = (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))).length →
      Canon.inv (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
        ≤ Canon.inv ρ') :
    A.canPlace d b = false ∧ b ≠ Sum.inr c ∧
      ((∃ j, b = Sum.inl j ∧ A.piles j = ⟨[], [c]⟩ ∧ c.rank = Rank.king ∧
          d.rank = Rank.king)
        ∨ (∃ z, b = Sum.inr z ∧ A.pileOfTop z = none ∧ d = c.twin)) := by
  have hplay' : ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) v := by
    rw [← heq]; exact hplay
  have hblock := Canon.canonical_free_corridor_blocked huwf hplay' hpre hstepR hpullB
    hfree hread hseat hsu hmin
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  have hne : b ≠ Sum.inr c := ne_inr_raised hAwf hstepR hpullB.2
  have hno : A.canPlace d b = false := by
    rcases hblock with h | h
    · exact h
    · exact absurd h hne
  have hrevR : reversibleAtW A (Move.tabToFound c) := rev_raise_of_corridor hplay' hpre
  obtain ⟨-, a, hca, -⟩ := step_tabToFound_inv hstepR
  exact ⟨hno, hne, raise_image_dichotomy hAwf hrevR hstepR hca hno hpullB.2 hsu⟩

/-- **THE SEAT-MATE FORM.**  `SeatMate` is the shadow of the dichotomy: kings
(shape 1) or twins (shape 3). -/
theorem canonical_corridor_seatMate
    {u v : State} {ρ pre γ tail : List Move} {c d : Card} {b : Base} {A B : State}
    (huwf : u.WF) (hplay : ShufflePlayW u ρ v)
    (heq : ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
    (hpre : ShufflePlayW u pre A)
    (hstepR : State.step A (Move.tabToFound c) = some B)
    (hpullB : PullKit.Pullable B d b)
    (hfree : Canon.FreeOnly γ) (hsu : c.suit ≠ d.suit)
    (hread : ∀ q ∈ γ, SlideFwd.ReadSafe d q)
    (hseat : ∀ q ∈ γ, MtnPr.SeatInert b q)
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v →
      ρ'.length = (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))).length →
      Canon.inv (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
        ≤ Canon.inv ρ') : SeatMate c d := by
  have hplay' : ShufflePlayW u
      (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))) v := by
    rw [← heq]; exact hplay
  have hAwf : A.WF := SatDifferCensus.ShufflePlayW.wf_end hpre huwf
  obtain ⟨hno, -, -⟩ := canonical_corridor_dichotomy huwf hplay heq hpre hstepR hpullB
    hfree hsu hread hseat hmin
  have hrevR : reversibleAtW A (Move.tabToFound c) := rev_raise_of_corridor hplay' hpre
  obtain ⟨-, a, hca, -⟩ := step_tabToFound_inv hstepR
  exact seatMate_of_raise_image hAwf hrevR hstepR hca hno hpullB.2 hsu

/-! ## §3. The ∃-form: the canonical geodesic strengthened -/

/-- **THE CANONICAL GEODESIC, SEAT-MATE FORM.**  Same statement as
`Canon.canonical_geodesic_obstruction`, with the conclusion strengthened from
the legality alternative to the structural dichotomy: every cross-suit free
corridor in the canonical geodesic carries a **seat-mate** pair, the pull is
illegal at the raise's origin, and the pull never lands on the raised card. -/
theorem canonical_geodesic_seatMate (u v : State) (huwf : u.WF)
    (hu : SSaturated u) (hv : SSaturated v) (hcls : sameOrbitSetoid.r u v) :
    ∃ ρ : List Move, ShufflePlayW u ρ v ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
        Canon.inv ρ ≤ Canon.inv ρ') ∧
      ∀ (pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
        ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
        Canon.FreeOnly γ → c.suit ≠ d.suit →
        ShufflePlayW u pre A → State.step A (Move.tabToFound c) = some B →
        PullKit.Pullable B d b →
        (∀ q ∈ γ, SlideFwd.ReadSafe d q) →
        (∀ q ∈ γ, MtnPr.SeatInert b q) →
        A.canPlace d b = false ∧ b ≠ Sum.inr c ∧ SeatMate c d := by
  obtain ⟨ρ, hplay, hminlen, hmininv⟩ := Canon.exists_canonical_play u v huwf hcls
  refine ⟨ρ, hplay, hminlen, hmininv, ?_⟩
  intro pre γ tail c d b A B heq hfree hsu hpre hstepR hpullB hread hseat
  have hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v →
      ρ'.length = (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail)))).length →
      Canon.inv (pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))))
        ≤ Canon.inv ρ' := by
    intro ρ' hρ' hlen'
    have hρlen : ρ'.length = ρ.length := hlen'.trans (congrArg List.length heq.symm)
    rw [← heq]
    exact hmininv ρ' hρ' hρlen
  have hd := canonical_corridor_dichotomy huwf hplay heq hpre hstepR hpullB hfree hsu
    hread hseat hmin
  obtain ⟨hno, hne, hdisj⟩ := hd
  refine ⟨hno, hne, ?_⟩
  rcases hdisj with ⟨j, hb, -, hck, hdk⟩ | ⟨z, hb, -, hdt⟩
  · exact Or.inl ⟨hck, hdk⟩
  · by_cases hk : c.rank = Rank.king
    · exact Or.inl ⟨hk, by rw [hdt, Card.twin_rank]; exact hk⟩
    · exact Or.inr ⟨hk, Or.inr hdt⟩

/-! ## §4. The surviving shape, named

The two residuals below are exactly what is left: shape 1 (`b = inl a`: the pull
lands on the raise's empties origin pile — both cards kings) and shape 3
(`b = inr z` with `A.pileOfTop z = none`: the pull lands on a twin the raise
exposed).  `NoSeatMateCrossSuit` is their common shadow, and
`noSeatMate_iff_shapes` says the three are the same statement. -/

/-- Shape 1, as a surviving exclusion: no canonical cross-suit corridor's pull
lands on an `inl` base. -/
def NoInlOrigin : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
      Canon.inv ρ ≤ Canon.inv ρ') →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit → ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B → PullKit.Pullable B d b →
    (∀ q ∈ γ, SlideFwd.ReadSafe d q) → (∀ q ∈ γ, MtnPr.SeatInert b q) →
    (∃ a, b = Sum.inl a) → False

/-- Shape 3, as a surviving exclusion: no canonical cross-suit corridor's pull
lands on an `inr` base. -/
def NoExposeBase : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
      Canon.inv ρ ≤ Canon.inv ρ') →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit → ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B → PullKit.Pullable B d b →
    (∀ q ∈ γ, SlideFwd.ReadSafe d q) → (∀ q ∈ γ, MtnPr.SeatInert b q) →
    (∃ z, b = Sum.inr z) → False

/-- **`NoSeatMateCrossSuit`** — the exact surviving shape: a canonical
cross-suit free corridor whose two cards are seat-mates (twins or two kings). -/
def NoSeatMateCrossSuit : Prop :=
  ∀ (u v : State) (ρ pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
      Canon.inv ρ ≤ Canon.inv ρ') →
    ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
    Canon.FreeOnly γ → c.suit ≠ d.suit → ShufflePlayW u pre A →
    State.step A (Move.tabToFound c) = some B → PullKit.Pullable B d b →
    (∀ q ∈ γ, SlideFwd.ReadSafe d q) → (∀ q ∈ γ, MtnPr.SeatInert b q) →
    SeatMate c d → False

/-- Shape 1 implies the seat-mate shadow. -/
theorem noSeatMate_of_noInl (h : NoSeatMateCrossSuit) : NoInlOrigin := by
  intro u v ρ pre γ tail c d b A B hwf hu hv hplay hminlen hmininv heq hfree hsu
    hpre hstepR hpullB hread hseat hb
  obtain ⟨a, ha⟩ := hb
  obtain ⟨-, -, hdisj⟩ := canonical_corridor_dichotomy hwf hplay heq hpre hstepR
    hpullB hfree hsu hread hseat (fun ρ' hρ' hlen' => by
      rw [← heq]
      exact hmininv ρ' hρ' (hlen'.trans (congrArg List.length heq.symm)))
  rcases hdisj with ⟨j, hbj, -, hck, hdk⟩ | ⟨z, hbz, -, hdt⟩
  · exact h u v ρ pre γ tail c d b A B hwf hu hv hplay hminlen hmininv heq hfree hsu
      hpre hstepR hpullB hread hseat (Or.inl ⟨hck, hdk⟩)
  · exact absurd (ha.symm.trans hbz) (by simp)

/-- Shape 3 implies the seat-mate shadow. -/
theorem noSeatMate_of_noExpose (h : NoSeatMateCrossSuit) : NoExposeBase := by
  intro u v ρ pre γ tail c d b A B hwf hu hv hplay hminlen hmininv heq hfree hsu
    hpre hstepR hpullB hread hseat hb
  obtain ⟨z, hz⟩ := hb
  obtain ⟨-, -, hdisj⟩ := canonical_corridor_dichotomy hwf hplay heq hpre hstepR
    hpullB hfree hsu hread hseat (fun ρ' hρ' hlen' => by
      rw [← heq]
      exact hmininv ρ' hρ' (hlen'.trans (congrArg List.length heq.symm)))
  rcases hdisj with ⟨j, hbj, -, hck, hdk⟩ | ⟨z', hbz, hzn, hdt⟩
  · exact absurd (hz.symm.trans hbj) (by simp)
  · by_cases hk : c.rank = Rank.king
    · exact h u v ρ pre γ tail c d b A B hwf hu hv hplay hminlen hmininv heq hfree
        hsu hpre hstepR hpullB hread hseat
        (Or.inl ⟨hk, by rw [hdt, Card.twin_rank]; exact hk⟩)
    · exact h u v ρ pre γ tail c d b A B hwf hu hv hplay hminlen hmininv heq hfree
        hsu hpre hstepR hpullB hread hseat (Or.inr ⟨hk, Or.inr hdt⟩)

/-- The two survivor exclusions together give the seat-mate shadow. -/
theorem noSeatMate_of_shapes (h1 : NoInlOrigin) (h2 : NoExposeBase) :
    NoSeatMateCrossSuit := by
  intro u v ρ pre γ tail c d b A B hwf hu hv hplay hminlen hmininv heq hfree hsu
    hpre hstepR hpullB hread hseat hsm
  obtain ⟨-, -, hdisj⟩ := canonical_corridor_dichotomy hwf hplay heq hpre hstepR
    hpullB hfree hsu hread hseat (fun ρ' hρ' hlen' => by
      rw [← heq]
      exact hmininv ρ' hρ' (hlen'.trans (congrArg List.length heq.symm)))
  rcases hdisj with ⟨j, hbj, -, -, -⟩ | ⟨z, hbz, -, -⟩
  · exact h1 u v ρ pre γ tail c d b A B hwf hu hv hplay hminlen hmininv heq hfree
      hsu hpre hstepR hpullB hread hseat ⟨j, hbj⟩
  · exact h2 u v ρ pre γ tail c d b A B hwf hu hv hplay hminlen hmininv heq hfree
      hsu hpre hstepR hpullB hread hseat ⟨z, hbz⟩

/-- **THE EXACT SURVIVING SHAPE.**  `NoSeatMateCrossSuit` is exactly the
conjunction of the two shape exclusions. -/
theorem noSeatMate_iff_shapes :
    NoSeatMateCrossSuit ↔ NoInlOrigin ∧ NoExposeBase :=
  ⟨fun h => ⟨noSeatMate_of_noInl h, noSeatMate_of_noExpose h⟩,
   fun h => noSeatMate_of_shapes h.1 h.2⟩

/-- **CROSS-SUIT VACUITY FROM THE TWO SURVIVORS.**  If neither surviving shape
occurs, the canonical geodesic carries no cross-suit free corridor at all. -/
theorem canonical_no_crossSuit_corridor (h1 : NoInlOrigin) (h2 : NoExposeBase)
    (u v : State) (huwf : u.WF) (hu : SSaturated u) (hv : SSaturated v)
    (hcls : sameOrbitSetoid.r u v) :
    ∃ ρ : List Move, ShufflePlayW u ρ v ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) ∧
      (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ'.length = ρ.length →
        Canon.inv ρ ≤ Canon.inv ρ') ∧
      ∀ (pre γ tail : List Move) (c d : Card) (b : Base) (A B : State),
        ρ = pre ++ (Move.tabToFound c :: (γ ++ (Move.foundToTab d b :: tail))) →
        Canon.FreeOnly γ → c.suit ≠ d.suit →
        ShufflePlayW u pre A → State.step A (Move.tabToFound c) = some B →
        PullKit.Pullable B d b →
        (∀ q ∈ γ, SlideFwd.ReadSafe d q) →
        (∀ q ∈ γ, MtnPr.SeatInert b q) → False := by
  obtain ⟨ρ, hplay, hminlen, hmininv, hprop⟩ :=
    canonical_geodesic_seatMate u v huwf hu hv hcls
  refine ⟨ρ, hplay, hminlen, hmininv, ?_⟩
  intro pre γ tail c d b A B heq hfree hsu hpre hstepR hpullB hread hseat
  obtain ⟨-, -, hsm⟩ := hprop pre γ tail c d b A B heq hfree hsu hpre hstepR hpullB
    hread hseat
  exact (noSeatMate_of_shapes h1 h2) u v ρ pre γ tail c d b A B huwf hu hv hplay
    hminlen hmininv heq hfree hsu hpre hstepR hpullB hread hseat hsm

end Blocks

/-! ## §5. Axiom battery

Expected: every row `[]`, `[propext]` or `[propext, Quot.sound]` — no `sorryAx`,
no `Classical.choice`, no `Lean.ofReduceBool` (`native_decide`). -/

#print axioms Blocks.isEmpty_eq_true_iff
#print axioms Blocks.isEmpty_false_of_faceUp_ne
#print axioms Blocks.isEmpty_afterRunRemoved
#print axioms Blocks.pile_eq_bare_of_chop_nil
#print axioms Blocks.bare_cell_of_chop_nil
#print axioms Blocks.eq_raiseSt_of_step
#print axioms Blocks.color_eq_of_ne_ne
#print axioms Blocks.eq_twin_of_color_eq_ne
#print axioms Blocks.ne_inr_raised
#print axioms Blocks.inl_shape
#print axioms Blocks.inr_expose_shape
#print axioms Blocks.seatMate_of_raise_image
#print axioms Blocks.raise_image_dichotomy
#print axioms Blocks.rev_raise_of_corridor
#print axioms Blocks.shape1_not_followed_by_raise
#print axioms Blocks.corridor_tail_cover_obligation
#print axioms Blocks.canonical_corridor_dichotomy
#print axioms Blocks.canonical_corridor_seatMate
#print axioms Blocks.canonical_geodesic_seatMate
#print axioms Blocks.noSeatMate_of_noInl
#print axioms Blocks.noSeatMate_of_noExpose
#print axioms Blocks.noSeatMate_of_shapes
#print axioms Blocks.noSeatMate_iff_shapes
#print axioms Blocks.canonical_no_crossSuit_corridor

#check @Blocks.NoInlOrigin
#check @Blocks.NoExposeBase
#check @Blocks.NoSeatMateCrossSuit
#check @Blocks.canonical_corridor_dichotomy
#check @Blocks.canonical_geodesic_seatMate

