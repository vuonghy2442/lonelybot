import Orig2.Classification
import Orig2.CargoKit
import Orig2.TwinLastPull
import Orig2.TwinRaiseCommute

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2.TwinCargoKernel — the pair-free kernel: refuted, with the empty-middle subcases

THE TARGET UNDER TEST (the pair-free kernel absorption theorem):

```
theorem pairFree_noDraw_play_cargo {s t : State} {play : List Move} {x : Card}
    (hwf : s.WF)
    (hplay : ShufflePlayW s play t)
    (hno : ∀ m ∈ play, NotFoundPair x m)
    (hnd : ∀ m ∈ play, m ≠ Move.draw)
    (hfound : s.found = t.found) :
    BareCargoEquiv s t
```

VERDICT: **FALSE**.  The file contains a compiled concrete counterexample
(`pairFree_noDraw_play_cargo_counterexample`) and the negation of the universal
statement (`pairFree_noDraw_play_cargo_refuted`).  The witness is the
king-relocation world `uA → wA`: seven bare singleton piles, the two kings
`K♠`, `K♥` raised and pulled back swapped through the foundations, a pair-free
no-draw witness shuffle with equal foundation tuples, while no cargo letter
fires at `uA` at all.  See the docstring of the witness section.

WHAT IS PROVED (the staged kernel pieces that are true):

* `pairFree_letter_classification` — every no-draw reversible letter avoiding
  `{x, x.twin}` is a cargo slide, a raise off the pair, or a pull off the pair;
* `raise_pull_self_eq` / `raise_pull_parent_bareCargo` — the empty-middle
  raise-pull excursion onto the source parent is a state-level loop, hence
  bare-cargo equivalent to the source (Deliverable 1, parent arm);
* `pulledAt_raisedAt_twin_eq_slidAt` / `raise_pull_twin_step_eq` — the
  empty-middle raise-pull excursion onto the parent's twin is exactly the
  one-letter cargo slide `tabToTab y (inr z.twin)` (Deliverable 1, twin arm,
  exact equality row; the reverse `CargoPath` is the explicit remaining goal
  `raise_pull_twin_close_goal` below);
* `raise_pull_parent_bareCargo` is the empty-middle induction base consumed by
  the staged plan (Deliverable 3).  The general induction cannot close because
  the target statement is refuted by the counterexample.

Zero `sorry`, zero `Classical.choice`, no new axioms; the audit battery is at
the tail.
-/

namespace TwinCargoKernel

open State
open TwinRaiseCommute

private def allTrue (l : List Card) (p : Card → Bool) : Bool :=
  match l with
  | [] => true
  | x :: t => (p x && allTrue t p)

private theorem allTrue_forall {l : List Card} {p : Card → Bool}
    (h : allTrue l p = true) : ∀ x ∈ l, p x = true := by
  induction l with
  | nil => intro x hx; cases hx
  | cons y t ih =>
      intro x hx
      rw [allTrue, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h.1
      · exact ih h.2 x hx'

private def kS : Card := ⟨Suit.spade, Rank.king⟩
private def kH : Card := ⟨Suit.heart, Rank.king⟩
private def kD : Card := ⟨Suit.diamond, Rank.king⟩
private def kC : Card := ⟨Suit.club, Rank.king⟩
private def cT : Card := ⟨Suit.club, Rank.ten⟩
private def cJ : Card := ⟨Suit.club, Rank.jack⟩
private def cQ : Card := ⟨Suit.club, Rank.queen⟩

private def foundsA : Suit → List Card := fun s =>
  match s with
  | .spade => (Suit.upCards Suit.spade).take 12
  | .heart => (Suit.upCards Suit.heart).take 12
  | .diamond => (Suit.upCards Suit.diamond).take 12
  | .club => (Suit.upCards Suit.club).take 9

private def uAp : Anchor → Pile := fun a =>
  match a with
  | .p0 => ⟨[], [kS]⟩
  | .p1 => ⟨[], [kH]⟩
  | .p2 => ⟨[], [kD]⟩
  | .p3 => ⟨[], [cT]⟩
  | .p4 => ⟨[], [cJ]⟩
  | .p5 => ⟨[], [cQ]⟩
  | .p6 => ⟨[], [kC]⟩

private def wAp : Anchor → Pile := fun a =>
  match a with
  | .p0 => ⟨[], [kH]⟩
  | .p1 => ⟨[], [kS]⟩
  | .p2 => ⟨[], [kD]⟩
  | .p3 => ⟨[], [cT]⟩
  | .p4 => ⟨[], [cJ]⟩
  | .p5 => ⟨[], [cQ]⟩
  | .p6 => ⟨[], [kC]⟩

private def uA : State :=
  { found := foundsA, piles := uAp, stock := [], waste := [], drawStep := 1 }

private def wA : State :=
  { found := foundsA, piles := wAp, stock := [], waste := [], drawStep := 1 }

/-- The seven cards of the witness tableau. -/
private def T7 : List Card := [kS, kH, kD, cT, cJ, cQ, kC]

private theorem inT7_of_faceUp_uA {a : Anchor} {x : Card}
    (h : x ∈ (uA.piles a).faceUp) : x ∈ T7 := by
  cases a with
  | p0 =>
      rcases List.mem_cons.mp h with rfl | hcon
      · decide
      · cases hcon
  | p1 =>
      rcases List.mem_cons.mp h with rfl | hcon
      · decide
      · cases hcon
  | p2 =>
      rcases List.mem_cons.mp h with rfl | hcon
      · decide
      · cases hcon
  | p3 =>
      rcases List.mem_cons.mp h with rfl | hcon
      · decide
      · cases hcon
  | p4 =>
      rcases List.mem_cons.mp h with rfl | hcon
      · decide
      · cases hcon
  | p5 =>
      rcases List.mem_cons.mp h with rfl | hcon
      · decide
      · cases hcon
  | p6 =>
      rcases List.mem_cons.mp h with rfl | hcon
      · decide
      · cases hcon

/-- The witness world's complete pair table: among the seven tableau cards,
the only sit-fit is `Q♣` under the red kings. -/
private theorem fitPairs_uA : allTrue T7 (fun x => allTrue T7 (fun y =>
    (!canSitOn x y) ||
      (decide (x = cQ) && (decide (y = kH) || decide (y = kD))))) = true := by
  decide

private theorem fitPair_uA {x y : Card} (hx : x ∈ T7) (hy : y ∈ T7)
    (h : canSitOn x y = true) : x = cQ ∧ (y = kH ∨ y = kD) := by
  have hh := allTrue_forall fitPairs_uA
  have hx' := allTrue_forall (hh x hx) y hy
  rw [h] at hx'
  cases hq : (decide (x = cQ) && (decide (y = kH) || decide (y = kD))) with
  | false => rw [hq] at hx'; exact absurd hx' (by simp)
  | true =>
      rw [Bool.and_eq_true] at hq
      refine ⟨of_decide_eq_true hq.1, ?_⟩
      cases h2 : (decide (y = kH) || decide (y = kD)) with
      | false => rw [h2] at hq; exact absurd hq.2 (by simp)
      | true =>
          rcases Bool.or_eq_true_iff.mp h2 with h' | h'
          · exact Or.inl (of_decide_eq_true h')
          · exact Or.inr (of_decide_eq_true h')

/-- WF of the witness states. The found-clause reads off the literal heights
(the raise legs bump a suit's pile to 13, the pulls chop it back);
runOK, cardCount (the `allTrue` funnel's kernel evaluation of all 52
counts) and the draw step are carried as hypotheses proven by `decide`. -/
private theorem wfA (n0 n1 n2 n3 : Nat) (st : State) (hd : 0 < st.drawStep)
    (e0 : st.found Suit.spade = (Suit.upCards Suit.spade).take n0)
    (e1 : st.found Suit.heart = (Suit.upCards Suit.heart).take n1)
    (e2 : st.found Suit.diamond = (Suit.upCards Suit.diamond).take n2)
    (e3 : st.found Suit.club = (Suit.upCards Suit.club).take n3)
    (hr : ∀ a : Anchor, runOK (st.piles a).faceUp = true)
    (hc : allTrue Card.universe (fun c => decide (st.cardCount c = 1)) = true) :
    st.WF := by
  refine ⟨fun s => ?_, fun a => hr a, fun c hc2 => ?_, hd⟩
  · cases s with
    | spade => exact ⟨n0, e0⟩
    | heart => exact ⟨n1, e1⟩
    | diamond => exact ⟨n2, e2⟩
    | club => exact ⟨n3, e3⟩
  · exact of_decide_eq_true (allTrue_forall hc c hc2)

private theorem uA_wf : uA.WF :=
  wfA 12 12 12 9 uA (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

private theorem wA_wf : wA.WF :=
  wfA 12 12 12 9 wA (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

/-! ### The forward journey `u_A → w_A` -/

private def s1A : State :=
  { uA.setFound Suit.spade (uA.found Suit.spade ++ [kS]) with
    piles := fun a' =>
      if a' = Anchor.p0 then
        Pile.afterRunRemoved (uA.piles Anchor.p0) (chop (uA.piles Anchor.p0).faceUp)
      else uA.piles a' }

private def s2A : State :=
  { s1A.setFound Suit.heart (s1A.found Suit.heart ++ [kH]) with
    piles := fun a' =>
      if a' = Anchor.p1 then
        Pile.afterRunRemoved (s1A.piles Anchor.p1) (chop (s1A.piles Anchor.p1).faceUp)
      else s1A.piles a' }

private def s3A : State :=
  (s2A.setFound Suit.heart (chop (s2A.found Suit.heart))).putCard kH (Sum.inl Anchor.p0)

private theorem stepA1 : State.step uA (Move.tabToFound kS) = some s1A :=
  step_tabToFound_splice (by decide) (by decide)

private theorem stepA2 : State.step s1A (Move.tabToFound kH) = some s2A :=
  step_tabToFound_splice (by decide) (by decide)

private theorem stepA3 : State.step s2A (Move.foundToTab kH (Sum.inl Anchor.p0)) = some s3A :=
  step_foundToTab_splice (by decide) (by decide)

private theorem stepA4 : State.step s3A (Move.foundToTab kS (Sum.inl Anchor.p1)) = some wA := by
  rw [step_foundToTab_splice (by decide) (by decide)]
  refine congrArg some (State.ext (funext fun s => ?_) (funext fun a => ?_) rfl rfl rfl)
  · cases s <;> decide
  · cases a <;> decide

/-! ### WF along the intermediate states -/
private theorem s1A_wf : s1A.WF :=
  wfA 13 12 12 9 s1A (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

private theorem s2A_wf : s2A.WF :=
  wfA 13 13 12 9 s2A (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

private theorem s3A_wf : s3A.WF :=
  wfA 13 12 12 9 s3A (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a; cases a <;> decide) (by decide)

/-! ### Leg reversibility via the certified oracle (WF at each origin) -/

private theorem revA1 : reversibleAtW uA (Move.tabToFound kS) :=
  (reversibleOf_iff_reversibleAtW uA_wf _).mp (by decide)

private theorem revA2 : reversibleAtW s1A (Move.tabToFound kH) :=
  (reversibleOf_iff_reversibleAtW s1A_wf _).mp (by decide)

private theorem revA3 : reversibleAtW s2A (Move.foundToTab kH (Sum.inl Anchor.p0)) :=
  (reversibleOf_iff_reversibleAtW s2A_wf _).mp (by decide)

private theorem revA4 : reversibleAtW s3A (Move.foundToTab kS (Sum.inl Anchor.p1)) :=
  (reversibleOf_iff_reversibleAtW s3A_wf _).mp (by decide)

private def playA : List Move :=
  [Move.tabToFound kS, Move.tabToFound kH,
   Move.foundToTab kH (Sum.inl Anchor.p0),
   Move.foundToTab kS (Sum.inl Anchor.p1)]

private theorem playA_fwd : ShufflePlayW uA playA wA :=
  .cons revA1 stepA1
    (.cons revA2 stepA2
      (.cons revA3 stepA3
        (.cons revA4 stepA4 (.nil wA))))

private theorem playA_nodraw : ∀ m ∈ playA, m ≠ Move.draw := by
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · decide
  · rcases List.mem_cons.mp hm with rfl | hm
    · decide
    · rcases List.mem_cons.mp hm with rfl | hm
      · decide
      · rcases List.mem_cons.mp hm with rfl | hm
        · decide
        · cases hm

theorem witnessA_founds : uA.found = wA.found := funext fun _ => rfl

theorem witnessA_ne : uA ≠ wA := by
  intro hcon
  have h0 : (uA.piles Anchor.p0).top = (wA.piles Anchor.p0).top := by rw [hcon]
  rw [show (uA.piles Anchor.p0).top = some kS from rfl,
    show (wA.piles Anchor.p0).top = some kH from rfl] at h0
  exact absurd h0 (by decide)

/-! ## §2. WITNESS A — the empty exchange world

No letter of either family fires nontrivially at `u_A`. -/

private theorem T7_cases {x : Card} (hx : x ∈ T7) :
    x = kS ∨ x = kH ∨ x = kD ∨ x = cT ∨ x = cJ ∨ x = cQ ∨ x = kC := by
  rcases List.mem_cons.mp hx with rfl | h
  · exact Or.inl rfl
  · rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr (Or.inl rfl)
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
              · cases h

/-- Both a card and its twin on the tableau force one of the two king pairs. -/
private theorem twin_in_T7 {x : Card} (hx : x ∈ T7) (hy : x.twin ∈ T7) :
    x = kS ∨ x = kD ∨ x = kH ∨ x = kC := by
  rcases T7_cases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd hy (by decide)
    | decide

private theorem uA_piles_nonempty (a : Anchor) : (uA.piles a).isEmpty = false := by
  cases a <;> decide

private theorem uA_mem_of_pileOfTop {k : Anchor} {x : Card}
    (h : uA.pileOfTop x = some k) : x ∈ T7 := by
  have h1 : decide (uA.topOf k = some x) = true :=
    firstWhere_sound (p := fun a => decide (uA.topOf a = some x)) h
  have h3 : lastOf (uA.piles k).faceUp = some x := of_decide_eq_true h1
  exact inT7_of_faceUp_uA (lastOf_mem h3)

/-- No cargo leg at all fires from `u_A`. -/
private theorem no_cargo_leg_uA {y : State} (hleg : CargoLeg uA y) : False := by
  obtain ⟨c, b, hfire, hrev⟩ := hleg
  obtain ⟨a₀, hhold, hcp, -, -⟩ := step_tabToTab_inv hfire
  cases b with
  | inl a =>
      obtain ⟨hempty, -⟩ := canPlace_inl hcp
      rw [uA_piles_nonempty a] at hempty
      exact absurd hempty (by decide)
  | inr y' =>
      obtain ⟨k, htop, hsit⟩ := canPlace_inr hcp
      have hcT : c ∈ T7 := inT7_of_faceUp_uA (pileHolding_mem hhold)
      have hyT : y' ∈ T7 := uA_mem_of_pileOfTop htop
      obtain ⟨rfl, hy'⟩ := fitPair_uA hcT hyT hsit
      rcases hy' with rfl | rfl
      · exact absurd ((reversibleOf_iff_reversibleAtW uA_wf _).mpr hrev) (by decide)
      · exact absurd ((reversibleOf_iff_reversibleAtW uA_wf _).mpr hrev) (by decide)



/-- The pair-free witness card: 7♣, untouched by the journey. -/
private def x7C : Card := ⟨Suit.club, Rank.seven⟩

private theorem nfp_tabToFound {x y : Card}
    (hyx : y ≠ x) (hyt : y ≠ x.twin) :
    NotFoundPair x (Move.tabToFound y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; injection h with h1; exact hyx h1
  · intro h; injection h with h1; exact hyt h1
  · intro b h; cases h
  · intro b h; cases h

private theorem nfp_foundToTab {x y : Card} {b : Base}
    (hyx : y ≠ x) (hyt : y ≠ x.twin) :
    NotFoundPair x (Move.foundToTab y b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h
  · intro b' h; injection h with h1 h2; exact hyx h1
  · intro b' h; injection h with h1 h2; exact hyt h1

private theorem playA_pairFree : ∀ m ∈ playA, NotFoundPair x7C m := by
  intro m hm
  simp only [playA, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact nfp_tabToFound (by decide) (by decide)
  · exact nfp_tabToFound (by decide) (by decide)
  · exact nfp_foundToTab (by decide) (by decide)
  · exact nfp_foundToTab (by decide) (by decide)

private theorem steps_isolated {Q : State → State → Prop} {x : State}
    (h : ∀ y, Q x y → y = x) {z : State} (t : Steps Q x z) : z = x := by
  induction t with
  | refl _ => rfl
  | @cons w m e hQ hrest ih =>
      have hm : m = w := h _ hQ
      subst hm
      exact ih h

theorem witnessA_not_bareCargo : ¬ BareCargoEquiv uA wA := by
  intro h
  have hpath : CargoPath uA wA := h.1
  have hEq : wA = uA :=
    steps_isolated (fun y hleg => absurd hleg no_cargo_leg_uA) hpath
  exact witnessA_ne hEq.symm

theorem pairFree_noDraw_play_cargo_counterexample :
    ∃ (s t : State) (play : List Move) (x : Card),
      s.WF ∧ ShufflePlayW s play t ∧
      (∀ m ∈ play, NotFoundPair x m) ∧
      (∀ m ∈ play, m ≠ Move.draw) ∧
      s.found = t.found ∧ ¬ BareCargoEquiv s t :=
  ⟨uA, wA, playA, x7C, uA_wf, playA_fwd, playA_pairFree, playA_nodraw,
    witnessA_founds, witnessA_not_bareCargo⟩

theorem pairFree_noDraw_play_cargo_refuted :
    ¬ (∀ {s t : State} {play : List Move} {x : Card},
        s.WF → ShufflePlayW s play t →
        (∀ m ∈ play, NotFoundPair x m) →
        (∀ m ∈ play, m ≠ Move.draw) →
        s.found = t.found → BareCargoEquiv s t) := by
  intro h
  obtain ⟨s, t, play, x, hwf, hplay, hno, hnd, hfound, hnot⟩ :=
    pairFree_noDraw_play_cargo_counterexample
  exact hnot (h hwf hplay hno hnd hfound)


/-! ## §1. Single pair-free letter classification -/

/-- Every reversible no-draw letter that avoids the pair `{x, x.twin}` is
exactly one of: a cargo slide (`tabToTab`), a raise (`tabToFound`) off the
pair, or a pull (`foundToTab`) off the pair. -/
theorem pairFree_letter_classification {x : Card} {u v : State} {m : Move}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m) (hnd : m ≠ Move.draw)
    (hno : NotFoundPair x m) :
    (∃ c b, m = Move.tabToTab c b) ∨
    (∃ y, m = Move.tabToFound y ∧ y ≠ x ∧ y ≠ x.twin) ∨
    (∃ y b, m = Move.foundToTab y b ∧ y ≠ x ∧ y ≠ x.twin) := by
  cases m with
  | draw => exact absurd rfl hnd
  | wasteToFound c =>
      exact absurd hrev (wasteToFound_not_reversibleAtW u c)
  | wasteToTab c b =>
      exact absurd hrev (wasteToTab_not_reversibleAtW u c b)
  | tabToFound y =>
      have hyx : y ≠ x := fun h => hno.1 (by rw [h])
      have hyt : y ≠ x.twin := fun h => hno.2.1 (by rw [h])
      exact Or.inr (Or.inl ⟨y, rfl, hyx, hyt⟩)
  | foundToTab y b =>
      have hyx : y ≠ x := fun h => hno.2.2.1 b (by rw [h])
      have hyt : y ≠ x.twin := fun h => hno.2.2.2 b (by rw [h])
      exact Or.inr (Or.inr ⟨y, b, rfl, hyx, hyt⟩)
  | tabToTab c b => exact Or.inl ⟨c, b, rfl⟩

/-! ## §2. The empty-middle raise-pull excursion onto the source parent -/

/-- Raising a card off its card parent and pulling it straight back onto
that parent restores the source exactly.  (Self-contained copy of the
`Orig2.TwinSuffixCancel` row `tsc_raise_pull_self_eq`.) -/
theorem raise_pull_self_eq {s s₁ s₂ : State} {x z : Card}
    (hwf : s.WF)
    (hx : seatOf s x = some (Sum.inr z))
    (hraise : State.step s (Move.tabToFound x) = some s₁)
    (hpull : State.step s₁ (Move.foundToTab x (Sum.inr z)) = some s₂) :
    s₂ = s := by
  obtain ⟨a, hhold, _hbelow_ne, hlast⟩ := tfc_seatOf_of_inr hx
  obtain ⟨_hnext, a₀, hpa₀, hs₁⟩ := step_tabToFound_inv hraise
  have htop₀ : (s.piles a₀).top = some x := (tfc_pileOfTop_top hpa₀).2
  have hhold₀ : s.pileHolding x = some a₀ :=
    (pileHolding_eq_some_iff hwf).mpr (Pile.mem_of_top htop₀)
  have ha₀ : a₀ = a := pileHolding_inj hhold₀ hhold
  subst a₀
  let st₁ : State :=
    { s.setFound x.suit (s.found x.suit ++ [x]) with
      piles := fun a' => if a' = a then
          Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
        else s.piles a' }
  have hs₁' : s₁ = st₁ := hs₁
  have htop : lastOf (s.piles a).faceUp = some x := (tfc_pileOfTop_top hpa₀).2
  have hface : (s.piles a).faceUp = chop (s.piles a).faceUp ++ [x] :=
    lastOf_chop htop
  have hnodup : (s.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
  have hx_not_chop : x ∉ chop (s.piles a).faceUp := by
    rw [hface] at hnodup
    exact List.snoc_nodup_notMem _ _ hnodup
  have hbelow_eq : below x (s.piles a).faceUp = chop (s.piles a).faceUp := by
    conv =>
      lhs
      rw [hface]
    exact below_snoc_not_mem hx_not_chop
  have hlast_chop : lastOf (chop (s.piles a).faceUp) = some z := by
    rw [← hbelow_eq]
    exact hlast
  have hchop_ne : chop (s.piles a).faceUp ≠ [] := by
    intro h
    rw [h] at hlast_chop
    nomatch hlast_chop
  have hs₁_pa : s₁.piles a =
      Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp) := by
    rw [hs₁']
    simp only [st₁, ite_true]
  have hs₁_pne : ∀ a' ≠ a, s₁.piles a' = s.piles a' := by
    intro a' ha'
    rw [hs₁']
    simp only [st₁, ite_eq_right ha']
  have hs₁_face : (s₁.piles a).faceUp = chop (s.piles a).faceUp := by
    rw [hs₁_pa, afterRunRemoved_faceUp_ne hchop_ne]
  have hwf₁ : s₁.WF := step_wf hwf hraise
  have hs₁_top_z : s₁.pileOfTop z = some a := by
    rw [pileOfTop_eq_some_iff hwf₁]
    show lastOf (s₁.piles a).faceUp = some z
    rw [hs₁_face]
    exact hlast_chop
  have hfit : canSitOn x z = true := (tfc_seat_parent hwf hhold hlast).1
  have hcp : s₁.canPlace x (Sum.inr z) = true := by
    rw [canPlace_inr_located hs₁_top_z]
    exact hfit
  have hfound_trio := tabToFound_found_trio (st := s) (s₁ := s₁)
    (c := x) (a := a) hs₁
  have hs₁_found_self : s₁.found x.suit = s.found x.suit ++ [x] :=
    hfound_trio.1
  have hs₁_found_ne : ∀ σ, σ ≠ x.suit → s₁.found σ = s.found σ :=
    hfound_trio.2.1
  have hs₁_foundTop : s₁.foundTop x.suit = some x := hfound_trio.2.2
  have hpull_eq : s₂ =
      (s₁.setFound x.suit (chop (s₁.found x.suit))).putCard x (Sum.inr z) := by
    have hfire := step_foundToTab_splice (st := s₁) (c := x)
      (b := Sum.inr z) hs₁_foundTop hcp
    rw [hfire] at hpull
    exact (Option.some.inj hpull).symm
  subst hpull_eq
  refine State.ext ?_ ?_ ?_ ?_ ?_
  · funext σ
    rw [putCard_found]
    by_cases hσ : σ = x.suit
    · rw [hσ, setFound_found_self, hs₁_found_self, chop_snoc]
    · rw [setFound_found_ne hσ, hs₁_found_ne σ hσ]
  · funext a'
    have hset_top : (s₁.setFound x.suit (chop (s₁.found x.suit))).pileOfTop z =
        some a := by
      unfold State.pileOfTop State.topOf
      rw [setFound_piles]
      exact hs₁_top_z
    rw [putCard_piles_inr (s₁.setFound x.suit (chop (s₁.found x.suit))) x z a
      hset_top]
    dsimp only
    by_cases ha' : a' = a
    · rw [ha', ite_eq_left rfl, setFound_piles]
      apply Pile.ext
      · rw [hs₁_pa, afterRunRemoved_ne hchop_ne]
      · rw [hs₁_face]
        exact hface.symm
    · rw [ite_eq_right ha', setFound_piles, hs₁_pne a' ha']
  · rw [putCard_stock, setFound_stock]
    rw [hs₁']
    rfl
  · rw [putCard_waste, setFound_waste]
    rw [hs₁']
    rfl
  · rw [putCard_drawStep, setFound_drawStep]
    rw [hs₁']
    rfl

/-- **Deliverable 1, parent arm.**  The empty-middle raise-pull excursion
onto the source parent is a state-level loop, hence bare-cargo equivalent
to the source (the empty cargo path). -/
theorem raise_pull_parent_bareCargo {s s₁ t : State} {y z : Card}
    (hwf : s.WF) (hy : seatOf s y = some (Sum.inr z))
    (hraise : State.step s (Move.tabToFound y) = some s₁)
    (hpull : State.step s₁ (Move.foundToTab y (Sum.inr z)) = some t) :
    BareCargoEquiv s t := by
  have ht : t = s := raise_pull_self_eq hwf hy hraise hpull
  rw [ht]
  exact ⟨Steps.refl s, Steps.refl s⟩

private theorem pulledAt_raisedAt_twin_eq_slidAt
    {s : State} {y z : Card} {a c : Anchor}
    (hwf : s.WF)
    (hpo : s.pileOfTop y = some a)
    (hparent : lastOf (below y (s.piles a).faceUp) = some z)
    (hbelow : below y (s.piles a).faceUp = chop (s.piles a).faceUp)
    (hchop_ne : chop (s.piles a).faceUp ≠ [])
    (hfrom : fromCard y (s.piles a).faceUp = [y])
    (htop : s.pileOfTop z.twin = some c)
    (hca : c ≠ a)
    (hraise : State.step s (Move.tabToFound y) = some (raisedAt s y a)) :
    pulledAt (raisedAt s y a) y (Sum.inr z.twin) =
      slidAt s y (Sum.inr z.twin) a := by
  have hwfR : (raisedAt s y a).WF := step_wf hwf hraise
  have htopR : (raisedAt s y a).pileOfTop z.twin = some c :=
    pileOfTop_raisedAt_other hwf hwfR hpo htop hca
  have hlast_chop : lastOf (chop (s.piles a).faceUp) = some z := by
    rw [← hbelow]
    exact hparent
  have htopRA : (Pile.afterRunRemoved (s.piles a)
      (chop (s.piles a).faceUp)).top ≠ some z.twin := by
    intro h
    have hz : (Pile.afterRunRemoved (s.piles a)
        (chop (s.piles a).faceUp)).top = some z := by
      unfold Pile.top
      rw [afterRunRemoved_faceUp_ne hchop_ne]
      exact hlast_chop
    rw [hz] at h
    exact card_twin_ne z (Option.some.inj h).symm
  have htopS : (s.setPile a
      (Pile.afterRunRemoved (s.piles a)
        (below y (s.piles a).faceUp))).pileOfTop z.twin = some c := by
    rw [hbelow]
    exact pileOfTop_setPile_ne hwf htop (Ne.symm hca) htopRA
  have htopRset : ((raisedAt s y a).setFound y.suit
      (chop ((raisedAt s y a).found y.suit))).pileOfTop z.twin = some c := by
    unfold State.pileOfTop State.topOf
    rw [setFound_piles]
    exact htopR
  apply State.ext
  · funext σ
    simp only [pulledAt, slidAt, raisedAt]
    rw [putCard_found, putRun_found]
    by_cases hσ : σ = y.suit
    · subst hσ
      simp [State.setFound, State.setPile, setFound_piles, setPile_found, chop_snoc]
    · simp [State.setFound, State.setPile, setFound_piles, setPile_found, hσ]
  · funext a'
    simp only [pulledAt, slidAt]
    rw [putCard_piles_inr ((raisedAt s y a).setFound y.suit
          (chop ((raisedAt s y a).found y.suit))) y z.twin c htopRset,
        putRun_piles_inr (s.setPile a (Pile.afterRunRemoved (s.piles a)
          (below y (s.piles a).faceUp))) (fromCard y (s.piles a).faceUp) z.twin c htopS]
    rw [hfrom]
    by_cases h1 : a' = a
    · rw [h1]
      dsimp only
      apply Pile.ext <;>
        simp [raisedAt, State.setPile, State.setFound, setFound_piles,
          setPile_found, hbelow, Ne.symm hca]
    · by_cases h2 : a' = c
      · rw [h2]
        dsimp only
        apply Pile.ext <;>
          simp [raisedAt, State.setPile, State.setFound, setFound_piles,
            setPile_found, hca]
      · dsimp only
        apply Pile.ext <;>
          simp [raisedAt, State.setPile, State.setFound, setFound_piles,
            setPile_found, h1, h2]
  · simp [pulledAt, slidAt, raisedAt, State.setFound, State.setPile,
      putCard_stock, putRun_stock]
  · simp [pulledAt, slidAt, raisedAt, State.setFound, State.setPile,
      putCard_waste, putRun_waste]
  · simp [pulledAt, slidAt, raisedAt, State.setFound, State.setPile,
      putCard_drawStep, putRun_drawStep]


private theorem canSitOn_rank_lt {y z : Card} (h : canSitOn y z = true) :
    y.rank.toIdx < z.rank.toIdx := by
  obtain ⟨h1, -⟩ := (canSitOn_eq y z).mp h
  omega

private theorem ne_twin_of_canSitOn {y z : Card} (h : canSitOn y z = true) :
    y ≠ z.twin := by
  intro hcon
  have hlt := canSitOn_rank_lt h
  rw [hcon] at hlt
  have hlt' : z.rank.toIdx < z.rank.toIdx := by simpa [Card.twin] using hlt
  exact Nat.lt_irrefl _ hlt'

theorem raise_pull_twin_step_eq {s s₁ t : State} {y z : Card}
    (hwf : s.WF)
    (hy : seatOf s y = some (Sum.inr z))
    (hraise : State.step s (Move.tabToFound y) = some s₁)
    (hpull : State.step s₁ (Move.foundToTab y (Sum.inr z.twin)) = some t) :
    State.step s (Move.tabToTab y (Sum.inr z.twin)) = some t := by
  obtain ⟨hnext, a, hpo, hs₁⟩ := step_tabToFound_inv hraise
  obtain ⟨a', hhold', _, hlast'⟩ := tfc_seatOf_of_inr hy
  have hhold_a : s.pileHolding y = some a := by
    have htop : (s.piles a).top = some y := (tfc_pileOfTop_top hpo).2
    exact (pileHolding_eq_some_iff hwf).mpr (Pile.mem_of_top htop)
  have ha' : a' = a := Option.some.inj (hhold'.symm.trans hhold_a)
  subst a'
  have htop : lastOf (s.piles a).faceUp = some y := (tfc_pileOfTop_top hpo).2
  have hface : (s.piles a).faceUp = chop (s.piles a).faceUp ++ [y] :=
    lastOf_chop htop
  have hnodup : (s.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
  have hy_not_chop : y ∉ chop (s.piles a).faceUp := by
    rw [hface] at hnodup
    exact List.snoc_nodup_notMem _ _ hnodup
  have hbelow : below y (s.piles a).faceUp = chop (s.piles a).faceUp := by
    conv => lhs; rw [hface]
    exact below_snoc_not_mem hy_not_chop
  have hlast_a : lastOf (below y (s.piles a).faceUp) = some z := hlast'
  have hparent : lastOf (chop (s.piles a).faceUp) = some z := by
    rw [← hbelow]
    exact hlast_a
  have hchop_ne : chop (s.piles a).faceUp ≠ [] := by
    intro hnil
    rw [hnil] at hparent
    nomatch hparent
  have hfrom : fromCard y (s.piles a).faceUp = [y] := by
    have hone := tfc_below_fromCard y (s.piles a).faceUp
    rw [hbelow] at hone
    exact List.append_cancel_left (hone.trans hface)
  have hfit : canSitOn y z = true := (tfc_seat_parent hwf hhold_a hlast_a).1
  have hyz : z.twin ≠ y := Ne.symm (ne_twin_of_canSitOn hfit)
  have hwf₁ : s₁.WF := step_wf hwf hraise
  obtain ⟨_, _, _, hcpP, _⟩ := step_foundToTab_inv hpull
  obtain ⟨c, htopS₁, hsit⟩ := canPlace_inr hcpP
  have hs₁_eq : s₁ = raisedAt s y a := hs₁
  have hraiseR : State.step s (Move.tabToFound y) = some (raisedAt s y a) := by
    rw [← hs₁_eq]; exact hraise
  have hwfR : (raisedAt s y a).WF := step_wf hwf hraiseR
  have hs₁_face : (s₁.piles a).faceUp = chop (s.piles a).faceUp := by
    rw [hs₁_eq]
    simp [raisedAt, afterRunRemoved_faceUp_ne hchop_ne]
  have htopA : lastOf (s₁.piles a).faceUp = some z := by
    rw [hs₁_face]; exact hparent
  have hca : c ≠ a := by
    intro hca
    have htopZ : lastOf (s₁.piles a).faceUp = some z.twin := by
      have h := (pileOfTop_eq_some_iff hwf₁).mp (by rwa [hca] at htopS₁)
      simpa [State.topOf, Pile.top] using h
    rw [htopA] at htopZ
    exact card_twin_ne z (Option.some.inj htopZ).symm
  have htop_s : s.pileOfTop z.twin = some c := by
    rw [hs₁_eq] at htopS₁
    exact pileOfTop_raisedAt_ne hwfR hpo hyz htopS₁ hca
  have hcp_s : s.canPlace y (Sum.inr z.twin) = true := by
    rw [canPlace_inr_located htop_s]
    exact hsit
  have ht_eq : t = pulledAt (raisedAt s y a) y (Sum.inr z.twin) := by
    rw [hs₁_eq] at hpull
    obtain ⟨_, _, _, _, hshape⟩ := step_foundToTab_inv hpull
    rw [hshape]
    rfl
  have heq := pulledAt_raisedAt_twin_eq_slidAt hwf hpo hlast_a hbelow hchop_ne
    hfrom htop_s hca hraiseR
  rw [ht_eq, heq]
  exact step_tabToTab_some hhold_a hcp_s


theorem raise_pull_twin_cargoLeg {s s₁ t : State} {y z : Card}
    (hwf : s.WF) (hy : seatOf s y = some (Sum.inr z))
    (hraise : State.step s (Move.tabToFound y) = some s₁)
    (hpull : State.step s₁ (Move.foundToTab y (Sum.inr z.twin)) = some t) :
    CargoLeg s t := by
  have hstep := raise_pull_twin_step_eq hwf hy hraise hpull
  obtain ⟨a, hh, hcp, -, -⟩ := step_tabToTab_inv hstep
  obtain ⟨a', hh', hbel', -⟩ := tfc_seatOf_of_inr hy
  have ha : a' = a := Option.some.inj (hh'.symm.trans hh)
  subst a'
  have hR : tabToTabR s y (Sum.inr z.twin) = true := by
    simp only [tabToTabR, hh, hcp]
    cases hbl : below y (s.piles a).faceUp with
    | nil => exact absurd hbl hbel'
    | cons w ws => simp
  exact ⟨y, Sum.inr z.twin, hstep,
    (tabToTabR_iff_reversibleAtW hwf y (Sum.inr z.twin)).mp hR⟩

theorem raise_pull_twin_cargoPath {s s₁ t : State} {y z : Card}
    (hwf : s.WF) (hy : seatOf s y = some (Sum.inr z))
    (hraise : State.step s (Move.tabToFound y) = some s₁)
    (hpull : State.step s₁ (Move.foundToTab y (Sum.inr z.twin)) = some t) :
    CargoPath s t :=
  Steps.cons (raise_pull_twin_cargoLeg hwf hy hraise hpull) (Steps.refl t)


/-! ## §3. The exact remaining goal of the twin arm

The forward cargo letter is proved (`raise_pull_twin_step_eq`).  The reverse
letter is the same slide run backwards; its exact statement is recorded here
as a predicate (not as a `sorry`):

```
raise_pull_twin_close_goal s t y z := CargoPath s t ∧ CargoPath t s
```

The forward half is `raise_pull_twin_step_eq` plus the `tabToTabR` oracle; the
reverse half is the symmetric slide of the same run from `z.twin` back onto
`z`.  The general kernel theorem above does not need this arm: it is already
false by the counterexample.
-/

/-- The exact closure goal of the twin raise-pull excursion. -/
def raise_pull_twin_close_goal (s t : State) (y z : Card) : Prop :=
  CargoPath s t ∧ CargoPath t s

/-- The exact universal statement under test, named for the report. -/
def PairFreeNoDrawCargoKernel : Prop :=
  ∀ {s t : State} {play : List Move} {x : Card},
    s.WF → ShufflePlayW s play t →
    (∀ m ∈ play, NotFoundPair x m) →
    (∀ m ∈ play, m ≠ Move.draw) →
    s.found = t.found → BareCargoEquiv s t

/-- **The target is false.** -/
theorem pairFree_noDraw_play_cargo_refuted' :
    ¬ PairFreeNoDrawCargoKernel :=
  pairFree_noDraw_play_cargo_refuted

/-! ## §4. Audit battery -/

#print axioms pairFree_letter_classification
#print axioms raise_pull_self_eq
#print axioms raise_pull_parent_bareCargo
#print axioms canSitOn_rank_lt
#print axioms ne_twin_of_canSitOn
#print axioms pulledAt_raisedAt_twin_eq_slidAt
#print axioms raise_pull_twin_step_eq
#print axioms raise_pull_twin_cargoLeg
#print axioms raise_pull_twin_cargoPath
#print axioms witnessA_founds
#print axioms witnessA_ne
#print axioms witnessA_not_bareCargo
#print axioms pairFree_noDraw_play_cargo_counterexample
#print axioms pairFree_noDraw_play_cargo_refuted
#print axioms pairFree_noDraw_play_cargo_refuted'

end TwinCargoKernel
