import Klondike.PileQuotient
import Klondike.C2Streamlined

open Klondike.C2

/-!
# PileQuotientCorollaries — wave-21: the count theorems on the quotient

The pile quotient (`Klondike/PileQuotient.lean`) identifies the
states a whole-pile transposition can move between (plus, for
pristine-like boards, the inert-deal wash — `PileContentClass`).
This file restates the C2 count theorems' CONTENT on it:

* **§1 The trivial descents.** The twin-receiver collapse and the
  stack determinism land class-to-class: `closureEq` (C2 §3's
  class equality: mutual accommodation reachability) passes to any
  solvability verdict by UNCHANGED PLAYS
  (`solvable_iff_mutuallyReaches`, Progress.lean — the plays ARE the
  reaches), so the quoted collapses fall through at the quotient:
  `commitTableau_class` (C2Streamlined §9.5, the destination
  collapse at the commitment level — the two tableau-arm successors
  of the same drawn card, rung premise), `crease_stack_deterministic`
  (the stack arm's determinism) and the assembled `c2_two_option`
  (three channel-labeled futures contain a fate-collapsed pair,
  under the five play premises) all descend verbatim.

* **§2 The first-cut graded bound (the ≤ 2 + 1 form).**  The true
  form of the commitment bound counts the futures as
  2 + #swap-orbits of usable anchor candidates: the two non-anchor
  channels (the deterministic stack arm; the receiver-tableau arm)
  plus one class per anchor-content orbit.  The first-cut
  instance: at a pristine-like board — every depth zero, the
  matching EMPTY — all vacant anchors carry identical (empty)
  content, so the anchor landings form ONE orbit
  (`emptyPiles_land_content_eq`), giving futures ≤ 2 + 1.
  `pristine_commit_firstCut` (any three futures contain a
  same-class pair — the ≤ 2-classes reading, the strongest clean
  form) and `pristine_commit_firstCut_graded` (any four futures
  contain a same-class pair — the literal ≤ 3-classes = 2 + 1
  pigeonhole) are the two readings; the verdict-corollary
  `pristine_commit_firstCut_fates` reads them through
  `solvableCW`.

* **§3 The reachable corner's survival is orbit-structural.**  The
  wave-20 countermodels (the reached-corner king landings in
  `witnesses/SuccLabeledWitness.lean`; the sibling wave's
  `witnesses/PileSwapConsequences.lean` §2: the public-deal twin
  `ReachCorner.sLand_swapRelated_iff` / `rState_survives`, the
  single-step non-relatedness of the dealt initial state's king
  landings over the shared WF deal with depths 0..6) are separated
  in the FULL content quotient: two same-deal, WF-dealt,
  not-all-emptied states are content-related only when equal
  (`sameDeal_content_separated`, via the lib's
  `pileContentOrbit_sameDeal_eq` — the chain representation +
  slot-length injectivity).

Zero `sorry`.  Axioms: the pins below — `[propext, Quot.sound]`,
no classical, no sorryAx.
-/

namespace PileQuotientCorollaries

/-! ## §1. The trivial descents (the C2 collapses at the quotient) -/

/-- `closureEq` passes to the content-class solvability verdict:
mutual accommodation reachability runs the same plays —
`solvable_iff_mutuallyReaches` — so every C2 class equality is
invisible to `solvableCW`. -/
theorem closureEq_solvableCW_iff {s s' : State} (h : closureEq s s') :
    solvableCW (PileContentClass.mk s) ↔ solvableCW (PileContentClass.mk s') := by
  obtain ⟨π₁, h₁, -⟩ := h.1
  obtain ⟨π₂, h₂, -⟩ := h.2
  rw [solvableCW_mk_iff, solvableCW_mk_iff]
  exact solvable_iff_mutuallyReaches ⟨π₁, h₁⟩ ⟨π₂, h₂⟩

/-- **The twin-receiver collapse, descended.**  `commitTableau_class`
(cite: C2Streamlined §9.5 — the two tableau-arm successors of the
same drawn card at one WF state are `closureEq`, stackable-rung
regime): the two futures share the content-class verdict. -/
theorem commitTableau_class_fate {u : State} (hwf : u.WF) {X : Card}
    (hrk : X.rank.toIdx = u.heights X.suit)
    {s s' : State} (hs : CommitTableau u X s) (hs' : CommitTableau u X s') :
    solvableCW (PileContentClass.mk s) ↔ solvableCW (PileContentClass.mk s') :=
  closureEq_solvableCW_iff (commitTableau_class hwf hrk hs hs')

/-- **The stack determinism, descended.**
`crease_stack_deterministic` (cite: C2Streamlined's stack arm) —
the two equal-window stack futures share the content-class
verdict. -/
theorem crease_stack_fate {u : State} {X : Card} {s s' : State}
    (hs : u.applyDrawStackTo X = some s) (hs' : u.applyDrawStackTo X = some s') :
    solvableCW (PileContentClass.mk s) ↔ solvableCW (PileContentClass.mk s') :=
  closureEq_solvableCW_iff (crease_stack_deterministic hs hs')

/-- **The assembled two-option bound, descended.**  Under
`c2_two_option`'s five play premises (cite: C2Streamlined's §9.7),
among three channel-labeled futures two share the content-class
verdict. -/
theorem c2_two_option_fate {st : State} (hwf : st.WF) {X : Card}
    {s₁ s₂ s₃ : State}
    (h₁ : macroStep st (MacroMove.drawCommit X) s₁)
    (h₂ : macroStep st (MacroMove.drawCommit X) s₂)
    (h₃ : macroStep st (MacroMove.drawCommit X) s₃)
    (hlab₁ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₁)
    (hlab₂ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₂)
    (hlab₃ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s₃)
    (hp2 : ∀ {sd : State}, commitApplies st (MacroMove.drawCommit X) sd →
      ∀ {r : Label X} {s : State}, SuccThrough st X r s →
      P2Safe st X r → closureEq sd s)
    (hpin : ∀ {r : Label X} {s s' : State}, LabelLive st X r →
      SuccThrough st X r s → SuccThrough st X r s' → closureEq s s')
    (hball : (¬∃ sd, commitApplies st (MacroMove.drawCommit X) sd) →
      ∀ {rₐ r_b : Label X} {s₀ sₐ s_b : State},
      LabelLive st X Label.toStack → SuccThrough st X Label.toStack s₀ →
      LabelLive st X rₐ → SuccThrough st X rₐ sₐ →
      LabelLive st X r_b → SuccThrough st X r_b s_b →
      rₐ ≠ r_b →
      closureEq s₀ sₐ ∨ closureEq s₀ s_b ∨ closureEq sₐ s_b) :
    (solvableCW (PileContentClass.mk s₁) ↔ solvableCW (PileContentClass.mk s₂)) ∨
    (solvableCW (PileContentClass.mk s₁) ↔ solvableCW (PileContentClass.mk s₃)) ∨
    (solvableCW (PileContentClass.mk s₂) ↔ solvableCW (PileContentClass.mk s₃)) := by
  rcases c2_two_option hwf h₁ h₂ h₃ hlab₁ hlab₂ hlab₃ hp2 hpin hball with q | q | q
  · exact Or.inl (closureEq_solvableCW_iff q)
  · exact Or.inr (Or.inl (closureEq_solvableCW_iff q))
  · exact Or.inr (Or.inr (closureEq_solvableCW_iff q))

/-! ## §2. The first-cut graded bound -/

/-- At an empty matching no card is visible anywhere. -/
theorem isVis_false_of_emptyBoard {st : State} (hb : st.board = Board.empty)
    (d : Card) : st.isVis d = false := by
  show (st.board.bottomOf d).isSome = false
  rw [hb, Board.empty_bottomOf]
  rfl

/-- The empty board's tableau-commit bases are anchor seats: card
seats carry no visible card, so `canPlace` fails there. -/
theorem commitTab_anchor_of_emptyBoard {st : State} (hb : st.board = Board.empty)
    {X : Card} {s : State} (htab : CommitTableau st X s) :
    ∃ a : Anchor, st.applyDrawTo X (Sum.inl a) = some s := by
  obtain ⟨b, hcp, hrun⟩ := htab
  cases b with
  | inl a => exact ⟨a, hrun⟩
  | inr d =>
      exfalso
      have hvis := isVis_of_canPlace_inr hcp
      rw [isVis_false_of_emptyBoard hb d] at hvis
      exact absurd hvis (by simp)

/-- Two stack-arm futures are the SAME STATE (the stack arm is a
function). -/
theorem commitStack_pair_eq {u : State} {X : Card} {s s' : State}
    (hs : CommitStack u X s) (hs' : CommitStack u X s') : s = s' :=
  Option.some.inj (hs.symm.trans hs')

/-- **The anchor arm's ONE orbit:** two tableau-arm futures of a
pristine-like commitment share the content class — the vacant
anchors carry identical (empty) content, so the landings live in
one orphan orbit (`emptyPiles_land_content_eq`). -/
theorem commitTab_pair_content {st : State} (hz : st.depthsZero)
    (hb : st.board = Board.empty) {X : Card} {s s' : State}
    (htab : CommitTableau st X s) (htab' : CommitTableau st X s') :
    PileContentClass.mk s = PileContentClass.mk s' := by
  obtain ⟨a, hrun⟩ := commitTab_anchor_of_emptyBoard hb htab
  obtain ⟨a', hrun'⟩ := commitTab_anchor_of_emptyBoard hb htab'
  exact emptyPiles_land_content_eq hz hb a a' hrun hrun'

/-- **THE FIRST CUT, CLEAN FORM.**  At a pristine-like commitment —
every hidden stack emptied, the matching empty — any THREE futures
of the `Draw(X)` commitment contain a pair landing in the SAME
content class.  Reading: the futures count at most TWO classes —
the deterministic stack arm (≤ 1) and the anchor arm's single
swap-orbit (≤ 1, all vacant anchors identical content) — well
inside the graded bound's 2 + #anchor-orbits with #orbits = 1:
futures ≤ 2 + 1. -/
theorem pristine_commit_firstCut {st : State} (hz : st.depthsZero)
    (hb : st.board = Board.empty) {X : Card} {s₁ s₂ s₃ : State}
    (h₁ : commitApplies st (MacroMove.drawCommit X) s₁)
    (h₂ : commitApplies st (MacroMove.drawCommit X) s₂)
    (h₃ : commitApplies st (MacroMove.drawCommit X) s₃) :
    PileContentClass.mk s₁ = PileContentClass.mk s₂ ∨
    PileContentClass.mk s₁ = PileContentClass.mk s₃ ∨
    PileContentClass.mk s₂ = PileContentClass.mk s₃ := by
  rcases (commitApplies_draw_cases st X s₁).mp h₁ with t₁ | k₁
  · rcases (commitApplies_draw_cases st X s₂).mp h₂ with t₂ | k₂
    · exact Or.inl (commitTab_pair_content hz hb t₁ t₂)
    · rcases (commitApplies_draw_cases st X s₃).mp h₃ with t₃ | k₃
      · exact Or.inr (Or.inl (commitTab_pair_content hz hb t₁ t₃))
      · exact Or.inr (Or.inr (by
          show PileContentClass.mk s₂ = PileContentClass.mk s₃
          rw [commitStack_pair_eq k₂ k₃]))
  · rcases (commitApplies_draw_cases st X s₂).mp h₂ with t₂ | k₂
    · rcases (commitApplies_draw_cases st X s₃).mp h₃ with t₃ | k₃
      · exact Or.inr (Or.inr (commitTab_pair_content hz hb t₂ t₃))
      · exact Or.inr (Or.inl (by
          show PileContentClass.mk s₁ = PileContentClass.mk s₃
          rw [commitStack_pair_eq k₁ k₃]))
    · rcases (commitApplies_draw_cases st X s₃).mp h₃ with t₃ | k₃
      · exact Or.inl (by
          show PileContentClass.mk s₁ = PileContentClass.mk s₂
          rw [commitStack_pair_eq k₁ k₂])
      · exact Or.inl (by
          show PileContentClass.mk s₁ = PileContentClass.mk s₂
          rw [commitStack_pair_eq k₁ k₂])

/-- **THE FIRST CUT, LITERAL ≤ 2 + 1 FORM.**  Any FOUR futures
contain a same-class pair — the graded bound's pigeonhole when the
non-anchor channels contribute 2 classes and the usable anchor
candidates form ONE orbit (2 + 1 = 3 classes). -/
theorem pristine_commit_firstCut_graded {st : State} (hz : st.depthsZero)
    (hb : st.board = Board.empty) {X : Card} {s₁ s₂ s₃ s₄ : State}
    (h₁ : commitApplies st (MacroMove.drawCommit X) s₁)
    (h₂ : commitApplies st (MacroMove.drawCommit X) s₂)
    (h₃ : commitApplies st (MacroMove.drawCommit X) s₃)
    (h₄ : commitApplies st (MacroMove.drawCommit X) s₄) :
    PileContentClass.mk s₁ = PileContentClass.mk s₂ ∨
    PileContentClass.mk s₁ = PileContentClass.mk s₃ ∨
    PileContentClass.mk s₁ = PileContentClass.mk s₄ ∨
    PileContentClass.mk s₂ = PileContentClass.mk s₃ ∨
    PileContentClass.mk s₂ = PileContentClass.mk s₄ ∨
    PileContentClass.mk s₃ = PileContentClass.mk s₄ := by
  have hw₁ := (commitApplies_draw_cases st X s₁).mp h₁
  have hw₂ := (commitApplies_draw_cases st X s₂).mp h₂
  have hw₃ := (commitApplies_draw_cases st X s₃).mp h₃
  have hw₄ := (commitApplies_draw_cases st X s₄).mp h₄
  rcases hw₁ with t₁ | k₁
  · rcases hw₂ with t₂ | k₂
    · exact Or.inl (commitTab_pair_content hz hb t₁ t₂)
    · rcases hw₃ with t₃ | k₃
      · exact Or.inr (Or.inl (commitTab_pair_content hz hb t₁ t₃))
      · rcases hw₄ with t₄ | k₄
        · exact Or.inr (Or.inr (Or.inl (commitTab_pair_content hz hb t₁ t₄)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by
            show PileContentClass.mk s₂ = PileContentClass.mk s₃
            rw [commitStack_pair_eq k₂ k₃]))))
  · rcases hw₂ with t₂ | k₂
    · rcases hw₃ with t₃ | k₃
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (commitTab_pair_content hz hb t₂ t₃))))
      · rcases hw₄ with t₄ | k₄
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            (commitTab_pair_content hz hb t₂ t₄)))))
        · exact Or.inr (Or.inl (by
            show PileContentClass.mk s₁ = PileContentClass.mk s₃
            rw [commitStack_pair_eq k₁ k₃]))
    · rcases hw₃ with t₃ | k₃
      · rcases hw₄ with t₄ | k₄
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (commitTab_pair_content hz hb t₃ t₄)))))
        · exact Or.inl (by
            show PileContentClass.mk s₁ = PileContentClass.mk s₂
            rw [commitStack_pair_eq k₁ k₂])
      · exact Or.inl (by
          show PileContentClass.mk s₁ = PileContentClass.mk s₂
          rw [commitStack_pair_eq k₁ k₂])

/-- The first cut read through the verdict: among three futures of a
pristine-like commitment, two share the content-class solvability
verdict. -/
theorem pristine_commit_firstCut_fates {st : State} (hz : st.depthsZero)
    (hb : st.board = Board.empty) {X : Card} {s₁ s₂ s₃ : State}
    (h₁ : commitApplies st (MacroMove.drawCommit X) s₁)
    (h₂ : commitApplies st (MacroMove.drawCommit X) s₂)
    (h₃ : commitApplies st (MacroMove.drawCommit X) s₃) :
    (solvableCW (PileContentClass.mk s₁) ↔ solvableCW (PileContentClass.mk s₂)) ∨
    (solvableCW (PileContentClass.mk s₁) ↔ solvableCW (PileContentClass.mk s₃)) ∨
    (solvableCW (PileContentClass.mk s₂) ↔ solvableCW (PileContentClass.mk s₃)) := by
  rcases pristine_commit_firstCut hz hb h₁ h₂ h₃ with q | q | q
  · exact Or.inl (by rw [q])
  · exact Or.inr (Or.inl (by rw [q]))
  · exact Or.inr (Or.inr (by rw [q]))

/-! ## §3. The reachable corner's survival — orbit-structural -/

/-- Two same-deal, WF-dealt, still-hidden states are content-related
only when EQUAL — the class-level separation.  The wave-20
reachable-corner countermodels (`rState` and its king landings:
`witnesses/SuccLabeledWitness.lean`, the dealt initial state over
the public WF deal with per-pile hidden stacks; the sibling wave's
`witnesses/PileSwapConsequences.lean` §2,
`ReachCorner.sLand_swapRelated_iff` + `rState_survives`) meet every
premise — same WF deal, distinct landings, depths 0..6
(not all-emptied) — so their separation survives the FULL content
quotient, not merely single transpositions: the countermodels are
orbit-structural. -/
theorem sameDeal_content_separated {s₁ s₂ : State} (hd : s₁.deal.WF)
    (hnz : ¬ s₁.depthsZero) (hneq : s₁ ≠ s₂) (hdeal : s₂.deal = s₁.deal) :
    PileContentClass.mk s₁ ≠ PileContentClass.mk s₂ := by
  intro hcon
  exact hneq (pileContentOrbit_sameDeal_eq hd hnz
    (PileContentClass.exact hcon) hdeal)

end PileQuotientCorollaries

/-! ### Axiom pins -/

/-- info: 'PileQuotientCorollaries.closureEq_solvableCW_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientCorollaries.closureEq_solvableCW_iff

/-- info: 'PileQuotientCorollaries.commitTableau_class_fate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientCorollaries.commitTableau_class_fate

/-- info: 'PileQuotientCorollaries.crease_stack_fate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientCorollaries.crease_stack_fate

/-- info: 'PileQuotientCorollaries.c2_two_option_fate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientCorollaries.c2_two_option_fate

/-- info: 'PileQuotientCorollaries.commitTab_pair_content' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientCorollaries.commitTab_pair_content

/-- info: 'PileQuotientCorollaries.pristine_commit_firstCut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientCorollaries.pristine_commit_firstCut

/-- info: 'PileQuotientCorollaries.pristine_commit_firstCut_graded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientCorollaries.pristine_commit_firstCut_graded

/-- info: 'PileQuotientCorollaries.pristine_commit_firstCut_fates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientCorollaries.pristine_commit_firstCut_fates

/-- info: 'PileQuotientCorollaries.sameDeal_content_separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientCorollaries.sameDeal_content_separated

/-- info: 'emptyPiles_land_content_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emptyPiles_land_content_eq

/-- info: 'pileContentOrbit_sameDeal_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pileContentOrbit_sameDeal_eq

/-- info: 'EngineSuccQ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms EngineSuccQ

/-- info: 'solvableCW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms solvableCW
