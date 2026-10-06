import Klondike.PileQuotient
import Klondike.C2Streamlined
import Witnesses.PileSwapConsequences

open Klondike.C2

/-!
# PileQuotientOrbit — wave-22: the king-side graded bound on the pile quotient

The pile quotient's carving kernel (`Klondike/PileQuotient.lean` §7:
`drawLand_pileSwapOrbit_iff`, `drawLand_content_eq_of_depthsZero`,
`drawLand_pile_class_inj`, `drawLand_content_class_inj`) meets the
C2 king-side machinery (read-only cites:
`Klondike/C2Streamlined.lean`'s `king_tableau_base` — kings land on
free anchors only; `receivers_king_nil` — the receiver channels die
at kings CARD-LEVEL, at every state; `succThrough_zeroSpend` — the
hole channel commits at the root; `commitApplies_draw_cases`; the
weak-corner regime `c2_two_option_king_frozen`/`same_pin_hole_
oneAnchor` — the closureEq twin at the same `hone`/`hfroz` shape;
and `commitTableau_class` — the previous rung-scoped collapse whose
rung premise the quotient reading drops).  This file assembles the
**anchor-graded two-option bound through the quotient**:

* **§1 The canonical-landing pincer** (decide-first outcome — the
  draft's "alive or unreachable-aside" resolves UNCONDITIONALLY: the
  receiver channels are dead at kings by `receivers_king_nil`, so
  every live-labeled TABLEAU future is the zero-spend hole channel —
  the root commit on a free anchor; the freeze premise of
  `labelLive_of_king_frozen` is needed ONLY to kill the stack
  channel, never for canonicality).  `king_live_tab_canonical`.

* **§2 The graded bound.**  The induced swap-orbit on usable vacant
  anchors (`kingLand`, `kingLandable`, `kingLandOrbit`) collapses at
  WF-deal states (`kingLandOrbit_iff`, mirroring §7's iff), the
  stack arm is deterministic (`kingStack_pair_class`) and — the
  freshness — a stack class meets NO landing class because the bump
  at the heights distinguishes the fibers (`kingStack_not_land_
  class`, the WF-deal same-deal fiber again).  Together:
  `king_pair_class_iff` — two futures of a king `Draw(X)` commit
  share the pile class EXACTLY when both are stack commits or both
  land on the SAME usable anchor.  That is the pair form of the
  count: the futures' classes are indexed by `{stack?} ∪
  usable-anchors` — the class-count is 1 + #(swap-orbits among
  usable vacant anchors) with singleton orbits at every WF-deal
  commitment; the first cut's pristine instance
  (`PileQuotientCorollaries.pristine_commit_firstCut_graded`) was
  the all-empty-point specialization with all-orbit-one.

* **§3 Pandemonium-free pigeonholes at the corner shapes** (no WF
  needed — the merges alone): the weak corner (≤ 1 usable anchor —
  the corpus's seed-26 ♣K world: any THREE futures share a class,
  `weak_corner_graded3`; the fates reading
  `weak_corner_graded3_fates`), the measured two-anchor world (any
  FOUR futures, `two_anchor_corner_graded4` + `_fates`), and the
  frozen weak-corner singleton (`weak_corner_frozen_class` — the
  quotient-graded subsumption of `c2_two_option_king_frozen`'s
  conclusion: ALL live futures are ONE class, via the pincer rather
  than the closureEq join).

* **§4 The measured corpus instances.**  The 6-anchor world
  (`ReachCorner.sState`: the king ♠K's usable anchors are exactly
  the six non-`p₀` anchors, the stack arm is dead —
  `rState_futures_sLand`, `rState_kingLandable_iff` — so the futures
  ARE the six landings, pairwise class-distinct in BOTH quotients
  (`rState_six_distinct`, `rState_six_content_distinct`): the graded
  bound's slack at the measured corner is ZERO).  The pristine
  corner's seven-futures collapse restated at the induced orbit
  (`pristine_oneContentClass` — the content merge through
  `KingAnchor.pileSwap_wSucc_washed`, the sibling wave's washed
  transposition identity).

Zero `sorry`.  Axiom pins at the file tail: `[propext, Quot.sound]`
for the count machinery (the pincer, the graded iff, the corner
pigeonholes, the cover lemmas); `[propext, Classical.choice,
Quot.sound]` exactly where the measured-corner instances consume the
siblings' decide-anchored exhibits (the rState six, the pristine
washed identity) — the same blessed sets those siblings pin.
-/

namespace PileQuotientOrbit

/-! ## §1. The canonical-landing pincer -/

/-- A king's tableau commit IS a free-anchor landing of the root
state (cite: `king_tableau_base` — the receiver arm is dead at
kings, `canPlace`'s anchor arm carries the freedom). -/
theorem king_landOutline {st : State} {X : Card} (hK : X.rank = Rank.king)
    {s : State} (htab : CommitTableau st X s) :
    ∃ a : Anchor, st.board.topOf (Sum.inl a) = none ∧
      st.applyDrawTo X (Sum.inl a) = some s := by
  obtain ⟨b, hcp, hto⟩ := htab
  obtain ⟨a, hbl, hfree⟩ := king_tableau_base hK hcp
  rw [hbl] at hto
  exact ⟨a, hfree, hto⟩

/-- The forced-shape death: a live label at a king is the hole or
the stack channel — `receivers_king_nil` kills the receiver
channels (direct, dig, borrow) at the CARD level, with no state
content consulted. -/
theorem king_live_le_hole {st : State} {X : Card} (hK : X.rank = Rank.king)
    {r : Label X} (hlive : LabelLive st X r) (hnea : r ≠ Label.hole) :
    r = Label.toStack := by
  cases r with
  | direct =>
      obtain ⟨Y, hd⟩ := hlive
      exact absurd hd.hY (receivers_king_nil hK)
  | dig =>
      obtain ⟨Y, hd⟩ := hlive
      exact absurd hd.hY (receivers_king_nil hK)
  | borrow p =>
      obtain ⟨hp, -⟩ := hlive
      exact absurd hp (receivers_king_nil hK)
  | toStack => rfl
  | hole => exact absurd rfl hnea

/-- **THE CANONICAL-LANDING PINCER.**  Every live-labeled TABLEAU
future of a king `Draw(X)` commitment is the ROOT commit's landing
on a free anchor: the receiver channels are dead at kings
(`king_live_le_hole`), and the hole channel's signature is the
empty play (`succThrough_zeroSpend`), so the commit fires at `st`
itself.  Hypothesis set: the king, `r ≠ toStack`, liveness, the
succ-through — no WF, no rung, no freeze, no anchor-count premise
(the draft's "unreachable-aside" leg is empty: kings have no
receiver channels at ANY state, reachable or not). -/
theorem king_live_tab_canonical {st : State} {X : Card} (hK : X.rank = Rank.king)
    {r : Label X} (hnot : r ≠ Label.toStack) (hlive : LabelLive st X r)
    {s : State} (h : SuccThrough st X r s) :
    ∃ a : Anchor, st.board.topOf (Sum.inl a) = none ∧
      st.applyDrawTo X (Sum.inl a) = some s := by
  by_cases hhole : r = Label.hole
  · rw [hhole] at h
    exact king_landOutline hK (succThrough_zeroSpend h (Or.inr rfl))
  · exact absurd (king_live_le_hole hK hlive hhole) hnot

/-! ## §2. The graded bound -/

/-- The stack arm's per-suit height read (the freshness carrier). -/
theorem kingStack_heights {st : State} {X : Card} {w : State}
    (hs : CommitStack st X w) :
    ∀ σ : Suit, w.heights σ =
      (if σ = X.suit then st.heights σ + 1 else st.heights σ) := by
  obtain ⟨i, hpos, hrk, hslit⟩ := applyDrawStackTo_iff.mp hs
  intro σ
  rw [hslit]

/-- The stack arm is deterministic — two stack futures are the same
class. -/
theorem kingStack_pair_class {st : State} {X : Card} {w w' : State}
    (hs : CommitStack st X w) (hs' : CommitStack st X w') :
    PileClass.mk w = PileClass.mk w' := by
  rw [show w = w' from Option.some.inj (hs.symm.trans hs')]

/-- **The stack freshness at WF-deal states:** a stack future's class
meets no anchor-landing class — an orbit between them would equal
the states (same deal, §6's fiber), but the stack commit bumped the
heights at the drawn card's suit while the landing kept them. -/
theorem kingStack_not_land_class {st : State} (hd : st.deal.WF) {X : Card}
    {w L : State} {a : Anchor}
    (hw : CommitStack st X w)
    (hL : st.applyDrawTo X (Sum.inl a) = some L) :
    PileClass.mk w ≠ PileClass.mk L := by
  intro hcon
  have hor : PileSwapOrbit w L := PileClass.exact hcon
  have hwd : w.deal = st.deal := by
    obtain ⟨i, hpos, hrk, hslit⟩ := applyDrawStackTo_iff.mp hw
    rw [hslit]
  have hLd : L.deal = st.deal := drawLand_deal hL
  have hwf : w.deal.WF := by rw [hwd]; exact hd
  have hdeal : L.deal = w.deal := hLd.trans hwd.symm
  have hstate : w = L := pileSwapOrbit_sameDeal_eq hwf hor hdeal
  have hhei := kingStack_heights hw (X.suit)
  have hLei : L.heights X.suit = st.heights X.suit := by
    rw [drawLand_heights hL]
  rw [hstate] at hhei
  rw [hLei] at hhei
  rw [ite_eq_left rfl] at hhei
  exact absurd hhei (by omega)

/-- The landing state of the anchor seat `a` (the repo's `getD`
idiom — the Prop-side consumers always guard by `kingLandable`). -/
def kingLand (st : State) (X : Card) (a : Anchor) : State :=
  (st.applyDrawTo X (Sum.inl a)).getD st

/-- `a` is USABLE at the commitment: the anchor landing fires. -/
def kingLandable (st : State) (X : Card) (a : Anchor) : Prop :=
  st.applyDrawTo X (Sum.inl a) = some (kingLand st X a)

/-- **The induced swap-orbit on usable vacant anchors** — the graded
bound's counting object: two anchors are orbit-related exactly when
their landing successors are `PileSwapOrbit`-related (on the
emptied-fragment reading the content variant of §7 of the lib file is
the honest coarsening: `PileContentClass.mk (kingLand … a₁) =
PileContentClass.mk (kingLand … a₂)` — see
`drawLand_content_eq_of_depthsZero`). -/
def kingLandOrbit (st : State) (X : Card) (a₁ a₂ : Anchor) : Prop :=
  PileSwapOrbit (kingLand st X a₁) (kingLand st X a₂)

/-- An anchor landing that fires makes the anchor usable. -/
theorem kingLandable_fires {st : State} {X : Card} {a : Anchor} {s : State}
    (h : st.applyDrawTo X (Sum.inl a) = some s) : kingLandable st X a := by
  show st.applyDrawTo X (Sum.inl a) = some (kingLand st X a)
  unfold kingLand
  rw [h]
  rfl

/-- Two landings on one anchor share the class (the landing map is
a function). -/
theorem king_land_pair_class {st : State} {X : Card} {a : Anchor} {s s' : State}
    (hta : st.applyDrawTo X (Sum.inl a) = some s)
    (hta' : st.applyDrawTo X (Sum.inl a) = some s') :
    PileClass.mk s = PileClass.mk s' := by
  rw [show s = s' from Option.some.inj (hta.symm.trans hta')]

/-- **THE INDUCED-ORBIT COLLAPSE.**  At a WF-deal state the induced
swap-orbit on usable vacant anchors is the IDENTITY: two usable
anchors are orbit-related exactly when equal (the lib §7 iff at the
`kingLand` spelling).  Hypothesis set: `st.deal.WF` and both
usabilities — no king (any drawn card), no liveness, no rung. -/
theorem kingLandOrbit_iff {st : State} (hd : st.deal.WF) {X : Card}
    {a₁ a₂ : Anchor}
    (q₁ : kingLandable st X a₁) (q₂ : kingLandable st X a₂) :
    kingLandOrbit st X a₁ a₂ ↔ a₁ = a₂ :=
  drawLand_pileSwapOrbit_iff hd q₁ q₂

/-- **THE KING-SIDE GRADED BOUND, PAIR FORM — the futures' count
read through the quotient.**  For a king `Draw(X)` commitment at a
WF-deal state, two futures share the pile class EXACTLY when both
are the (deterministic) stack commit, or both are the landing on
the SAME usable anchor.  With the singleton-orbit collapse
(`kingLandOrbit_iff`), this IS the count: the futures' classes are
`{the stack class, if it fires} ∪ {the landing class of each usable
vacant anchor}` — the class-count ≡ 1 + #(swap-orbits among usable
vacant anchors), and the merge side needs neither rung nor WF
(`king_pair_tabs_class`, `kingStack_pair_class`). -/
theorem king_pair_class_iff {st : State} (hd : st.deal.WF) {X : Card}
    (hK : X.rank = Rank.king) {s s' : State}
    (hs : commitApplies st (MacroMove.drawCommit X) s)
    (hs' : commitApplies st (MacroMove.drawCommit X) s') :
    (PileClass.mk s = PileClass.mk s') ↔
      ((CommitStack st X s ∧ CommitStack st X s') ∨
        ∃ a, st.applyDrawTo X (Sum.inl a) = some s ∧
             st.applyDrawTo X (Sum.inl a) = some s') := by
  constructor
  · intro hcon
    rcases (commitApplies_draw_cases st X s).mp hs with tb | k
    · obtain ⟨a, -, hta⟩ := king_landOutline hK tb
      rcases (commitApplies_draw_cases st X s').mp hs' with tb' | k'
      · obtain ⟨a', -, hta'⟩ := king_landOutline hK tb'
        have haa : a = a' :=
          drawLand_pileSwapOrbit_eq hd hta hta' (PileClass.exact hcon)
        rw [← haa] at hta'
        exact Or.inr ⟨a, hta, hta'⟩
      · exact absurd hcon.symm (kingStack_not_land_class hd k' hta)
    · rcases (commitApplies_draw_cases st X s').mp hs' with tb' | k'
      · obtain ⟨a, -, hta⟩ := king_landOutline hK tb'
        exact absurd hcon (kingStack_not_land_class hd k hta)
      · exact Or.inl ⟨k, k'⟩
  · intro h
    rcases h with ⟨k, k'⟩ | ⟨a, hta, hta'⟩
    · rw [show s = s' from Option.some.inj (k.symm.trans k')]
    · exact king_land_pair_class hta hta'

/-! ## §3. The corner pigeonholes (the merge side: no WF) -/

/-- Two tableau futures of a king commit join when every two usable
anchors coincide (the weak-corner world: the landing map collapses
to one anchor, hence to one class). -/
theorem king_pair_tabs_class {st : State} {X : Card} (hK : X.rank = Rank.king)
    (hale : ∀ a a' : Anchor, kingLandable st X a → kingLandable st X a' → a = a')
    {s s' : State} (htab : CommitTableau st X s) (htab' : CommitTableau st X s') :
    PileClass.mk s = PileClass.mk s' := by
  obtain ⟨a, -, hta⟩ := king_landOutline hK htab
  obtain ⟨a', -, hta'⟩ := king_landOutline hK htab'
  have haa : a = a' := hale a a' (kingLandable_fires hta) (kingLandable_fires hta')
  rw [← haa] at hta'
  exact king_land_pair_class hta hta'

/-- **THE WEAK-CORNER GRADED PIGEONHOLE** (the measured seed-26 ♣K
shape: one usable anchor).  Any THREE futures of a king `Draw(X)`
commit contain a same-class pair.  Hypothesis set: the king and the
≤-1-usable-anchor world — no WF, no rung, no freeze, no liveness
(the classes can only be the stack class and THE landing class). -/
theorem weak_corner_graded3 {st : State} {X : Card} (hK : X.rank = Rank.king)
    (hale : ∀ a a' : Anchor, kingLandable st X a → kingLandable st X a' → a = a')
    {s₁ s₂ s₃ : State}
    (h₁ : commitApplies st (MacroMove.drawCommit X) s₁)
    (h₂ : commitApplies st (MacroMove.drawCommit X) s₂)
    (h₃ : commitApplies st (MacroMove.drawCommit X) s₃) :
    PileClass.mk s₁ = PileClass.mk s₂ ∨
    PileClass.mk s₁ = PileClass.mk s₃ ∨
    PileClass.mk s₂ = PileClass.mk s₃ := by
  rcases (commitApplies_draw_cases st X s₁).mp h₁ with t₁ | k₁
  · rcases (commitApplies_draw_cases st X s₂).mp h₂ with t₂ | k₂
    · exact Or.inl (king_pair_tabs_class hK hale t₁ t₂)
    · rcases (commitApplies_draw_cases st X s₃).mp h₃ with t₃ | k₃
      · exact Or.inr (Or.inl (king_pair_tabs_class hK hale t₁ t₃))
      · exact Or.inr (Or.inr (kingStack_pair_class k₂ k₃))
  · rcases (commitApplies_draw_cases st X s₂).mp h₂ with t₂ | k₂
    · rcases (commitApplies_draw_cases st X s₃).mp h₃ with t₃ | k₃
      · exact Or.inr (Or.inr (king_pair_tabs_class hK hale t₂ t₃))
      · exact Or.inr (Or.inl (kingStack_pair_class k₁ k₃))
    · exact Or.inl (kingStack_pair_class k₁ k₂)

/-- The weak-corner pigeonhole through the quotient verdict. -/
theorem weak_corner_graded3_fates {st : State} {X : Card} (hK : X.rank = Rank.king)
    (hale : ∀ a a' : Anchor, kingLandable st X a → kingLandable st X a' → a = a')
    {s₁ s₂ s₃ : State}
    (h₁ : commitApplies st (MacroMove.drawCommit X) s₁)
    (h₂ : commitApplies st (MacroMove.drawCommit X) s₂)
    (h₃ : commitApplies st (MacroMove.drawCommit X) s₃) :
    (solvableQ (PileClass.mk s₁) ↔ solvableQ (PileClass.mk s₂)) ∨
    (solvableQ (PileClass.mk s₁) ↔ solvableQ (PileClass.mk s₃)) ∨
    (solvableQ (PileClass.mk s₂) ↔ solvableQ (PileClass.mk s₃)) := by
  rcases weak_corner_graded3 hK hale h₁ h₂ h₃ with q | q | q
  · exact Or.inl (by rw [q])
  · exact Or.inr (Or.inl (by rw [q]))
  · exact Or.inr (Or.inr (by rw [q]))

/-- Three tableau futures at a two-anchor world contain a
same-anchor pair (3-into-2, brace-by-brace). -/
theorem king_tabs3_pair_class {st : State} {X : Card} (hK : X.rank = Rank.king)
    (A B : Anchor) (hatwo : ∀ a : Anchor, kingLandable st X a → a = A ∨ a = B)
    {s₁ s₂ s₃ : State}
    (t₁ : CommitTableau st X s₁) (t₂ : CommitTableau st X s₂)
    (t₃ : CommitTableau st X s₃) :
    (PileClass.mk s₁ = PileClass.mk s₂) ∨
    (PileClass.mk s₁ = PileClass.mk s₃) ∨
    (PileClass.mk s₂ = PileClass.mk s₃) := by
  obtain ⟨a₁, -, hta₁⟩ := king_landOutline hK t₁
  obtain ⟨a₂, -, hta₂⟩ := king_landOutline hK t₂
  obtain ⟨a₃, -, hta₃⟩ := king_landOutline hK t₃
  have q₁ := kingLandable_fires hta₁
  have q₂ := kingLandable_fires hta₂
  have q₃ := kingLandable_fires hta₃
  rcases hatwo a₁ q₁ with h₁ | h₁
  · rcases hatwo a₂ q₂ with h₂ | h₂
    · rw [h₁.trans h₂.symm] at hta₁
      exact Or.inl (king_land_pair_class hta₁ hta₂)
    · rcases hatwo a₃ q₃ with h₃ | h₃
      · rw [h₁.trans h₃.symm] at hta₁
        exact Or.inr (Or.inl (king_land_pair_class hta₁ hta₃))
      · rw [h₂.trans h₃.symm] at hta₂
        exact Or.inr (Or.inr (king_land_pair_class hta₂ hta₃))
  · rcases hatwo a₂ q₂ with h₂ | h₂
    · rcases hatwo a₃ q₃ with h₃ | h₃
      · rw [h₂.trans h₃.symm] at hta₂
        exact Or.inr (Or.inr (king_land_pair_class hta₂ hta₃))
      · rw [h₁.trans h₃.symm] at hta₁
        exact Or.inr (Or.inl (king_land_pair_class hta₁ hta₃))
    · rcases hatwo a₃ q₃ with h₃ | h₃
      · rw [h₁.trans h₂.symm] at hta₁
        exact Or.inl (king_land_pair_class hta₁ hta₂)
      · rw [h₁.trans h₂.symm] at hta₁
        exact Or.inl (king_land_pair_class hta₁ hta₂)

/-- **THE TWO-ANCHOR GRADED PIGEONHOLE** (the corpus's measured
two-empty-piles concentration: `frozen2` at exactly 2 free piles).
Any FOUR futures of a king `Draw(X)` commit at a ≤-2-usable-anchor
state contain a same-class pair — the 1 + 2 = 3 pigeonhole.  No WF,
no rung, no freeze. -/
theorem two_anchor_corner_graded4 {st : State} {X : Card} (hK : X.rank = Rank.king)
    (A B : Anchor) (hatwo : ∀ a : Anchor, kingLandable st X a → a = A ∨ a = B)
    {s₁ s₂ s₃ s₄ : State}
    (h₁ : commitApplies st (MacroMove.drawCommit X) s₁)
    (h₂ : commitApplies st (MacroMove.drawCommit X) s₂)
    (h₃ : commitApplies st (MacroMove.drawCommit X) s₃)
    (h₄ : commitApplies st (MacroMove.drawCommit X) s₄) :
    (PileClass.mk s₁ = PileClass.mk s₂) ∨
    (PileClass.mk s₁ = PileClass.mk s₃) ∨
    (PileClass.mk s₁ = PileClass.mk s₄) ∨
    (PileClass.mk s₂ = PileClass.mk s₃) ∨
    (PileClass.mk s₂ = PileClass.mk s₄) ∨
    (PileClass.mk s₃ = PileClass.mk s₄) := by
  rcases (commitApplies_draw_cases st X s₁).mp h₁ with tb₁ | k₁
  · rcases (commitApplies_draw_cases st X s₂).mp h₂ with tb₂ | k₂
    · rcases (commitApplies_draw_cases st X s₃).mp h₃ with tb₃ | k₃
      · rcases (commitApplies_draw_cases st X s₄).mp h₄ with tb₄ | k₄
        · rcases king_tabs3_pair_class hK A B hatwo tb₁ tb₂ tb₃ with q | q | q
          · exact Or.inl q
          · exact Or.inr (Or.inl q)
          · exact Or.inr (Or.inr (Or.inr (Or.inl q)))
        · rcases king_tabs3_pair_class hK A B hatwo tb₁ tb₂ tb₃ with q | q | q
          · exact Or.inl q
          · exact Or.inr (Or.inl q)
          · exact Or.inr (Or.inr (Or.inr (Or.inl q)))
      · rcases (commitApplies_draw_cases st X s₄).mp h₄ with tb₄ | k₄
        · rcases king_tabs3_pair_class hK A B hatwo tb₁ tb₂ tb₄ with q | q | q
          · exact Or.inl q
          · exact Or.inr (Or.inr (Or.inl q))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (kingStack_pair_class k₃ k₄)))))
    · rcases (commitApplies_draw_cases st X s₃).mp h₃ with tb₃ | k₃
      · rcases (commitApplies_draw_cases st X s₄).mp h₄ with tb₄ | k₄
        · rcases king_tabs3_pair_class hK A B hatwo tb₁ tb₃ tb₄ with q | q | q
          · exact Or.inr (Or.inl q)
          · exact Or.inr (Or.inr (Or.inl q))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (kingStack_pair_class k₂ k₄)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (kingStack_pair_class k₂ k₃))))
  · rcases (commitApplies_draw_cases st X s₂).mp h₂ with tb₂ | k₂
    · rcases (commitApplies_draw_cases st X s₃).mp h₃ with tb₃ | k₃
      · rcases (commitApplies_draw_cases st X s₄).mp h₄ with tb₄ | k₄
        · rcases king_tabs3_pair_class hK A B hatwo tb₂ tb₃ tb₄ with q | q | q
          · exact Or.inr (Or.inr (Or.inr (Or.inl q)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))
        · exact Or.inr (Or.inr (Or.inl (kingStack_pair_class k₁ k₄)))
      · exact Or.inr (Or.inl (kingStack_pair_class k₁ k₃))
    · exact Or.inl (kingStack_pair_class k₁ k₂)

/-! ### The frozen weak corner: the singleton class -/

/-- **THE FROZEN WEAK-CORNER SINGLETON.**  At a frozen-suit king
corner with at most one free anchor (the hypothesis shape of
`c2_two_option_king_frozen` — the closureEq twin consumed for its
calibration: freeze + `hone`), ANY two live-labeled futures share
the pile class.  Stronger and different in kind from the closureEq
join: the futures are all THE ONE canonical landing (the pincer),
so the quotient collapses them outright — and the freeze premise is
used only to kill the stack channel, in keeping with §1. -/
theorem weak_corner_frozen_class {st : State} {X : Card} (hK : X.rank = Rank.king)
    (hone : ∀ a a' : Anchor, st.board.topOf (Sum.inl a) = none →
      st.board.topOf (Sum.inl a') = none → a = a')
    (hfroz : ¬ LabelLive st X Label.toStack)
    {s s' : State}
    (hl₁ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s)
    (hl₂ : ∃ r : Label X, LabelLive st X r ∧ SuccThrough st X r s') :
    PileClass.mk s = PileClass.mk s' := by
  obtain ⟨r₁, hl₁', hst₁⟩ := hl₁
  obtain ⟨r₂, hl₂', hst₂⟩ := hl₂
  have hn₁ : r₁ ≠ Label.toStack := fun hc => absurd (hc ▸ hl₁') hfroz
  have hn₂ : r₂ ≠ Label.toStack := fun hc => absurd (hc ▸ hl₂') hfroz
  obtain ⟨a₁, hfree₁, hta₁⟩ := king_live_tab_canonical hK hn₁ hl₁' hst₁
  obtain ⟨a₂, hfree₂, hta₂⟩ := king_live_tab_canonical hK hn₂ hl₂' hst₂
  have haa : a₁ = a₂ := hone a₁ a₂ hfree₁ hfree₂
  rw [← haa] at hta₂
  exact king_land_pair_class hta₁ hta₂

/-! ## §4. The measured corpus instances -/

/-- Spades witness cartridge. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩

/-! ### The 6-anchor world: `ReachCorner.sState` -/

/-- The reachable corner's six free anchors are exactly the
non-`p₀` ones — the p₀ seat holds the dealt head (the anchored ♠A of
the public deal). -/
theorem rState_p0_seated :
    ∃ c : Card, ReachCorner.sState.board.topOf (Sum.inl Anchor.p0) = some c := by
  refine ⟨S Rank.ace, ?_⟩
  show (initialBoard KingAnchor.wDeal).topOf
      (initBase KingAnchor.wDeal Anchor.p0) = some (S Rank.ace)
  rw [initialBoard_seats KingAnchor.wDeal ReachCorner.sDeal_wf Anchor.p0]
  decide

/-- The stack arm is dead at the reachable corner (king rung 12,
all heights 0). -/
theorem rState_stack_dead :
    ¬ ∃ w : State, CommitStack ReachCorner.sState (S Rank.king) w := by
  intro hwr
  obtain ⟨w, hw⟩ := hwr
  have hrk := heights_of_applyDrawStackTo hw
  have hh : ReachCorner.sState.heights (S Rank.king).suit = 0 := rfl
  rw [hh] at hrk
  have h12 : (S Rank.king).rank.toIdx = 12 := rfl
  rw [h12] at hrk
  exact absurd hrk (by omega)

/-- **THE 6-ANCHOR COVER:** every future of the king ♠K `Draw`
commitment at the reachable corner is one of the six landings on
the non-`p₀` anchors. -/
theorem rState_futures_sLand {s : State}
    (hs : commitApplies ReachCorner.sState
        (MacroMove.drawCommit (S Rank.king)) s) :
    ∃ a : Anchor, a ≠ Anchor.p0 ∧ s = ReachCorner.sLand a := by
  rcases (commitApplies_draw_cases ReachCorner.sState (S Rank.king) s).mp hs
    with tb | k
  · obtain ⟨a, hfree, hta⟩ := king_landOutline rfl tb
    refine ⟨a, ?_, ?_⟩
    · intro hap
      obtain ⟨c, hc⟩ := rState_p0_seated
      rw [hap] at hfree
      rw [hc] at hfree
      exact absurd hfree (by simp)
    · show s = (ReachCorner.sState.applyDrawTo (S Rank.king) (Sum.inl a)).getD
        ReachCorner.sState
      rw [hta]
      rfl
  · exact absurd ⟨s, k⟩ rState_stack_dead

/-- The measured world's usable-anchor characterization. -/
theorem rState_kingLandable_iff {a : Anchor} :
    kingLandable ReachCorner.sState (S Rank.king) a ↔ a ≠ Anchor.p0 := by
  constructor
  · intro hq hap
    rw [hap] at hq
    obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq hq
    obtain ⟨c, hc⟩ := rState_p0_seated
    have hfree : ReachCorner.sState.board.topOf (Sum.inl Anchor.p0) = none :=
      ((Board.attach_eq_some_iff ReachCorner.sState.board
        (Sum.inl Anchor.p0) (S Rank.king)).mp (by rw [hatt]; simp)).1
    rw [hc] at hfree
    exact absurd hfree (by simp)
  · intro h
    exact kingLandable_fires (ReachCorner.sLand_apply h)

/-- The reachable corner's king landings are pairwise
class-DISTINCT in the pure quotient — six singleton orbits; the
graded bound is TIGHT at the measured corner (the wave-20
countermodels are orbit-real: six content-carrying futures, no
quotient mercy from the pure classes). -/
theorem rState_six_distinct {a b : Anchor}
    (ha : a ≠ Anchor.p0) (hb : b ≠ Anchor.p0) (hab : a ≠ b) :
    PileClass.mk (ReachCorner.sLand a) ≠ PileClass.mk (ReachCorner.sLand b) := by
  have hfa : ReachCorner.sState.applyDrawTo (S Rank.king) (Sum.inl a)
      = some (ReachCorner.sLand a) := ReachCorner.sLand_apply ha
  have hfb : ReachCorner.sState.applyDrawTo (S Rank.king) (Sum.inl b)
      = some (ReachCorner.sLand b) := ReachCorner.sLand_apply hb
  have hwf : ReachCorner.sState.deal.WF := by
    show KingAnchor.wDeal.WF
    exact ReachCorner.sDeal_wf
  exact drawLand_pile_class_inj hwf hfa hfb hab

/-- The reachable corner is not all-emptied — the hidden stacks run
depths `0..6`. -/
theorem rState_not_depthsZero : ¬ ReachCorner.sState.depthsZero := by
  intro hz
  have h6 : ReachCorner.sState.depths Anchor.p6 = 0 := hz Anchor.p6
  have h6' : ReachCorner.sState.depths Anchor.p6 = Anchor.p6.toIdx := rfl
  rw [h6'] at h6
  exact absurd h6 (by decide)

/-- The six landings are pairwise distinct in the CONTENT quotient
too — anchor names are content at the measured corner; the
separation survives the wash (§4 purity + §7 injectivity). -/
theorem rState_six_content_distinct {a b : Anchor}
    (ha : a ≠ Anchor.p0) (hb : b ≠ Anchor.p0) (hab : a ≠ b) :
    PileContentClass.mk (ReachCorner.sLand a)
      ≠ PileContentClass.mk (ReachCorner.sLand b) := by
  have hfa : ReachCorner.sState.applyDrawTo (S Rank.king) (Sum.inl a)
      = some (ReachCorner.sLand a) := ReachCorner.sLand_apply ha
  have hfb : ReachCorner.sState.applyDrawTo (S Rank.king) (Sum.inl b)
      = some (ReachCorner.sLand b) := ReachCorner.sLand_apply hb
  have hwf : ReachCorner.sState.deal.WF := by
    show KingAnchor.wDeal.WF
    exact ReachCorner.sDeal_wf
  exact drawLand_content_class_inj hwf rState_not_depthsZero hfa hfb hab

/-! ### The pristine corner -/

/-- **THE PRISTINE 7-FUTURES COLLAPSE, THROUGH THE INDUCED ORBIT.**
The seven closure-separated anchor landings of the KingAnchor
pristine corner (the wave-18 refutation's labeled classes) are ONE
content class: the sibling wave's washed transposition identity
(`KingAnchor.pileSwap_wSucc_washed`) is exactly the two-step content
orbit — swap, then the inert-deal wash the all-emptied state
licenses (`KingAnchor.wSucc_depthsZero`).  The first cut's
`emptyPiles_land_content_eq` instance, restated at the induced-orbit
level: usable anchors at an all-emptied state carry no content at
all (`drawLand_content_eq_of_depthsZero`'s world). -/
theorem pristine_oneContentClass (a₁ a₂ : Anchor) :
    PileContentClass.mk (KingAnchor.wSucc a₁)
      = PileContentClass.mk (KingAnchor.wSucc a₂) := by
  refine Quot.sound ?_
  rw [show KingAnchor.wSucc a₂ =
      ((KingAnchor.wSucc a₁).swapPiles a₁ a₂).setDeal KingAnchor.wDeal
        from (KingAnchor.pileSwap_wSucc_washed a₁ a₂).symm]
  exact EqvClosure.trans
    (EqvClosure.single (Or.inl ⟨a₁, a₂, rfl⟩))
    (EqvClosure.single (Or.inr ⟨State.depthsZero_swapPiles
      (KingAnchor.wSucc_depthsZero a₁) a₁ a₂, KingAnchor.wDeal, rfl⟩))

end PileQuotientOrbit

/-! ### Axiom pins -/

/-- info: 'PileQuotientOrbit.king_landOutline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.king_landOutline

/-- info: 'PileQuotientOrbit.king_live_le_hole' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.king_live_le_hole

/-- info: 'PileQuotientOrbit.king_live_tab_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.king_live_tab_canonical

/-- info: 'PileQuotientOrbit.kingStack_heights' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.kingStack_heights

/-- info: 'PileQuotientOrbit.kingStack_pair_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.kingStack_pair_class

/-- info: 'PileQuotientOrbit.kingStack_not_land_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.kingStack_not_land_class

/-- info: 'PileQuotientOrbit.kingLandable_fires' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.kingLandable_fires

/-- info: 'PileQuotientOrbit.king_land_pair_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.king_land_pair_class

/-- info: 'PileQuotientOrbit.kingLandOrbit_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.kingLandOrbit_iff

/-- info: 'PileQuotientOrbit.king_pair_class_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.king_pair_class_iff

/-- info: 'PileQuotientOrbit.king_pair_tabs_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.king_pair_tabs_class

/-- info: 'PileQuotientOrbit.weak_corner_graded3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.weak_corner_graded3

/-- info: 'PileQuotientOrbit.weak_corner_graded3_fates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.weak_corner_graded3_fates

/-- info: 'PileQuotientOrbit.king_tabs3_pair_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.king_tabs3_pair_class

/-- info: 'PileQuotientOrbit.two_anchor_corner_graded4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.two_anchor_corner_graded4

/-- info: 'PileQuotientOrbit.weak_corner_frozen_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.weak_corner_frozen_class

/-- info: 'PileQuotientOrbit.rState_p0_seated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.rState_p0_seated

/-- info: 'PileQuotientOrbit.rState_stack_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.rState_stack_dead

/-- info: 'PileQuotientOrbit.rState_futures_sLand' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.rState_futures_sLand

/-- info: 'PileQuotientOrbit.rState_kingLandable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.rState_kingLandable_iff

/-- info: 'PileQuotientOrbit.rState_six_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.rState_six_distinct

/-- info: 'PileQuotientOrbit.rState_not_depthsZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.rState_not_depthsZero

/-- info: 'PileQuotientOrbit.rState_six_content_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.rState_six_content_distinct

/-- info: 'PileQuotientOrbit.pristine_oneContentClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PileQuotientOrbit.pristine_oneContentClass
