import Klondike.PileSwap
import Klondike.Initial
import Witnesses.C2KingAnchorWitness

/-!
# PileSwapConsequences — wave-21: what the pile symmetry changes
about today's witnesses

The pile transposition Π (`Klondike/PileSwap.lean`) renames
*positions* the way the twin fibration renames cards.  This file
cashes it in against the wave-18/20 witness results:

* **§1 THE PRISTINE COLLAPSE.**  At `KingAnchor.wState` (the C2
  pristine board: empty matching, all depths zero) the seven anchor
  landings `KingAnchor.wSucc a` — pairwise **closure-separated** by
  the wave-18 refutation's labeled classes — are all related by pile
  transpositions *up to the inert deal*: transposing the piles of
  `wSucc a₁` by `a₁ ↔ a₂` and washing the deal back to `wDeal`
  *is* `wSucc a₂` (`KingAnchor.pileSwap_wSucc_washed`); the wash is
  solvability-inert at an all-hidden-empty state
  (`State.solvableFrom_setDeal_iff_of_depthsZero`), hence any two
  landings are equi-solvable (`KingAnchor.pileSwap_all_landings`,
  with the any-two-states reading
  `KingAnchor.pileSwap_all_landings'`).  **Reading:** the wave-18
  refutation (`wSucc` is unsolvable, at every anchor, in *seven
  separated labeled classes*) stands literally as stated — the state
  labels differ — but its *content* is one future class up to Π:
  the pristine board's piles are all fully empty, so the anchor
  names carry no distinguishing content, and the seven futures
  are a single solvable-fate class.

* **§2 THE REACHABLE CORNER SURVIVES.**  `SuccLabeledWitness.rState`
  is private, so the survival content is replicated here on the
  public `KingAnchor.wDeal` deal: the dealt initial state
  `ReachCorner.sState = State.initial wDeal 1` has genuinely
  distinct hidden stacks per pile — depths `0..6`, slices `1..7`
  long (`ReachCorner.sHidden_distinct`, decide-anchored).  Its king
  landings `ReachCorner.sLand a` (free anchors) are **not related
  by any transposition** (`ReachCorner.sLand_swapRelated_iff`: a
  swap-relation forces `i = j ∧ a = b`), because a swap-relation
  between same-deal states forces the trivial transposition
  (`swapPiles_eq_sameDeal_forced_eq`) while the WF deal's slices
  have pairwise distinct lengths.  **Reading:** unlike the pristine
  board, the wave-20 reachable refutation's separated successors
  are content-real — the hidden-stack content survives the Π
  quotient, and the anchored-head route's countermodels do not
  collapse.

* **§3 THE SHARPENED GRADED BOUND — first cut.**  At a commitment
  over a state whose piles are ALL fully empty (empty matching and
  all depths zero), the king landings on any two anchors are
  equi-solvable (`emptyPiles_kingLandings_collapse`): the fully-empty
  piles form a single swap-class, so the closure-separated king
  futures bounded by the swap-classes are at most ONE, not k.  The
  pristine `KingAnchor.wState` corner is the concrete instance.

Axiom targets: `[propext, (Classical.choice,) Quot.sound]`; zero
`sorryAx`.  All the symmetry-side machinery is in the lib
(`Klondike/PileSwap.lean`, axiom-clean); the only `decide`-anchored
facts here (`sHidden_distinct`, the `wDeal.WF` replay) are kernel
computations.
-/

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- Conjugating the empty board's landing on `a₁` by the
transposition yields the landing board on `a₂` — the visible content
of the empty-pile corner's orbit.  Instance-free: only the
`attach_topOf/_ne` readings of the two one-edge boards and the
anchor involution. -/
theorem attach_empty_conj {bd₁ bd₂ : Board} {a₁ a₂ : Anchor} {c : Card}
    (h1 : Board.empty.attach (Sum.inl a₁) c = some bd₁)
    (h2 : Board.empty.attach (Sum.inl a₂) c = some bd₂) :
    bd₁.mapByPileSwap a₁ a₂ = bd₂ := by
  refine Board.ext_topOf (funext (fun b => ?_))
  rw [mapByPileSwap_topOf]
  cases b with
  | inl x =>
      show bd₁.topOf (Sum.inl (Anchor.swap a₁ a₂ x)) = bd₂.topOf (Sum.inl x)
      by_cases hx : x = a₂
      · have hxs : Anchor.swap a₁ a₂ x = a₁ := by
          rw [hx, Anchor.swap_self_right]
        rw [hxs, Board.attach_topOf _ _ _ h1, hx, Board.attach_topOf _ _ _ h2]
      · have hxs : (Sum.inl (Anchor.swap a₁ a₂ x) : Base) ≠ Sum.inl a₁ := by
          intro hcon
          have hh := congrArg (Anchor.swap a₁ a₂) (Sum.inl.inj hcon)
          rw [Anchor.swap_swap] at hh
          rw [Anchor.swap_self_left] at hh
          exact hx hh
        have hxs2 : (Sum.inl x : Base) ≠ Sum.inl a₂ := by
          intro hcon
          exact hx (Sum.inl.inj hcon)
        rw [Board.attach_topOf_ne _ _ _ h1 hxs, Board.empty_topOf,
            Board.attach_topOf_ne _ _ _ h2 hxs2, Board.empty_topOf]
  | inr cd =>
      show bd₁.topOf (Base.swapBase (Sum.inr cd) a₁ a₂) = bd₂.topOf (Sum.inr cd)
      rw [show Base.swapBase (Sum.inr cd) a₁ a₂ = Sum.inr cd from rfl,
        Board.attach_topOf_ne _ _ _ h1 (by simp), Board.empty_topOf,
        Board.attach_topOf_ne _ _ _ h2 (by simp), Board.empty_topOf]

/-! ## §1. The pristine collapse -/

namespace KingAnchor

/-- The empty board accepts the king at every anchor — the C2
witness's private `wAttach`, replayed so the visible orbit of the
landing boards can be computed here. -/
private theorem wAttach' (a : Anchor) :
    wState.board.attach (Sum.inl a) (S .king) = some (wBoard a) := by
  have h1 : wState.board.topOf (Sum.inl a) = none := rfl
  have h2 : wState.board.bottomOf (S .king) = none := rfl
  unfold Board.attach
  rw [dite_eq_left h1, dite_eq_left h2]
  refine congrArg some (Board.ext_topOf (funext (fun b' => ?_)))
  by_cases hb : b' = Sum.inl a
  · rw [hb]
    show Board.update Board.empty.topOf (Sum.inl a) (some (S .king))
        (Sum.inl a) = (if Sum.inl a = Sum.inl a then some (S .king) else none)
    rw [Board.update_self, ite_eq_left rfl]
  · show Board.update Board.empty.topOf (Sum.inl a) (some (S .king)) b'
      = (if b' = Sum.inl a then some (S .king) else none)
    rw [Board.update_ne _ _ _ _ hb, ite_eq_right hb]
    exact Board.empty_topOf b'

theorem wBoard_empty_attach (a : Anchor) :
    Board.empty.attach (Sum.inl a) (S .king) = some (wBoard a) := by
  have hw := wAttach' a
  have hbe : wState.board = Board.empty := rfl
  rw [hbe] at hw
  exact hw

/-- The transposed one-edge landing board is the landing board of the
transposed anchor — the boards are the visible part of the
transposition's orbit. -/
theorem wBoard_mapByPileSwap (a₁ a₂ : Anchor) :
    (wBoard a₁).mapByPileSwap a₁ a₂ = wBoard a₂ :=
  attach_empty_conj (wBoard_empty_attach a₁) (wBoard_empty_attach a₂)

/-- The pristine state's piles are all fully empty. -/
theorem wState_depthsZero : wState.depthsZero := fun _ => rfl

/-- Each landing state's piles remain fully empty. -/
theorem wSucc_depthsZero (a : Anchor) : (wSucc a).depthsZero := by
  intro a'
  rw [wS_shape a]
  rfl

/-- **The orbit step:** transposing a landing state's piles and washing
the deal back restores the transposed anchor's landing state.  The
wash is legitimate because the landing's piles are all fully empty
(the deal is inert there), and the wash exactly undoes the slice
travel that the full-state transposition performs on the deal. -/
theorem pileSwap_wSucc_washed (a₁ a₂ : Anchor) :
    ((wSucc a₁).swapPiles a₁ a₂).setDeal wDeal = wSucc a₂ := by
  rw [wS_shape a₁, wS_shape a₂]
  refine state_ext rfl ?_ rfl ?_ rfl rfl
  · have hbb : ({ wState with
                 board := wBoard a₁,
                 stock := ⟨Cycle.removeIdx wState.stock.cards 0, 0⟩ } : State).board
        = wBoard a₁ := rfl
    show (State.swapPiles ({ wState with
                             board := wBoard a₁,
                             stock := ⟨Cycle.removeIdx wState.stock.cards 0, 0⟩ }
              : State) a₁ a₂).board = wBoard a₂
    rw [State.swapPiles_board, hbb, wBoard_mapByPileSwap]
  · funext x
    show wState.depths (Anchor.swap a₁ a₂ x) = wState.depths x
    rfl

/-- **THE PRISTINE COLLAPSE:** any two of the seven anchor landings
are equi-solvable.  The wave-18 refutation's labeled classes are
distinct states; up to Π (plus the inert-deal wash) they are ONE
future. -/
theorem pileSwap_all_landings (a₁ a₂ : Anchor) :
    (wSucc a₁).solvableFrom ↔ (wSucc a₂).solvableFrom := by
  constructor
  · intro hs
    have h1 : ((wSucc a₁).swapPiles a₁ a₂).solvableFrom :=
      (solvable_swapPiles_iff a₁ a₂ (wSucc a₁)).mp hs
    have h1z : ((wSucc a₁).swapPiles a₁ a₂).depthsZero :=
      State.depthsZero_swapPiles (wSucc_depthsZero a₁) a₁ a₂
    have h2 : (((wSucc a₁).swapPiles a₁ a₂).setDeal wDeal).solvableFrom :=
      (State.solvableFrom_setDeal_iff_of_depthsZero h1z wDeal).mp h1
    rw [pileSwap_wSucc_washed] at h2
    exact h2
  · intro hs
    have h1 : ((wSucc a₂).swapPiles a₂ a₁).solvableFrom :=
      (solvable_swapPiles_iff a₂ a₁ (wSucc a₂)).mp hs
    have h1z : ((wSucc a₂).swapPiles a₂ a₁).depthsZero :=
      State.depthsZero_swapPiles (wSucc_depthsZero a₂) a₂ a₁
    have h2 : (((wSucc a₂).swapPiles a₂ a₁).setDeal wDeal).solvableFrom :=
      (State.solvableFrom_setDeal_iff_of_depthsZero h1z wDeal).mp h1
    rw [pileSwap_wSucc_washed] at h2
    exact h2

/-- The same collapse, at any two landing *states*. -/
theorem pileSwap_all_landings' {s₁ s₂ : State}
    (h₁ : ∃ a, s₁ = wSucc a) (h₂ : ∃ a, s₂ = wSucc a) :
    s₁.solvableFrom ↔ s₂.solvableFrom := by
  obtain ⟨a₁, rfl⟩ := h₁
  obtain ⟨a₂, rfl⟩ := h₂
  exact pileSwap_all_landings a₁ a₂

end KingAnchor

/-! ## §2. The reachable corner survives -/

namespace ReachCorner

open KingAnchor

/-- The wave-20 reachable corner, replicated on the public deal
(`SuccLabeledWitness.rState` is private): the dealt initial state —
all seven piles headed, hidden stacks of depths `0..6` over slices
of lengths `1..7`. -/
def sState : State := State.initial wDeal 1

/-- The deal is WF (the C2 file's proof is private; this is the same
computation). -/
theorem sDeal_wf : wDeal.WF := by
  refine ⟨fun a => ?_, by decide, ?_⟩
  · cases a <;> decide
  · intro i j hi hj heq
    have hflat : (Anchor.all.flatMap wDeal.piles).length = 28 := by decide
    have hstock : wDeal.stock.length = 24 := by decide
    rw [List.length_append, hflat, hstock] at hi hj
    have hall : ∀ i ∈ List.range 52, ∀ j ∈ List.range 52,
        (Anchor.all.flatMap wDeal.piles ++ wDeal.stock)[i]? =
          (Anchor.all.flatMap wDeal.piles ++ wDeal.stock)[j]? → i = j := by decide
    exact hall i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) heq

theorem sState_wf : sState.WF := initial_wf sDeal_wf (by omega)

/-- **Decide-anchored:** the hidden stacks genuinely differ per pile —
no two piles of the dealt corner share their hidden content. -/
theorem sHidden_distinct : ∀ a ∈ Anchor.all, ∀ a' ∈ Anchor.all,
    sState.hidden a = sState.hidden a' → a = a' := by
  decide

/-- No pile head is the spade king (all seven heads are decided). -/
theorem sNoKingHead (a : Anchor) : (wDeal.piles a).getLast? ≠ some (S .king) := by
  cases a <;> decide

/-- On the dealt initial board, no anchor seat is occupied except
`p₀`'s (every head sits on an `initBase` — card-seats for the
`p₁..p₆` heads, the `p₀` head on the anchor). -/
theorem sBoard_inl_none (a : Anchor) (x : Card) (h : a ≠ Anchor.p0) :
    sState.board.topOf (Sum.inl a) ≠ some x := by
  intro htop
  obtain ⟨a', _, hb, -⟩ := initialBoard_topOf wDeal (Sum.inl a) x htop
  cases a' <;> simp_all [initBase, Anchor.toIdx, wDeal]

theorem sBoard_none (a : Anchor) (h : a ≠ Anchor.p0) :
    sState.board.topOf (Sum.inl a) = none := by
  match hs : sState.board.topOf (Sum.inl a) with
  | none => rfl
  | some x => exact absurd hs (sBoard_inl_none a x h)

/-- The spade king sits nowhere on the dealt initial board. -/
theorem sNoKingSeated : sState.board.bottomOf (S .king) = none := by
  refine (Board.bottomOf_eq_none _ _).mpr (fun b hb => ?_)
  obtain ⟨a', _, -, hlast⟩ := initialBoard_topOf wDeal b (S .king) hb
  exact sNoKingHead a' hlast

/-- The spade king is the dealt stock's head — the commitment is
available at the initial cursor, as in the pristine corner. -/
theorem sReachablePos : sState.reachablePos (S .king) = some 0 := by
  rw [State.reachablePos_step1 sState_wf rfl (S .king)]
  rfl

/-- The king-landing successor on the free anchor `a`
(the wave-20 `rLand` shape, replicated). -/
def sLand (a : Anchor) : State :=
  (sState.applyDrawTo (S .king) (Sum.inl a)).getD sState

theorem sLand_apply {a : Anchor} (h : a ≠ Anchor.p0) :
    sState.applyDrawTo (S .king) (Sum.inl a) = some (sLand a) := by
  have htop : sState.board.topOf (Sum.inl a) = none := sBoard_none a h
  have hbot : sState.board.bottomOf (S .king) = none := sNoKingSeated
  have hreach : sState.reachablePos (S .king) = some 0 := sReachablePos
  obtain ⟨bd, hatt⟩ : ∃ bd, sState.board.attach (Sum.inl a) (S .king) = some bd := by
    have hne : sState.board.attach (Sum.inl a) (S .king) ≠ none :=
      Board.attach_eq_some_iff _ _ _ |>.mpr ⟨htop, hbot⟩
    cases hc : sState.board.attach (Sum.inl a) (S .king) with
    | none => rw [hc] at hne; exact absurd hne (by simp)
    | some bd0 => exact ⟨bd0, rfl⟩
  have hto : sState.applyDrawTo (S .king) (Sum.inl a)
      = some { sState with board := bd, stock := (sState.stock.drawTo 0).removeAt 0 } :=
    applyDrawTo_iff.mpr ⟨0, bd, hreach, hatt, rfl⟩
  cases hs : sState.applyDrawTo (S .king) (Sum.inl a) with
  | none => rw [hs] at hto; exact absurd hto (by simp)
  | some s' =>
      have hw : sLand a = s' := by
        show (sState.applyDrawTo (S .king) (Sum.inl a)).getD sState = s'
        rw [hs]
        rfl
      rw [hw]

theorem sLand_shape {a : Anchor} (h : a ≠ Anchor.p0) :
    ∃ bd, (sLand a).deal = sState.deal ∧
      sState.board.attach (Sum.inl a) (S .king) = some bd ∧
      (∀ b : Base, ((sLand a).board.topOf b = some (S .king) ∧ b = Sum.inl a)
        ∨ ((sLand a).board.topOf b = sState.board.topOf b ∧ b ≠ Sum.inl a)) := by
  obtain ⟨i, bd, hpos, hatt, hs⟩ := applyDrawTo_eq (sLand_apply h)
  refine ⟨bd, ?_, hatt, ?_⟩
  · rw [hs]
  · intro b
    rw [hs]
    by_cases hb : b = Sum.inl a
    · refine Or.inl ⟨?_, hb⟩
      rw [hb, Board.attach_topOf _ _ _ hatt]
    · refine Or.inr ⟨?_, hb⟩
      rw [Board.attach_topOf_ne _ _ _ hatt hb]

theorem sLand_topSame {a : Anchor} (h : a ≠ Anchor.p0) :
    (sLand a).board.topOf (Sum.inl a) = some (S .king) := by
  obtain ⟨bd, -, hatt, hshape⟩ := sLand_shape h
  rcases hshape (Sum.inl a) with ⟨h1, -⟩ | ⟨-, hne⟩
  · exact h1
  · exact absurd rfl hne

theorem sLand_topOther {a x : Anchor} (ha : a ≠ Anchor.p0) (hx : x ≠ Anchor.p0)
    (hne : (Sum.inl x : Base) ≠ Sum.inl a) :
    (sLand a).board.topOf (Sum.inl x) = none := by
  obtain ⟨bd, -, hatt, hshape⟩ := sLand_shape ha
  rcases hshape (Sum.inl x) with ⟨-, hxe⟩ | ⟨h1, -⟩
  · exact absurd hxe hne
  · rw [h1]
    exact sBoard_none x hx

theorem sLand_deal {a : Anchor} (h : a ≠ Anchor.p0) :
    (sLand a).deal = sState.deal := by
  obtain ⟨bd, hdeal, -⟩ := sLand_shape h
  exact hdeal

/-- **THE SURVIVAL:** the reachable corner's separated king landings
are *not* related by any pile transposition.  A swap-relation swaps
deal slices, so across two same-deal states it forces `i = j` (the
WF deal's slices have pairwise distinct lengths); the degenerate
swap is the identity, and two landings on different anchors read
differently on the anchor seats. -/
theorem sLand_swapRelated_iff (i j a b : Anchor) (ha : a ≠ Anchor.p0) (hb : b ≠ Anchor.p0) :
    (sLand a).swapPiles i j = sLand b ↔ i = j ∧ a = b := by
  constructor
  · intro hsw
    have hdeal : (sLand b).deal = (sLand a).deal := by
      rw [sLand_deal hb, sLand_deal ha]
    have hij : i = j := by
      refine swapPiles_eq_sameDeal_forced_eq (hd := ?_) hsw hdeal
      rw [sLand_deal ha]
      exact sDeal_wf
    rw [hij] at hsw
    rw [State.swapPiles_self] at hsw
    have h1 : (sLand a).board.topOf (Sum.inl a) = some (S .king) :=
      sLand_topSame ha
    rw [hsw] at h1
    by_cases hab : a = b
    · exact ⟨hij, hab⟩
    · exfalso
      have hnone : (sLand b).board.topOf (Sum.inl a) = none :=
        sLand_topOther hb ha (fun hcon => hab (Sum.inl.inj hcon))
      rw [hnone] at h1
      exact absurd h1 (by simp)
  · intro ⟨hij, hab⟩
    subst hij
    subst hab
    rw [State.swapPiles_self]

/-- The wave-20 reachable refutations are **content-real**: two
landings on different free anchors are related by *no* pile
transposition — the hidden-stack content survives the symmetry
quotient. -/
theorem rState_survives (a b : Anchor) (ha : a ≠ Anchor.p0) (hb : b ≠ Anchor.p0)
    (hab : a ≠ b) : ∀ i j : Anchor, (sLand a).swapPiles i j ≠ sLand b := by
  intro i j hcon
  have h := (sLand_swapRelated_iff i j a b ha hb).mp hcon
  exact hab h.2

end ReachCorner

/-! ## §3. The sharpened graded bound — the first cut -/

/-- **The first-cut graded bound:** at a state whose piles are all
fully empty (empty matching, every depth zero), the king-commitment
landings on ANY two anchors are equi-solvable — the k vacant anchors
form a single swap-class (m = 1), so the closure-separated king
futures number at most one up to solvable content, not k.  The
pristine `KingAnchor.wState` corner is the concrete instance; here
the collapse is stated for an arbitrary all-empty-pile state. -/
theorem emptyPiles_kingLandings_collapse {st : State}
    (hz : st.depthsZero) (hb : st.board = Board.empty)
    (hreach : st.reachablePos (S .king) = some i₀)
    (a₁ a₂ : Anchor) {L₁ L₂ : State}
    (hL₁ : st.applyDrawTo (S .king) (Sum.inl a₁) = some L₁)
    (hL₂ : st.applyDrawTo (S .king) (Sum.inl a₂) = some L₂) :
    L₁.solvableFrom ↔ L₂.solvableFrom := by
  obtain ⟨i₁, bd₁, hp₁, hatt₁, hs₁⟩ := applyDrawTo_eq hL₁
  obtain ⟨i₂, bd₂, hp₂, hatt₂, hs₂⟩ := applyDrawTo_eq hL₂
  have hi₁ : i₁ = i₀ := Option.some.inj (hp₁.symm.trans hreach)
  have hi₂ : i₂ = i₀ := Option.some.inj (hp₂.symm.trans hreach)
  rw [hi₁] at hs₁
  rw [hi₂] at hs₂
  have hatt₁' : Board.empty.attach (Sum.inl a₁) (S .king) = some bd₁ := by
    rw [show st.board = Board.empty from hb] at hatt₁
    exact hatt₁
  have hatt₂' : Board.empty.attach (Sum.inl a₂) (S .king) = some bd₂ := by
    rw [show st.board = Board.empty from hb] at hatt₂
    exact hatt₂
  have hbd : bd₁.mapByPileSwap a₁ a₂ = bd₂ := attach_empty_conj hatt₁' hatt₂'
  -- the washed transposition of L₁ is L₂:
  have hwash : (L₁.swapPiles a₁ a₂).setDeal st.deal = L₂ := by
    rw [hs₁, hs₂]
    refine state_ext rfl ?_ rfl ?_ rfl rfl
    · show bd₁.mapByPileSwap a₁ a₂ = bd₂
      rw [hbd]
    · funext x
      show st.depths (Anchor.swap a₁ a₂ x) = st.depths x
      rw [hz x]
      exact hz _
  constructor
  · intro hsol
    have h1 : (L₁.swapPiles a₁ a₂).solvableFrom :=
      (solvable_swapPiles_iff a₁ a₂ L₁).mp hsol
    have hL1z : L₁.depthsZero := by
      intro a'
      rw [hs₁]
      exact hz a'
    have h1z : (L₁.swapPiles a₁ a₂).depthsZero :=
      State.depthsZero_swapPiles hL1z a₁ a₂
    have h2 : ((L₁.swapPiles a₁ a₂).setDeal st.deal).solvableFrom :=
      (State.solvableFrom_setDeal_iff_of_depthsZero h1z st.deal).mp h1
    rw [hwash] at h2
    exact h2
  · intro hsol
    have h1 : (L₂.swapPiles a₂ a₁).solvableFrom :=
      (solvable_swapPiles_iff a₂ a₁ L₂).mp hsol
    have hL2z : L₂.depthsZero := by
      intro a'
      rw [hs₂]
      exact hz a'
    have h1z : (L₂.swapPiles a₂ a₁).depthsZero :=
      State.depthsZero_swapPiles hL2z a₂ a₁
    have h2 : ((L₂.swapPiles a₂ a₁).setDeal st.deal).solvableFrom :=
      (State.solvableFrom_setDeal_iff_of_depthsZero h1z st.deal).mp h1
    have hwash' : (L₂.swapPiles a₂ a₁).setDeal st.deal = L₁ := by
      rw [hs₂, hs₁]
      refine state_ext rfl ?_ rfl ?_ rfl rfl
      · show bd₂.mapByPileSwap a₂ a₁ = bd₁
        rw [← hbd, Board.mapByPileSwap_rev]
      · funext x
        show st.depths (Anchor.swap a₂ a₁ x) = st.depths x
        rw [hz x]
        exact hz _
    rw [hwash'] at h2
    exact h2

/-! ### Axiom pins -/

/-- info: 'KingAnchor.pileSwap_all_landings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KingAnchor.pileSwap_all_landings

/-- info: 'KingAnchor.pileSwap_all_landings'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KingAnchor.pileSwap_all_landings'

/-- info: 'KingAnchor.pileSwap_wSucc_washed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KingAnchor.pileSwap_wSucc_washed

/-- info: 'ReachCorner.sLand_swapRelated_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReachCorner.sLand_swapRelated_iff

/-- info: 'ReachCorner.rState_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReachCorner.rState_survives

/-- info: 'emptyPiles_kingLandings_collapse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emptyPiles_kingLandings_collapse

/-- info: 'solvable_swapPiles_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms solvable_swapPiles_iff
