import Klondike.Restriction
import Klondike.TwinQuotient
import Witnesses.EngineWitness

/-!
# The reachability probe for B2 (Restriction.lean's refute-first gate)

The EngineWitness state (`wstate`, the reveal-deadlock refutation of the
naive no-pile-to-pile iff, `Witnesses.EngineWitness`) is **not reachable
from its own deal** — by ANY play, engine or full.  So the
`initialReachable` hypothesis of `solvableEngine_iff_solvable_of_reachable`
(Restriction.lean:78) is doing exactly its job: the witness lives off the
dealt-reachable fragment, and the statement stands as written.

The certificate is a small probe invariant.  Pile `p3` of `wdeal` is
mono-suit — `[♥10, ♥9, ♥8, ♥7]` — and its inner edges form ONLY through
reveals, in descending dig order (`wh9 := wh8` at the 3 → 2 reveal,
`wh10 := wh9` at the 2 → 1 reveal); every other attach passes
`canSitOn`, so a severed same-suit link never heals, and digging deeper
requires the boundary's cover bare — a vacation that breaks exactly such
a link.  The watchdog (p3 is never simultaneously fully dug and
chain-intact):

    ProbeInv st :=  depths p3 ≠ 0
                  ∨ topOf (inr wh10) ≠ some wh9
                  ∨ topOf (inr wh9)  ≠ some wh8
                  ∨ topOf (inr wh8)  ≠ some wh7

— `wstate` falsifies all four (depth 0, chain pristine).  The one
subtlety is the kill-move, the 1 → 0 reveal: it needs the boundary's
cover BARE, and the auxiliary invariant pins that cover to `wh9` (the
seat of the still-hidden `wh10` rejects `canPlace`-gated attaches, and
the only reveal deposit there is the 2 → 1 reveal's `wh9`) — so when the
killer fires, the `wh9 := wh8` link is already broken, and the killer's
own attach lands at the anchor, off the watched seats.
-/

namespace EngineWitness

/-- The deal never changes along a step. -/
theorem apply_deal {st st' : State} {m : Move} (h : st.apply m = some st') :
    st'.deal = st.deal := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at h; obtain rfl := h; rfl
  | reveal c =>
      rw [apply_reveal_iff] at h
      obtain ⟨-, -, -, -, -, -, -, rfl⟩ := h; rfl
  | deckPile c b =>
      rw [apply_deckPile_iff] at h
      obtain ⟨-, -, -, -, rfl⟩ := h; rfl
  | deckStack c =>
      rw [apply_deckStack_iff] at h
      obtain ⟨-, -, rfl⟩ := h; rfl
  | pileStack c =>
      rw [apply_pileStack_iff] at h
      obtain ⟨-, -, -, -, rfl⟩ := h; rfl
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨-, -, -, -, rfl⟩ := h; rfl
  | pilePile c b =>
      rw [apply_pilePile_iff] at h
      obtain ⟨-, -, -, -, -, -, rfl⟩ := h; rfl

/-- The deal never changes along a play. -/
theorem run_deal : ∀ (play : List Move) (st st' : State),
    st.run play = some st' → st'.deal = st.deal := by
  intro play
  induction play with
  | nil =>
      intro st st' h
      simp only [State.run] at h
      obtain rfl := Option.some.inj h
      rfl
  | cons m ms ih =>
      intro st st' h
      simp only [State.run] at h
      cases hap : st.apply m with
      | none => rw [hap] at h; exact absurd h (by simp)
      | some R => rw [hap] at h; exact (ih R st' h).trans (apply_deal hap)

/-- The probe invariant. -/
def ProbeInv (st : State) : Prop :=
  (st.depths Anchor.p3 ≠ 0
    ∨ st.board.topOf (Sum.inr wh10) ≠ some wh9
    ∨ st.board.topOf (Sum.inr wh9) ≠ some wh8
    ∨ st.board.topOf (Sum.inr wh8) ≠ some wh7)
  ∧ (∀ X, st.depths Anchor.p3 ≠ 0 → st.board.topOf (Sum.inr wh10) = some X → X = wh9)
  ∧ st.depths Anchor.p3 ≤ 3

/-! ### Small computation helpers -/

/-- A take-membership is a membership. -/
theorem mem_of_take {l : List Card} {k : Nat} {c : Card} (h : c ∈ l.take k) : c ∈ l := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
      cases k with
      | zero => simp at h
      | succ k =>
          rw [List.take_succ_cons] at h
          rcases List.mem_cons.mp h with hh | hh
          · exact List.mem_cons.mpr (Or.inl hh)
          · exact List.mem_cons.mpr (Or.inr (ih hh))

/-- The `wdeal` pile-`p3` content. -/
theorem wdeal_piles_p3 : wdeal.piles Anchor.p3 = [wh10, wh9, wh8, wh7] := rfl

/-- A `p3` pile-card's membership pins the anchor. -/
theorem anchor_eq_p3_of_p3_mem {q : Card} {a : Anchor}
    (hq3 : q ∈ wdeal.piles Anchor.p3) (hm : q ∈ wdeal.piles a) : a = Anchor.p3 := by
  rw [wdeal_piles_p3] at hq3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq3
  rcases hq3 with rfl | rfl | rfl | rfl <;> revert hm <;> cases a <;> decide

/-- Off-`p3` reveals deposit nowhere near the watched seats. -/
theorem hiddenBase_ne_p3_cards {st : State} (hdeal : st.deal = wdeal) {a : Anchor}
    (ha3 : a ≠ Anchor.p3) :
    st.hiddenBase a ≠ Sum.inr wh10 ∧ st.hiddenBase a ≠ Sum.inr wh9
      ∧ st.hiddenBase a ≠ Sum.inr wh8 := by
  have hkey : ∀ q : Card, (q ∈ wdeal.piles Anchor.p3) → st.hiddenBase a ≠ Sum.inr q := by
    intro q hq hbq
    have hqin : q ∈ st.hidden a := State.mem_hidden_of_hiddenBase hbq
    rw [State.hidden, hdeal] at hqin
    have hq2 : q ∈ wdeal.piles a := mem_of_take hqin
    exact absurd (anchor_eq_p3_of_p3_mem hq hq2) ha3
  exact ⟨hkey wh10 (by rw [wdeal_piles_p3]; decide),
    hkey wh9 (by rw [wdeal_piles_p3]; decide),
    hkey wh8 (by rw [wdeal_piles_p3]; decide)⟩

/-- `wh10` is hidden whenever the pile is unfinished (depth ≥ 1). -/
theorem wh10_hidden {st : State} (hdeal : st.deal = wdeal)
    (h0 : st.depths Anchor.p3 ≠ 0) : wh10 ∈ st.hidden Anchor.p3 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
  show wh10 ∈ (st.deal.piles Anchor.p3).take (st.depths Anchor.p3)
  rw [hdeal, hk, wdeal_piles_p3, List.take_succ_cons]
  exact List.mem_cons_self

/-- The mono-suit card arithmetic: no same-color reattachment. -/
theorem canSitOn_wh9_wh10 : canSitOn wh9 wh10 = false := by decide
theorem canSitOn_wh8_wh9 : canSitOn wh8 wh9 = false := by decide
theorem canSitOn_wh7_wh8 : canSitOn wh7 wh8 = false := by decide

/-- Initial satisfaction. -/
theorem probeInv_initial (s : Nat) : ProbeInv (State.initial wdeal s) := by
  have hb0 : (State.initial wdeal s).board = initialBoard wdeal := rfl
  have htop10 : (initialBoard wdeal).topOf (Sum.inr wh10) = none := by decide
  refine ⟨Or.inl ?_, ?_, ?_⟩
  · show (fun a => a.toIdx) Anchor.p3 ≠ 0; decide
  · intro X _ hX
    rw [hb0, htop10] at hX
    exact absurd hX (by simp)
  · show (fun a => a.toIdx) Anchor.p3 ≤ 3; decide

/-- **Maintenance**: the probe invariant survives every move (the full
game, not just the engine's).  Needs WF (hidden cards' seats reject
`canPlace`) and the deal being `wdeal`. -/
theorem probeInv_apply {st st' : State} (hdeal : st.deal = wdeal) (hwf : st.WF)
    (hI : ProbeInv st) {m : Move} (h : st.apply m = some st') : ProbeInv st' := by
  obtain ⟨hmain, haux, hmax⟩ := hI
  cases m with
  | draw =>
      rw [apply_draw_iff] at h; obtain rfl := h
      exact ⟨hmain, haux, hmax⟩
  | deckStack c =>
      rw [apply_deckStack_iff] at h; obtain ⟨-, -, rfl⟩ := h
      exact ⟨hmain, haux, hmax⟩
  | reveal c =>
      rw [apply_reveal_iff] at h
      obtain ⟨ht, r, a, bd, hbot, hpile, hatt, rfl⟩ := h
      by_cases ha3 : a = Anchor.p3
      · subst ha3
        obtain ⟨-, hth⟩ := findFirst_mem (fun a' => decide (st.topHidden a' = some r))
          Anchor.all Anchor.p3 hpile
        have hth' : st.topHidden Anchor.p3 = some r := of_decide_eq_true hth
        have hk4 : st.depths Anchor.p3 = 0 ∨ st.depths Anchor.p3 = 1 ∨
            st.depths Anchor.p3 = 2 ∨ st.depths Anchor.p3 = 3 := by omega
        rcases hk4 with hk | hk | hk | hk
        · -- depth 0: nothing hidden — no reveal can fire here
          have hnothing : st.topHidden Anchor.p3 = none := by
            show (st.hidden Anchor.p3).getLast? = none
            rw [State.hidden, hdeal, hk, wdeal_piles_p3]; rfl
          rw [hnothing] at hth'
          exact absurd hth' (by simp)
        · -- **the killer** (1 → 0): the aux pins the cover to wh9, which
          -- must be bare — so the wh9-seat link is already broken, and the
          -- killer's attach lands at the anchor, off the watched seats.
          have hbv : st.hidden Anchor.p3 = [wh10] := by
            rw [State.hidden, hdeal, hk, wdeal_piles_p3]; rfl
          have hbdlist : ((st.hidden Anchor.p3).reverse.drop 1).head? = none := by
            rw [hbv]; rfl
          have hr10 : r = wh10 := by
            have h1 : st.topHidden Anchor.p3 = some wh10 := by
              show (st.hidden Anchor.p3).getLast? = some wh10
              rw [hbv]; rfl
            exact Option.some.inj (hth'.symm.trans h1)
          have hcb : c = wh9 := by
            rw [hr10] at hbot
            exact haux c (by rw [hk]; decide) ((Board.bottomOf_eq _ _ _).mp hbot)
          subst hr10; subst hcb
          have hbase : st.hiddenBase Anchor.p3 = Sum.inl Anchor.p3 := by
            show (match ((st.hidden Anchor.p3).reverse.drop 1).head? with
              | some d => Sum.inr d | none => Sum.inl Anchor.p3) = _
            rw [hbdlist]
          rw [hbase] at hatt
          refine ⟨?_, ?_, ?_⟩
          · show (if Anchor.p3 = Anchor.p3 then st.depths Anchor.p3 - 1
                else st.depths Anchor.p3) ≠ 0
                ∨ bd.topOf (Sum.inr wh10) ≠ some wh9
                ∨ bd.topOf (Sum.inr wh9) ≠ some wh8
                ∨ bd.topOf (Sum.inr wh8) ≠ some wh7
            rw [if_pos rfl]
            refine Or.inr (Or.inr (Or.inl ?_))
            have hne : Sum.inr wh9 ≠ Sum.inl Anchor.p3 := by decide
            rw [Board.attach_topOf_ne _ _ _ hatt hne, ht]
            simp
          · show ∀ X, (if Anchor.p3 = Anchor.p3 then st.depths Anchor.p3 - 1
                else st.depths Anchor.p3) ≠ 0 →
                bd.topOf (Sum.inr wh10) = some X → X = wh9
            intro X hX0 hXtop
            rw [if_pos rfl, hk] at hX0
            exact absurd rfl hX0
          · show (if Anchor.p3 = Anchor.p3 then st.depths Anchor.p3 - 1
                else st.depths Anchor.p3) ≤ 3
            rw [if_pos rfl]
            omega
        · -- 2 → 1: deposits wh9 on wh10's seat (feeds the aux); depth stays ≥ 1
          have hbv : st.hidden Anchor.p3 = [wh10, wh9] := by
            rw [State.hidden, hdeal, hk, wdeal_piles_p3]; rfl
          have hr9 : r = wh9 := by
            have h1 : st.topHidden Anchor.p3 = some wh9 := by
              show (st.hidden Anchor.p3).getLast? = some wh9
              rw [hbv]; rfl
            exact Option.some.inj (hth'.symm.trans h1)
          have hbase : st.hiddenBase Anchor.p3 = Sum.inr wh10 := by
            show (match ((st.hidden Anchor.p3).reverse.drop 1).head? with
              | some d => Sum.inr d | none => Sum.inl Anchor.p3) = _
            rw [hbv]; rfl
          subst hr9
          rw [hbase] at hatt
          refine ⟨?_, ?_, ?_⟩
          · show st.depths Anchor.p3 - 1 ≠ 0
                ∨ bd.topOf (Sum.inr wh10) ≠ some wh9
                ∨ bd.topOf (Sum.inr wh9) ≠ some wh8
                ∨ bd.topOf (Sum.inr wh8) ≠ some wh7
            rw [hk]
            exact Or.inl (by decide)
          · show ∀ X, st.depths Anchor.p3 - 1 ≠ 0 →
                bd.topOf (Sum.inr wh10) = some X → X = wh9
            intro X _ hX
            rw [Board.attach_topOf _ _ _ hatt] at hX
            exact (Option.some.inj hX).symm
          · show st.depths Anchor.p3 - 1 ≤ 3
            omega
        · -- 3 → 2: deposits wh8 on wh9's seat (forms that link, but depth
          -- ≥ 2 carries the invariant); wh10's cover is untouched
          have hbv : st.hidden Anchor.p3 = [wh10, wh9, wh8] := by
            rw [State.hidden, hdeal, hk, wdeal_piles_p3]; rfl
          have hr8 : r = wh8 := by
            have h1 : st.topHidden Anchor.p3 = some wh8 := by
              show (st.hidden Anchor.p3).getLast? = some wh8
              rw [hbv]; rfl
            exact Option.some.inj (hth'.symm.trans h1)
          have hbase : st.hiddenBase Anchor.p3 = Sum.inr wh9 := by
            show (match ((st.hidden Anchor.p3).reverse.drop 1).head? with
              | some d => Sum.inr d | none => Sum.inl Anchor.p3) = _
            rw [hbv]; rfl
          subst hr8
          rw [hbase] at hatt
          refine ⟨?_, ?_, ?_⟩
          · show st.depths Anchor.p3 - 1 ≠ 0
                ∨ bd.topOf (Sum.inr wh10) ≠ some wh9
                ∨ bd.topOf (Sum.inr wh9) ≠ some wh8
                ∨ bd.topOf (Sum.inr wh8) ≠ some wh7
            exact Or.inl (by rw [hk]; decide)
          · show ∀ X, st.depths Anchor.p3 - 1 ≠ 0 →
                bd.topOf (Sum.inr wh10) = some X → X = wh9
            intro X _ hX
            have hne : (Sum.inr wh10 : Base) ≠ Sum.inr wh9 := by decide
            rw [Board.attach_topOf_ne _ _ _ hatt hne] at hX
            exact haux X (by rw [hk]; decide) hX
          · show st.depths Anchor.p3 - 1 ≤ 3
            omega
      · -- another pile's reveal: the deposit base is off every watched seat
        obtain ⟨hne10, hne9, hne8⟩ := hiddenBase_ne_p3_cards hdeal ha3
        refine ⟨?_, ?_, ?_⟩
        · show (if Anchor.p3 = a then st.depths a - 1 else st.depths Anchor.p3) ≠ 0
              ∨ bd.topOf (Sum.inr wh10) ≠ some wh9
              ∨ bd.topOf (Sum.inr wh9) ≠ some wh8
              ∨ bd.topOf (Sum.inr wh8) ≠ some wh7
          rw [if_neg (fun hh => ha3 hh.symm)]
          rcases hmain with h0 | h1 | h2 | h3
          · exact Or.inl h0
          · exact Or.inr (Or.inl (by
              rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hne10 hh.symm)]
              exact h1))
          · exact Or.inr (Or.inr (Or.inl (by
              rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hne9 hh.symm)]
              exact h2)))
          · exact Or.inr (Or.inr (Or.inr (by
              rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hne8 hh.symm)]
              exact h3)))
        · show ∀ X, (if Anchor.p3 = a then st.depths a - 1 else st.depths Anchor.p3) ≠ 0 →
              bd.topOf (Sum.inr wh10) = some X → X = wh9
          intro X hX0 hX
          rw [if_neg (fun hh => ha3 hh.symm)] at hX0
          rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hne10 hh.symm)] at hX
          exact haux X hX0 hX
        · show (if Anchor.p3 = a then st.depths a - 1 else st.depths Anchor.p3) ≤ 3
          rw [if_neg (fun hh => ha3 hh.symm)]
          exact hmax
  | deckPile c b =>
      rw [apply_deckPile_iff] at h
      obtain ⟨hp, hcp, bd, hatt, rfl⟩ := h
      refine ⟨?_, ?_, ?_⟩
      · show st.depths Anchor.p3 ≠ 0
            ∨ bd.topOf (Sum.inr wh10) ≠ some wh9
            ∨ bd.topOf (Sum.inr wh9) ≠ some wh8
            ∨ bd.topOf (Sum.inr wh8) ≠ some wh7
        rcases hmain with h0 | h1 | h2 | h3
        · exact Or.inl h0
        · by_cases hb : b = Sum.inr wh10
          · subst hb
            obtain ⟨-, -, hcs⟩ := canPlace_inr_iff.mp hcp
            refine Or.inr (Or.inl ?_)
            intro hcon
            rw [Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hcon
            subst hcon
            rw [canSitOn_wh9_wh10] at hcs; exact absurd hcs (by simp)
          · refine Or.inr (Or.inl ?_)
            rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)]
            exact h1
        · by_cases hb : b = Sum.inr wh9
          · subst hb
            obtain ⟨-, -, hcs⟩ := canPlace_inr_iff.mp hcp
            refine Or.inr (Or.inr (Or.inl ?_))
            intro hcon
            rw [Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hcon
            subst hcon
            rw [canSitOn_wh8_wh9] at hcs; exact absurd hcs (by simp)
          · refine Or.inr (Or.inr (Or.inl ?_))
            rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)]
            exact h2
        · by_cases hb : b = Sum.inr wh8
          · subst hb
            obtain ⟨-, -, hcs⟩ := canPlace_inr_iff.mp hcp
            refine Or.inr (Or.inr (Or.inr ?_))
            intro hcon
            rw [Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hcon
            subst hcon
            rw [canSitOn_wh7_wh8] at hcs; exact absurd hcs (by simp)
          · refine Or.inr (Or.inr (Or.inr ?_))
            rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)]
            exact h3
      · show ∀ X, st.depths Anchor.p3 ≠ 0 → bd.topOf (Sum.inr wh10) = some X → X = wh9
        intro X hX0 hX
        by_cases hb : b = Sum.inr wh10
        · subst hb
          exfalso
          obtain ⟨-, hvis, -⟩ := canPlace_inr_iff.mp hcp
          exact hwf.vis_not_hidden wh10 hvis Anchor.p3 (wh10_hidden hdeal hX0)
        · rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)] at hX
          exact haux X hX0 hX
      · exact hmax
  | pileStack c =>
      rw [apply_pileStack_iff] at h
      obtain ⟨ht, b, hb, hrk, rfl⟩ := h
      refine ⟨?_, ?_, ?_⟩
      · show st.depths Anchor.p3 ≠ 0
            ∨ (st.board.detach b).topOf (Sum.inr wh10) ≠ some wh9
            ∨ (st.board.detach b).topOf (Sum.inr wh9) ≠ some wh8
            ∨ (st.board.detach b).topOf (Sum.inr wh8) ≠ some wh7
        rcases hmain with h0 | h1 | h2 | h3
        · exact Or.inl h0
        · by_cases hb' : b = Sum.inr wh10
          · subst hb'
            exact Or.inr (Or.inl (by rw [Board.detach_topOf]; simp))
          · refine Or.inr (Or.inl ?_)
            rw [Board.detach_topOf_ne _ _ _ (fun hh => hb' hh.symm)]
            exact h1
        · by_cases hb' : b = Sum.inr wh9
          · subst hb'
            exact Or.inr (Or.inr (Or.inl (by rw [Board.detach_topOf]; simp)))
          · refine Or.inr (Or.inr (Or.inl ?_))
            rw [Board.detach_topOf_ne _ _ _ (fun hh => hb' hh.symm)]
            exact h2
        · by_cases hb' : b = Sum.inr wh8
          · subst hb'
            exact Or.inr (Or.inr (Or.inr (by rw [Board.detach_topOf]; simp)))
          · refine Or.inr (Or.inr (Or.inr ?_))
            rw [Board.detach_topOf_ne _ _ _ (fun hh => hb' hh.symm)]
            exact h3
      · show ∀ X, st.depths Anchor.p3 ≠ 0 →
            (st.board.detach b).topOf (Sum.inr wh10) = some X → X = wh9
        intro X hX0 hX
        by_cases hb' : b = Sum.inr wh10
        · subst hb'
          rw [Board.detach_topOf] at hX
          exact absurd hX (by simp)
        · rw [Board.detach_topOf_ne _ _ _ (fun hh => hb' hh.symm)] at hX
          exact haux X hX0 hX
      · exact hmax
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨hrk, hcp, bd, hatt, rfl⟩ := h
      refine ⟨?_, ?_, ?_⟩
      · show st.depths Anchor.p3 ≠ 0
            ∨ bd.topOf (Sum.inr wh10) ≠ some wh9
            ∨ bd.topOf (Sum.inr wh9) ≠ some wh8
            ∨ bd.topOf (Sum.inr wh8) ≠ some wh7
        rcases hmain with h0 | h1 | h2 | h3
        · exact Or.inl h0
        · by_cases hb : b = Sum.inr wh10
          · subst hb
            obtain ⟨-, -, hcs⟩ := canPlace_inr_iff.mp hcp
            refine Or.inr (Or.inl ?_)
            intro hcon
            rw [Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hcon
            subst hcon
            rw [canSitOn_wh9_wh10] at hcs; exact absurd hcs (by simp)
          · refine Or.inr (Or.inl ?_)
            rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)]
            exact h1
        · by_cases hb : b = Sum.inr wh9
          · subst hb
            obtain ⟨-, -, hcs⟩ := canPlace_inr_iff.mp hcp
            refine Or.inr (Or.inr (Or.inl ?_))
            intro hcon
            rw [Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hcon
            subst hcon
            rw [canSitOn_wh8_wh9] at hcs; exact absurd hcs (by simp)
          · refine Or.inr (Or.inr (Or.inl ?_))
            rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)]
            exact h2
        · by_cases hb : b = Sum.inr wh8
          · subst hb
            obtain ⟨-, -, hcs⟩ := canPlace_inr_iff.mp hcp
            refine Or.inr (Or.inr (Or.inr ?_))
            intro hcon
            rw [Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hcon
            subst hcon
            rw [canSitOn_wh7_wh8] at hcs; exact absurd hcs (by simp)
          · refine Or.inr (Or.inr (Or.inr ?_))
            rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)]
            exact h3
      · show ∀ X, st.depths Anchor.p3 ≠ 0 → bd.topOf (Sum.inr wh10) = some X → X = wh9
        intro X hX0 hX
        by_cases hb : b = Sum.inr wh10
        · subst hb
          exfalso
          obtain ⟨-, hvis, -⟩ := canPlace_inr_iff.mp hcp
          exact hwf.vis_not_hidden wh10 hvis Anchor.p3 (wh10_hidden hdeal hX0)
        · rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)] at hX
          exact haux X hX0 hX
      · exact hmax
  | pilePile c b =>
      rw [apply_pilePile_iff] at h
      obtain ⟨b₀, hbot, hbne, hcmr, bd, hatt, rfl⟩ := h
      have hcp : st.canPlace c b = true := by
        cases b with
        | inl a => exact canMoveRun_inl_iff.mp hcmr
        | inr d => exact (canMoveRun_inr_iff.mp hcmr).1
      refine ⟨?_, ?_, ?_⟩
      · show st.depths Anchor.p3 ≠ 0
            ∨ bd.topOf (Sum.inr wh10) ≠ some wh9
            ∨ bd.topOf (Sum.inr wh9) ≠ some wh8
            ∨ bd.topOf (Sum.inr wh8) ≠ some wh7
        rcases hmain with h0 | h1 | h2 | h3
        · exact Or.inl h0
        · by_cases hb : b = Sum.inr wh10
          · subst hb
            obtain ⟨-, -, hcs⟩ := canPlace_inr_iff.mp hcp
            refine Or.inr (Or.inl ?_)
            intro hcon
            rw [Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hcon
            subst hcon
            rw [canSitOn_wh9_wh10] at hcs; exact absurd hcs (by simp)
          · by_cases hb0 : b₀ = Sum.inr wh10
            · subst hb0
              refine Or.inr (Or.inl ?_)
              rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm), Board.detach_topOf]
              intro hcon
              exact absurd hcon (by simp)
            · refine Or.inr (Or.inl ?_)
              rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)]
              rw [Board.detach_topOf_ne _ _ _ (fun hh => hb0 hh.symm)]
              exact h1
        · by_cases hb : b = Sum.inr wh9
          · subst hb
            obtain ⟨-, -, hcs⟩ := canPlace_inr_iff.mp hcp
            refine Or.inr (Or.inr (Or.inl ?_))
            intro hcon
            rw [Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hcon
            subst hcon
            rw [canSitOn_wh8_wh9] at hcs; exact absurd hcs (by simp)
          · by_cases hb0 : b₀ = Sum.inr wh9
            · subst hb0
              refine Or.inr (Or.inr (Or.inl ?_))
              rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm), Board.detach_topOf]
              intro hcon
              exact absurd hcon (by simp)
            · refine Or.inr (Or.inr (Or.inl ?_))
              rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)]
              rw [Board.detach_topOf_ne _ _ _ (fun hh => hb0 hh.symm)]
              exact h2
        · by_cases hb : b = Sum.inr wh8
          · subst hb
            obtain ⟨-, -, hcs⟩ := canPlace_inr_iff.mp hcp
            refine Or.inr (Or.inr (Or.inr ?_))
            intro hcon
            rw [Board.attach_topOf _ _ _ hatt, Option.some.injEq] at hcon
            subst hcon
            rw [canSitOn_wh7_wh8] at hcs; exact absurd hcs (by simp)
          · by_cases hb0 : b₀ = Sum.inr wh8
            · subst hb0
              refine Or.inr (Or.inr (Or.inr ?_))
              rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm), Board.detach_topOf]
              intro hcon
              exact absurd hcon (by simp)
            · refine Or.inr (Or.inr (Or.inr ?_))
              rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)]
              rw [Board.detach_topOf_ne _ _ _ (fun hh => hb0 hh.symm)]
              exact h3
      · show ∀ X, st.depths Anchor.p3 ≠ 0 →
            bd.topOf (Sum.inr wh10) = some X → X = wh9
        intro X hX0 hX
        by_cases hb : b = Sum.inr wh10
        · subst hb
          exfalso
          obtain ⟨-, hvis, -⟩ := canPlace_inr_iff.mp hcp
          exact hwf.vis_not_hidden wh10 hvis Anchor.p3 (wh10_hidden hdeal hX0)
        · by_cases hb0 : b₀ = Sum.inr wh10
          · subst hb0
            rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm), Board.detach_topOf] at hX
            exact absurd hX (by simp)
          · rw [Board.attach_topOf_ne _ _ _ hatt (fun hh => hb hh.symm)] at hX
            rw [Board.detach_topOf_ne _ _ _ (fun hh => hb0 hh.symm)] at hX
            exact haux X hX0 hX
      · exact hmax

/-- The invariant holds along every play. -/
theorem probeInv_run : ∀ (play : List Move) (st0 st : State),
    st0.deal = wdeal → st0.WF → ProbeInv st0 →
    st0.run play = some st → ProbeInv st := by
  intro play
  induction play with
  | nil =>
      intro st0 st _ _ hI h
      simp only [State.run] at h
      obtain rfl := Option.some.inj h
      exact hI
  | cons m ms ih =>
      intro st0 st hdeal hwf hI h
      simp only [State.run] at h
      cases hap : st0.apply m with
      | none => rw [hap] at h; exact absurd h (by simp)
      | some R =>
          rw [hap] at h
          exact ih R st ((apply_deal hap).trans hdeal) (apply_wf hwf m R hap)
            (probeInv_apply hdeal hwf hI hap) h

/-- The witness violates the invariant: p3 is fully dug (depth 0) with the
pristine mono-heart chain `wh10 := wh9 := wh8 := wh7`. -/
theorem wstate_not_probeInv : ¬ ProbeInv wstate := by
  intro hI
  obtain ⟨hd, -, -⟩ := hI
  rcases hd with h0 | h1 | h2 | h3
  · exact h0 (by decide)
  · exact h1 (by decide)
  · exact h2 (by decide)
  · exact h3 (by decide)

/-- **The probe verdict**: the EngineWitness state is not reachable from
any dealt game (constancy pins the deal to `wdeal`).  In particular B2's
`solvableEngine_iff_solvable_of_reachable` is NOT wounded by the
EngineWitness: the reveal-deadlock lives outside the dealt-reachable
fragment.  Maintenance covers the full move set — the engine's
restriction to engine moves is not even needed for the fence. -/
theorem wstate_not_reachable : ¬ initialReachable wstate := by
  rintro ⟨d, s, play, hdWF, hstep, hrun⟩
  have h1 : wstate.deal = (State.initial d s).deal := run_deal play _ _ hrun
  have hd : d = wdeal := by
    have h2 : (State.initial d s).deal = d := rfl
    have h3 : wstate.deal = wdeal := rfl
    rw [h3, h2] at h1
    exact h1.symm
  subst hd
  exact wstate_not_probeInv (probeInv_run play (State.initial wdeal s) wstate rfl
    (initial_wf wdeal_wf hstep) (probeInv_initial s) hrun)

end EngineWitness
