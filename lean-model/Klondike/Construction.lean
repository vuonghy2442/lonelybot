import Klondike.Restriction

/-!
# The sufficiency construction — the endgame fragments

`initialReachable` (Restriction.lean) is a deposit: a deal, a step, a
play.  The fences prove that reachability *implies* invariants
(`visClean`, `accounted`, WF, …).  This file is the other direction's
first rung: for a state whose shape carries no cycle bookkeeping, a
play exists — the sufficiency construction, per the wave-20 ladder:

1. **Fragment (1), the pristine endgame** (this file): target states
   with EMPTY stock (`st.stock = ⟨[], 0⟩`), draw step 1, no reveals
   (`depths = toIdx`), no foundations (`heights = 0`), and a board
   that is the seven initial edges plus rider chains fed from the
   stock — `PristineEndgame st → initialReachable st`.
2. **Fragment (2), the stockful endgame** (this file, wave 21): target
   states with a general loaded cycle — the construction consumes the
   AWAY cards (the deal's stock minus the target cycle) in the same
   rank-tier descent (with the anchor-rider arm for kings), rotates
   the phase onto the target cursor with the pure-draw tail, and
   closes the end-state deck match through the filter identities.
3. **Fragment (3), the assembled iff** (this file, wave 21):
   `StockfulEndgame_iff_initialReachable` — the distillate is exactly
   dealt-reachability under the four pristine flights (necessity
   decoded from the standing fences; see the fence ledger in
   `Restriction.lean`'s wave-21 stock-side section).  Launching the
   flights (the reveal/foundation evacuation geometry, the draw-3
   batch discipline — whose standalone arithmetic sits at this file's
   tail) is the next rung (FARM.md ticket 1).

The scaffolding lemmas (the draw iteration, the consume round, the
tier descent) are deliberately reusable across both fragments.

## The construction (fragment 1)

The deal is *forced* (`run` never rewrites `deal` or `drawStep`, so
the witness deal is `st.deal` itself and the witness step is
`st.drawStep`); the only freedom is the play.  At draw step 1 every
in-stock card can be brought to the waste top: the cursor walks to
the pass end, wraps to zero, and re-advances — segments of pure
`draw`s, then one `deckPile`.  Nothing about the stock's order can
obstruct the schedule, so the "landing geometry" precondition
reduces to the per-edge shape below.

The seating order is the **rank-tier descent**: process rider cards
from rank 12 down to rank 0 (`st.deal.stock.filter` per rank — the
schedule is data, no choice).  Each rider `x` sits (at the target) on
a card base `Sum.inr d` with `canSitOn x d`, so `d` is either a dealt
tail (seated since the deal) or another stock rider of rank exactly
one higher — processed one tier earlier, hence already seated.  So
each round's `deckPile` is legal: base free (the invariant: current
tops are target tops of *processed* riders plus the initial edges),
base visible (seated), card unseated, fit.  The last rider left is
the only card in the cycle — position 0 — and consuming it lands the
cursor at 0 with the card list empty, so the end stock is `⟨[], 0⟩`
without any byte bookkeeping.

## Provenance of the precondition's conjuncts

`PristineEndgame` is the fragment-1 distillate `I₀` (each conjunct
cites the fence it is distilled from):

* `st.deal.WF` — from `initial_wf` (Initial.lean): the deposit's deal
  is well-formed.
* `st.stock = ⟨[], 0⟩` — fragment 1's own scoping (no cycle byte).
* `st.drawStep = 1` — fragment 1's batch-free channel (the pad and
  mask analysis belong to fragment 2).
* `∀ a, st.depths a = a.toIdx` — the no-reveal fragment: reveals only
  decrement depths from `fun a => a.toIdx` (`State.initial`), and the
  reveal evacuation problem (the subject of the launch-geometry
  fragment) is deferred.
* `∀ s, st.heights s = 0` — the no-foundation fragment.
* the tail seats kept, the edge catalogue (every edge is initial or a
  stock rider on a card base whose card is a tail or a stock rider),
  and every stock card seated — from `WF.board_edges`,
  `initialReachable_anchorOK` (Restriction.lean) and the probe's pile
  conservation (`KingAnchorReach.accounted_of_initialReachable`,
  witnesses/KingAnchorReachProbe.lean): stock cards are consumed and
  seated, anchor non-king tenants are dealt heads, and edges above
  card bases are `canSitOn`-fitted.
-/

namespace Construction

/-! ## The draw iteration kit

At draw step 1, a `draw` always succeeds and moves the cursor one
card forward (wrapping from the pass end to zero).  A round of the
construction iterates `draw`s to bring the targeted card to the waste
top, then consumes it with one `deckPile`.
-/

/-- `findFirstIdx` pointing at `i` means the `i`-th element satisfies
the predicate (the value fact behind position queries). -/
theorem findFirstIdx_get {α : Type} (p : α → Bool) : ∀ (l : List α) (i : Nat),
    Cycle.findFirstIdx p l = some i → ∃ x, l[i]? = some x ∧ p x = true := by
  intro l
  induction l with
  | nil => intro i h; simp [Cycle.findFirstIdx] at h
  | cons a t ih =>
      intro i h
      simp only [Cycle.findFirstIdx] at h
      by_cases hp : p a = true
      · rw [if_pos hp, Option.some.injEq] at h
        subst h
        exact ⟨a, rfl, hp⟩
      · rw [if_neg hp] at h
        cases hh : Cycle.findFirstIdx p t with
        | none => rw [hh] at h; simp at h
        | some j =>
            rw [hh] at h
            simp only [Option.map_some, Option.some.injEq] at h
            obtain ⟨x, hx, hpx⟩ := ih j hh
            subst h
            exact ⟨x, by rw [List.getElem?_cons_succ]; exact hx, hpx⟩

/-- A positioned card is at its position (the index reads the card). -/
theorem Cycle.posOf_get {c : Card} {cy : Cycle Card} {i : Nat}
    (h : cy.posOf c = some i) : cy.cards[i]? = some c := by
  obtain ⟨x, hx, hpx⟩ := findFirstIdx_get _ cy.cards i h
  have hxc : x = c := of_decide_eq_true hpx
  rw [hxc] at hx
  exact hx

/-- Iterated single-card deals: `iterDraw k cy` deals one card `k`
times (the first `dealOnce` is the first `draw`). -/
def Cycle.iterDraw : Nat → Cycle Card → Cycle Card
  | 0, cy => cy
  | k + 1, cy => iterDraw k (cy.dealOnce 1)

theorem Cycle.iterDraw_succ (k : Nat) (cy : Cycle Card) :
    iterDraw (k + 1) cy = iterDraw k (cy.dealOnce 1) := rfl

theorem Cycle.iterDraw_zero (cy : Cycle Card) : iterDraw 0 cy = cy := rfl

theorem Cycle.iterDraw_one (cy : Cycle Card) : iterDraw 1 cy = cy.dealOnce 1 := rfl

/-- Dealing `a` cards then `b` more is dealing `a + b` (the
self-composition of the cursor machine). -/
theorem Cycle.iterDraw_add (a : Nat) : ∀ (b : Nat) (cy : Cycle Card),
    iterDraw (a + b) cy = iterDraw b (iterDraw a cy) := by
  induction a with
  | zero =>
      intro b cy
      rw [Nat.zero_add, Cycle.iterDraw_zero]
  | succ a ih =>
      intro b cy
      have hab : a + 1 + b = a + b + 1 := by omega
      rw [hab, Cycle.iterDraw_succ, ih b (cy.dealOnce 1), Cycle.iterDraw_succ]

/-- One more deal from mid-pass: the cursor advances by one card. -/
theorem Cycle.dealOnce_step {cy : Cycle Card}
    (hn : cy.cursor < cy.cards.length) :
    cy.dealOnce 1 = ⟨cy.cards, cy.cursor + 1⟩ := by
  simp only [Cycle.dealOnce]
  split
  · next h => exact absurd h (by omega)
  · next h =>
      rw [Nat.min_eq_left (by omega : cy.cursor + 1 ≤ cy.cards.length)]

/-- One more deal at (or beyond) the pass end: the cursor wraps to
zero. -/
theorem Cycle.dealOnce_wrap' {cy : Cycle Card} (hn : cy.cards.length ≤ cy.cursor) :
    cy.dealOnce 1 = ⟨cy.cards, 0⟩ := by
  simp only [Cycle.dealOnce]
  rw [ite_eq_left (by show cy.cursor ≥ cy.cards.length; omega)]

/-- Iterating within the pass: `k` deals from a mid-pass cursor `j`
land at `j + k` (never past the length). -/
theorem Cycle.iterDraw_lt : ∀ (k : Nat) (L : List Card) (j : Nat),
    j + k ≤ L.length → iterDraw k ⟨L, j⟩ = ⟨L, j + k⟩ := by
  intro k
  induction k with
  | zero => intro L j _; rw [Nat.add_zero]; rfl
  | succ k ih =>
      intro L j h
      rw [Cycle.iterDraw_succ]
      have hstep : (⟨L, j⟩ : Cycle Card).dealOnce 1 = ⟨L, j + 1⟩ := by
        apply Cycle.dealOnce_step
        show j < L.length
        omega
      rw [hstep, ih L (j + 1) (by omega)]
      have hassoc : j + 1 + k = j + (k + 1) := by omega
      rw [hassoc]

/-- **The wrap excursion**: from a mid-pass cursor `j`, dealing to the
pass end (`L.length - j` draws), one wrapping draw, and advancing to
the target position `i + 1`. -/
theorem Cycle.iterDraw_wrap {L : List Card} {j i : Nat}
    (hj : j ≤ L.length) (hi : i + 1 ≤ L.length) :
    iterDraw ((L.length - j) + 1 + (i + 1)) ⟨L, j⟩ = ⟨L, i + 1⟩ := by
  have hcnt : (L.length - j) + 1 + (i + 1)
      = (L.length - j) + (1 + (i + 1)) := by omega
  have h1 : iterDraw (L.length - j) ⟨L, j⟩ = ⟨L, L.length⟩ := by
    have h2 := Cycle.iterDraw_lt (L.length - j) L j (by omega)
    rw [h2]
    congr 1
    omega
  have hw : iterDraw 1 (⟨L, L.length⟩ : Cycle Card) = ⟨L, 0⟩ :=
    (Cycle.iterDraw_one _).trans (Cycle.dealOnce_wrap' (Nat.le_refl _))
  rw [hcnt, Cycle.iterDraw_add _ _ ⟨L, j⟩, h1,
    Cycle.iterDraw_add 1 (i + 1) (⟨L, L.length⟩ : Cycle Card), hw,
    Cycle.iterDraw_lt (i + 1) L 0 (by omega), Nat.zero_add]

/-- Running a block of pure deals advances exactly the iteration
(the round's `draw` segments). -/
theorem run_replicate_draw (st : State) (k : Nat) (hds : st.drawStep = 1) :
    st.run (List.replicate k Move.draw) =
      some { st with stock := Cycle.iterDraw k st.stock } := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, State.run]
      have hap : st.apply Move.draw
          = some { st with stock := st.stock.dealOnce st.drawStep } := rfl
      rw [hds] at hap
      rw [hap]
      show State.run
        { deal := st.deal, board := st.board, heights := st.heights,
          depths := st.depths, stock := st.stock.dealOnce 1, drawStep := 1 }
        (List.replicate k Move.draw) = _
      rw [ih { deal := st.deal, board := st.board, heights := st.heights,
               depths := st.depths, stock := st.stock.dealOnce 1, drawStep := 1 }
          rfl,
        hds, Cycle.iterDraw_succ]

/-! ## The consume round

Bringing the target card to the waste top (pure `draw`s — advancing
within the pass, or wrapping through the pass end) then splicing it
out with one `deckPile`.  The cursor always lands at the consumed
position `i`.
-/

/-- The waste top at cursor `i + 1` is the `i`-th card. -/
theorem Cycle.prev_top {L : List Card} {c : Card} {i : Nat} (h : L[i]? = some c) :
    (⟨L, i + 1⟩ : Cycle Card).prev = some c := by
  show (if i + 1 = 0 then none else L[i + 1 - 1]?) = some c
  rw [if_neg (by omega), Nat.add_sub_cancel]
  exact h

/-- The waste-top read, cycle-abstract: a cursor sitting at `i + 1`
exposes the `i`-th card as the previous. -/
theorem Cycle.prev_of_top {cy : Cycle Card} {c : Card} {i : Nat}
    (hcy : cy.cursor = i + 1) (h : cy.cards[i]? = some c) :
    cy.prev = some c := by
  show (if cy.cursor = 0 then none else cy.cards[cy.cursor - 1]?) = some c
  rw [hcy, if_neg (by omega), Nat.add_sub_cancel]
  exact h

/-- Consuming a below-cursor position steps the cursor down to it. -/
theorem Cycle.removeAt_of_lt {c : Cycle Card} {i : Nat} (h : i < c.cursor) :
    c.removeAt i = ⟨Cycle.removeIdx c.cards i, c.cursor - 1⟩ := by
  show ({ cards := Cycle.removeIdx c.cards i,
          cursor := if i < c.cursor then c.cursor - 1 else c.cursor } : Cycle Card)
      = ⟨Cycle.removeIdx c.cards i, c.cursor - 1⟩
  rw [if_pos h]

/-- Consuming the waste top itself: the cursor lands at `i`, the
card is spliced out — the round's end-cycle. -/
theorem Cycle.removeAt_of_top {c : Cycle Card} {i : Nat} (h : c.cursor = i + 1) :
    c.removeAt i = ⟨Cycle.removeIdx c.cards i, i⟩ := by
  rw [Cycle.removeAt_of_lt (by rw [h]; omega)]
  congr 1
  omega

/-- The consume step, at a state whose cursor already exposes the
target: one `deckPile` seats the card (attach) and splices the cycle
down to position `i`. -/
theorem deckPile_from_top {st : State} {c : Card} {b : Base} {bd : Board} {i : Nat}
    (htop : st.stock.cursor = i + 1) (hi : st.stock.posOf c = some i)
    (hfit : st.canPlace c b = true) (hatt : st.board.attach b c = some bd) :
    st.run [Move.deckPile c b] =
      some { st with board := bd, stock := ⟨Cycle.removeIdx st.stock.cards i, i⟩ } := by
  rw [run_singleton]
  refine (apply_deckPile_iff).mpr ⟨?_, hfit, bd, hatt, ?_⟩
  · exact Cycle.prev_of_top htop (Cycle.posOf_get hi)
  · have hrm : st.stock.removeAt (st.stock.cursor - 1)
        = ⟨Cycle.removeIdx st.stock.cards i, i⟩ := by
      rw [htop, Nat.add_sub_cancel]
      exact Cycle.removeAt_of_top htop
    rw [hrm]

/-- **The round**: from any cursor within the cycle, bring the
target card to the waste top by pure draws and consume it — the
whole per-rider update as one existential segment. -/
theorem round_deckPile {st : State} (hds : st.drawStep = 1)
    {c : Card} {b : Base} {bd : Board} {i : Nat}
    (hi : st.stock.posOf c = some i)
    (hcur : st.stock.cursor ≤ st.stock.cards.length)
    (hfit : st.canPlace c b = true) (hatt : st.board.attach b c = some bd) :
    ∃ seg, st.run seg = some
      { st with board := bd, stock := ⟨Cycle.removeIdx st.stock.cards i, i⟩ } := by
  have hlen := Cycle.posOf_lt hi
  by_cases hcse : st.stock.cursor ≤ i + 1
  · refine ⟨List.replicate (i + 1 - st.stock.cursor) Move.draw ++ [Move.deckPile c b], ?_⟩
    rw [run_append, run_replicate_draw _ _ hds]
    have hiter : Cycle.iterDraw (i + 1 - st.stock.cursor) st.stock
        = ⟨st.stock.cards, i + 1⟩ := by
      have h2 := Cycle.iterDraw_lt (i + 1 - st.stock.cursor) st.stock.cards
        st.stock.cursor (by omega)
      rw [h2]
      congr 1
      omega
    rw [hiter]
    show State.run { st with stock := ⟨st.stock.cards, i + 1⟩ } [Move.deckPile c b] = _
    exact deckPile_from_top rfl hi hfit hatt
  · refine ⟨List.replicate
        ((st.stock.cards.length - st.stock.cursor) + 1 + (i + 1)) Move.draw
        ++ [Move.deckPile c b], ?_⟩
    rw [run_append, run_replicate_draw _ _ hds]
    have hiter : Cycle.iterDraw
        ((st.stock.cards.length - st.stock.cursor) + 1 + (i + 1)) st.stock
        = ⟨st.stock.cards, i + 1⟩ :=
      Cycle.iterDraw_wrap hcur (by omega)
    rw [hiter]
    show State.run { st with stock := ⟨st.stock.cards, i + 1⟩ } [Move.deckPile c b] = _
    exact deckPile_from_top rfl hi hfit hatt

/-! ## The dealt tails' initial seats

The initial board seats every pile's top dealt card (the *tail*) at
its `initBase` — the fragment's always-seated bases.  (Machinery
re-proved here from `Init.lean`'s fold because the probe's copy is
private to witnesses/KingAnchorReachProbe.lean; see the deprivatize
ticket for retiring the duplication.) -/

private def InitImg (d : Deal) (proc : List Anchor) (bd : Board) : Prop :=
  (∀ a ∈ proc, bd.topOf (initBase d a) = (d.piles a).getLast?) ∧
  (∀ b c, bd.topOf b = some c →
    ∃ a, a ∈ proc ∧ b = initBase d a ∧ (d.piles a).getLast? = some c)

private theorem initImg_empty (d : Deal) : InitImg d [] Board.empty := by
  refine ⟨fun a ha => absurd ha (by simp), fun b c hb => ?_⟩
  rw [Board.empty_topOf] at hb
  exact absurd hb (by simp)

private theorem anchor_toIdx_inj {a a' : Anchor} (h : a.toIdx = a'.toIdx) :
    a = a' := by
  cases a <;> cases a' <;> simp_all [Anchor.toIdx]

private theorem initBase_shape (d : Deal) (hd : d.WF) (a : Anchor) :
    a = Anchor.p0 ∨ ∃ u, initBase d a = Sum.inr u ∧ u ∈ d.piles a := by
  cases hti : a.toIdx with
  | zero => exact Or.inl (anchor_toIdx_inj hti)
  | succ k =>
      refine Or.inr ?_
      have hlen : (d.piles a).length = k + 2 := by rw [hd.1 a, hti]
      cases hgt : (d.piles a)[k]? with
      | none =>
          have hbad := List.getElem?_eq_none_iff.mp hgt
          rw [hlen] at hbad
          exact absurd hbad (by omega)
      | some u =>
          refine ⟨u, ?_, ?_⟩
          · show initBase d a = Sum.inr u
            simp only [initBase, hti, hgt]
          · exact List.mem_iff_getElem?.mpr ⟨k, hgt⟩

private theorem initBase_eq_of_eq (d : Deal) (hd : d.WF) {a a' : Anchor}
    (h : initBase d a = initBase d a') : a = a' := by
  have hp0 : initBase d Anchor.p0 = Sum.inl Anchor.p0 := rfl
  rcases initBase_shape d hd a with hap | ⟨u, hu, hmu⟩
  · rcases initBase_shape d hd a' with hap' | ⟨u', hu', hmu'⟩
    · rw [hap, hap']
    · rw [hap, hp0, hu'] at h
      exact absurd h (by simp)
  · rcases initBase_shape d hd a' with hap' | ⟨u', hu', hmu'⟩
    · rw [hu, hap', hp0] at h
      exact absurd h (by simp)
    · rw [hu, hu'] at h
      have huu : u = u' := Sum.inr.inj h
      have hmu2 : u ∈ d.piles a' := by rw [huu]; exact hmu'
      exact Deal.piles_disj hd hmu hmu2

private theorem initBase_free (d : Deal) (hd : d.WF) {proc : List Anchor}
    {bd : Board} (himg : InitImg d proc bd) {a₀ : Anchor} (hnot : a₀ ∉ proc) :
    bd.topOf (initBase d a₀) = none := by
  cases hocc : bd.topOf (initBase d a₀) with
  | none => rfl
  | some c =>
      exfalso
      obtain ⟨a, ham, hbase, -⟩ := himg.2 _ c hocc
      exact hnot (by rw [initBase_eq_of_eq d hd hbase]; exact ham)

private theorem initStep_preserves_Img (d : Deal) (hd : d.WF)
    {proc : List Anchor} {bd : Board} {a₀ : Anchor}
    (himg : InitImg d proc bd) (hnot : a₀ ∉ proc) :
    InitImg d (a₀ :: proc) (initStep d bd a₀) := by
  obtain ⟨h1, h2⟩ := himg
  cases hgt : (d.piles a₀).getLast? with
  | none =>
      have hstep : initStep d bd a₀ = bd := by simp only [initStep, hgt]
      rw [hstep]
      refine ⟨?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | hap
        · rw [initBase_free d hd ⟨h1, h2⟩ hnot, hgt]
        · exact h1 a hap
      · intro b c hb
        obtain ⟨a, ham, hbase, hlast⟩ := h2 b c hb
        exact ⟨a, List.mem_cons_of_mem _ ham, hbase, hlast⟩
  | some top =>
      have hfree := initBase_free d hd ⟨h1, h2⟩ hnot
      have hbotnone : bd.bottomOf top = none := by
        refine (Board.bottomOf_eq_none bd top).mpr (fun b' hb => ?_)
        obtain ⟨a, ham, hb, hlast⟩ := h2 b' top hb
        have hmema : top ∈ d.piles a := mem_of_getLast hlast
        have hmem0 : top ∈ d.piles a₀ := mem_of_getLast hgt
        have hae := Deal.piles_disj hd hmem0 hmema
        rw [← hae] at ham
        exact hnot ham
      have hattach : bd.attach (initBase d a₀) top ≠ none :=
        (Board.attach_eq_some_iff bd (initBase d a₀) top).mpr ⟨hfree, hbotnone⟩
      cases hatt : bd.attach (initBase d a₀) top with
      | none => rw [hatt] at hattach; exact absurd hattach (by simp)
      | some bd' =>
          have hstep : initStep d bd a₀ = bd' := by
            simp only [initStep, hgt, hatt, Option.getD]
          rw [hstep]
          refine ⟨?_, ?_⟩
          · intro a ha
            rcases List.mem_cons.mp ha with hhead | hap
            · rw [hhead]
              rw [Board.attach_topOf bd (initBase d a₀) top hatt, hgt]
            · have hne : initBase d a ≠ initBase d a₀ := by
                intro hcon
                exact hnot (by
                  have heq := (initBase_eq_of_eq d hd hcon).symm
                  rw [heq]
                  exact hap)
              rw [Board.attach_topOf_ne bd (initBase d a₀) top hatt hne]
              exact h1 a hap
          · intro b c hb
            by_cases hbb : b = initBase d a₀
            · rw [hbb, Board.attach_topOf bd (initBase d a₀) top hatt,
                Option.some.injEq] at hb
              exact ⟨a₀, (by simp), hbb, by rw [← hb]; exact hgt⟩
            · rw [Board.attach_topOf_ne bd (initBase d a₀) top hatt hbb] at hb
              obtain ⟨a, ham, hbase, hlast⟩ := h2 b c hb
              exact ⟨a, List.mem_cons_of_mem _ ham, hbase, hlast⟩

private theorem initFold_img_aux (d : Deal) (hd : d.WF) :
    ∀ (as proc : List Anchor) (bd : Board),
    as.Nodup → proc.Nodup → (∀ a ∈ as, a ∉ proc) →
    (∀ a ∈ as, a ∈ Anchor.all) → (∀ a ∈ proc, a ∈ Anchor.all) →
    InitImg d proc bd →
    InitImg d (as.reverse ++ proc) (as.foldl (initStep d) bd) := by
  intro as
  induction as with
  | nil =>
      intro proc bd _ _ _ _ _ himg
      exact himg
  | cons a₀ rest ih =>
      intro proc bd hnd hndp hdis hallp hallproc himg
      have hstep := initStep_preserves_Img d hd himg (hdis a₀ (by simp))
      obtain ⟨ha0nr, hndr⟩ := List.nodup_cons.mp hnd
      have hproc' : (a₀ :: proc).Nodup :=
        List.nodup_cons.mpr ⟨hdis a₀ (by simp), hndp⟩
      have hdis' : ∀ a ∈ rest, a ∉ a₀ :: proc := by
        intro a har hap
        rcases List.mem_cons.mp hap with heq | happ
        · rw [heq] at har
          exact ha0nr har
        · exact hdis a (List.mem_cons_of_mem _ har) happ
      have hallas : ∀ a ∈ rest, a ∈ Anchor.all :=
        fun a har => hallp a (List.mem_cons_of_mem _ har)
      have hallproc' : ∀ a ∈ a₀ :: proc, a ∈ Anchor.all := by
        intro a hap
        rcases List.mem_cons.mp hap with heq | hp
        · rw [heq]
          exact a₀.mem_all
        · exact hallproc a hp
      have hmm := ih (a₀ :: proc) (initStep d bd a₀) hndr hproc' hdis'
        hallas hallproc' hstep
      rw [show (a₀ :: rest).reverse ++ proc = rest.reverse ++ a₀ :: proc from by
        rw [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]]
      exact hmm

/-- **The initial board seats every tail**: each pile's top dealt
card sits at its `initBase` (the seed fact of the construction — the
always-seated bases). -/
theorem initial_seats (d : Deal) (hd : d.WF) (a : Anchor) :
    (initialBoard d).topOf (initBase d a) = (d.piles a).getLast? := by
  have hall := initFold_img_aux d hd Anchor.all [] Board.empty
    (by decide) (by decide)
    (fun _ _ ha => absurd ha (by simp))
    (fun a _ => a.mem_all) (fun _ ha => absurd ha (by simp))
    (initImg_empty d)
  refine hall.1 a ?_
  exact List.mem_reverse.mpr a.mem_all

/-! ## The fragment-1 precondition (the pristine endgame) -/

/-- `c` is one of the seven dealt tails: some pile's top dealt
card. -/
def IsTail (d : Deal) (c : Card) : Prop :=
  ∃ a, (d.piles a).getLast? = some c

/-- **The fragment-1 distillate** `I₀` (the pristine endgame —
per-conjunct provenance in the file header):
* `deal.WF`, `WF` — the fences' baseline (`initial_wf`,
  `initialReachable_visClean`);
* empty final cycle, draw step 1 — fragment 1's no-byte scoping;
* no reveals (`depths = toIdx`), no foundations (`heights = 0`);
* every tail kept at its dealt base (the launch geometry's
  always-playable anchors);
* the edge catalogue: every edge is either a tail's kept initial
  edge or a stock rider on a card base whose card is a tail or
  another stock rider;
* every stock card is seated at the target (consumed-and-placed, the
  probe's conservation). -/
def PristineEndgame (st : State) : Prop :=
  st.deal.WF ∧ st.WF ∧
  st.drawStep = 1 ∧
  st.stock.cards = [] ∧ st.stock.cursor = 0 ∧
  (∀ a, st.depths a = a.toIdx) ∧
  (∀ s, st.heights s = 0) ∧
  (∀ a, st.board.topOf (initBase st.deal a) = (st.deal.piles a).getLast?) ∧
  (∀ b c, st.board.topOf b = some c →
     (∃ a, b = initBase st.deal a ∧ (st.deal.piles a).getLast? = some c) ∨
     (c ∈ st.deal.stock ∧ ∃ d, b = Sum.inr d ∧
       (IsTail st.deal d ∨ d ∈ st.deal.stock))) ∧
  (∀ c, c ∈ st.deal.stock → st.board.bottomOf c ≠ none)

/-- The stock-pile disjointness reading of `IsTail` at a pristine
endgame: a tail card is never a stock card. -/
theorem PristineEndgame.tail_not_stock {st : State} (h : PristineEndgame st)
    {d : Card} (ht : IsTail st.deal d) : d ∉ st.deal.stock := by
  obtain ⟨a, hgt⟩ := ht
  exact fun hc => Deal.piles_stock_disj h.1 (mem_of_getLast hgt) hc

/-- **The rider seat shape**: every stock card sits, at the target, on
a card base whose card is a tail or a stock rider, one rank up and
colour-shifted (the catalogue + `board_edges` decoded). -/
theorem PristineEndgame.riderSeat {st : State} (h : PristineEndgame st)
    {c : Card} (hcs : c ∈ st.deal.stock) :
    ∃ d : Card, st.board.topOf (Sum.inr d) = some c ∧
      (IsTail st.deal d ∨ d ∈ st.deal.stock) ∧ canSitOn c d = true := by
  obtain ⟨hdeals, hwf, -, -, -, -, -, -, hcat, hseated⟩ := h
  obtain ⟨b, hb⟩ : ∃ b, st.board.topOf b = some c := by
    cases hbot : st.board.bottomOf c with
    | none =>
        exact absurd (hseated c hcs) (by rw [hbot]; simp)
    | some b =>
        exact ⟨b, (Board.bottomOf_eq st.board c b).mp hbot⟩
  rcases hcat b c hb with ⟨a, hba, hgt⟩ | ⟨-, d, hbd, df⟩
  · exact absurd hcs
      (fun hh => Deal.piles_stock_disj hdeals (mem_of_getLast hgt) hh)
  · rw [hbd] at hb
    have hleg := hwf.board_edges (Sum.inr d) c hb
    rcases hleg.2 with ⟨a, t, rest, hadj, -⟩ | ⟨-, hfit⟩
    · -- the deal-adjacent arm is unavailable to a stock card
      exfalso
      have hmem : c ∈ st.deal.piles a := by
        rw [hadj]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self))))
      exact Deal.piles_stock_disj hdeals hmem hcs
    · exact ⟨d, hb, df, hfit⟩

/-! ## The worklist frame and the tier descent -/

/-- (internal) The frame between the dealt initial state and the
target `st`: `w` is the current intermediate state, `done` the stock
cards consumed so far.  The current tops are exactly the target's
tops of processed-or-tail cards; the current cycle holds exactly the
unprocessed stock cards. -/
def FrameOK (st : State) (w : State) (done : List Card) : Prop :=
  w.deal = st.deal ∧ w.depths = st.depths ∧ w.heights = st.heights ∧
  w.drawStep = st.drawStep ∧
  (∀ b y, w.board.topOf b = some y →
     st.board.topOf b = some y ∧ (y ∈ done ∨ IsTail st.deal y)) ∧
  (∀ b y, st.board.topOf b = some y → (y ∈ done ∨ IsTail st.deal y) →
     w.board.topOf b = some y) ∧
  (∀ x, x ∈ w.stock.cards ↔ x ∈ st.deal.stock ∧ x ∉ done) ∧
  (∀ x ∈ done, x ∈ st.deal.stock) ∧
  noDupCards w.stock.cards ∧
  w.stock.cursor ≤ w.stock.cards.length

/-- **The step**: consume one more stock rider `c` — draw the target
card to the waste top (by `round_deckPile`), seat it at its target
base (a tail or an already-processed rider sits there), and hand back
the segment together with the refreshed frame.  The only order
constraint consumed here: every stock card of rank above `c`'s is
already processed. -/
theorem frame_step {st : State} (hpe : PristineEndgame st) {c : Card}
    (hcs : c ∈ st.deal.stock)
    {w : State} {done : List Card} (hinv : FrameOK st w done)
    (hcnd : c ∉ done)
    (hhigh : ∀ z ∈ st.deal.stock, c.rank.toIdx < z.rank.toIdx → z ∈ done) :
    ∃ w' seg, w.run seg = some w' ∧ FrameOK st w' (done ++ [c]) := by
  obtain ⟨hdeals, hwf, hdraw0, -, -, -, -, hkept, hcat, hseated⟩ := id hpe
  obtain ⟨iv_deal, iv_depths, iv_heights, iv_draw, iv_out, iv_in, iv_stock,
      iv_dom, iv_nd, iv_cur⟩ := hinv
  obtain ⟨d0, hseat, hdform, hfit⟩ := PristineEndgame.riderSeat hpe hcs
  have hwmem : c ∈ w.stock.cards := (iv_stock c).mpr ⟨hcs, hcnd⟩
  cases hp : w.stock.posOf c with
  | none => exact absurd hp (Cycle.posOf_mem hwmem)
  | some i =>
      have hwfree : w.board.topOf (Sum.inr d0) = none := by
        cases hwtop : w.board.topOf (Sum.inr d0) with
        | none => rfl
        | some y =>
            exfalso
            obtain ⟨hy1, hy2⟩ := iv_out (Sum.inr d0) y hwtop
            have hyc : y = c := Option.some.inj (hy1.symm.trans hseat)
            subst hyc
            rcases hy2 with hmem | htail
            · exact absurd hmem hcnd
            · exact PristineEndgame.tail_not_stock hpe htail hcs
      have hwnew : w.board.bottomOf c = none :=
        (Board.bottomOf_eq_none w.board c).mpr (fun b' hb' => by
          obtain ⟨-, hy2⟩ := iv_out b' c hb'
          rcases hy2 with hmem | htail
          · exact absurd hmem hcnd
          · exact PristineEndgame.tail_not_stock hpe htail hcs)
      have hbased : ∃ b₀, w.board.topOf b₀ = some d0 := by
        rcases hdform with htail | hstock
        · obtain ⟨a, hgt⟩ := htail
          refine ⟨initBase st.deal a,
            iv_in (initBase st.deal a) d0 ?_ (Or.inr ⟨a, hgt⟩)⟩
          rw [hkept a, hgt]
        · have hdrank : c.rank.toIdx + 1 = d0.rank.toIdx :=
            (canSitOn_eq c d0).mp hfit |>.1
          have hddone : d0 ∈ done := hhigh d0 hstock (by omega)
          cases hbd0 : st.board.bottomOf d0 with
          | none => exact absurd (hseated d0 hstock) (by rw [hbd0]; simp)
          | some b₀ =>
              exact ⟨b₀, iv_in b₀ d0
                ((Board.bottomOf_eq st.board d0 b₀).mp hbd0) (Or.inl hddone)⟩
      have hwvis : w.isVis d0 = true := by
        obtain ⟨b₀, hwso⟩ := hbased
        show (w.board.bottomOf d0).isSome = true
        rw [(Board.bottomOf_eq w.board d0 b₀).mpr hwso]
        rfl
      have hwbbd0 : w.board.bottomOf d0 ≠ none := by
        obtain ⟨b₀, hwso⟩ := hbased
        rw [(Board.bottomOf_eq w.board d0 b₀).mpr hwso]
        simp
      have hwplace : w.canPlace c (Sum.inr d0) = true := by
        show (decide (w.board.topOf (Sum.inr d0) = none) &&
              (w.isVis d0 && canSitOn c d0)) = true
        rw [hwfree, hwvis, hfit]
        rfl
      have hwds : w.drawStep = 1 := by rw [iv_draw]; exact hdraw0
      have hne : w.board.attach (Sum.inr d0) c ≠ none :=
        (Board.attach_eq_some_iff w.board (Sum.inr d0) c).mpr ⟨hwfree, hwnew⟩
      cases hattc : w.board.attach (Sum.inr d0) c with
      | none => rw [hattc] at hne; exact absurd hne (by simp)
      | some bd =>
      obtain ⟨seg, hseg⟩ :=
        round_deckPile hwds hp iv_cur hwplace hattc
      refine ⟨
        { w with board := bd, stock := ⟨Cycle.removeIdx w.stock.cards i, i⟩ },
        seg, hseg, ?_⟩
      -- the frame refresh, component by component
      have hnd' : ∀ x, x ∈ Cycle.removeIdx w.stock.cards i ↔
          x ∈ w.stock.cards ∧ x ≠ c := fun x =>
        mem_removeIdx_iff iv_nd (Cycle.posOf_get hp) x
      have hmemd : ∀ z ∈ done, z ∈ done ++ [c] :=
        fun z hz => List.mem_append.mpr (Or.inl hz)
      refine ⟨iv_deal, iv_depths, iv_heights, iv_draw, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- OUT: current tops are target tops of processed-or-tail cards
        intro b₁ y₁ hb₁
        by_cases hb : b₁ = Sum.inr d0
        · rw [hb] at hb₁ ⊢
          rw [Board.attach_topOf w.board (Sum.inr d0) c hattc] at hb₁
          have hb1y : y₁ = c := Option.some.inj hb₁.symm
          subst hb1y
          exact ⟨hseat, Or.inl (List.mem_append.mpr (Or.inr (by simp)))⟩
        · rw [Board.attach_topOf_ne w.board (Sum.inr d0) c hattc hb] at hb₁
          obtain ⟨hst, hmem⟩ := iv_out b₁ y₁ hb₁
          exact ⟨hst, hmem.elim (fun hz => Or.inl (hmemd y₁ hz)) Or.inr⟩
      · -- IN: target tops of processed-or-tail cards are current tops
        intro b₁ y₁ hsty hmem
        rcases hmem with hmem' | htail
        · rcases List.mem_append.mp hmem' with hz | hzc
          · -- y₁ already processed: its base cannot be the new seat
            have hbdiff : b₁ ≠ Sum.inr d0 := by
              intro hcon
              rw [hcon] at hsty
              have hyc : y₁ = c := Option.some.inj (hsty.symm.trans hseat)
              rw [hyc] at hz
              exact hcnd hz
            rw [Board.attach_topOf_ne w.board (Sum.inr d0) c hattc hbdiff]
            exact iv_in b₁ y₁ hsty (Or.inl hz)
          · -- y₁ = c: the fresh seat is exactly the target's
            have hyc : y₁ = c := List.mem_singleton.mp hzc
            rw [hyc] at hsty
            have hbdiff : b₁ = Sum.inr d0 :=
              st.board.inj b₁ (Sum.inr d0) c hsty hseat
            rw [hyc, hbdiff]
            exact Board.attach_topOf w.board (Sum.inr d0) c hattc
        · -- y₁ is a tail: never a stock card, so not the fresh seat
          have hbdiff : b₁ ≠ Sum.inr d0 := by
            intro hcon
            rw [hcon] at hsty
            have hyc : y₁ = c := Option.some.inj (hsty.symm.trans hseat)
            rw [hyc] at htail
            exact PristineEndgame.tail_not_stock hpe htail hcs
          rw [Board.attach_topOf_ne w.board (Sum.inr d0) c hattc hbdiff]
          exact iv_in b₁ y₁ hsty (Or.inr htail)
      · -- stock membership
        intro x
        constructor
        · intro hx
          obtain ⟨hl', hxc⟩ := (hnd' x).mp hx
          obtain ⟨hs', hndm⟩ := (iv_stock x).mp hl'
          refine ⟨hs', fun hmem => ?_⟩
          rcases List.mem_append.mp hmem with hz | hxc'
          · exact hndm hz
          · exact hxc (List.mem_singleton.mp hxc')
        · intro hsnd
          obtain ⟨hs', hcnd'⟩ := hsnd
          have hl' : x ∈ w.stock.cards := (iv_stock x).mpr
            ⟨hs', fun hz => hcnd' (List.mem_append.mpr (Or.inl hz))⟩
          have hxc : x ≠ c := fun hcon =>
            hcnd' (by rw [hcon]; exact List.mem_append.mpr (Or.inr (by simp)))
          exact (hnd' x).mpr ⟨hl', hxc⟩
      · -- done ⊆ stock
        intro z hz
        rcases List.mem_append.mp hz with hz' | hzc
        · exact iv_dom z hz'
        · have hzc' : z = c := List.mem_singleton.mp hzc
          rw [hzc']
          exact hcs
      · -- noDup survives the splice
        exact noDupCards_removeIdx _ _ iv_nd
      · -- cursor: the consumed position sits within the new list
        have hlt := Cycle.posOf_lt hp
        have hlen := Cycle.removeIdx_length w.stock.cards i hlt
        show i ≤ (Cycle.removeIdx w.stock.cards i).length
        omega

/-! ## The tier induction and the descent ladder -/

/-- One rank's worth of the schedule: the stock cards of rank
exactly `n` (the order within a tier is immaterial — within a tier
the bases are independent). -/
def tier (st : State) (n : Nat) : List Card :=
  st.deal.stock.filter fun x => decide (x.rank.toIdx = n)

theorem tier_mem {st : State} {n : Nat} {x : Card} (hx : x ∈ tier st n) :
    x ∈ st.deal.stock ∧ x.rank.toIdx = n := by
  simp only [tier, List.mem_filter, decide_eq_true_iff] at hx
  exact hx

theorem tier_catch {st : State} {n : Nat} {x : Card}
    (hxs : x ∈ st.deal.stock) (hx : x.rank.toIdx = n) : x ∈ tier st n := by
  simp only [tier, List.mem_filter, decide_eq_true_iff]
  exact ⟨hxs, hx⟩

/-- The rank-tier lists, descending (tier `t` first, then `t - 1`,
…, then `0`): the remaining work below a processed frontier of
`t + 1`.  Data, no choice. -/
def chain (st : State) : Nat → List Card
  | 0 => tier st 0
  | t + 1 => tier st (t + 1) ++ chain st t

theorem chain_succ (st : State) (t : Nat) :
    chain st (t + 1) = tier st (t + 1) ++ chain st t := rfl

theorem chain_nil_unfold (st : State) : chain st 0 = tier st 0 := rfl

theorem chain_stock {st : State} : ∀ (t : Nat) (x : Card),
    x ∈ chain st t → x ∈ st.deal.stock := by
  intro t
  induction t with
  | zero =>
      intro x hx
      exact (tier_mem hx).1
  | succ t ih =>
      intro x hx
      rw [chain_succ] at hx
      rcases List.mem_append.mp hx with h | h
      · exact (tier_mem h).1
      · exact ih x h

/-- The chain catalogue: membership in the remaining work is
stock-membership below the frontier. -/
theorem chain_mem_iff {st : State} : ∀ (t : Nat) (x : Card),
    x ∈ chain st t ↔ (x ∈ st.deal.stock ∧ x.rank.toIdx ≤ t) := by
  intro t
  induction t with
  | zero =>
      intro x
      rw [chain_nil_unfold]
      constructor
      · intro hx
        exact ⟨(tier_mem hx).1, by
            have := (tier_mem hx).2
            omega⟩
      · intro ⟨hxs, hrk⟩
        exact tier_catch hxs (by omega)
  | succ t ih =>
      intro x
      rw [chain_succ]
      constructor
      · intro hx
        rcases List.mem_append.mp hx with h | h
        · exact ⟨(tier_mem h).1, by
            have := (tier_mem h).2
            omega⟩
        · obtain ⟨h1, h2⟩ := (ih x).mp h
          exact ⟨h1, by omega⟩
      · intro ⟨hxs, hrk⟩
        by_cases hx : x.rank.toIdx = t + 1
        · exact List.mem_append.mpr (Or.inl (tier_catch hxs hx))
        · exact List.mem_append.mpr (Or.inr ((ih x).mpr ⟨hxs, by omega⟩))

/-- (internal) `noDupCards` carries `List.Nodup`. -/
theorem nodup_of_noDupCards {l : List Card} (h : noDupCards l) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
        have hlt : k < t.length := (List.getElem?_eq_some_iff.mp hk).1
        have h0 : (a :: t)[0]? = some a := rfl
        have h1 : (a :: t)[k + 1]? = some a := by
          rw [List.getElem?_cons_succ]
          exact hk
        have hlenc : (a :: t).length = t.length + 1 := by
          show List.length (a :: t) = _
          simp only [List.length_cons]
        have h01 : (a :: t)[0]? = (a :: t)[k + 1]? := by rw [h0, h1]
        have := h 0 (k + 1) (by omega) (by omega) h01
        omega
      · apply ih
        intro i j hi hj hij
        have h1 : (a :: t)[i + 1]? = t[i]? := by rw [List.getElem?_cons_succ]
        have h2 : (a :: t)[j + 1]? = t[j]? := by rw [List.getElem?_cons_succ]
        have hlenc : (a :: t).length = t.length + 1 := by
          show List.length (a :: t) = _
          simp only [List.length_cons]
        have h3 := h (i + 1) (j + 1) (by omega) (by omega) (by rw [h1, h2]; exact hij)
        omega

/-- (internal) filters keep duplicate-freedom. -/
theorem List.filter_nodup {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.Nodup → (l.filter p).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
      intro hnd
      by_cases hp : p a = true
      · rw [List.filter_cons, if_pos hp]
        refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih (List.nodup_cons.mp hnd).2⟩
        have h1 := (List.mem_filter.mp hmem).1
        exact (List.nodup_cons.mp hnd).1 h1
      · rw [List.filter_cons, if_neg hp]
        exact ih (List.nodup_cons.mp hnd).2

/-- (internal) the append-intro for duplicate-freedom. -/
theorem nodup_append_intro {α : Type} : ∀ (l₁ l₂ : List α),
    l₁.Nodup → l₂.Nodup → (∀ x ∈ l₁, x ∉ l₂) → (l₁ ++ l₂).Nodup := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ h2 _; exact h2
  | cons a t ih =>
      intro l₂ h1 h2 hdis
      refine List.nodup_cons.mpr ⟨?_, ih l₂ (List.nodup_cons.mp h1).2 h2 ?_⟩
      · intro hmem
        rcases List.mem_append.mp hmem with h' | h'
        · exact (List.nodup_cons.mp h1).1 h'
        · exact hdis a (List.mem_cons_self) h'
      · intro x hx
        exact hdis x (List.mem_cons_of_mem _ hx)

theorem chain_nodup {st : State} (hnd : noDupCards st.deal.stock) :
    ∀ (t : Nat), (chain st t).Nodup := by
  intro t
  induction t with
  | zero =>
      exact List.filter_nodup _ _ (nodup_of_noDupCards hnd)
  | succ t ih =>
      have h1 : (tier st (t + 1)).Nodup :=
        List.filter_nodup _ _ (nodup_of_noDupCards hnd)
      refine nodup_append_intro _ _ h1 ih ?_
      intro x hx hmem
      have hrkx := (tier_mem hx).2
      have hrkc := (chain_mem_iff t x).mp hmem |>.2
      omega

/-- **One tier's work**: consume every card of the tier-list `L`
(all of rank `n`, all unprocessed, every above-rank stock card
already processed). -/
theorem frame_tier {st : State} (hpe : PristineEndgame st) :
    ∀ (n : Nat) (L : List Card) (w : State) (done : List Card),
    (∀ x ∈ L, x ∈ st.deal.stock) →
    (∀ x ∈ L, x.rank.toIdx = n) →
    L.Nodup →
    (∀ z ∈ st.deal.stock, n < z.rank.toIdx → z ∈ done) →
    (∀ x ∈ L, x ∉ done) →
    FrameOK st w done →
    ∃ (w' : State) (seg : List Move),
      w.run seg = some w' ∧ FrameOK st w' (done ++ L) := by
  intro n L
  induction L with
  | nil =>
      intro w done _ _ _ _ _ hinv
      refine ⟨w, [], rfl, ?_⟩
      rw [List.append_nil]
      exact hinv
  | cons x L' ih =>
      intro w done hLstock hLrank hLnd hgt hLnd' hinv
      have hxs : x ∈ st.deal.stock := hLstock x (List.mem_cons_self)
      have hxnd : x ∉ done := hLnd' x (List.mem_cons_self)
      have hhigh : ∀ z ∈ st.deal.stock, x.rank.toIdx < z.rank.toIdx → z ∈ done := by
        intro z hzs hlt
        exact hgt z hzs (by
          have := hLrank x (List.mem_cons_self)
          omega)
      obtain ⟨w₁, seg₁, hrun₁, hinv₁⟩ := frame_step hpe hxs hinv hxnd hhigh
      obtain ⟨w₂, seg₂, hrun₂, hinv₂⟩ :=
        ih w₁ (done ++ [x])
          (fun y hy => hLstock y (List.mem_cons_of_mem _ hy))
          (fun y hy => hLrank y (List.mem_cons_of_mem _ hy))
          (List.nodup_cons.mp hLnd).2
          (fun z hzs hlt =>
            List.mem_append.mpr (Or.inl (hgt z hzs hlt)))
          (fun y hy hmem => by
            rcases List.mem_append.mp hmem with hz | hyx
            · exact hLnd' y (List.mem_cons_of_mem _ hy) hz
            · exact (List.nodup_cons.mp hLnd).1 (by
                rw [<- List.mem_singleton.mp hyx]
                exact hy))
          hinv₁
      refine ⟨w₂, seg₁ ++ seg₂, ?_, ?_⟩
      · rw [run_append, hrun₁]
        exact hrun₂
      · rw [show x :: L' = [x] ++ L' from rfl, <- List.append_assoc]
        exact hinv₂

/-- **The descent ladder**: with every stock card above rank `t`
already processed, finish all remaining tiers (`t` down to `0`). -/
theorem frame_ladder {st : State} (hpe : PristineEndgame st)
    (hnd : noDupCards st.deal.stock) :
    ∀ (t : Nat), t ≤ 12 →
    ∀ (w : State) (done : List Card),
    (∀ z ∈ st.deal.stock, t < z.rank.toIdx → z ∈ done) →
    (∀ d ∈ done, t < d.rank.toIdx) →
    FrameOK st w done →
    ∃ (w' : State) (seg : List Move),
      w.run seg = some w' ∧ FrameOK st w' (done ++ chain st t) := by
  intro t
  induction t with
  | zero =>
      intro _ w done hgt hdom hinv
      obtain ⟨w', seg, hrun, hframe⟩ :=
        frame_tier hpe 0 (tier st 0) w done
          (fun x hx => (tier_mem hx).1)
          (fun x hx => (tier_mem hx).2)
          (chain_nodup hnd 0)
          hgt
          (fun x hx hd => absurd (hdom x hd) (by
            have := (tier_mem hx).2
            omega))
          hinv
      exact ⟨w', seg, hrun, hframe⟩
  | succ t ih =>
      intro ht12 w done hgt hdom hinv
      have ht1 : t ≤ 12 := by omega
      have htierstock : ∀ x ∈ tier st (t + 1), x ∈ st.deal.stock :=
        fun x hx => (tier_mem hx).1
      have htierrk : ∀ x ∈ tier st (t + 1), x.rank.toIdx = t + 1 :=
        fun x hx => (tier_mem hx).2
      have htiernd : ∀ x ∈ tier st (t + 1), x ∉ done :=
        fun x hx hd => absurd (hdom x hd) (by
          have := (tier_mem hx).2
          omega)
      have hgt' : ∀ z ∈ st.deal.stock, t + 1 < z.rank.toIdx → z ∈ done :=
        fun z hzs hlt => hgt z hzs hlt
      obtain ⟨w₁, seg₁, hrun₁, hinv₁⟩ :=
        frame_tier hpe (t + 1) (tier st (t + 1)) w done
          htierstock htierrk (List.filter_nodup _ _ (nodup_of_noDupCards hnd))
          hgt' htiernd hinv
      obtain ⟨w₂, seg₂, hrun₂, hinv₂⟩ :=
        ih ht1 w₁ (done ++ tier st (t + 1))
          (fun z hzs hlt => by
            by_cases hz : (t + 1) < z.rank.toIdx
            · exact List.mem_append.mpr
                (Or.inl (hgt z hzs hz))
            · refine List.mem_append.mpr (Or.inr ?_)
              have hrk : z.rank.toIdx = t + 1 := by omega
              exact tier_catch hzs hrk)
          (fun d hd => by
            rcases List.mem_append.mp hd with hd1 | hd2
            · have := hdom d hd1
              omega
            · have := (tier_mem hd2).2
              omega)
          hinv₁
      refine ⟨w₂, seg₁ ++ seg₂, ?_, ?_⟩
      · rw [run_append, hrun₁]
        exact hrun₂
      · rw [chain_succ, ← List.append_assoc]
        exact hinv₂

/-! ## The fragment-1 main theorem -/

/-- (internal) State equality by fields. -/
theorem state_ext_fields {s₁ s₂ : State}
    (h1 : s₁.deal = s₂.deal) (h2 : s₁.board = s₂.board)
    (h3 : s₁.heights = s₂.heights) (h4 : s₁.depths = s₂.depths)
    (h5 : s₁.stock = s₂.stock) (h6 : s₁.drawStep = s₂.drawStep) :
    s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;>
    subst h1 <;> subst h2 <;> subst h3 <;> subst h4 <;> subst h5 <;> subst h6 <;> rfl

/-- **Fragment 1 proven (`I₀ → initialReachable`)**: every
pristine-endgame state — empty final cycle, draw step 1, no
reveals, no foundations, the seven tail seats kept, board = the
initial edges plus stock riders on tail-or-rider card bases, every
stock card seated — is reachable from a dealt game.  The witness
play: one `frame_step` per stock card, in the rank-tier descent
(`frame_ladder`), each step drawing the target card to the waste top
and consuming it with a `deckPile`. -/
theorem PristineEndgame.initialReachable {st : State}
    (hpe : PristineEndgame st) : initialReachable st := by
  obtain ⟨hdeals, hwf, hdraw, hcards, hcursor0, hdepths, hheights, hkept, hcat,
      hseated⟩ := id hpe
  have hnd : noDupCards st.deal.stock := noDupCards_append_right hdeals.2.2
  -- the seeded frame: the dealt initial state, nothing done yet
  have hframe0 : FrameOK st (State.initial st.deal st.drawStep) [] := by
    refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_, hnd, Nat.zero_le _⟩
    · funext a
      show a.toIdx = st.depths a
      rw [hdepths a]
    · funext su
      show (0 : Nat) = st.heights su
      rw [hheights su]
    · intro b y hby
      obtain ⟨a, -, hba, hgt⟩ := initialBoard_topOf st.deal b y hby
      refine ⟨?_, Or.inr ⟨a, hgt⟩⟩
      rw [hba, hkept a, hgt]
    · intro b y hy hmem
      rcases hmem with hnil | ⟨a, hgt⟩
      · exact absurd hnil (by simp)
      · rcases hcat b y hy with ⟨a', hba', hgt'⟩ | ⟨hstock, -, -⟩
        · rw [hba']
          show (initialBoard st.deal).topOf (initBase st.deal a') = some y
          rw [initial_seats st.deal hdeals a', hgt']
        · exact absurd hstock (PristineEndgame.tail_not_stock hpe ⟨a, hgt⟩)
    · intro x
      constructor
      · intro hx
        refine ⟨hx, fun hc => absurd hc (by simp)⟩
      · intro hx
        exact hx.1
    · intro x hx
      exact absurd hx (by simp)
  -- the descent: twelve rank tiers, forty-hundred segments
  obtain ⟨w₂, SEG, hrun, hframe⟩ :=
    frame_ladder hpe hnd 12 (by omega)
      (State.initial st.deal st.drawStep) []
      (fun z hzs hlt => absurd hlt (by
        have := Rank.toIdx_lt z.rank
        omega))
      (fun x hx => absurd hx (by simp))
      hframe0
  obtain ⟨fw_deal, fw_depths, fw_heights, fw_draw, fw_up, fw_in, fw_stock,
      fw_dom, fw_nd, fw_cur⟩ := hframe
  -- the delivered cycle is empty
  have hnil : w₂.stock.cards = [] := by
    cases hc : w₂.stock.cards with
    | nil => rfl
    | cons x t =>
        have hxc : x ∈ w₂.stock.cards := by
          rw [hc]
          exact List.mem_cons_self
        obtain ⟨hxs, hxc2⟩ := (fw_stock x).mp hxc
        exact absurd ((chain_mem_iff 12 x).mpr
          ⟨hxs, by have := Rank.toIdx_lt x.rank; omega⟩) hxc2
  have hcur0 : w₂.stock.cursor = 0 := Nat.le_zero.mp (by
    rw [hnil] at fw_cur
    exact fw_cur)
  -- the delivered board matches the target pointwise
  have hboard : w₂.board = st.board :=
    Board.ext_topOf (funext (fun b => by
      cases hs : st.board.topOf b with
      | none =>
          cases hw : w₂.board.topOf b with
          | none => rfl
          | some y =>
              obtain ⟨hy1, -⟩ := fw_up b y hw
              rw [hs] at hy1
              exact absurd hy1 (by simp)
      | some y =>
          have hmem : y ∈ ([] ++ chain st 12) ∨ IsTail st.deal y := by
            rcases hcat b y hs with ⟨a, -, hgt⟩ | ⟨hstock, -, -⟩
            · exact Or.inr ⟨a, hgt⟩
            · refine Or.inl ((chain_mem_iff 12 y).mpr
                ⟨hstock, by have := Rank.toIdx_lt y.rank; omega⟩)
          exact fw_in b y hs hmem))
  -- the delivered state IS the target
  have hstock_eq : w₂.stock = st.stock := by
    rw [show w₂.stock = ⟨w₂.stock.cards, w₂.stock.cursor⟩ from rfl,
      hnil, hcur0,
      show st.stock = ⟨st.stock.cards, st.stock.cursor⟩ from rfl,
      hcards, hcursor0]
  have hw_eq : w₂ = st :=
    state_ext_fields fw_deal hboard fw_heights fw_depths hstock_eq fw_draw
  refine ⟨st.deal, st.drawStep, SEG, hdeals, ?_, ?_⟩
  · rw [hdraw]
    omega
  · rw [hw_eq] at hrun
    exact hrun

/-! ## Fragment 2: the stockful endgame

The target's cycle stays loaded: the construction consumes exactly
the *away* cards — the deal's stock cards that are NOT in the target
cycle — and lands the cycle byte (cards AND cursor) at the target's.
The ride from fragment 1: (a) the away-cards are drawn and seated in
the same rank-tier descent (their target bases are tails, processed
away riders, or free anchors for kings), all at draw step 1, so no
batch structure constrains the draws yet; (b) after the last consume
the cursor is rotated onto the target phase by the pure-draw tail —
the draw-1 offset walk (the batch-step arithmetic holds off until a
draw-3 flight; the standalone pieces are below); (c) the end-state
deck match is a filter identity — the consumed `done ++ chainAway`
selects exactly the complement of the target cycle in deal order.

The fragment's necessity fences live in Restriction.lean (the
wave-21 stock-side additions): `stockAccounted` (every dealt stock
card is in the cycle, visible, or founded), `cycleSelective` (the
cycle is its own membership selection from the deal's stock, in deal
order) and `seatedOrigins` (every visible or founded card is one of
the deal's cards).  `StockfulEndgame_iff_initialReachable` assembles
the iff against them. -/

/-- `contains` reads membership (the bridge between the raw-Boolean
filters and the proposition filters). -/
theorem contains_true_iff_mem (l : List Card) (x : Card) :
    l.contains x = true ↔ x ∈ l :=
  List.contains_iff_mem

/-- `contains` at false reads non-membership. -/
theorem contains_false_iff_notMem (l : List Card) (x : Card) :
    l.contains x = false ↔ x ∉ l := by
  constructor
  · intro h hmem
    have ht := List.contains_iff_mem.mpr hmem
    rw [h] at ht
    simp at ht
  · intro h
    cases hcd : l.contains x with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.mp hcd) h

/-- The away cards: the deal's stock cards that are NOT in the target
cycle — the construction's consuming set; the cycle keeps the rest
and the construction must land on it exactly. -/
def Away (st : State) : List Card :=
  st.deal.stock.filter fun x => !(st.stock.cards.contains x)

theorem mem_away_iff {st : State} {x : Card} :
    x ∈ Away st ↔ (x ∈ st.deal.stock ∧ x ∉ st.stock.cards) := by
  simp only [Away, List.mem_filter]
  constructor
  · rintro ⟨hmem, hc⟩
    refine ⟨hmem, fun hmem' => ?_⟩
    cases hcd : st.stock.cards.contains x with
    | false => exact absurd hmem' ((contains_false_iff_notMem _ x).mp hcd)
    | true => rw [hcd] at hc; simp at hc
  · intro ⟨hmem, hnc⟩
    refine ⟨hmem, ?_⟩
    show (!st.stock.cards.contains x) = true
    have hcd : st.stock.cards.contains x = false :=
      (contains_false_iff_notMem _ x).mpr (fun hmem' => hnc hmem')
    rw [hcd]
    rfl

theorem away_stock {st : State} {x : Card} (h : x ∈ Away st) :
    x ∈ st.deal.stock := (mem_away_iff.mp h).1

theorem away_not_cycle {st : State} {x : Card} (h : x ∈ Away st) :
    x ∉ st.stock.cards := (mem_away_iff.mp h).2

theorem away_nodup {st : State} (hnd : noDupCards st.deal.stock) :
    noDupCards (Away st) :=
  NoDupP_noDupCards (nodupP_filter _ (noDupCards_NoDupP hnd))

/-- The away set covers the cycle's complement in the deal's stock. -/
theorem stock_cycle_away {st : State} {x : Card} (h : x ∈ st.deal.stock) :
    x ∈ st.stock.cards ∨ x ∈ Away st := by
  by_cases hx : x ∈ st.stock.cards
  · exact Or.inl hx
  · refine Or.inr ?_
    rw [mem_away_iff]
    exact ⟨h, hx⟩

/-- **The fragment-2 distillate** `Iₛ` (the stockful endgame — the
I₀-style scoping with the cycle free; per-conjunct provenance in the
file header and the iff below): pristine flights (draw step 1, no
reveals, no foundations, tail seats kept), the edge catalogue
generalized to the away set with the anchor-rider arm (the necessity
side needs kings on free anchors — the decode of `board_edges`'s
anchor arm at a no-reveal target), every away card seated, and the
cycle's order fence (`cycleSelective`). -/
def StockfulEndgame (st : State) : Prop :=
  st.deal.WF ∧ st.WF ∧
  st.drawStep = 1 ∧
  (∀ a, st.depths a = a.toIdx) ∧
  (∀ s, st.heights s = 0) ∧
  (∀ a, st.board.topOf (initBase st.deal a) = (st.deal.piles a).getLast?) ∧
  (∀ b c, st.board.topOf b = some c →
     (∃ a, b = initBase st.deal a ∧ (st.deal.piles a).getLast? = some c) ∨
     (c ∈ Away st ∧ ∃ d, b = Sum.inr d ∧
        (IsTail st.deal d ∨ d ∈ Away st) ∧ canSitOn c d = true) ∨
     (c ∈ Away st ∧ c.rank = Rank.king ∧ ∃ a, b = Sum.inl a)) ∧
  (∀ c, c ∈ Away st → ∃ b, st.board.topOf b = some c) ∧
  st.cycleSelective

theorem StockfulEndgame.not_tail_of_away {st : State} (h : StockfulEndgame st)
    {d : Card} (hc : d ∈ Away st) : ¬ IsTail st.deal d := by
  intro ht
  obtain ⟨a, hgt⟩ := ht
  exact Deal.piles_stock_disj h.1 (mem_of_getLast hgt) (away_stock hc)

/-- **The rider seat shape, fragment 2**: every away card's target seat
is a card base whose card is a tail or another away card
(`canSitOn`-fitted), or a free anchor as a king. -/
theorem StockfulEndgame.riderSeat2 {st : State} (h : StockfulEndgame st)
    {c : Card} (hcs : c ∈ Away st) :
    ∃ b, st.board.topOf b = some c ∧
      ((∃ d, b = Sum.inr d ∧ (IsTail st.deal d ∨ d ∈ Away st)
          ∧ canSitOn c d = true)
        ∨ (∃ a, b = Sum.inl a ∧ c.rank = Rank.king)) := by
  obtain ⟨hdeals, hwf, -, -, -, hkept, hcat, hseated, -⟩ := id h
  obtain ⟨b, hb⟩ := hseated c hcs
  rcases hcat b c hb with ⟨a, hba, hgt⟩ | ⟨-, d, hbd, hform, hfit⟩ | ⟨-, hking, a, hba⟩
  · exfalso
    obtain ⟨hmem, -⟩ := mem_away_iff.mp hcs
    exact Deal.piles_stock_disj hdeals (mem_of_getLast hgt) hmem
  · exact ⟨b, hb, Or.inl ⟨d, hbd, hform, hfit⟩⟩
  · exact ⟨b, hb, Or.inr ⟨a, hba, hking⟩⟩

/-! ### The fragment-2 worklist frame

The frame carries the consuming bookkeeping as a *filter identity*:
the current cycle is the deal's stock with the consumed cards spliced
out, in deal order.  This is the list-level upgrade of fragment 1's
set-shaped invariant — what the end-state deck match needs.
-/

/-- (internal) The fragment-2 frame: same board discipline as
`FrameOK`; the cycle list is tracked exactly, `done` stays inside the
away set. -/
def Frame2 (st : State) (w : State) (done : List Card) : Prop :=
  w.deal = st.deal ∧ w.depths = st.depths ∧ w.heights = st.heights ∧
  w.drawStep = st.drawStep ∧
  (∀ b y, w.board.topOf b = some y →
     st.board.topOf b = some y ∧ (y ∈ done ∨ IsTail st.deal y)) ∧
  (∀ b y, st.board.topOf b = some y → (y ∈ done ∨ IsTail st.deal y) →
     w.board.topOf b = some y) ∧
  (w.stock.cards = st.deal.stock.filter fun x => !(done.contains x)) ∧
  (∀ x ∈ done, x ∈ Away st) ∧
  noDupCards w.stock.cards ∧
  w.stock.cursor ≤ w.stock.cards.length

/-- The frame's membership view: the current cycle holds exactly the
not-yet-consumed stock cards. -/
theorem Frame2.stock_mem {st : State} {w : State} {done : List Card}
    (hf : Frame2 st w done) {x : Card} :
    x ∈ w.stock.cards ↔ (x ∈ st.deal.stock ∧ x ∉ done) := by
  obtain ⟨-, -, -, -, -, -, hlist, -, -, -⟩ := id hf
  rw [hlist]
  simp only [List.mem_filter]
  constructor
  · rintro ⟨hmem, hc⟩
    refine ⟨hmem, fun hmem' => ?_⟩
    cases hcd : done.contains x with
    | false => exact absurd hmem' ((contains_false_iff_notMem _ x).mp hcd)
    | true =>
        rw [hcd] at hc
        simp at hc
  · intro ⟨hmem, hnc⟩
    refine ⟨hmem, ?_⟩
    show (!done.contains x) = true
    have hcd : done.contains x = false :=
      (contains_false_iff_notMem _ x).mpr (fun hmem' => hnc hmem')
    rw [hcd]
    rfl

/-- **The step with the placement in hand** (the base-generic tail of
the consume step): attach, round, refresh. -/
private theorem frame_step2_go {st : State} {c : Card}
    {w : State} {done : List Card} (hinv : Frame2 st w done)
    (hse : StockfulEndgame st) (hcs : c ∈ Away st)
    (hcnd : c ∉ done)
    {i : Nat} (hp : w.stock.posOf c = some i)
    {b : Base} (hseat : st.board.topOf b = some c)
    (hwfree : w.board.topOf b = none)
    (hwnew : w.board.bottomOf c = none)
    (hwplace : w.canPlace c b = true) :
    ∃ w' seg, w.run seg = some w' ∧ Frame2 st w' (done ++ [c]) := by
  obtain ⟨hdeals, hwf, hdraw0, -, -, -, -, -, -⟩ := id hse
  obtain ⟨iv_deal, iv_depths, iv_heights, iv_draw, iv_out, iv_in, iv_list,
      iv_dom, iv_nd, iv_cur⟩ := id hinv
  have hwds : w.drawStep = 1 := by rw [iv_draw]; exact hdraw0
  have hne : w.board.attach b c ≠ none :=
    (Board.attach_eq_some_iff w.board b c).mpr ⟨hwfree, hwnew⟩
  cases hattc : w.board.attach b c with
  | none => rw [hattc] at hne; exact absurd hne (by simp)
  | some bd =>
      obtain ⟨seg, hseg⟩ := round_deckPile hwds hp iv_cur hwplace hattc
      refine ⟨
        { w with board := bd, stock := ⟨Cycle.removeIdx w.stock.cards i, i⟩ },
        seg, hseg, ?_⟩
      have hnd' : ∀ x, x ∈ Cycle.removeIdx w.stock.cards i ↔
          x ∈ w.stock.cards ∧ x ≠ c := fun x =>
        mem_removeIdx_iff iv_nd (Cycle.posOf_get hp) x
      have hmemd : ∀ z ∈ done, z ∈ done ++ [c] :=
        fun z hz => List.mem_append.mpr (Or.inl hz)
      -- the list identity refresh (a splice is a filter)
      have hLsel : w.stock.cards
          = st.deal.stock.filter fun x => decide (x ∈ w.stock.cards) :=
        filter_mem_self iv_list
      have hL' : Cycle.removeIdx w.stock.cards i
          = st.deal.stock.filter fun x => !((done ++ [c]).contains x) := by
        rw [splice_selective iv_nd hLsel]
        refine List.filter_congr fun x hx => ?_
        have hpred : x ∈ Cycle.removeIdx w.stock.cards i ↔
            (x ∈ st.deal.stock ∧ x ∉ done ∧ x ≠ c) := by
          constructor
          · intro hx'
            obtain ⟨hwmem', hxc'⟩ := (hnd' x).mp hx'
            obtain ⟨hfull, hdone⟩ := (Frame2.stock_mem hinv).mp hwmem'
            exact ⟨hfull, hdone, hxc'⟩
          · intro ⟨hfull, hdone, hxc'⟩
            exact (hnd' x).mpr ⟨(Frame2.stock_mem hinv).mpr ⟨hfull, hdone⟩, hxc'⟩
        by_cases hxmem : x ∈ Cycle.removeIdx w.stock.cards i
        · obtain ⟨-, hdone', hxc'⟩ := hpred.mp hxmem
          have hcont : (done ++ [c]).contains x = false :=
            (contains_false_iff_notMem _ x).mpr (fun hmem => by
              rcases List.mem_append.mp hmem with h | h
              · exact hdone' h
              · exact hxc' (List.mem_singleton.mp h))
          rw [decide_eq_true hxmem, hcont]
          rfl
        · rw [decide_eq_false hxmem]
          have hcont : (done ++ [c]).contains x = true := by
            refine (contains_true_iff_mem _ x).mpr ?_
            by_cases hxd : x ∈ done
            · exact List.mem_append.mpr (Or.inl hxd)
            · have hxc : x = c := by
                by_cases hxc' : x = c
                · exact hxc'
                · exact absurd (hpred.mpr ⟨hx, hxd, hxc'⟩) hxmem
              rw [hxc]
              exact List.mem_append.mpr (Or.inr (by simp))
          rw [hcont]
          rfl
      refine ⟨iv_deal, iv_depths, iv_heights, iv_draw, ?_, ?_, hL', ?_, ?_, ?_⟩
      · -- OUT: current tops are target tops of processed-or-tail cards
        intro b₁ y₁ hb₁
        by_cases hb : b₁ = b
        · rw [hb] at hb₁ ⊢
          rw [Board.attach_topOf w.board b c hattc] at hb₁
          have hb1y : y₁ = c := Option.some.inj hb₁.symm
          subst hb1y
          exact ⟨hseat, Or.inl (List.mem_append.mpr (Or.inr (by simp)))⟩
        · rw [Board.attach_topOf_ne w.board b c hattc hb] at hb₁
          obtain ⟨hst, hmem⟩ := iv_out b₁ y₁ hb₁
          exact ⟨hst, hmem.elim (fun hz => Or.inl (hmemd y₁ hz)) Or.inr⟩
      · -- IN: target tops of processed-or-tail cards are current tops
        intro b₁ y₁ hsty hmem
        rcases hmem with hmem' | htail
        · rcases List.mem_append.mp hmem' with hz | hzc
          · have hbdiff : b₁ ≠ b := by
              intro hcon
              rw [hcon] at hsty
              have hyc : y₁ = c := Option.some.inj (hsty.symm.trans hseat)
              rw [hyc] at hz
              exact hcnd hz
            rw [Board.attach_topOf_ne w.board b c hattc hbdiff]
            exact iv_in b₁ y₁ hsty (Or.inl hz)
          · have hyc : y₁ = c := List.mem_singleton.mp hzc
            rw [hyc] at hsty ⊢
            have hbdiff : b₁ = b := st.board.inj b₁ b c hsty hseat
            rw [hbdiff]
            exact Board.attach_topOf w.board b c hattc
        · have hbdiff : b₁ ≠ b := by
            intro hcon
            rw [hcon] at hsty
            have hyc : y₁ = c := Option.some.inj (hsty.symm.trans hseat)
            rw [hyc] at htail
            exact StockfulEndgame.not_tail_of_away hse hcs htail
          rw [Board.attach_topOf_ne w.board b c hattc hbdiff]
          exact iv_in b₁ y₁ hsty (Or.inr htail)
      · -- done stays inside the away set
        intro z hz
        rcases List.mem_append.mp hz with hz' | hzc
        · exact iv_dom z hz'
        · have hzc' : z = c := List.mem_singleton.mp hzc
          rw [hzc']
          exact hcs
      · -- noDup survives the splice
        exact noDupCards_removeIdx _ _ iv_nd
      · -- cursor: the consumed position sits within the new list
        have hlt := Cycle.posOf_lt hp
        have hlen := Cycle.removeIdx_length w.stock.cards i hlt
        show i ≤ (Cycle.removeIdx w.stock.cards i).length
        omega

/-- **The fragment-2 consume step**: draw the away rider `c` to the
waste top and seat it at its target base — a card base (tail or an
already-processed away rider) or a free anchor (kings).  The frame's
list identity refreshes through the splice kit (a splice is a filter). -/
theorem frame_step2 {st : State} (hse : StockfulEndgame st) {c : Card}
    (hcs : c ∈ Away st)
    {w : State} {done : List Card} (hinv : Frame2 st w done)
    (hcnd : c ∉ done)
    (hhigh : ∀ z ∈ Away st, c.rank.toIdx < z.rank.toIdx → z ∈ done) :
    ∃ w' seg, w.run seg = some w' ∧ Frame2 st w' (done ++ [c]) := by
  obtain ⟨hdeals, hwfs, hdraw0, hdepths0, hheights0, hkept, hcat, hseated, hsel⟩ := id hse
  have hwmem : c ∈ w.stock.cards := (Frame2.stock_mem hinv).mpr
    ⟨away_stock hcs, hcnd⟩
  cases hp : w.stock.posOf c with
  | none => exact absurd hp (Cycle.posOf_mem hwmem)
  | some i =>
      obtain ⟨b, hseat, hbc⟩ := StockfulEndgame.riderSeat2 hse hcs
      obtain ⟨-, -, -, -, iv_out, iv_in, iv_list,
          iv_dom, iv_nd, iv_cur⟩ := id hinv
      have hwfree : w.board.topOf b = none := by
        cases hwtop : w.board.topOf b with
        | none => rfl
        | some y =>
            exfalso
            obtain ⟨hy1, hy2⟩ := iv_out b y hwtop
            have hyc : y = c := Option.some.inj (hy1.symm.trans hseat)
            subst hyc
            rcases hy2 with hmem | htail
            · exact absurd hmem hcnd
            · exact StockfulEndgame.not_tail_of_away hse hcs htail
      have hwnew : w.board.bottomOf c = none :=
        (Board.bottomOf_eq_none w.board c).mpr (fun b' hb' => by
          obtain ⟨-, hy2⟩ := iv_out b' c hb'
          rcases hy2 with hmem | htail
          · exact absurd hmem hcnd
          · exact StockfulEndgame.not_tail_of_away hse hcs htail)
      rcases hbc with ⟨d0, hbd, hdform, hfit⟩ | ⟨a0, hba, hking⟩
      · -- card base: the base card must sit in w (its own target seat)
        subst hbd
        have hbased : ∃ b₀, w.board.topOf b₀ = some d0 := by
          rcases hdform with htail | haway
          · obtain ⟨a, hgt⟩ := htail
            refine ⟨initBase st.deal a,
              iv_in (initBase st.deal a) d0 ?_ (Or.inr ⟨a, hgt⟩)⟩
            rw [hkept a, hgt]
          · have hdrank : c.rank.toIdx + 1 = d0.rank.toIdx :=
              (canSitOn_eq c d0).mp hfit |>.1
            have hddone : d0 ∈ done := hhigh d0 haway (by omega)
            obtain ⟨b₀, hb₀⟩ := hseated d0 haway
            exact ⟨b₀, iv_in b₀ d0 hb₀ (Or.inl hddone)⟩
        have hwvis : w.isVis d0 = true := by
          obtain ⟨b₀, hwso⟩ := hbased
          show (w.board.bottomOf d0).isSome = true
          rw [(Board.bottomOf_eq w.board d0 b₀).mpr hwso]
          rfl
        have hwplace : w.canPlace c (Sum.inr d0) = true := by
          show (decide (w.board.topOf (Sum.inr d0) = none) &&
                (w.isVis d0 && canSitOn c d0)) = true
          rw [hwfree, hwvis, hfit]
          rfl
        exact frame_step2_go hinv hse hcs hcnd hp hseat hwfree hwnew hwplace
      · -- anchor base: kings only
        subst hba
        have hwplace : w.canPlace c (Sum.inl a0) = true := by
          show (decide (w.board.topOf (Sum.inl a0) = none) &&
                decide (c.rank = Rank.king)) = true
          rw [hwfree, hking]
          rfl
        exact frame_step2_go hinv hse hcs hcnd hp hseat hwfree hwnew hwplace

/-! ### The away tier descent -/

/-- One rank's worth of the fragment-2 schedule: the away cards of
rank exactly `n` (the order within a tier is immaterial). -/
def tierAway (st : State) (n : Nat) : List Card :=
  (Away st).filter fun x => decide (x.rank.toIdx = n)

theorem tierAway_mem {st : State} {n : Nat} {x : Card}
    (hx : x ∈ tierAway st n) : x ∈ Away st ∧ x.rank.toIdx = n := by
  simp only [tierAway, List.mem_filter, decide_eq_true_iff] at hx
  exact hx

theorem tierAway_catch {st : State} {n : Nat} {x : Card}
    (hxs : x ∈ Away st) (hx : x.rank.toIdx = n) : x ∈ tierAway st n := by
  simp only [tierAway, List.mem_filter, decide_eq_true_iff]
  exact ⟨hxs, hx⟩

/-- The rank-tier lists of the away set, descending. -/
def chainAway (st : State) : Nat → List Card
  | 0 => tierAway st 0
  | t + 1 => tierAway st (t + 1) ++ chainAway st t

theorem chainAway_succ (st : State) (t : Nat) :
    chainAway st (t + 1) = tierAway st (t + 1) ++ chainAway st t := rfl

theorem chainAway_nil_unfold (st : State) :
    chainAway st 0 = tierAway st 0 := rfl

theorem chainAway_away {st : State} : ∀ (t : Nat) (x : Card),
    x ∈ chainAway st t → x ∈ Away st := by
  intro t
  induction t with
  | zero =>
      intro x hx
      exact (tierAway_mem hx).1
  | succ t ih =>
      intro x hx
      rw [chainAway_succ] at hx
      rcases List.mem_append.mp hx with h | h
      · exact (tierAway_mem h).1
      · exact ih x h

/-- The chain catalogue: membership in the remaining away work. -/
theorem chainAway_mem_iff {st : State} : ∀ (t : Nat) (x : Card),
    x ∈ chainAway st t ↔ (x ∈ Away st ∧ x.rank.toIdx ≤ t) := by
  intro t
  induction t with
  | zero =>
      intro x
      rw [chainAway_nil_unfold]
      constructor
      · intro hx
        exact ⟨(tierAway_mem hx).1, by
            have := (tierAway_mem hx).2
            omega⟩
      · intro ⟨hxs, hrk⟩
        exact tierAway_catch hxs (by omega)
  | succ t ih =>
      intro x
      rw [chainAway_succ]
      constructor
      · intro hx
        rcases List.mem_append.mp hx with h | h
        · exact ⟨(tierAway_mem h).1, by
            have := (tierAway_mem h).2
            omega⟩
        · obtain ⟨h1, h2⟩ := (ih x).mp h
          exact ⟨h1, by omega⟩
      · intro ⟨hxs, hrk⟩
        by_cases hx : x.rank.toIdx = t + 1
        · exact List.mem_append.mpr (Or.inl (tierAway_catch hxs hx))
        · exact List.mem_append.mpr (Or.inr ((ih x).mpr ⟨hxs, by omega⟩))

theorem chainAway_nodup {st : State} (hnd : noDupCards (Away st)) :
    ∀ (t : Nat), (chainAway st t).Nodup := by
  intro t
  induction t with
  | zero =>
      exact List.filter_nodup _ _ (nodup_of_noDupCards hnd)
  | succ t ih =>
      have h1 : (tierAway st (t + 1)).Nodup :=
        List.filter_nodup _ _ (nodup_of_noDupCards hnd)
      refine nodup_append_intro _ _ h1 ih ?_
      intro x hx hmem
      have hrkx := (tierAway_mem hx).2
      have hrkc := (chainAway_mem_iff t x).mp hmem |>.2
      omega

/-- **One away tier's work** (fragment 2's `frame_tier`). -/
theorem frame_tier2 {st : State} (hse : StockfulEndgame st) :
    ∀ (n : Nat) (L : List Card) (w : State) (done : List Card),
    (∀ x ∈ L, x ∈ Away st) →
    (∀ x ∈ L, x.rank.toIdx = n) →
    L.Nodup →
    (∀ z ∈ Away st, n < z.rank.toIdx → z ∈ done) →
    (∀ x ∈ L, x ∉ done) →
    Frame2 st w done →
    ∃ (w' : State) (seg : List Move),
      w.run seg = some w' ∧ Frame2 st w' (done ++ L) := by
  intro n L
  induction L with
  | nil =>
      intro w done _ _ _ _ _ hinv
      refine ⟨w, [], rfl, ?_⟩
      rw [List.append_nil]
      exact hinv
  | cons x L' ih =>
      intro w done hLaway hLrank hLnd hgt hLnd' hinv
      have hxa : x ∈ Away st := hLaway x (List.mem_cons_self)
      have hxnd : x ∉ done := hLnd' x (List.mem_cons_self)
      have hhigh : ∀ z ∈ Away st, x.rank.toIdx < z.rank.toIdx → z ∈ done := by
        intro z hzs hlt
        exact hgt z hzs (by
          have := hLrank x (List.mem_cons_self)
          omega)
      obtain ⟨w₁, seg₁, hrun₁, hinv₁⟩ := frame_step2 hse hxa hinv hxnd hhigh
      obtain ⟨w₂, seg₂, hrun₂, hinv₂⟩ :=
        ih w₁ (done ++ [x])
          (fun y hy => hLaway y (List.mem_cons_of_mem _ hy))
          (fun y hy => hLrank y (List.mem_cons_of_mem _ hy))
          (List.nodup_cons.mp hLnd).2
          (fun z hzs hlt =>
            List.mem_append.mpr (Or.inl (hgt z hzs hlt)))
          (fun y hy hmem => by
            rcases List.mem_append.mp hmem with hz | hyx
            · exact hLnd' y (List.mem_cons_of_mem _ hy) hz
            · exact (List.nodup_cons.mp hLnd).1 (by
                rw [<- List.mem_singleton.mp hyx]
                exact hy))
          hinv₁
      refine ⟨w₂, seg₁ ++ seg₂, ?_, ?_⟩
      · rw [run_append, hrun₁]
        exact hrun₂
      · rw [show x :: L' = [x] ++ L' from rfl, <- List.append_assoc]
        exact hinv₂

/-- **The away descent ladder** (fragment 2's `frame_ladder`). -/
theorem frame_ladder2 {st : State} (hse : StockfulEndgame st)
    (hnd : noDupCards (Away st)) :
    ∀ (t : Nat), t ≤ 12 →
    ∀ (w : State) (done : List Card),
    (∀ z ∈ Away st, t < z.rank.toIdx → z ∈ done) →
    (∀ d ∈ done, t < d.rank.toIdx) →
    Frame2 st w done →
    ∃ (w' : State) (seg : List Move),
      w.run seg = some w' ∧ Frame2 st w' (done ++ chainAway st t) := by
  intro t
  induction t with
  | zero =>
      intro _ w done hgt hdom hinv
      obtain ⟨w', seg, hrun, hframe⟩ :=
        frame_tier2 hse 0 (tierAway st 0) w done
          (fun x hx => (tierAway_mem hx).1)
          (fun x hx => (tierAway_mem hx).2)
          (chainAway_nodup hnd 0)
          hgt
          (fun x hx hd => absurd (hdom x hd) (by
            have := (tierAway_mem hx).2
            omega))
          hinv
      exact ⟨w', seg, hrun, hframe⟩
  | succ t ih =>
      intro ht12 w done hgt hdom hinv
      have ht1 : t ≤ 12 := by omega
      have htieraway : ∀ x ∈ tierAway st (t + 1), x ∈ Away st :=
        fun x hx => (tierAway_mem hx).1
      have htierrk : ∀ x ∈ tierAway st (t + 1), x.rank.toIdx = t + 1 :=
        fun x hx => (tierAway_mem hx).2
      have htiernd : ∀ x ∈ tierAway st (t + 1), x ∉ done :=
        fun x hx hd => absurd (hdom x hd) (by
          have := (tierAway_mem hx).2
          omega)
      have hgt' : ∀ z ∈ Away st, t + 1 < z.rank.toIdx → z ∈ done :=
        fun z hzs hlt => hgt z hzs hlt
      obtain ⟨w₁, seg₁, hrun₁, hinv₁⟩ :=
        frame_tier2 hse (t + 1) (tierAway st (t + 1)) w done
          htieraway htierrk (List.filter_nodup _ _ (nodup_of_noDupCards hnd))
          hgt' htiernd hinv
      obtain ⟨w₂, seg₂, hrun₂, hinv₂⟩ :=
        ih ht1 w₁ (done ++ tierAway st (t + 1))
          (fun z hzs hlt => by
            by_cases hz : (t + 1) < z.rank.toIdx
            · exact List.mem_append.mpr
                (Or.inl (hgt z hzs hz))
            · refine List.mem_append.mpr (Or.inr ?_)
              have hrk : z.rank.toIdx = t + 1 := by omega
              exact tierAway_catch hzs hrk)
          (fun d hd => by
            rcases List.mem_append.mp hd with hd1 | hd2
            · have := hdom d hd1
              omega
            · have := (tierAway_mem hd2).2
              omega)
          hinv₁
      refine ⟨w₂, seg₁ ++ seg₂, ?_, ?_⟩
      · rw [run_append, hrun₁]
        exact hrun₂
      · rw [chainAway_succ, ← List.append_assoc]
        exact hinv₂

/-! ### The fragment-2 main theorem -/

/-- `decide`-membership reads `contains` (the decide-instance bridge). -/
theorem decide_mem_eq_contains (l : List Card) (x : Card) :
    decide (x ∈ l) = l.contains x := by
  cases h : l.contains x with
  | true =>
      rw [decide_eq_true (List.contains_iff_mem.mp h)]
  | false =>
      rw [decide_eq_false (fun hm =>
        by rw [List.contains_iff_mem.mpr hm] at h; simp at h)]

/-- **Fragment 2 proven (`Iₛ → initialReachable`)**: every stockful
endgame state — the pristine flights (draw step 1, no reveals, no
foundations, tail seats kept), a general loaded cycle, the edge
catalogue over the away set (with the anchor-rider arm), every away
card seated, the cycle's order fence — is reachable from a deal.
The witness play: one `frame_step2` per away card in the rank-descent
(`frame_ladder2`), then the pure-draw tail rotating the cursor onto
the target phase (`Cycle.iterDraw` walks), and the deck match closes
through the filter identities (`cycleSelective`, the frame's list
identity). -/
theorem StockfulEndgame.initialReachable {st : State}
    (hse : StockfulEndgame st) : initialReachable st := by
  obtain ⟨hdeals, hwf, hdraw, hdepths, hheights, hkept, hcat, hseated, hsel⟩ := id hse
  have hnd : noDupCards st.deal.stock := noDupCards_append_right hdeals.2.2
  have hawnd : noDupCards (Away st) := away_nodup hnd
  obtain ⟨-, -, -, -, -, -, -, -, hcurle, -⟩ := id hwf
  -- the seeded frame: the dealt initial state, nothing done yet
  have hframe0 : Frame2 st (State.initial st.deal st.drawStep) [] := by
    refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_, hnd, Nat.zero_le _⟩
    · funext a
      show a.toIdx = st.depths a
      rw [hdepths a]
    · funext su
      show (0 : Nat) = st.heights su
      rw [hheights su]
    · intro b y hby
      obtain ⟨a, -, hba, hgt⟩ := initialBoard_topOf st.deal b y hby
      refine ⟨?_, Or.inr ⟨a, hgt⟩⟩
      rw [hba, hkept a, hgt]
    · intro b y hy hmem
      rcases hmem with hnil | ⟨a, hgt⟩
      · exact absurd hnil (by simp)
      · rcases hcat b y hy with ⟨a', hba', hgt'⟩ | ⟨hcaw, -, -, -⟩
          | ⟨hcaw, -, -, -⟩
        · rw [hba']
          show (initialBoard st.deal).topOf (initBase st.deal a') = some y
          rw [initial_seats st.deal hdeals a', hgt']
        · exact absurd ⟨a, hgt⟩ (StockfulEndgame.not_tail_of_away hse hcaw)
        · exact absurd ⟨a, hgt⟩ (StockfulEndgame.not_tail_of_away hse hcaw)
    · show (State.initial st.deal st.drawStep).stock.cards
          = st.deal.stock.filter fun x => !(([] : List Card).contains x)
      rw [show (State.initial st.deal st.drawStep).stock.cards
          = st.deal.stock from rfl]
      have hf : List.filter (fun x => !(([ ] : List Card).contains x)) st.deal.stock
          = st.deal.stock :=
        List.filter_eq_self.mpr (fun x _ => by
          show (!(([ ] : List Card).contains x)) = true
          simp)
      exact hf.symm
    · intro x hx
      exact absurd hx (by simp)
  -- the away descent: twelve rank tiers
  obtain ⟨w₂, SEG, hrun, hframe⟩ :=
    frame_ladder2 hse hawnd 12 (by omega)
      (State.initial st.deal st.drawStep) []
      (fun z hzs hlt => absurd hlt (by
        have := Rank.toIdx_lt z.rank
        omega))
      (fun x hx => absurd hx (by simp))
      hframe0
  obtain ⟨fw_deal, fw_depths, fw_heights, fw_draw, fw_up, fw_in, fw_list,
      fw_dom, fw_nd, fw_cur⟩ := hframe
  -- the consumed set at the end is exactly the away set
  have hdoneall : ∀ x, x ∈ ([] ++ chainAway st 12) ↔ x ∈ Away st := by
    intro x
    constructor
    · intro hx
      rcases List.mem_append.mp hx with h | h
      · exact absurd h (by simp)
      · exact chainAway_away 12 x h
    · intro hx
      refine List.mem_append.mpr (Or.inr ?_)
      exact (chainAway_mem_iff 12 x).mpr
        ⟨hx, by have := Rank.toIdx_lt x.rank; omega⟩
  -- (c) THE END-STATE DECK MATCH: the cycle's cards are the target's
  have hcards : w₂.stock.cards = st.stock.cards := by
    rw [fw_list, hsel]
    refine List.filter_congr fun x hx => ?_
    by_cases haw : x ∈ Away st
    · have hch : (([] ++ chainAway st 12) : List Card).contains x = true :=
        (contains_true_iff_mem _ x).mpr ((hdoneall x).mpr haw)
      have hcyc : (st.stock.cards.contains x) = false :=
        (contains_false_iff_notMem _ x).mpr (away_not_cycle haw)
      rw [decide_mem_eq_contains, hch, hcyc]
      rfl
    · have hch : (([] ++ chainAway st 12) : List Card).contains x = false :=
        (contains_false_iff_notMem _ x).mpr
          (fun hxmem => haw ((hdoneall x).mp hxmem))
      have hcyc : st.stock.cards.contains x = true := by
        refine (contains_true_iff_mem _ x).mpr ?_
        rcases stock_cycle_away hx with hxin | haw'
        · exact hxin
        · exact absurd haw' haw
      rw [decide_mem_eq_contains, hch, hcyc]
      rfl
  -- (b) THE PHASE TAIL: rotate the cursor onto the target phase
  have hk : st.stock.cursor ≤ st.stock.cards.length := hcurle
  have hiter : Cycle.iterDraw
      (w₂.stock.cards.length - w₂.stock.cursor + 1 + st.stock.cursor)
      ⟨w₂.stock.cards, w₂.stock.cursor⟩ = ⟨st.stock.cards, st.stock.cursor⟩ := by
    have hj : w₂.stock.cursor ≤ w₂.stock.cards.length := fw_cur
    have hw1 : Cycle.iterDraw (w₂.stock.cards.length - w₂.stock.cursor)
        ⟨w₂.stock.cards, w₂.stock.cursor⟩
        = ⟨w₂.stock.cards, w₂.stock.cards.length⟩ := by
      have h4 := Cycle.iterDraw_lt
        (w₂.stock.cards.length - w₂.stock.cursor) w₂.stock.cards w₂.stock.cursor
        (by omega)
      rw [show w₂.stock.cursor + (w₂.stock.cards.length - w₂.stock.cursor)
            = w₂.stock.cards.length from by omega] at h4
      exact h4
    have hw2 : Cycle.iterDraw 1 (⟨w₂.stock.cards, w₂.stock.cards.length⟩ : Cycle Card)
        = ⟨w₂.stock.cards, 0⟩ :=
      (Cycle.iterDraw_one _).trans (Cycle.dealOnce_wrap' (Nat.le_refl _))
    have hk2 : st.stock.cursor ≤ w₂.stock.cards.length := by
      rw [hcards]
      exact hk
    have h3 : Cycle.iterDraw st.stock.cursor (⟨w₂.stock.cards, 0⟩ : Cycle Card)
        = ⟨w₂.stock.cards, 0 + st.stock.cursor⟩ :=
      Cycle.iterDraw_lt st.stock.cursor w₂.stock.cards 0 (by omega)
    rw [show (w₂.stock.cards.length - w₂.stock.cursor) + 1 + st.stock.cursor
          = (w₂.stock.cards.length - w₂.stock.cursor) + (1 + st.stock.cursor) from by omega,
      Cycle.iterDraw_add, Cycle.iterDraw_add, hw1, hw2]
    rw [hcards, Nat.zero_add] at h3
    rw [hcards]
    exact h3
  have hwds2 : w₂.drawStep = 1 := by rw [fw_draw]; exact hdraw
  have htail : w₂.run (List.replicate
      (w₂.stock.cards.length - w₂.stock.cursor + 1 + st.stock.cursor) Move.draw)
      = some { w₂ with stock := st.stock } := by
    rw [run_replicate_draw _ _ hwds2, hiter]
  -- the delivered board matches the target pointwise
  have hboard : w₂.board = st.board :=
    Board.ext_topOf (funext (fun b => by
      cases hs : st.board.topOf b with
      | none =>
          cases hw : w₂.board.topOf b with
          | none => rfl
          | some y =>
              obtain ⟨hy1, -⟩ := fw_up b y hw
              rw [hs] at hy1
              exact absurd hy1 (by simp)
      | some y =>
          have hmem : y ∈ ([] ++ chainAway st 12) ∨ IsTail st.deal y := by
            rcases hcat b y hs with ⟨a, -, hgt⟩ | ⟨hcaw, -, -, -⟩ | ⟨hcaw, -, -, -⟩
            · exact Or.inr ⟨a, hgt⟩
            · exact Or.inl ((hdoneall y).mpr hcaw)
            · exact Or.inl ((hdoneall y).mpr hcaw)
          exact fw_in b y hs hmem))
  -- assemble: state equality, then the deposit
  have hw_eq : { w₂ with stock := st.stock } = st :=
    state_ext_fields fw_deal hboard fw_heights fw_depths rfl fw_draw
  refine ⟨st.deal, st.drawStep,
    SEG ++ List.replicate
      (w₂.stock.cards.length - w₂.stock.cursor + 1 + st.stock.cursor) Move.draw,
    hdeals, ?_, ?_⟩
  · rw [hdraw]
    omega
  · rw [run_append, hrun]
    rw [hw_eq] at htail
    exact htail

/-! ### The necessity side: the fences assemble the distillate -/

/-- (internal) an early position is in the take. -/
private theorem mem_take_of_getElem : ∀ {l : List Card} {c : Card} {n k : Nat},
    l[k]? = some c → k < n → c ∈ l.take n := by
  intro l
  induction l with
  | nil => intro c n k hk _; simp at hk
  | cons x t ih =>
      intro c n k hk hlt
      cases n with
      | zero => omega
      | succ n' =>
          cases k with
          | zero =>
              have hxc : x = c := Option.some.inj hk
              show c ∈ x :: t.take n'
              rw [hxc]
              exact List.mem_cons_self
          | succ k' =>
              show c ∈ x :: t.take n'
              have hk' : t[k']? = some c := by
                rw [List.getElem?_cons_succ] at hk
                exact hk
              have hlt' : k' < n' := by omega
              exact List.mem_cons_of_mem _ (ih hk' hlt')

/-- (internal) a visible pile card at a no-reveal state is its pile's
dealt tail (the hidden slice is the take, so a visible member sits at
the take boundary). -/
private theorem tail_of_vis_pile {st : State} {a : Anchor} {c : Card}
    (hdeals : st.deal.WF) (hnr : st.depths a = a.toIdx)
    (hvnh : st.vis_not_hidden) (hvis : st.isVis c = true)
    (hmem : c ∈ st.deal.piles a) :
    (st.deal.piles a).getLast? = some c := by
  obtain ⟨k, hk2⟩ := List.mem_iff_getElem?.mp hmem
  have hlen : (st.deal.piles a).length = a.toIdx + 1 := hdeals.1 a
  have hk1 : k < (st.deal.piles a).length := (List.getElem?_eq_some_iff.mp hk2).1
  rcases Nat.lt_or_ge k a.toIdx with hkt | hkge
  · exfalso
    refine hvnh c hvis a ?_
    show c ∈ (st.deal.piles a).take (st.depths a)
    rw [hnr]
    exact mem_take_of_getElem hk2 hkt
  · refine getLast?_of_index _ c ?_
    rw [show (st.deal.piles a).length - 1 = a.toIdx from by rw [hlen]; omega]
    have hke : k = a.toIdx := by omega
    rw [hke] at hk2
    exact hk2

/-- **The assembled iff** (fragment 2's ladder head): under the four
flight conditions — draw step 1, no reveals, no foundations, tail
seats kept — the stockful-endgame distillate is exactly
dealt-reachability.  Sufficiency is `StockfulEndgame.initialReachable`
(the construction); necessity is the fence decode: `visClean` +
`board_edges` give the edge catalogue (a visible pile card is a kept
tail by `tail_of_vis_pile`; an away rider's card base is fitted and
its base card a tail or another away card; the anchor arm carries the
king), `stockAccounted` seats the away cards (the heights-0 flight
kills the foundation disjunct), and `cycleSelective` is the order
fence.  Provenance per conjunct: the four flights are this statement's
hypotheses (the fragment's scope, necessity not claimed); the rest
cites the three wave-21 fences plus the wave-13/19 reachability
fences (`initialReachable_visClean`). -/
theorem StockfulEndgame_iff_initialReachable {st : State}
    (hs1 : st.drawStep = 1) (hnr : ∀ a, st.depths a = a.toIdx)
    (hnf : ∀ s, st.heights s = 0)
    (hkept : ∀ a, st.board.topOf (initBase st.deal a) = (st.deal.piles a).getLast?) :
    StockfulEndgame st ↔ initialReachable st := by
  constructor
  · exact StockfulEndgame.initialReachable
  · intro hr
    obtain ⟨hwf, hvis⟩ := initialReachable_visClean hr
    have hstockacc := stockAccounted_of_initialReachable hr
    have horigins := seatedOrigins_of_initialReachable hr
    have hselfence := cycleSelective_of_initialReachable hr
    refine ⟨hwf.deal_wf, hwf, hs1, hnr, hnf, hkept, ?_, ?_, hselfence⟩
    · -- the edge catalogue
      intro b c htop
      obtain ⟨hbot, hedge⟩ := hwf.board_edges b c htop
      have hvisc : st.isVis c = true := by
        show (st.board.bottomOf c).isSome = true
        rw [hbot]
        rfl
      rcases horigins c (Or.inl hvisc) with ⟨a₀, hpile⟩ | hstock
      · have hgt := tail_of_vis_pile hwf.deal_wf (hnr a₀) hwf.vis_not_hidden hvisc hpile
        refine Or.inl ⟨a₀, ?_, hgt⟩
        exact st.board.inj b (initBase st.deal a₀) c htop
          (by rw [hkept a₀, hgt])
      · rcases stock_cycle_away hstock with hcyc | hcaw
        · exfalso
          exact absurd hcyc (fun hcon =>
            Cycle.posOf_mem hcon (hwf.vis_off_cycle c hvisc))
        · cases b with
          | inl a =>
              rcases hedge with hking | hhead
              · exact Or.inr (Or.inr ⟨hcaw, hking, a, rfl⟩)
              · exfalso
                have hpm : c ∈ st.deal.piles a := by
                  cases hpiles : (st.deal.piles a) with
                  | nil =>
                      rw [hpiles] at hhead
                      exact absurd hhead (by simp)
                  | cons x t =>
                      rw [hpiles] at hhead
                      show c ∈ x :: t
                      rw [Option.some.inj hhead]
                      exact List.mem_cons_self
                exact Deal.piles_stock_disj hwf.deal_wf hpm (away_stock hcaw)
          | inr d =>
              rcases hedge with ⟨a₁, t, rest, hadj, -⟩ | ⟨hdseated, hfit⟩
              · exfalso
                have hcm : c ∈ st.deal.piles a₁ := by
                  rw [hadj]
                  exact List.mem_append.mpr (Or.inr
                    (List.mem_cons.mpr (Or.inr (List.mem_cons_self))))
                exact Deal.piles_stock_disj hwf.deal_wf hcm (away_stock hcaw)
              · refine Or.inr (Or.inl ⟨hcaw, d, rfl, ?_, hfit⟩)
                have hdvis : st.isVis d = true := by
                  show (st.board.bottomOf d).isSome = true
                  exact hdseated
                rcases horigins d (Or.inl hdvis) with ⟨a₂, hpile₂⟩ | hstock₂
                · exact Or.inl ⟨a₂,
                    tail_of_vis_pile hwf.deal_wf (hnr a₂) hwf.vis_not_hidden hdvis hpile₂⟩
                · rcases stock_cycle_away hstock₂ with hdcyc | hdcaw
                  · exact absurd hdcyc (fun hcon =>
                      Cycle.posOf_mem hcon (hwf.vis_off_cycle d hdvis))
                  · exact Or.inr hdcaw
    · -- every away card is seated
      intro c hc
      obtain ⟨-, hncycle⟩ := mem_away_iff.mp hc
      rcases hstockacc c (away_stock hc) with hcyc | hvisc | hfnd
      · exact absurd hcyc hncycle
      · cases hbot : st.board.bottomOf c with
        | none =>
            exfalso
            have hf : (st.board.bottomOf c).isSome = true := hvisc
            rw [hbot] at hf
            simp at hf
        | some b => exact ⟨b, (Board.bottomOf_eq st.board c b).mp hbot⟩
      · exfalso
        have hlt : c.rank.toIdx < st.heights c.suit := of_decide_eq_true hfnd
        rw [hnf c.suit] at hlt
        omega

/-! ### The batch-step offset kit (standalone, draw step s ≥ 1)

The stockful fragment's flights pin draw step 1 — the phase tail
walks by the single-card `iterDraw` facts and no batch structure
constrains the schedule.  The general-step arithmetic — the *offset
lemma's* content — sits here as standalone pieces for the next rung
(the draw-3 flight): the mid-pass batch advance, the pass-end clamp
(the partial final batch — the tail draw, whose count is determined),
the pass-end wrap (step-size independent), and the waste-top LIFO —
a drawn batch is consumed top-first, the *batch-reversal* as a list
identity: any target waste/cycle phase decomposes into (full batches
of `s` draws) + (the clamped tail draw) + (the wrap), and the batch's
content leaves the cycle in reverse deal order while the pass body
stays untouched. -/

/-- The mid-pass advance at any step: a full batch when the pass is
long enough. -/
theorem Cycle.dealOnce_step_any {cy : Cycle Card} (s : Nat)
    (hgt : cy.cursor < cy.cards.length)
    (h : cy.cursor + s ≤ cy.cards.length) :
    cy.dealOnce s = ⟨cy.cards, cy.cursor + s⟩ := by
  simp only [Cycle.dealOnce]
  rw [ite_eq_right (by show ¬(cy.cursor ≥ cy.cards.length); omega),
    Nat.min_eq_left h]

/-- The pass-end clamp at any step: a partial final batch lands the
cursor AT the pass end (the tail draw is clamped, its position
determined by the pass length alone). -/
theorem Cycle.dealOnce_tail_any {cy : Cycle Card} (s : Nat)
    (hgt : cy.cursor < cy.cards.length)
    (h : cy.cards.length ≤ cy.cursor + s) :
    cy.dealOnce s = ⟨cy.cards, cy.cards.length⟩ := by
  simp only [Cycle.dealOnce]
  rw [ite_eq_right (by show ¬(cy.cursor ≥ cy.cards.length); omega),
    Nat.min_eq_right (by omega)]

/-- The wrap from the pass end at any step (the wrap condition is at
the position, not the step size). -/
theorem Cycle.dealOnce_wrap_any {cy : Cycle Card} (s : Nat)
    (hn : cy.cards.length ≤ cy.cursor) :
    cy.dealOnce s = ⟨cy.cards, 0⟩ := by
  simp only [Cycle.dealOnce]
  rw [ite_eq_left (by show cy.cursor ≥ cy.cards.length; omega)]

/-- Consume the waste top `k` times (the LIFO iteration inside the
drawn batches). -/
def Cycle.iterRemoveTop : Nat → Cycle Card → Cycle Card
  | 0, cy => cy
  | k + 1, cy => iterRemoveTop k (cy.removeAt (cy.cursor - 1))

private theorem take_removeIdx : ∀ {L : List Card} {i j : Nat}, j ≤ i →
    (Cycle.removeIdx L i).take j = L.take j := by
  intro L
  induction L with
  | nil => intro i j _; simp
  | cons x t ih =>
      intro i j hj
      match i, j with
      | 0, 0 => simp
      | 0, (j + 1) => omega
      | (i + 1), 0 => simp
      | (i + 1), (j + 1) =>
          show x :: (Cycle.removeIdx t i).take j = x :: t.take j
          rw [ih (by omega)]

private theorem drop_removeIdx : ∀ {L : List Card} {i j : Nat}, i ≤ j →
    (Cycle.removeIdx L i).drop j = L.drop (j + 1) := by
  intro L
  induction L with
  | nil => intro i j _; simp
  | cons x t ih =>
      intro i j hij
      match i, j with
      | 0, 0 =>
          show t.drop 0 = (x :: t).drop 1
          simp
      | 0, (j + 1) =>
          show t.drop (j + 1) = (x :: t).drop (j + 2)
          simp
      | (i + 1), 0 => omega
      | (i + 1), (j + 1) =>
          show (Cycle.removeIdx t i).drop j = t.drop (j + 1)
          exact ih (by omega)

/-- **The batch-reversal arithmetic** (standalone list lemma): the
drawn batch's cards are consumed top-first — the LIFO inside every
drawn batch of the offset decomposition; after `k` waste-top
consumptions from cursor `j + k` the cycle is the pass body prefix-cut
at `j`, with everything drawn past it spliced out IN REVERSE deal
order (the take keeps the prefix intact, the drop skips past the
removed batch). -/
theorem Cycle.iterRemoveTop_spec : ∀ (k : Nat) (L : List Card) (j : Nat),
    j + k ≤ L.length →
    Cycle.iterRemoveTop k ⟨L, j + k⟩
      = ⟨L.take j ++ L.drop (j + k), j⟩ := by
  intro k
  induction k with
  | zero =>
      intro L j _
      show (⟨L, j + 0⟩ : Cycle Card) = ⟨L.take j ++ L.drop (j + 0), j⟩
      rw [Cycle.mk.injEq]
      exact And.intro (List.take_append_drop j L).symm rfl
  | succ k ih =>
      intro L j hlt
      have hstep : Cycle.iterRemoveTop (k + 1) ⟨L, j + k + 1⟩
          = Cycle.iterRemoveTop k
              (Cycle.removeAt (j + k + 1 - 1) (⟨L, j + k + 1⟩ : Cycle Card)) := rfl
      have hrem : Cycle.removeAt (j + k + 1 - 1) (⟨L, j + k + 1⟩ : Cycle Card)
          = ⟨Cycle.removeIdx L (j + k), j + k⟩ := by
        rw [show j + k + 1 - 1 = ((j + k) + 1) - 1 from rfl]
        exact Cycle.removeAt_of_top rfl
      rw [show j + (k + 1) = (j + k) + 1 from rfl]
      rw [hstep, hrem]
      rw [ih (Cycle.removeIdx L (j + k)) j (by
        have hlen := Cycle.removeIdx_length L (j + k) (by omega)
        omega)]
      rw [Cycle.mk.injEq]
      have h1 := take_removeIdx (L := L) (i := j + k) (j := j) (Nat.le_add_right j k)
      have h2 := drop_removeIdx (L := L) (i := j + k) (j := j + k) (Nat.le_refl _)
      rw [h1, h2]
      exact And.intro rfl rfl



end Construction




