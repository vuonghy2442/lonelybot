import Orig.Fate

/-!
# The original game — the draw's phase line

Every draw deals cards from the stock's front onto the waste's top, and
when the stock runs dry the *next* draw recycles the waste into the
stock (reversed) and deals from there.  Two regimes fall out of that
mechanic:

* aligned positions (`inPhase`): the stock is empty ("at the end"), or
  the waste holds a whole number of deals, so the cycle passes through
  a clean phase boundary;
* offset positions: cards remain in the stock *and* the waste sits
  strictly inside a deal (`waste.length % drawStep ≠ 0`).

The chapter's theorem, `draw_irreversible_offset`: **a draw made at an
offset position is a commitment in the strongest sense** — no legal
play whatsoever returns to the position.  The argument runs on
`cycleCount` (cards outside the foundations) and the invariance of the
offset residue along the draw cycle:

1. `cycleCount` never rises; each `wasteTo*` move *strictly* drops it,
   while a draw conserves it.  A play returning to the origin hence
   cannot contain any `wasteTo*` move (it would have to drop the count
   and build it back up).
2. The remaining moves leave `(stock, waste, drawStep)` exactly as
   they were (`tabToFound`, `foundToTab`, `tabToTab`) or advance it
   along the draw cycle (`draw`), so the whole returning play carries
   one state-level invariant: every state on it either has strictly
   fewer stock cards than the origin had (the first stock pass, whose
   length is never re-attained), or is phase-aligned (any state at or
   past a recycle draws `inPhase = true` forever after).
3. The invariant holds at the committed successor `s₁` (its stock is
   strictly shorter), so it holds at the play's end — which is `st`
   itself.  But at `st` the invariant reads "strictly fewer stock
   cards than itself had" (absurd) or "`inPhase st = true`"
   (contradicting the offset hypotheses).

The residue algebra is uniform in `drawStep`: for `drawStep = 1` the
offset hypothesis is vacuous and the theorem specializes with no case
split.  A `drawStep = 0` position, however, makes every draw a no-op —
`drawStep_zero_reversible` below witnesses that some positivity
assumption is unavoidable, hence the `0 < st.drawStep` hypothesis on
the main theorem.
-/

/-! ## Small helpers -/


/-- A non-`none` option carries a value. -/
private theorem option_some_of_ne_none {α : Type} {o : Option α} (h : o ≠ none) :
    ∃ v, o = some v := by
  cases o with
  | none => exact absurd rfl h
  | some v => exact ⟨v, rfl⟩

/-- Every `Bool` is `true` or `false` (case analysis that never has to
case on the term producing it). -/
private theorem bool_dich (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

/-! ## The phase predicate -/

/-- `true` exactly at the phase boundaries of the draw cycle: no cards
remain in the stock ("at the end"), or the waste holds a whole number
of deals so the next recycle would begin cleanly. -/
def inPhase (st : State) : Bool :=
  match st.stock with
  | [] => true
  | _ => decide (st.waste.length % st.drawStep = 0)

/-- With cards left in the stock, `inPhase` is literally the decide on
the waste residue. -/
theorem inPhase_eq_decide_of_cons {st : State} {c : Card} {t : List Card}
    (hcon : st.stock = c :: t) :
    inPhase st = decide (st.waste.length % st.drawStep = 0) := by
  simp only [inPhase, hcon]

/-- `inPhase` depends only on the stock, the waste, and the draw step. -/
theorem inPhase_congr {x y : State} (h1 : x.stock = y.stock)
    (h2 : x.waste = y.waste) (h3 : x.drawStep = y.drawStep) :
    inPhase x = inPhase y := by
  simp only [inPhase, h1, h2, h3]

/-- No stock cards means aligned: the cycle sits at its end. -/
theorem inPhase_eq_true_of_nil {st : State} (hnil : st.stock = []) :
    inPhase st = true := by
  simp only [inPhase, hnil]

/-- `inPhase = false` is exactly the offset condition: cards remain in
the stock *and* the waste sits strictly inside a deal. -/
theorem inPhase_eq_false_iff {st : State} :
    inPhase st = false ↔ st.stock ≠ [] ∧ st.waste.length % st.drawStep ≠ 0 := by
  constructor
  · intro h
    by_cases hst : st.stock = []
    · rw [inPhase_eq_true_of_nil hst] at h
      exact absurd h (by simp)
    · obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hst
      rw [inPhase_eq_decide_of_cons hcon] at h
      exact ⟨hst, of_decide_eq_false h⟩
  · rintro ⟨hst, hres⟩
    obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hst
    rw [inPhase_eq_decide_of_cons hcon, decide_eq_false hres]

/-- **The offset residue lemma.**  At a position with cards left in the
stock that is not phase-aligned, the waste sits strictly inside a deal:
"offset but not at the end" is exactly `¬ inPhase`. -/
theorem offset_not_inPhase {st : State} (hs : st.stock ≠ [])
    (h : ¬ (inPhase st = true)) : st.waste.length % st.drawStep ≠ 0 := by
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  intro hres
  apply h
  rw [inPhase_eq_decide_of_cons hcon, decide_eq_true hres]

/-- The converse shape: cards in the stock and a waste strictly inside
a deal force the position off the phase line. -/
theorem not_inPhase_of_offset {st : State} (hs : st.stock ≠ [])
    (hres : st.waste.length % st.drawStep ≠ 0) : ¬ (inPhase st = true) := by
  intro h
  have hf := inPhase_eq_false_iff.2 ⟨hs, hres⟩
  rw [hf] at h
  exact absurd h (by simp)

/-! ## The cycle count -/

/-- How many cards sit outside the foundations: the stock and the waste
together.  A draw merely moves cards *within* this pool (recycling the
waste reverses it but keeps it), while every move that builds onto the
foundations drains one card out of it. -/
private def cycleCount (st : State) : Nat := st.stock.length + st.waste.length

/-- Lengths of the `dealUpTo` split: the dealt part has `min k |l|`
cards, and the two parts recombine to `l`. -/
private theorem dealUpTo_lens (k : Nat) : ∀ (l : List Card),
    (State.dealUpTo k l).1.length = min k l.length ∧
    (State.dealUpTo k l).1.length + (State.dealUpTo k l).2.length = l.length := by
  induction k with
  | zero =>
      intro l
      refine ⟨?_, ?_⟩
      · exact (Nat.min_eq_left (Nat.zero_le l.length)).symm
      · exact Nat.zero_add l.length
  | succ k ih =>
      intro l
      cases l with
      | nil =>
          refine ⟨?_, ?_⟩
          · exact (Nat.min_eq_right (Nat.zero_le (k + 1))).symm
          · rfl
      | cons c cs =>
          obtain ⟨h1, h2⟩ := ih cs
          have hs1 : (State.dealUpTo (k + 1) (c :: cs)).1.length
              = (State.dealUpTo k cs).1.length + 1 := rfl
          have hs2 : (State.dealUpTo (k + 1) (c :: cs)).2.length
              = (State.dealUpTo k cs).2.length := rfl
          have hlen : List.length (c :: cs) = List.length cs + 1 := rfl
          rw [hs1, hs2, hlen]
          rcases Nat.lt_or_ge k cs.length with hlt | hge
          · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
            refine ⟨?_, ?_⟩
            · rw [h1, Nat.min_eq_left (Nat.succ_le_succ (Nat.le_of_lt hlt))]
            · omega
          · rw [Nat.min_eq_right hge] at h1
            refine ⟨?_, ?_⟩
            · rw [h1, Nat.min_eq_right (Nat.succ_le_succ hge)]
            · omega

/-- A full deal: when the list has no more than `k` cards, every card
is dealt and nothing remains. -/
private theorem dealUpTo_all (k : Nat) : ∀ (l : List Card), l.length ≤ k →
    State.dealUpTo k l = (l, ([] : List Card)) := by
  induction k with
  | zero =>
      intro l hlen
      have hnil : l = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hnil]
      rfl
  | succ k ih =>
      intro l hlen
      cases l with
      | nil => rfl
      | cons c cs =>
          have hcc : List.length (c :: cs) = List.length cs + 1 := List.length_cons
          have hcs : List.length cs ≤ k := by omega
          have hrs := ih cs hcs
          show State.dealUpTo (k+1) (c :: cs) = _
          rw [State.dealUpTo, hrs]


/-- Recycling conserves the cycle count: reversing and swapping the two
pools keeps their total. -/
private theorem recycle_cycleCount (st : State) :
    cycleCount (State.recycle st) = cycleCount st := by
  by_cases hst : st.stock = []
  · by_cases hw : st.waste = []
    · rw [recycle_allEmpty st hst hw]
    · rw [recycle_nil st hst hw]
      simp only [cycleCount, List.length_reverse, List.length_nil]
      rw [hst, List.length_nil]
      omega
  · rw [recycle_keep st hst]


/-- A full deal: when the stock has no more cards than one deal, all of
the stock is dealt onto the waste and nothing remains. -/
private theorem dealStock_full {st : State} (hs : st.stock ≠ [])
    (hsize : st.stock.length ≤ st.drawStep) :
    State.dealStock st = some
      { st with stock := ([] : List Card), waste := st.stock.reverse ++ st.waste } := by
  rw [dealStock_eq_of_ne_nil st hs, dealUpTo_all st.drawStep st.stock hsize]


/-- A draw conserves the cycle count: cards only move between the stock
and the waste (reversing on the way). -/
private theorem draw_cycleCount {x y : State} (hsuc : x.stepDraw = some y) :
    cycleCount y = cycleCount x := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hrc : r.stock.length + r.waste.length = x.stock.length + x.waste.length := by
    rw [← hrec]
    exact recycle_cycleCount x
  have hyW : y.waste = (State.dealUpTo r.drawStep r.stock).1.reverse ++ r.waste := by
    rw [hy]
  have hyS : y.stock = (State.dealUpTo r.drawStep r.stock).2 := by
    rw [hy]
  obtain ⟨_, h2⟩ := dealUpTo_lens r.drawStep r.stock
  have hcx : cycleCount x = x.stock.length + x.waste.length := rfl
  have hcy : cycleCount y = r.stock.length + r.waste.length := by
    show y.stock.length + y.waste.length = r.stock.length + r.waste.length
    rw [hyS, hyW, List.length_append, List.length_reverse]
    omega
  omega

/-- A drawn-from stock strictly shrinks: the deal takes at least one
card (`drawStep ≥ 1`, stock nonempty). -/
private theorem draw_dropStock {x y : State} (hsuc : x.stepDraw = some y)
    (hd : 0 < x.drawStep) (hne : x.stock ≠ []) : y.stock.length < x.stock.length := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hxr : x = r := ((recycle_keep x hne).symm).trans hrec
  rw [← hxr] at hy
  have hyS : y.stock = (State.dealUpTo x.drawStep x.stock).2 := by
    rw [hy]
  obtain ⟨h1, h2⟩ := dealUpTo_lens x.drawStep x.stock
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hne
  have hsl : x.stock.length = 1 + t.length := by
    show (x.stock).length = 1 + t.length
    rw [hcon, List.length_cons]
    omega
  rcases Nat.lt_or_ge x.drawStep x.stock.length with hlt | hge
  · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
    rw [hyS]
    omega
  · rw [Nat.min_eq_right hge] at h1
    rw [hyS]
    omega

/-- The draw step is permanent: no move in the model re-labels the
draw width. -/
private theorem recycle_drawStep (st : State) :
    (State.recycle st).drawStep = st.drawStep := by
  by_cases hst : st.stock = []
  · by_cases hw : st.waste = []
    · rw [recycle_allEmpty st hst hw]
    · rw [recycle_nil st hst hw]
  · rw [recycle_keep st hst]

/-- Every state along a draw has the same draw step as its parent. -/
private theorem draw_drawStep {x y : State} (hsuc : x.stepDraw = some y) :
    y.drawStep = x.drawStep := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hyD : y.drawStep = r.drawStep := by
    rw [hy]
  rw [hyD, ← hrec]
  exact recycle_drawStep x

/-- **The first half of the trap.**  A draw fired at the end of the
stock (a recycle) lands phase-aligned: the recycled deal takes exactly
`drawStep` cards (all that remain, if fewer), so the new waste is a
whole number of deals — or the stock is empty again. -/
private theorem draw_nil_inPhase {x y : State} (hst : x.stock = [])
    (hsuc : x.stepDraw = some y) : inPhase y = true := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  by_cases hw : x.waste = []
  · exfalso
    have hrx : r = x := hrec.symm.trans (recycle_allEmpty x hst hw)
    rw [hrx] at hrne
    rw [hst] at hrne
    exact absurd rfl hrne
  · have hrfl : r = { x with stock := x.waste.reverse, waste := [] } :=
      hrec.symm.trans (recycle_nil x hst hw)
    rw [hrfl] at hy
    have hyS : y.stock = (State.dealUpTo x.drawStep x.waste.reverse).2 := by
      rw [hy]
    have hyW : y.waste =
        (State.dealUpTo x.drawStep x.waste.reverse).1.reverse ++ ([] : List Card) := by
      rw [hy]
    have hwr : (x.waste.reverse).length = x.waste.length := List.length_reverse
    obtain ⟨h1, h2⟩ := dealUpTo_lens x.drawStep x.waste.reverse
    rcases Nat.lt_or_ge x.drawStep x.waste.length with hlt | hge
    · rw [hwr, Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
      have hyne : y.stock ≠ [] := by
        intro hc0
        have hc2 : (State.dealUpTo x.drawStep x.waste.reverse).2 = ([] : List Card) :=
          hyS.symm.trans hc0
        rw [hc2, List.length_nil] at h2
        omega
      obtain ⟨c', t', hys⟩ := list_cons_of_ne_nil hyne
      have hdec : inPhase y = decide (y.waste.length % y.drawStep = 0) := by
        simp only [inPhase, hys]
      have hywl : y.waste.length = x.drawStep := by
        rw [hyW, List.length_append, List.length_reverse, List.length_nil, h1]
        omega
      have hyD : y.drawStep = x.drawStep := by
        rw [hy]
      rw [hdec, hywl, hyD]
      exact decide_eq_true (Nat.mod_self x.drawStep)
    · rw [hwr, Nat.min_eq_right hge] at h1
      have hyv : y.stock = [] := by
        have hy0 : y.stock.length = 0 := by
          rw [hyS]
          omega
        exact List.length_eq_zero_iff.mp hy0
      exact inPhase_eq_true_of_nil hyv

/-- **The second half of the trap.**  Alignment is drawn into: a draw
from a phase-aligned position stays phase-aligned. -/
private theorem draw_keeps_inPhase {x y : State} (hsuc : x.stepDraw = some y)
    (hin : inPhase x = true) : inPhase y = true := by
  by_cases hst : x.stock = []
  · exact draw_nil_inPhase hst hsuc
  · obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
    have hxr : x = r := ((recycle_keep x hst).symm).trans hrec
    rw [← hxr] at hy
    obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hst
    have hres : x.waste.length % x.drawStep = 0 := by
      rw [inPhase_eq_decide_of_cons hcon] at hin
      exact of_decide_eq_true hin
    have hyS : y.stock = (State.dealUpTo x.drawStep x.stock).2 := by
      rw [hy]
    have hyW : y.waste = (State.dealUpTo x.drawStep x.stock).1.reverse ++ x.waste := by
      rw [hy]
    have hyD : y.drawStep = x.drawStep := by
      rw [hy]
    obtain ⟨h1, h2⟩ := dealUpTo_lens x.drawStep x.stock
    have hsl : x.stock.length = 1 + t.length := by
      show (x.stock).length = 1 + t.length
      rw [hcon, List.length_cons]
      omega
    rcases Nat.lt_or_ge x.drawStep x.stock.length with hlt | hge
    · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
      have hyne : y.stock ≠ [] := by
        intro hc0
        have hc2 : (State.dealUpTo x.drawStep x.stock).2 = ([] : List Card) :=
          hyS.symm.trans hc0
        rw [hc2, List.length_nil] at h2
        omega
      obtain ⟨c', t', hys⟩ := list_cons_of_ne_nil hyne
      have hdec : inPhase y = decide (y.waste.length % y.drawStep = 0) := by
        simp only [inPhase, hys]
      have hywl : y.waste.length = x.drawStep + x.waste.length := by
        rw [hyW, List.length_append, List.length_reverse, h1]
      rw [hdec, hywl, hyD, Nat.add_mod_left]
      try exact decide_eq_true hres
    · rw [Nat.min_eq_right hge] at h1
      have hyv : y.stock = [] := by
        have hy0 : y.stock.length = 0 := by
          rw [hyS]
          omega
        exact List.length_eq_zero_iff.mp hy0
      exact inPhase_eq_true_of_nil hyv

/-! ## The move table -/

/-- The two moves that spend a waste card. -/
private def isWasteMove (m : Move) : Bool :=
  match m with
  | .wasteToFound _ => true
  | .wasteToTab _ _ => true
  | _ => false

/-- Placing a card on the tableau never touches the stock, the waste,
or the draw step. -/
private theorem putCard_zone_keep (x : State) (c : Card) (b : Base) :
    (x.putCard c b).stock = x.stock ∧ (x.putCard c b).waste = x.waste ∧
    (x.putCard c b).drawStep = x.drawStep := by
  cases b with
  | inl a => exact ⟨rfl, rfl, rfl⟩
  | inr z =>
      simp only [State.putCard]
      split <;> exact ⟨rfl, rfl, rfl⟩

/-- Placing a run on the tableau never touches the stock, the waste, or
the draw step. -/
private theorem putRun_keep (x : State) (run : List Card) (b : Base) :
    (x.putRun run b).stock = x.stock ∧ (x.putRun run b).waste = x.waste ∧
    (x.putRun run b).drawStep = x.drawStep := by
  cases b with
  | inl a => exact ⟨rfl, rfl, rfl⟩
  | inr z =>
      simp only [State.putRun]
      split <;> exact ⟨rfl, rfl, rfl⟩

/-- Building the waste top onto its foundation spends exactly one
cycle-count unit. -/
private theorem cycleCount_lt_wasteToFound {x y : State} {c : Card}
    (h : State.step x (.wasteToFound c) = some y) :
    cycleCount y < cycleCount x := by
  simp only [State.step] at h
  split at h
  · by_cases hw : x.waste = []
    · rw [hw] at h
      simp at h
    · obtain ⟨w', ws, hcon⟩ := list_cons_of_ne_nil hw
      rw [hcon] at h
      simp only [Option.some.injEq] at h
      subst h
      show x.stock.length + ws.length < x.stock.length + x.waste.length
      rw [hcon, List.length_cons]
      omega
  · simp at h

/-- Building the waste top onto the tableau spends exactly one
cycle-count unit. -/
private theorem cycleCount_lt_wasteToTab {x y : State} {c : Card} {b : Base}
    (h : State.step x (.wasteToTab c b) = some y) :
    cycleCount y < cycleCount x := by
  simp only [State.step] at h
  split at h
  · by_cases hw : x.waste = []
    · rw [hw] at h
      simp at h
    · obtain ⟨w', ws, hcon⟩ := list_cons_of_ne_nil hw
      rw [hcon] at h
      simp only [Option.some.injEq] at h
      subst h
      have hpc := putCard_zone_keep x c b
      show (x.putCard c b).stock.length + ws.length < x.stock.length + x.waste.length
      rw [hpc.1, hcon, List.length_cons]
      omega
  · simp at h

/-- A pile top onto its foundation leaves the stock, the waste, and
the draw step verbatim. -/
private theorem tabToFound_fixed {x y : State} {c : Card}
    (h : State.step x (.tabToFound c) = some y) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  simp only [State.step] at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
  · simp at h

/-- A foundation top back onto the tableau leaves the stock, the waste,
and the draw step verbatim. -/
private theorem foundToTab_fixed {x y : State} {c : Card} {b : Base}
    (h : State.step x (.foundToTab c b) = some y) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  simp only [State.step] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨(putCard_zone_keep _ c b).1, (putCard_zone_keep _ c b).2.1,
        (putCard_zone_keep _ c b).2.2⟩
    · simp at h
  · simp at h

/-- A run between piles leaves the stock, the waste, and the draw step
verbatim. -/
private theorem tabToTab_fixed {x y : State} {c : Card} {b : Base}
    (h : State.step x (.tabToTab c b) = some y) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  simp only [State.step] at h
  by_cases hph : x.pileHolding c = none
  · rw [hph] at h
    simp at h
  · obtain ⟨a, hph'⟩ := option_some_of_ne_none hph
    simp only [hph'] at h
    split at h
    · by_cases hfc : fromCard c (x.piles a).faceUp = []
      · rw [hfc] at h
        simp at h
      · obtain ⟨rhd, rtl, hfc'⟩ := list_cons_of_ne_nil hfc
        rw [hfc'] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨(putRun_keep _ _ _).1, (putRun_keep _ _ _).2.1,
          (putRun_keep _ _ _).2.2⟩
    · simp at h

/-- **The per-move step table.**  Every legal move leaves the cycle
count weakly down. -/
private theorem step_cycleCount_le {x y : State} : ∀ m : Move,
    State.step x m = some y → cycleCount y ≤ cycleCount x := by
  intro m h
  cases m with
  | draw => exact Nat.le_of_eq (draw_cycleCount h)
  | wasteToFound c =>
      have hlt := cycleCount_lt_wasteToFound h
      omega
  | wasteToTab c b =>
      have hlt := cycleCount_lt_wasteToTab h
      omega
  | tabToFound c =>
      obtain ⟨h1, h2, _⟩ := tabToFound_fixed h
      exact Nat.le_of_eq (by simp only [cycleCount, h1, h2])
  | foundToTab c b =>
      obtain ⟨h1, h2, _⟩ := foundToTab_fixed h
      exact Nat.le_of_eq (by simp only [cycleCount, h1, h2])
  | tabToTab c b =>
      obtain ⟨h1, h2, _⟩ := tabToTab_fixed h
      exact Nat.le_of_eq (by simp only [cycleCount, h1, h2])

/-! ## Plays -/

/-- The play lift of the step table: no play raises the cycle count. -/
private theorem run_cycleCount_le : ∀ {play : List Move} {x w : State},
    x.run play = some w → cycleCount w ≤ cycleCount x := by
  intro play
  induction play with
  | nil =>
      intro x w hrun
      have hx : some x = some w := hrun
      injection hx with h
      rw [← h]
      exact Nat.le_refl _
  | cons m rest ih =>
      intro x w hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      have h1 := ih hrs
      have h2 := step_cycleCount_le m hm
      omega

/-- A play that spends a waste card strictly drops the cycle count. -/
private theorem run_cycleCount_lt : ∀ {play : List Move} {x w : State},
    x.run play = some w → (∃ m ∈ play, isWasteMove m = true) →
    cycleCount w < cycleCount x := by
  intro play
  induction play with
  | nil =>
      intro x w _ hmem
      obtain ⟨m, hm, _⟩ := hmem
      exact absurd hm (by simp)
  | cons m rest ih =>
      intro x w hrun hmem
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      by_cases hmv : isWasteMove m = true
      · have hlt : cycleCount s₁ < cycleCount x := by
          cases m with
          | draw => simp [isWasteMove] at hmv
          | wasteToFound c => exact cycleCount_lt_wasteToFound hm
          | wasteToTab c b => exact cycleCount_lt_wasteToTab hm
          | tabToFound c => simp [isWasteMove] at hmv
          | foundToTab c b => simp [isWasteMove] at hmv
          | tabToTab c b => simp [isWasteMove] at hmv
        have hle := run_cycleCount_le hrs
        omega
      · obtain ⟨m', hm', hmis⟩ := hmem
        rcases List.mem_cons.1 hm' with heq | hmem2
        · exact absurd (heq ▸ hmis) hmv
        · have hlt := ih hrs ⟨m', hmem2, hmis⟩
          have hle := step_cycleCount_le m hm
          omega

/-! ## The commitment invariant -/

/-- A list appended to a nonempty list is nonempty. -/
private theorem append_ne_nil_right (A : List Card) {B : List Card}
    (h : B ≠ []) : A ++ B ≠ [] := by
  obtain ⟨b, bs, hb⟩ := list_cons_of_ne_nil h
  intro hc
  subst hb
  cases A <;> simp_all

/-- **The pristine-step invariant.**  In a `wasteTo*`-free play at a
positive draw step, a state with a nonempty waste is never followed by
one with an empty waste: the three tableau/foundation moves quote the
waste field, and every draw deals at least one card onto it. -/
private theorem step_wasteNe_preserved {x y : State} (hd : 0 < x.drawStep)
    {m : Move} (hgood : isWasteMove m ≠ true) (hs : State.step x m = some y)
    (hw : x.waste ≠ []) : y.waste ≠ [] ∧ y.drawStep = x.drawStep := by
  cases m with
  | draw =>
      have hsuc : x.stepDraw = some y := hs
      refine ⟨?_, draw_drawStep hsuc⟩
      by_cases hst : x.stock = []
      · obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
        have hrfl : r = { x with stock := x.waste.reverse, waste := [] } :=
          hrec.symm.trans (recycle_nil x hst hw)
        rw [hrfl] at hy
        have hyW : y.waste =
            (State.dealUpTo x.drawStep x.waste.reverse).1.reverse ++ ([] : List Card) := by
          rw [hy]
        obtain ⟨h1, _⟩ := dealUpTo_lens x.drawStep x.waste.reverse
        have hwr : (x.waste.reverse).length = x.waste.length := List.length_reverse
        have hwlen : 1 ≤ x.waste.length := by
          obtain ⟨c0, t0, hwcon⟩ := list_cons_of_ne_nil hw
          rw [hwcon, List.length_cons]
          omega
        rcases Nat.lt_or_ge x.drawStep x.waste.length with hlt | hge
        · rw [hwr, Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
          intro hc0
          rw [hyW] at hc0
          have hlen := congrArg List.length hc0
          rw [List.length_append, List.length_reverse, List.length_nil] at hlen
          omega
        · rw [hwr, Nat.min_eq_right hge] at h1
          intro hc0
          rw [hyW] at hc0
          have hlen := congrArg List.length hc0
          rw [List.length_append, List.length_reverse, List.length_nil] at hlen
          omega
      · obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
        have hxr : x = r := ((recycle_keep x hst).symm).trans hrec
        rw [← hxr] at hy
        have hyW : y.waste = (State.dealUpTo x.drawStep x.stock).1.reverse ++ x.waste := by
          rw [hy]
        rw [hyW]
        exact append_ne_nil_right _ hw
  | wasteToFound c => simp [isWasteMove] at hgood
  | wasteToTab c b => simp [isWasteMove] at hgood
  | tabToFound c =>
      obtain ⟨_, h2, h3⟩ := tabToFound_fixed hs
      refine ⟨?_, h3⟩
      rw [h2]
      exact hw
  | foundToTab c b =>
      obtain ⟨_, h2, h3⟩ := foundToTab_fixed hs
      refine ⟨?_, h3⟩
      rw [h2]
      exact hw
  | tabToTab c b =>
      obtain ⟨_, h2, h3⟩ := tabToTab_fixed hs
      refine ⟨?_, h3⟩
      rw [h2]
      exact hw

/-- The pristine run lift: a `wasteTo*`-free play from a positive-draw
state with nonempty waste ends with nonempty waste (and the same draw
step throughout). -/
private theorem run_wasteNe (st : State) : ∀ {play : List Move} {x w : State},
    0 < st.drawStep → (∀ m ∈ play, isWasteMove m ≠ true) →
    x.drawStep = st.drawStep → x.waste ≠ [] →
    x.run play = some w → w.waste ≠ [] ∧ w.drawStep = st.drawStep := by
  intro play
  induction play with
  | nil =>
      intro x w _hd _hgood hsd hw hrun
      have hx : some x = some w := hrun
      injection hx with h
      rw [← h]
      exact ⟨hw, hsd⟩
  | cons m rest ih =>
      intro x w hd hgood hsd hw hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      have hmne : isWasteMove m ≠ true := hgood m (by simp)
      have hdx : 0 < x.drawStep := by
        rw [hsd]
        exact hd
      obtain ⟨hw', hsd'⟩ := step_wasteNe_preserved hdx hmne hm hw
      exact ih hd (fun m' hm' => hgood m' (by simp [hm'])) (hsd'.trans hsd) hw' hrs

/-- The committed successor of a pristine draw: the first deal drops at
least one card onto the (previously empty) waste. -/
private theorem draw_pristine_s1 {st s₁ : State} (hd : 0 < st.drawStep)
    (hs : st.stock ≠ []) (hw : st.waste = []) (hsuc : st.stepDraw = some s₁) :
    s₁.waste ≠ [] ∧ s₁.drawStep = st.drawStep := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hxr : st = r := ((recycle_keep st hs).symm).trans hrec
  rw [← hxr] at hy
  have hyW : s₁.waste =
      (State.dealUpTo st.drawStep st.stock).1.reverse ++ st.waste := by
    rw [hy]
  refine ⟨?_, draw_drawStep hsuc⟩
  rw [hyW, hw]
  obtain ⟨h1, _⟩ := dealUpTo_lens st.drawStep st.stock
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  have hsl : st.stock.length = 1 + t.length := by
    show (st.stock).length = 1 + t.length
    rw [hcon, List.length_cons]
    omega
  rcases Nat.lt_or_ge st.drawStep st.stock.length with hlt | hge
  · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at h1
    intro hc0
    have hlen := congrArg List.length hc0
    rw [List.length_append, List.length_reverse, List.length_nil] at hlen
    omega
  · rw [Nat.min_eq_right hge] at h1
    intro hc0
    have hlen := congrArg List.length hc0
    rw [List.length_append, List.length_reverse, List.length_nil] at hlen
    omega

/-- The invariant carried along a returning play, relative to the
commitment origin `x₀`: a position either holds strictly fewer stock
cards than the origin had (we are inside the first stock pass — its
length is never re-attained), or the position is phase-aligned (the
post-recycle regime).  Either way the position cannot be the origin
itself, which is neither. -/
private def beforeOriginOrAligned (x₀ x : State) : Prop :=
  x.stock.length < x₀.stock.length ∨ inPhase x = true

/-- One step of a `wasteTo*`-free play preserves the commitment
invariant and the draw step. -/
private theorem step_inv_preserved {x₀ x y : State} (hd : 0 < x₀.drawStep)
    {m : Move} (hsd : x.drawStep = x₀.drawStep)
    (hgood : isWasteMove m ≠ true) (hs : State.step x m = some y)
    (hinv : beforeOriginOrAligned x₀ x) :
    beforeOriginOrAligned x₀ y ∧ y.drawStep = x.drawStep := by
  have hdx : 0 < x.drawStep := by
    rw [hsd]
    exact hd
  cases m with
  | draw =>
      have hsuc : x.stepDraw = some y := hs
      refine ⟨?_, draw_drawStep hsuc⟩
      rcases hinv with h | h
      · by_cases hst : x.stock = []
        · exact Or.inr (draw_nil_inPhase hst hsuc)
        · exact Or.inl (by
            have := draw_dropStock hsuc hdx hst
            omega)
      · exact Or.inr (draw_keeps_inPhase hsuc h)
  | wasteToFound c => simp [isWasteMove] at hgood
  | wasteToTab c b => simp [isWasteMove] at hgood
  | tabToFound c =>
      obtain ⟨h1, h2, h3⟩ := tabToFound_fixed hs
      refine ⟨?_, h3⟩
      rcases hinv with h | h
      · exact Or.inl (by rw [h1]; exact h)
      · exact Or.inr (by
          have hc := inPhase_congr (x := y) (y := x) h1 h2 h3
          rw [hc]
          exact h)
  | foundToTab c b =>
      obtain ⟨h1, h2, h3⟩ := foundToTab_fixed hs
      refine ⟨?_, h3⟩
      rcases hinv with h | h
      · exact Or.inl (by rw [h1]; exact h)
      · exact Or.inr (by
          have hc := inPhase_congr (x := y) (y := x) h1 h2 h3
          rw [hc]
          exact h)
  | tabToTab c b =>
      obtain ⟨h1, h2, h3⟩ := tabToTab_fixed hs
      refine ⟨?_, h3⟩
      rcases hinv with h | h
      · exact Or.inl (by rw [h1]; exact h)
      · exact Or.inr (by
          have hc := inPhase_congr (x := y) (y := x) h1 h2 h3
          rw [hc]
          exact h)

/-- The play lift: a `wasteTo*`-free play carries the commitment
invariant from its start to its end. -/
private theorem run_inv_preserved : ∀ {play : List Move} {x₀ x w : State},
    0 < x₀.drawStep → x.drawStep = x₀.drawStep →
    (∀ m ∈ play, isWasteMove m ≠ true) →
    beforeOriginOrAligned x₀ x →
    x.run play = some w → beforeOriginOrAligned x₀ w := by
  intro play
  induction play with
  | nil =>
      intro x₀ x w _hd _hsd _hgood hinv hrun
      have hx : some x = some w := hrun
      injection hx with h
      rw [← h]
      exact hinv
  | cons m rest ih =>
      intro x₀ x w hd hsd hgood hinv hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      have hmne : isWasteMove m ≠ true := hgood m (by simp)
      obtain ⟨hinv', hsd'⟩ := step_inv_preserved hd hsd hmne hm hinv
      have hgood' : ∀ m' ∈ rest, isWasteMove m' ≠ true := by
        intro m' hm'
        exact hgood m' (by simp [hm'])
      exact ih hd (hsd'.trans hsd) hgood' hinv' hrs

/-! ## The theorem -/

/-- The zero-width draw, as a computed step: the recycle is theidentity
(no recycle fires) and the deal of zero cards changes nothing. -/
private theorem drawStep_zero_draw {st : State} (hne : st.stock ≠ [])
    (hd : st.drawStep = 0) : State.step st Move.draw = some st := by
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hne
  show st.stepDraw = some st
  rw [State.stepDraw, show State.recycle st = st from recycle_keep st hne,
    dealStock_eq_of_ne_nil st hne, hcon, hd,
    show (State.dealUpTo 0 (c :: t)).1.reverse ++ st.waste = st.waste from rfl,
    show (State.dealUpTo 0 (c :: t)).2 = (c :: t) from rfl,
    ← hcon, ← hd]

/-- The pass-end full-redeal, as a computed step: the recycle reverses
the waste into the stock and the full deal deals it straight back. -/
private theorem selfRecycle_draw {st : State} (hstock : st.stock = [])
    (hw : st.waste ≠ []) (hsize : st.waste.length ≤ st.drawStep) :
    State.step st Move.draw = some st := by
  show st.stepDraw = some st
  rw [State.stepDraw, recycle_nil st hstock hw]
  have hrne : st.waste.reverse ≠ [] := by
    intro hc
    have hlen := congrArg List.length hc
    rw [List.length_reverse, List.length_nil] at hlen
    obtain ⟨c0, t0, hwcon0⟩ := list_cons_of_ne_nil hw
    have h1 : 1 ≤ st.waste.length := by
      rw [hwcon0, List.length_cons]
      omega
    omega
  have hfull : State.dealStock { st with stock := st.waste.reverse, waste := [] } = some { st with stock := ([] : List Card), waste := (st.waste.reverse).reverse ++ ([] : List Card) } :=
    dealStock_full (st := { st with stock := st.waste.reverse, waste := [] })
      (by
        show st.waste.reverse ≠ []
        exact hrne)
      (by
        show (st.waste.reverse).length ≤ st.drawStep
        rw [List.length_reverse]
        exact hsize)
  rw [hfull, List.reverse_reverse, List.append_nil, ← hstock]

/-- **The zero-width no-op, witness form (primary).**  At `drawStep = 0`
with cards in the stock every draw is the identity, so the empty play
returns; the negative form `drawStep_zero_reversible` follows from this
via `reversibleAt_of_W`. -/
theorem drawStep_zero_reversibleW {st : State} (hne : st.stock ≠ [])
    (hd : st.drawStep = 0) : reversibleAtW st Move.draw :=
  ⟨st, [], drawStep_zero_draw hne hd, rfl⟩

/-- With the draw step set to zero, every draw is the identity — the
positivity hypothesis (`0 < st.drawStep`) on the main theorem is
genuinely necessary.  Witness form: `drawStep_zero_reversibleW`. -/
theorem drawStep_zero_reversible {st : State} (hne : st.stock ≠ [])
    (hd : st.drawStep = 0) : reversibleAt st Move.draw :=
  reversibleAt_of_W (drawStep_zero_reversibleW hne hd)

/-- **Draws at offset positions are commitments.**  At a position with
cards still in the stock whose waste sits strictly inside a deal
(`st.waste.length % st.drawStep ≠ 0`) — and with a positive draw step —
the draw commits: no legal play whatsoever returns to the position.
The offset residue is carried unchanged through the whole first stock
pass, so no state before the first recycle can be the origin; and every
state from the first recycle onward is phase-aligned, which the origin
is not. -/
theorem draw_irreversible_offset {st : State}
    (hd : 0 < st.drawStep)
    (hs : st.stock ≠ [])
    (hoff : st.waste.length % st.drawStep ≠ 0) :
    irreversibleAt st Move.draw := by
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  have hinF : inPhase st = false := by
    rw [inPhase_eq_decide_of_cons hcon, decide_eq_false hoff]
  intro s₁ play hst hrun
  have hsuc : st.stepDraw = some s₁ := hst
  have hnoWaste : ∀ m ∈ play, isWasteMove m ≠ true := by
    intro m hm hc
    have hlt := run_cycleCount_lt hrun ⟨m, hm, hc⟩
    have hcc := draw_cycleCount hsuc
    rw [hcc] at hlt
    omega
  have hsd : s₁.drawStep = st.drawStep := draw_drawStep hsuc
  have hbase : beforeOriginOrAligned st s₁ := Or.inl (draw_dropStock hsuc hd hs)
  have hfinal : beforeOriginOrAligned st st :=
    run_inv_preserved hd hsd hnoWaste hbase hrun
  rcases hfinal with hlt | hph
  · exact absurd hlt (Nat.lt_irrefl _)
  · rw [hinF] at hph
    exact absurd hph (by simp)

/-- **Draws at pristine positions are commitments.**  A draw made with
stock cards present and an *empty* waste also commits: the committed
successor receives dealt cards in its waste, no `wasteTo*`-free play
ever empties a nonempty waste, and a returning play cannot contain
`wasteTo*` moves (they would strictly drop the cycle count). -/
theorem draw_irreversible_pristine {st : State}
    (hd : 0 < st.drawStep) (hs : st.stock ≠ []) (hw : st.waste = []) :
    irreversibleAt st Move.draw := by
  intro s₁ play hstep hrun
  have hsuc : st.stepDraw = some s₁ := hstep
  have hnoWaste : ∀ m ∈ play, isWasteMove m ≠ true := by
    intro m hm hc
    have hlt := run_cycleCount_lt hrun ⟨m, hm, hc⟩
    have hcc := draw_cycleCount hsuc
    rw [hcc] at hlt
    omega
  obtain ⟨hw₁, hsd₁⟩ := draw_pristine_s1 hd hs hw hsuc
  exact (run_wasteNe st hd hnoWaste hsd₁ hw₁ hrun).1 hw

/-- **The irreversible shape.**  Under a positive draw step and a
nonempty stock, a draw commits exactly when the waste is empty
(pristine) or sits strictly inside a deal (offset) — the two
off-the-phase-line regimes. -/
theorem draw_irreversible_of_wasteShape {st : State}
    (hd : 0 < st.drawStep) (hs : st.stock ≠ [])
    (h : st.waste = [] ∨ st.waste.length % st.drawStep ≠ 0) :
    irreversibleAt st Move.draw := by
  rcases h with hpr | hoff
  · exact draw_irreversible_pristine hd hs hpr
  · exact draw_irreversible_offset hd hs hoff

/-- **A constructive reversible base case, witness form (primary).**
At the end of the stock with the whole cycle no bigger than one deal,
the draw is a state-wise no-op, and the empty play returns; the
negative form `draw_reversible_selfRecycle` follows from this via
`reversibleAt_of_W`. -/
theorem draw_reversible_selfRecycleW {st : State} (hstock : st.stock = [])
    (hw : st.waste ≠ []) (hsize : st.waste.length ≤ st.drawStep) :
    reversibleAtW st Move.draw :=
  ⟨st, [], selfRecycle_draw hstock hw hsize, rfl⟩

/-- The negative form of the pass-end full redeal.  Witness form:
`draw_reversible_selfRecycleW`. -/
theorem draw_reversible_selfRecycle {st : State} (hstock : st.stock = [])
    (hw : st.waste ≠ []) (hsize : st.waste.length ≤ st.drawStep) :
    reversibleAt st Move.draw :=
  reversibleAt_of_W (draw_reversible_selfRecycleW hstock hw hsize)

/-! ## Generic ascent bridges -/

/-- **The mono ascent.**  If `Q` is non-decreasing under every single
legal move, then `Q` is non-decreasing along every legal play. -/
theorem mono_run_asc (Q : State → Nat)
    (h : ∀ {s m s'}, State.step s m = some s' → Q s ≤ Q s') :
    ∀ {s play w}, s.run play = some w → Q s ≤ Q w := by
  intro s play
  revert s
  induction play with
  | nil =>
      intro s w hrun
      have hx : some s = some w := hrun
      injection hx with hq
      rw [← hq]
      exact Nat.le_refl _
  | cons m rest ih =>
      intro s w hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      have h1 := h hm
      have h2 := ih hrs
      omega

/-- **The commitment from a rising measure.**  If `Q` never decreases
under a legal move, and the move's committed successor strictly
increases it, then no play ever returns: the returning play would
force `Q st ≤ Q st` back with the strict rise in between. -/
theorem irr_of_asc (Q : State → Nat)
    (h : ∀ {s m s'}, State.step s m = some s' → Q s ≤ Q s')
    {st : State} {m : Move} {s₁ : State}
    (hstep : State.step st m = some s₁) (hrise : Q st < Q s₁) :
    irreversibleAt st m := by
  intro s₁' play hstep' hrun
  rw [hstep'] at hstep
  injection hstep with hq
  subst hq
  have h1 := h hstep'
  have h2 := mono_run_asc Q h hrun
  omega

/-! ## The lex-pair machinery -/

/-- The working order for the measure packaging: pairs of naturals in
the *descending* lexicographic order — the first component never
rises, and at a tied first component the second never rises either.
Stated directly as a `Prop` (the plain binary-relation form needs
fewer helper lemmas than this toolchain's `Prod.Lex`, which is wired
as the well-founded relation product). -/
def lexDesc (p p' : Nat × Nat) : Prop :=
  p'.1 ≤ p.1 ∧ (p'.1 = p.1 → p'.2 ≤ p.2)

/-- Strict descent in the descending lex order: the first component
strictly drops, or holds while the second strictly drops. -/
def lexDescStrict (p p' : Nat × Nat) : Prop :=
  p'.1 < p.1 ∨ (p'.1 = p.1 ∧ p'.2 < p.2)

/-- Reflexivity of the descending lex order. -/
theorem lexDesc_refl (p : Nat × Nat) : lexDesc p p :=
  ⟨Nat.le_refl p.1, fun _ => Nat.le_refl p.2⟩

/-- Transitivity of the descending lex order. -/
theorem lexDesc_trans {p q r : Nat × Nat} (h1 : lexDesc p q) (h2 : lexDesc q r) :
    lexDesc p r := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  refine ⟨Nat.le_trans h2a h1a, fun hE => ?_⟩
  have hq : q.1 = p.1 := by omega
  have hr : r.1 = q.1 := by omega
  exact Nat.le_trans (h2b hr) (h1b hq)

/-- A strict descent cannot be retraced by a weak one: the end of
every returning play. -/
theorem lexDescStrict_contra {p q : Nat × Nat}
    (h1 : lexDescStrict p q) (h2 : lexDesc q p) : False := by
  obtain ⟨h2a, h2b⟩ := h2
  rcases h1 with hlt | ⟨heq, hlt⟩
  · omega
  · have hp2 := h2b heq.symm
    omega

/-- **The lex ascent.**  If `Q` does not ascend (in the descending
order: does not descend) under any single legal move, it does not
along any legal play. -/
theorem mono_run_lex (Q : State → Nat × Nat)
    (h : ∀ {s m s'}, State.step s m = some s' → lexDesc (Q s) (Q s')) :
    ∀ {s play w}, s.run play = some w → lexDesc (Q s) (Q w) := by
  intro s play
  revert s
  induction play with
  | nil =>
      intro s w hrun
      have hx : some s = some w := hrun
      injection hx with hq
      rw [← hq]
      exact lexDesc_refl _
  | cons m rest ih =>
      intro s w hrun
      obtain ⟨s₁, hm, hrs⟩ := State.run_cons hrun
      exact lexDesc_trans (h hm) (ih hrs)

/-- **The commitment from a strictly descending lex measure.** -/
theorem irr_of_lex_desc (Q : State → Nat × Nat)
    (h : ∀ {s m s'}, State.step s m = some s' → lexDesc (Q s) (Q s'))
    {st : State} {m : Move} {s₁ : State}
    (hstep : State.step st m = some s₁) (hstrict : lexDescStrict (Q st) (Q s₁)) :
    irreversibleAt st m := by
  intro s₁' play hstep' hrun
  rw [hstep'] at hstep
  injection hstep with hq
  subst hq
  exact lexDescStrict_contra hstrict (mono_run_lex Q h hrun)

/-- The draw-distance potential against the in-phase attractor: `0` on
phase-aligned positions, otherwise the number of whole deals left
before the stock drains (in ceiling form). -/
def D (st : State) : Nat :=
  if (inPhase st) = true then 0 else (st.stock.length + st.drawStep - 1) / st.drawStep

/-- The measure pair: the cycle count first, the draw distance
second — both components of a position descend along the cycle. -/
def QPair (st : State) : Nat × Nat := (cycleCount st, D st)

/-- One successful draw from a nonempty stock, as four bookkeeping
facts: conservation of the cycle count, permanence of the draw step,
and the exact length accounting of the split (`k = min drawStep |stock|`). -/
private theorem draw_facts {x y : State} (hsuc : x.stepDraw = some y)
    (hne : x.stock ≠ []) :
    cycleCount y = cycleCount x ∧ y.drawStep = x.drawStep ∧
      y.stock.length + min x.drawStep x.stock.length = x.stock.length ∧
      y.waste.length = min x.drawStep x.stock.length + x.waste.length := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold hsuc
  have hxr : x = r := ((recycle_keep x hne).symm).trans hrec
  rw [← hxr] at hy
  have hyS : y.stock = (State.dealUpTo x.drawStep x.stock).2 := by rw [hy]
  have hyW : y.waste = (State.dealUpTo x.drawStep x.stock).1.reverse ++ x.waste := by
    rw [hy]
  obtain ⟨h1, h2⟩ := dealUpTo_lens x.drawStep x.stock
  refine ⟨draw_cycleCount hsuc, draw_drawStep hsuc, ?_, ?_⟩
  · rw [hyS]
    omega
  · rw [hyW, List.length_append, List.length_reverse]
    omega

/-- `D` only reads the stock, the waste, and the draw step. -/
private theorem D_congr {x y : State} (h1 : x.stock = y.stock)
    (h2 : x.waste = y.waste) (h3 : x.drawStep = y.drawStep) : D x = D y := by
  show (if (inPhase x) = true then 0 else
          (x.stock.length + x.drawStep - 1) / x.drawStep) =
       (if (inPhase y) = true then 0 else
          (y.stock.length + y.drawStep - 1) / y.drawStep)
  rw [inPhase_congr h1 h2 h3, h1, h3]

/-- `D` vanishes on phase-aligned positions. -/
theorem D_of_inPhase_true {x : State} (h : inPhase x = true) : D x = 0 := by
  show (if (inPhase x) = true then 0 else _) = 0
  rw [h]
  rfl

/-- `D` opens to its ceiling form on off-line positions. -/
theorem D_of_inPhase_false {x : State} (h : inPhase x = false) :
    D x = (x.stock.length + x.drawStep - 1) / x.drawStep := by
  show (if (inPhase x) = true then 0 else
          (x.stock.length + x.drawStep - 1) / x.drawStep) = _
  rw [h]
  rfl

/-- The measure pair is verbatim under a move that copies the stock,
the waste, and the draw step. -/
private theorem lex_of_fixed {x y : State} (h1 : y.stock = x.stock)
    (h2 : y.waste = x.waste) (h3 : y.drawStep = x.drawStep) :
    lexDesc (QPair x) (QPair y) :=
  ⟨show y.stock.length + y.waste.length ≤ x.stock.length + x.waste.length by
      rw [h1, h2]
      omega,
    fun _ => Nat.le_of_eq (D_congr h1 h2 h3)⟩

/-- **The per-move lex table.**  Every legal move descends the measure
pair `(cycleCount, D)`: tableau and foundation moves change nothing
(the pair is constant), a waste exit strictly drops the first
component, and a draw conserves the first while never raising the
second — no domination arithmetic, the lex order itself carries the
strictness of the first component. -/
private theorem step_lexDesc : ∀ {x y : State} {m : Move},
    State.step x m = some y → lexDesc (QPair x) (QPair y) := by
  intro x y m hs
  cases m with
  | draw =>
      have hsuc : x.stepDraw = some y := hs
      refine ⟨Nat.le_of_eq (draw_cycleCount hsuc), fun _ => ?_⟩
      by_cases hstock : x.stock = []
      · have hDy : D y = 0 := D_of_inPhase_true (draw_nil_inPhase hstock hsuc)
        show D y ≤ D x
        omega
      · obtain ⟨_, hdeq, hslen, hwlen⟩ := draw_facts hsuc hstock
        by_cases hin : inPhase x = true
        · have hDy : D y = 0 := D_of_inPhase_true (draw_keeps_inPhase hsuc hin)
          show D y ≤ D x
          omega
        · rcases bool_dich (inPhase x) with hb | hb
          · exact absurd hb hin
          · obtain ⟨hnx, hres⟩ := inPhase_eq_false_iff.1 hb
            by_cases hdr : y.stock = []
            · have hDy : D y = 0 := D_of_inPhase_true (inPhase_eq_true_of_nil hdr)
              show D y ≤ D x
              omega
            · obtain ⟨c', t', hcon'⟩ := list_cons_of_ne_nil hdr
              have hp' : 1 ≤ y.stock.length := by
                rw [hcon', List.length_cons]
                omega
              have hk : min x.drawStep x.stock.length = x.drawStep := by omega
              have hresy : y.waste.length % x.drawStep = x.waste.length % x.drawStep := by
                rw [show y.waste.length =
                    min x.drawStep x.stock.length + x.waste.length from hwlen,
                  hk, Nat.add_mod_left]
              have hiny : inPhase y = false := by
                rw [inPhase_eq_decide_of_cons hcon']
                refine decide_eq_false (fun hc0 => ?_)
                rw [hdeq, hresy] at hc0
                exact hres hc0
              show D y ≤ D x
              rw [D_of_inPhase_false hiny, D_of_inPhase_false hb,
                show y.drawStep = x.drawStep from hdeq]
              exact Nat.div_le_div_right (show y.stock.length + x.drawStep - 1 ≤
                  x.stock.length + x.drawStep - 1 from by omega)
  | wasteToFound c =>
      have hlt := cycleCount_lt_wasteToFound hs
      refine ⟨?_, fun hE => absurd hE
        (show ¬(cycleCount y = cycleCount x) from by omega)⟩
      show cycleCount y ≤ cycleCount x
      omega
  | wasteToTab c b =>
      have hlt := cycleCount_lt_wasteToTab hs
      refine ⟨?_, fun hE => absurd hE
        (show ¬(cycleCount y = cycleCount x) from by omega)⟩
      show cycleCount y ≤ cycleCount x
      omega
  | tabToFound c =>
      obtain ⟨h1, h2, h3⟩ := tabToFound_fixed hs
      exact lex_of_fixed h1 h2 h3
  | foundToTab c b =>
      obtain ⟨h1, h2, h3⟩ := foundToTab_fixed hs
      exact lex_of_fixed h1 h2 h3
  | tabToTab c b =>
      obtain ⟨h1, h2, h3⟩ := tabToTab_fixed hs
      exact lex_of_fixed h1 h2 h3

/-- **Draws at offset positions are commitments — the measure proof.**
The same theorem as `draw_irreversible_offset`, re-proved through the
`Prod.Lex` descent of `(cycleCount, D)`: the committed draw conserves
the cycle count and strictly drops the draw distance `D` — one more
whole deal of the stock passes — and since no legal play ascends the
measure pair, no play can re-attain the origin's value. -/
theorem draw_irreversible_offset_lex {st : State}
    (hd : 0 < st.drawStep) (hs : st.stock ≠ [])
    (hoff : st.waste.length % st.drawStep ≠ 0) :
    irreversibleAt st Move.draw := by
  obtain ⟨s₁, hsuc⟩ : ∃ s₁, st.stepDraw = some s₁ :=
    ⟨{ st with stock := (State.dealUpTo st.drawStep st.stock).2, waste := (State.dealUpTo st.drawStep st.stock).1.reverse ++ st.waste },
      by
        rw [State.stepDraw, show State.recycle st = st from recycle_keep st hs,
          dealStock_eq_of_ne_nil st hs]⟩
  obtain ⟨_, hdeq, hslen, hwlen⟩ := draw_facts hsuc hs
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  have hp : 1 ≤ st.stock.length := by
    rw [hcon, List.length_cons]
    omega
  have hinF : inPhase st = false := by
    rw [inPhase_eq_decide_of_cons hcon, decide_eq_false hoff]
  have hDst : D st = (st.stock.length - 1) / st.drawStep + 1 := by
    rw [D_of_inPhase_false hinF]
    have hshift : st.stock.length + st.drawStep - 1 =
        (st.stock.length - 1) + st.drawStep := by omega
    rw [hshift, Nat.add_div_right _ hd]
  refine irr_of_lex_desc QPair step_lexDesc hsuc
    (Or.inr ⟨show (QPair s₁).fst = (QPair st).fst from draw_cycleCount hsuc, ?_⟩)
  show D s₁ < D st
  by_cases hdr : s₁.stock = []
  · have hD0 : D s₁ = 0 := D_of_inPhase_true (inPhase_eq_true_of_nil hdr)
    rw [hD0, hDst]
    have hq : 0 ≤ (st.stock.length - 1) / st.drawStep := Nat.zero_le _
    omega
  · obtain ⟨c', t', hcon'⟩ := list_cons_of_ne_nil hdr
    have hp' : 1 ≤ s₁.stock.length := by
      rw [hcon', List.length_cons]
      omega
    have hresy : s₁.waste.length % st.drawStep = st.waste.length % st.drawStep := by
      have hk : min st.drawStep st.stock.length = st.drawStep := by omega
      rw [show s₁.waste.length =
          min st.drawStep st.stock.length + st.waste.length from hwlen,
        hk, Nat.add_mod_left]
    have hiny : inPhase s₁ = false := by
      rw [inPhase_eq_decide_of_cons hcon']
      refine decide_eq_false (fun hc0 => ?_)
      rw [hdeq, hresy] at hc0
      exact hoff hc0
    have hDs₁ : D s₁ = (s₁.stock.length - 1) / st.drawStep + 1 := by
      rw [D_of_inPhase_false hiny,
        show s₁.drawStep = st.drawStep from hdeq]
      have hshift : s₁.stock.length + st.drawStep - 1 =
          (s₁.stock.length - 1) + st.drawStep := by omega
      rw [hshift, Nat.add_div_right _ hd]
    have hchain : st.stock.length - 1 = (s₁.stock.length - 1) + st.drawStep := by omega
    calc D s₁ = (s₁.stock.length - 1) / st.drawStep + 1 := hDs₁
      _ < ((s₁.stock.length - 1) + st.drawStep) / st.drawStep + 1 := by
          rw [Nat.add_div_right _ hd]
          omega
      _ = D st := by rw [hDst, hchain]







/-! ## The orbit scaffolding: the draw at exact depth -/

/-- One plain draw (the stock is nonempty, so no recycle fires): the
head card moves stock-to-waste, list-exact. -/
private theorem plain_draw_shape {x : State} (hne : x.stock ≠ []) :
    x.stepDraw = some
      { x with stock := x.stock.drop x.drawStep,
               waste := (x.stock.take x.drawStep).reverse ++ x.waste } := by
  rw [State.stepDraw, show State.recycle x = x from recycle_keep x hne,
    dealStock_eq_of_ne_nil x hne, dealUpTo_eq_take_drop]

/-- One pass-end draw (the stock is empty and the waste nonempty, so
the recycle fires): the waste becomes the stock reversed, and one clipped
deal moves back onto the waste. -/
private theorem base_draw_shape {x : State} (hstock : x.stock = ([] : List Card))
    (hw : x.waste ≠ []) :
    x.stepDraw = some
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) } := by
  have hrne : x.waste.reverse ≠ [] := by
    intro hc
    have hlen := congrArg List.length hc
    rw [List.length_reverse, List.length_nil] at hlen
    obtain ⟨c0, t0, hwcon0⟩ := list_cons_of_ne_nil hw
    have h1 : 1 ≤ x.waste.length := by
      rw [hwcon0, List.length_cons]; omega
    omega
  rw [State.stepDraw, recycle_nil x hstock hw,
    dealStock_eq_of_ne_nil _ hrne, dealUpTo_eq_take_drop]



/-! ## The in-phase round trip -/

/-- The additive take split: the first `i + j` cards of a deal-ordered
list are the first `i`, then the next `j`.  The workhorse identity
behind every drain and redeal step. -/
private theorem take_drop_add {α : Type} : ∀ (i j : Nat) (l : List α),
    l.take (i + j) = l.take i ++ (l.drop i).take j := by
  intro i
  induction i with
  | zero =>
      intro j l
      simp
  | succ i ih =>
      intro j l
      have hidx : i + 1 + j = i + j + 1 := by omega
      rw [hidx]
      cases l with
      | nil => simp only [List.take_nil, List.drop_nil, List.nil_append]
      | cons a t =>
          show a :: t.take (i + j) = a :: (t.take i ++ (t.drop i).take j)
          exact congrArg (a :: ·) (ih j t)

/-- The redeal leaf split: one more dealt card is the current prefix
plus a single card off the remaining stock. -/
private theorem take_succ_split {α : Type} (l : List α) (n : Nat) :
    l.take (n + 1) = l.take n ++ (l.drop n).take 1 :=
  take_drop_add n 1 l

/-- The additive drop split: dropping `j` more after dropping `i` is
dropping `i + j`. -/
private theorem drop_drop_add {α : Type} : ∀ (i j : Nat) (l : List α),
    (l.drop i).drop j = l.drop (i + j) := by
  intro i
  induction i with
  | zero =>
      intro j l
      simp
  | succ i ih =>
      intro j l
      have hidx : i + 1 + j = i + j + 1 := by omega
      rw [hidx]
      cases l with
      | nil => simp only [List.drop_nil]
      | cons a t =>
          show (t.drop i).drop j = t.drop (i + j)
          exact ih j t

/-- Take and drop recombine to the whole list — the partition
totality of a deal. -/
private theorem take_drop_append {α : Type} : ∀ (n : Nat) (l : List α),
    l.take n ++ l.drop n = l := by
  intro n
  induction n with
  | zero => intro l; simp
  | succ m ih =>
      intro l
      cases l with
      | nil => rfl
      | cons a t =>
          show a :: (t.take m ++ t.drop m) = a :: t
          exact congrArg (a :: ·) (ih t)

/-- Taking past (or exactly to) the end of a list takes the whole
list — the clip that swallows every min. -/
private theorem take_ge_length {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.take n = l := by
  intro l
  induction l with
  | nil =>
      intro n _
      exact List.take_nil
  | cons a t ih =>
      intro n
      intro h
      match n with
      | 0 =>
          exact absurd h (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          have hm : t.length ≤ m := by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega
          show a :: t.take m = a :: t
          exact congrArg (a :: ·) (ih m hm)

/-- Dropping past (or exactly to) the end of a list drops it to
nothing. -/
private theorem drop_ge_length {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.drop n = [] := by
  intro l
  induction l with
  | nil =>
      intro n _
      exact List.drop_nil
  | cons a t ih =>
      intro n
      intro h
      match n with
      | 0 =>
          exact absurd h (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          have hm : t.length ≤ m := by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega
          exact ih m hm

/-- The prefix clip on an appended list: dropping past a known
prefix returns the suffix. -/
private theorem drop_append_prefix {α : Type} : ∀ (A B : List α),
    (A ++ B).drop A.length = B := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons a t ih =>
      intro B
      show (t ++ B).drop t.length = B
      exact ih B

/-- The prefix clip on an appended list, take side: taking exactly
through a known prefix returns the prefix. -/
private theorem take_append_prefix {α : Type} : ∀ (A B : List α),
    (A ++ B).take A.length = A := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons a t ih =>
      intro B
      show a :: (t ++ B).take t.length = a :: t
      exact congrArg (a :: ·) (ih B)

/-- The two dealt segments recombine under reversal: the dealt
`n`-tail then the dealt prefix, reversed segmentwise and reappended,
equal the whole list reversed. -/
private theorem seg_reverse_merge {α : Type} (l : List α) (n : Nat) (w : List α) :
    (l.drop n).reverse ++ (l.take n).reverse ++ w = l.reverse ++ w := by
  rw [show l.reverse = (l.take n ++ l.drop n).reverse from
        congrArg List.reverse (take_drop_append n l).symm,
      List.reverse_append, List.append_assoc]

/-- The stepwise dealt-pair merge: two consecutively dealt segments —
the first `j` cards past position `i`, then the first `i` cards —
recombine under reversal to the take `(i + j)`'s reversal. -/
private theorem take_reverse_merge {α : Type} (l : List α) (i j : Nat) (w : List α) :
    ((l.drop i).take j).reverse ++ (l.take i).reverse ++ w = (l.take (i + j)).reverse ++ w := by
  rw [take_drop_add, List.reverse_append, List.append_assoc]

/-- One draw followed by the rest of the play: the step projection of
`State.run` specialized to the draw. -/
private theorem run_draw_cons {x y : State} {rest : List Move}
    (hstep : State.step x Move.draw = some y) :
    x.run (Move.draw :: rest) = y.run rest := by
  show (match State.step x Move.draw with
      | some st' => State.run st' rest
      | none => none) = State.run y rest
  rw [hstep]

/-- Append-glue for pure-draw plays: after `q` draws land at `z`, the
following suffix continues from `z`. -/
private theorem run_replicate_append :
    ∀ (q : Nat) (x z : State) (rest : List Move),
    x.run (List.replicate q Move.draw) = some z →
    x.run (List.replicate q Move.draw ++ rest) = z.run rest := by
  intro q
  induction q with
  | zero =>
      intro x z rest h
      have hx : (some x : Option State) = some z := h
      injection hx with hx2
      rw [← hx2]
      rfl
  | succ q ih =>
      intro x z rest h
      obtain ⟨y, hstep, hrest⟩ := State.run_cons h
      show x.run (Move.draw :: (List.replicate q Move.draw ++ rest)) = z.run rest
      rw [run_draw_cons hstep]
      exact ih y z rest hrest

/-- **The drain positions.**  From a state whose stock is `l`, `q`
consecutive draws — each a full deal, so the running offset `n =
q * drawStep` stays within the stock — move exactly those `n` cards
from the stock's front to the waste's front, list-exact. -/
private theorem drain_positions_one :
    ∀ (q : Nat) (x : State) (n : Nat) (l : List Card),
    0 < x.drawStep → n = q * x.drawStep → n ≤ l.length → x.stock = l →
    x.run (List.replicate q Move.draw) = some
      { x with stock := l.drop n, waste := (l.take n).reverse ++ x.waste } := by
  intro q
  induction q with
  | zero =>
      intro x n l _hd hn _hle hstock
      have hn0 : n = 0 := by
        rw [Nat.zero_mul] at hn
        exact hn
      subst hn0
      show (some x : Option State) = some
        { x with stock := l.drop 0, waste := (l.take 0).reverse ++ x.waste }
      rw [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append,
        ← hstock]
  | succ q ih =>
      intro x n l hd hn hle hstock
      have hnsm : n = q * x.drawStep + x.drawStep := by
        rw [Nat.succ_mul] at hn
        exact hn
      have hlne : l ≠ [] := by
        intro hc
        have hlen : l.length = 0 := by rw [hc]; simp
        omega
      have hsne : x.stock ≠ [] := by
        intro hc
        apply hlne
        rw [← hstock]
        exact hc
      have hstep : State.step x Move.draw = some
        { x with stock := x.stock.drop x.drawStep,
                 waste := (x.stock.take x.drawStep).reverse ++ x.waste } :=
        plain_draw_shape hsne
      have hrep : List.replicate (q + 1) Move.draw
          = Move.draw :: List.replicate q Move.draw := rfl
      rw [hrep, run_draw_cons hstep, hstock]
      have hle' : q * x.drawStep ≤ (l.drop x.drawStep).length := by
        have h1 := List.length_drop (i := x.drawStep) (l := l)
        omega
      have hres := ih
        { x with stock := l.drop x.drawStep,
                 waste := (l.take x.drawStep).reverse ++ x.waste }
        (q * x.drawStep) (l.drop x.drawStep) hd rfl hle' rfl
      rw [hres]
      have hSw : (show State from
          { x with stock := l.drop x.drawStep,
                   waste := (l.take x.drawStep).reverse ++ x.waste }).waste
          = (l.take x.drawStep).reverse ++ x.waste := rfl
      rw [hSw]
      have hidx : x.drawStep + q * x.drawStep = n := by omega
      rw [drop_drop_add x.drawStep (q * x.drawStep) l, hidx]
      have hmerge : (List.take (q * x.drawStep) (List.drop x.drawStep l)).reverse
            ++ ((List.take x.drawStep l).reverse ++ x.waste)
          = (l.take (x.drawStep + q * x.drawStep)).reverse ++ x.waste := by
        rw [take_drop_add, List.reverse_append, List.append_assoc]
      rw [hmerge, hidx]

/-- **The redeal positions.**  From a pass base (empty stock,
nonempty waste), `k + 1` consecutive draws — the first recycles the
waste into the stock reversed and deals, the rest drain that recycled
stock at a full deal each, while the running offset `(k + 1) *
drawStep` stays within the recycled length — move exactly that many
cards back onto the waste, list-exact. -/
private theorem base_positions_one :
    ∀ (k : Nat) (x : State),
    x.stock = ([] : List Card) → x.waste ≠ [] → 0 < x.drawStep →
    (k + 1) * x.drawStep ≤ x.waste.length →
    x.run (List.replicate (k + 1) Move.draw) = some
      { x with stock := x.waste.reverse.drop ((k + 1) * x.drawStep),
               waste := (x.waste.reverse.take ((k + 1) * x.drawStep)).reverse ++ ([] : List Card) } := by
  intro k x hstock hw hd hsize
  rw [Nat.succ_mul] at hsize
  have hstep : State.step x Move.draw = some
    { x with stock := x.waste.reverse.drop x.drawStep,
             waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) } :=
    base_draw_shape hstock hw
  rw [show List.replicate (k + 1) Move.draw
        = Move.draw :: List.replicate k Move.draw from rfl,
    run_draw_cons hstep]
  have hle' : k * x.drawStep ≤ (x.waste.reverse.drop x.drawStep).length := by
    have h1 := List.length_drop (i := x.drawStep) (l := x.waste.reverse)
    have h2 : x.waste.reverse.length = x.waste.length := List.length_reverse
    omega
  have hres := drain_positions_one k
    { x with stock := x.waste.reverse.drop x.drawStep,
             waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) }
    (k * x.drawStep) (x.waste.reverse.drop x.drawStep) hd rfl hle' rfl
  rw [hres]
  have hSw : (show State from
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) }).waste
      = (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) := rfl
  rw [hSw]
  have hidx : x.drawStep + k * x.drawStep = (k + 1) * x.drawStep := by
    rw [Nat.succ_mul]; omega
  rw [drop_drop_add x.drawStep (k * x.drawStep) x.waste.reverse, hidx]
  have hmerge : (List.take (k * x.drawStep)
          (List.drop x.drawStep x.waste.reverse)).reverse
        ++ ((List.take x.drawStep x.waste.reverse).reverse ++ ([] : List Card))
      = ((List.take (x.drawStep + k * x.drawStep) x.waste.reverse).reverse
          ++ ([] : List Card)) := by
    rw [take_drop_add, List.reverse_append, List.append_assoc]
  rw [hmerge, hidx]

/-- **The short-stock full deal.**  With a nonempty stock shorter than
the (positive) draw step, the deal empties the stock — the take clips
the whole stock — and reverses its cards onto the waste, list-exact. -/
private theorem draw_full_shape (x : State) (hne : x.stock ≠ [])
    (hx : x.stock.length < x.drawStep) :
    State.step x Move.draw = some
      (State.mk x.found x.piles ([] : List Card) (x.stock.reverse ++ x.waste) x.drawStep) := by
  have ge := Nat.le_of_lt hx
  rw [show State.step x Move.draw = x.stepDraw from rfl, plain_draw_shape hne,
    drop_ge_length x.stock x.drawStep ge, take_ge_length x.stock x.drawStep ge]

/-- **The in-phase round trip, witness form.**  At a phase-aligned
position with a positive draw step, cards left in the stock, and a
nonempty whole number of deals in the waste, the draw is undone by an
explicit pure-draw play: drain the committed stock to the pass base
(as many whole deals as it holds, plus the boundary deal when its
length is not a whole number of deals), then redeal exactly the
waste's whole number of deals from the recycled pool — the two legs
rotate the cycle's pool by exactly its own length, landing back on
the origin.  The negative form `draw_reversible_inphase` follows
from this via `reversibleAt_of_W`. -/
theorem draw_reversible_inphaseW {st : State} (hd : 0 < st.drawStep)
    (hs : st.stock ≠ []) (hw : st.waste ≠ []) (hph : inPhase st = true) :
    reversibleAtW st Move.draw := by
  obtain ⟨c, t, hcon⟩ := list_cons_of_ne_nil hs
  have hres0 : st.waste.length % st.drawStep = 0 := by
    rw [inPhase_eq_decide_of_cons hcon] at hph
    exact of_decide_eq_true hph
  have hjd : st.drawStep * (st.waste.length / st.drawStep) = st.waste.length := by
    have := Nat.div_add_mod st.waste.length st.drawStep
    omega
  have hstep : State.step st Move.draw = some
      (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep) :=
    plain_draw_shape hs
  obtain ⟨w0, t0, hwcon⟩ := list_cons_of_ne_nil hw
  have hw1 : 1 ≤ st.waste.length := by rw [hwcon, List.length_cons]; omega
  have hp1 : 1 ≤ st.stock.length := by rw [hcon, List.length_cons]; omega
  have hNl : (st.stock.reverse ++ st.waste).length
      = st.stock.length + st.waste.length := by
    rw [List.length_append, List.length_reverse]
  have hpool : (st.stock.drop st.drawStep).reverse
      ++ ((st.stock.take st.drawStep).reverse ++ st.waste)
      = st.stock.reverse ++ st.waste := by
    rw [show st.stock.reverse
          = (st.stock.take st.drawStep ++ st.stock.drop st.drawStep).reverse from
          congrArg List.reverse (take_drop_append st.drawStep st.stock).symm,
      List.reverse_append, List.append_assoc]
  -- the waste's whole number of deals, in successor form for the redeal leg
  rcases hqj : st.waste.length / st.drawStep with _ | jk
  · exfalso
    rw [hqj, Nat.mul_zero] at hjd
    omega
  rw [hqj] at hjd
  have hjd2 : (jk + 1) * st.drawStep = st.waste.length := by
    rw [Nat.mul_comm]
    exact hjd
  -- the pass base's pool waste carries the whole cycle; it is not empty
  have hwB : (st.stock.reverse ++ st.waste) ≠ [] := by
    intro hc
    rw [hc] at hNl
    simp only [List.length_nil] at hNl
    omega
  have hsizeB : (jk + 1) * st.drawStep
      ≤ (st.stock.reverse ++ st.waste).length := by rw [hNl]; omega
  have hmfull :=
    Nat.div_add_mod (st.stock.drop st.drawStep).length st.drawStep
  have hmodlt : (st.stock.drop st.drawStep).length % st.drawStep < st.drawStep :=
    Nat.mod_lt _ hd
  by_cases hdr : (st.stock.drop st.drawStep).length % st.drawStep = 0
  · -- the drain reaches the base at whole deals only
    have hnA : (st.stock.drop st.drawStep).length
        = ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep := by
      rw [Nat.mul_comm]
      omega
    have hDA := drain_positions_one
      ((st.stock.drop st.drawStep).length / st.drawStep)
      (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep)
      (st.stock.drop st.drawStep).length
      (st.stock.drop st.drawStep)
      hd hnA (Nat.le_refl _) rfl
    have hdrop0 : (st.stock.drop st.drawStep).drop
        (st.stock.drop st.drawStep).length = [] :=
      drop_ge_length _ _ (Nat.le_refl _)
    have htake0 : (st.stock.drop st.drawStep).take
        (st.stock.drop st.drawStep).length = st.stock.drop st.drawStep :=
      take_ge_length _ _ (Nat.le_refl _)
    have hSw1 : (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).waste
        = (st.stock.take st.drawStep).reverse ++ st.waste := rfl
    refine ⟨State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep,
      List.replicate ((st.stock.drop st.drawStep).length / st.drawStep) Move.draw
        ++ List.replicate (jk + 1) Move.draw,
      hstep, ?_⟩
    rw [run_replicate_append _ _ _ (List.replicate (jk + 1) Move.draw) hDA,
      hdrop0, htake0, hSw1, hpool]
    -- the redeal leg from the pass base
    have hb := base_positions_one jk
      (State.mk st.found st.piles ([] : List Card) (st.stock.reverse ++ st.waste) st.drawStep)
      rfl hwB hd hsizeB
    rw [hb]
    -- the two final matches: the recycled pool splits back into st
    have hz1w : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).waste
        = st.stock.reverse ++ st.waste := rfl
    have hz1d : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).drawStep
        = st.drawStep := rfl
    rw [hz1w, hz1d]
    have hSpl : st.waste.reverse ++ st.stock
        = (st.stock.reverse ++ st.waste).reverse := by
      rw [List.reverse_append, List.reverse_reverse]
    rw [← hSpl, hjd2, ← List.length_reverse, drop_append_prefix, take_append_prefix,
      List.reverse_reverse, List.append_nil]
  · -- the stock's remainder forces one boundary deal before the base
    have hqB : ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep
        + (st.stock.drop st.drawStep).length % st.drawStep
        = (st.stock.drop st.drawStep).length := by
      have h := hmfull
      rw [Nat.mul_comm] at h
      exact h
    -- the post-drain state, restated with flat fields
    have hDB := drain_positions_one
      ((st.stock.drop st.drawStep).length / st.drawStep)
      (State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep)
      (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
      (st.stock.drop st.drawStep)
      hd rfl (by omega) rfl
    have hDB2 : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).run
        (List.replicate ((st.stock.drop st.drawStep).length / st.drawStep) Move.draw) = some
      (State.mk st.found st.piles
        ((st.stock.drop st.drawStep).drop
          (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
        ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
            (List.drop st.drawStep st.stock)).reverse
          ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
        st.drawStep) := by
      have hXf : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).found
          = st.found := rfl
      have hXp : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).piles
          = st.piles := rfl
      have hXw : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).waste
          = (st.stock.take st.drawStep).reverse ++ st.waste := rfl
      have hXd : (State.mk st.found st.piles (st.stock.drop st.drawStep)
          ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep).drawStep
          = st.drawStep := rfl
      rw [hDB, hXf, hXp, hXw, hXd]
    -- the boundary draw acts on the post-drain state as a short-stock full deal
    have hx₀ne : (st.stock.drop st.drawStep).drop
        (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep) ≠ [] := by
      intro hc
      have hld := List.length_drop
        (i := ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
        (l := st.stock.drop st.drawStep)
      rw [hc] at hld
      simp only [List.length_nil] at hld
      omega
    have hx₀len : ((st.stock.drop st.drawStep).drop
        (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)).length
        < st.drawStep := by
      have hld := List.length_drop
        (i := ((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
        (l := st.stock.drop st.drawStep)
      rw [hld]
      omega
    have hBstep : State.step
        (State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep) Move.draw = some
        (State.mk (State.mk st.found st.piles
            ((st.stock.drop st.drawStep).drop
              (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
            ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                (List.drop st.drawStep st.stock)).reverse
              ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
            st.drawStep).found
          (State.mk st.found st.piles
            ((st.stock.drop st.drawStep).drop
              (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
            ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                (List.drop st.drawStep st.stock)).reverse
              ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
            st.drawStep).piles
          ([] : List Card)
          ((State.mk st.found st.piles
              ((st.stock.drop st.drawStep).drop
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
              ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                  (List.drop st.drawStep st.stock)).reverse
                ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
              st.drawStep).stock.reverse
            ++ (State.mk st.found st.piles
                ((st.stock.drop st.drawStep).drop
                  (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
                ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                    (List.drop st.drawStep st.stock)).reverse
                  ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
                st.drawStep).waste)
          (State.mk st.found st.piles
            ((st.stock.drop st.drawStep).drop
              (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
            ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
                (List.drop st.drawStep st.stock)).reverse
              ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
            st.drawStep).drawStep) :=
      draw_full_shape
        (State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep)
        hx₀ne hx₀len
    -- the y0 position from the boundary draw carries x₀'s flat fields by iota
    have hySt : (show State from
        State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep).stock
        = (st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep) := rfl
    have hyWs : (show State from
        State.mk st.found st.piles
          ((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep))
          ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste))
          st.drawStep).waste
        = (List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste) := rfl
    -- the boundary segments merge into the whole stock, reversed
    have hpool2 : (((st.stock.drop st.drawStep).drop
            (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)).reverse
          ++ ((List.take ((st.stock.drop st.drawStep).length / st.drawStep * st.drawStep)
              (List.drop st.drawStep st.stock)).reverse
            ++ ((st.stock.take st.drawStep).reverse ++ st.waste)))
        = st.stock.reverse ++ st.waste := by
      rw [show st.stock.reverse
            = (st.stock.take st.drawStep ++ st.stock.drop st.drawStep).reverse from
            congrArg List.reverse (take_drop_append st.drawStep st.stock).symm,
        List.reverse_append,
        show (st.stock.drop st.drawStep).reverse
            = ((st.stock.drop st.drawStep).take
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
              ++ (st.stock.drop st.drawStep).drop
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)).reverse from
            congrArg List.reverse
              (take_drop_append
                (((st.stock.drop st.drawStep).length / st.drawStep) * st.drawStep)
                (st.stock.drop st.drawStep)).symm,
        List.reverse_append]
      simp only [List.append_assoc]
    refine ⟨State.mk st.found st.piles (st.stock.drop st.drawStep)
        ((st.stock.take st.drawStep).reverse ++ st.waste) st.drawStep,
      List.replicate
        ((st.stock.drop st.drawStep).length / st.drawStep) Move.draw
        ++ (Move.draw :: List.replicate (jk + 1) Move.draw),
      hstep, ?_⟩
    rw [run_replicate_append _ _ _
      (Move.draw :: List.replicate (jk + 1) Move.draw) hDB2,
      run_draw_cons hBstep]
    -- the boundary deal's position is the pass base with the merged pool
    rw [hySt, hyWs, hpool2]
    -- the redeal leg from the pass base
    have hb := base_positions_one jk
      (State.mk st.found st.piles ([] : List Card) (st.stock.reverse ++ st.waste) st.drawStep)
      rfl hwB hd hsizeB
    rw [hb]
    -- the two final matches: the recycled pool splits back into st
    have hz1w : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).waste
        = st.stock.reverse ++ st.waste := rfl
    have hz1d : (State.mk st.found st.piles ([] : List Card)
        (st.stock.reverse ++ st.waste) st.drawStep).drawStep
        = st.drawStep := rfl
    rw [hz1w, hz1d]
    have hSpl : st.waste.reverse ++ st.stock
        = (st.stock.reverse ++ st.waste).reverse := by
      rw [List.reverse_append, List.reverse_reverse]
    rw [← hSpl, hjd2, ← List.length_reverse, drop_append_prefix, take_append_prefix,
      List.reverse_reverse, List.append_nil]






/-- **The in-phase round trip, negative form.**  The constructive
witness of `draw_reversible_inphaseW` exported through
`reversibleAt_of_W`, keeping the negative row visible for the
classification assembly. -/
theorem draw_reversible_inphase {st : State} (hd : 0 < st.drawStep)
    (hs : st.stock ≠ []) (hw : st.waste ≠ []) (hph : inPhase st = true) :
    reversibleAt st Move.draw :=
  reversibleAt_of_W (draw_reversible_inphaseW hd hs hw hph)

/-- **The draw irreversibility classification.**  With a positive draw
step and a nonempty stock, the draw is irreversible exactly when the
position is not phase-aligned: either the waste is empty (the
pristine draw opens a fresh cycle) or its length is not a whole
number of deals (the misaligned draw desynchronizes the cycle).  The
`st.stock ≠ []` hypothesis is deliberate: at an empty stock the
statement degenerates, because every pass-base position is fully
reversible through its own cycle and no waste-shape dichotomy
survives there. -/
theorem draw_irreversibility_class {st : State} (hd : 0 < st.drawStep)
    (hs : st.stock ≠ []) :
    irreversibleAt st Move.draw ↔
      (st.waste = [] ∨ st.waste.length % st.drawStep ≠ 0) := by
  constructor
  · intro hirr
    by_cases hw : st.waste = []
    · exact Or.inl hw
    · by_cases hres : st.waste.length % st.drawStep = 0
      · exfalso
        obtain ⟨c0, t0, hcon⟩ := list_cons_of_ne_nil hs
        have hph : inPhase st = true := by
          rw [inPhase_eq_decide_of_cons hcon, decide_eq_true hres]
        exact not_reversibleAtW_of_irreversibleAt hirr
          (draw_reversible_inphaseW hd hs hw hph)
      · exact Or.inr hres
  · intro hbad
    rcases hbad with hpr | hoff
    · exact draw_irreversible_pristine hd hs hpr
    · exact draw_irreversible_offset hd hs hoff

/-- **The draw-one base round trip.**  At the pass base (empty stock,
nonempty waste) with unit draw step, the draw is undone by draining
the recycled stock one card at a time: `waste.length - 1` draws cycle
the whole waste pool back to its starting arrangement. -/
private theorem draw_step_one_base (st : State)
    (hst : st.stock = ([] : List Card)) (hw : st.waste ≠ [])
    (hd : st.drawStep = 1) : reversibleAtW st Move.draw := by
  have hstep0 := base_draw_shape hst hw
  have hn : st.waste.length - 1 = (st.waste.length - 1) * st.drawStep := by
    rw [hd]; omega
  have hle : st.waste.length - 1 ≤ (st.waste.reverse.drop st.drawStep).length := by
    have h1 := List.length_drop (i := st.drawStep) (l := st.waste.reverse)
    have h2 : st.waste.reverse.length = st.waste.length := List.length_reverse
    omega
  have hD := drain_positions_one (st.waste.length - 1)
    (State.mk st.found st.piles (st.waste.reverse.drop st.drawStep)
      ((st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card)) st.drawStep)
    (st.waste.length - 1) (st.waste.reverse.drop st.drawStep)
    (by rw [hd]; omega) hn hle rfl
  refine ⟨State.mk st.found st.piles (st.waste.reverse.drop st.drawStep)
      ((st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card)) st.drawStep,
    List.replicate (st.waste.length - 1) Move.draw, ?_, ?_⟩
  · rw [show State.step st Move.draw = State.stepDraw st from rfl]
    exact hstep0
  · rw [hD]
    have hSw : (State.mk st.found st.piles (st.waste.reverse.drop st.drawStep)
        ((st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card)) st.drawStep).waste
        = (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card) := rfl
    rw [hSw]
    have hdrop1 : (st.waste.reverse.drop st.drawStep).drop (st.waste.length - 1)
        = ([] : List Card) := by
      have h1 := List.length_drop (i := st.drawStep) (l := st.waste.reverse)
      have h2 : st.waste.reverse.length = st.waste.length := List.length_reverse
      exact drop_ge_length _ _ (by omega)
    rw [hdrop1]
    have htake1 : (st.waste.reverse.drop st.drawStep).take (st.waste.length - 1)
        = st.waste.reverse.drop st.drawStep := by
      have h1 := List.length_drop (i := st.drawStep) (l := st.waste.reverse)
      have h2 : st.waste.reverse.length = st.waste.length := List.length_reverse
      exact take_ge_length _ _ (by omega)
    rw [htake1]
    have hpool3 : (st.waste.reverse.drop st.drawStep).reverse
        ++ ((st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card))
        = st.waste ++ ([] : List Card) := by
      rw [show st.waste ++ ([] : List Card)
            = (st.waste.reverse.take st.drawStep
                ++ st.waste.reverse.drop st.drawStep).reverse
              ++ ([] : List Card) from
            congrArg (· ++ ([] : List Card))
              ((List.reverse_reverse st.waste).symm.trans
                (congrArg List.reverse (take_drop_append st.drawStep st.waste.reverse).symm)),
        List.reverse_append, List.append_assoc]
    rw [hpool3,
      show st.waste ++ ([] : List Card) = st.waste from List.append_nil st.waste,
      show ([] : List Card) = st.stock from hst.symm]

/-- **The draw-one sanity classification.**  With unit draw step and a
legal draw, irreversibility is exactly pristine emptiness of the
waste: at one card per deal every nonempty waste is phase-aligned
(`n % 1 = 0`), so the in-phase round trip covers the stock-bearing
positions and the draw-one base drain covers the pass-base positions. -/
theorem drawStep_one_class {st : State} (hd : st.drawStep = 1)
    (hly : ∃ s₁, State.step st Move.draw = some s₁) :
    irreversibleAt st Move.draw ↔ st.waste = [] := by
  have hdpos : 0 < st.drawStep := by rw [hd]; omega
  constructor
  · intro hirr
    by_cases hw : st.waste = []
    · exact hw
    · exfalso
      by_cases hst : st.stock = []
      · exact not_reversibleAtW_of_irreversibleAt hirr
          (draw_step_one_base st hst hw hd)
      · obtain ⟨c0, t0, hcon⟩ := list_cons_of_ne_nil hst
        have hres : st.waste.length % st.drawStep = 0 := by
          rw [hd]
          omega
        have hph : inPhase st = true := by
          rw [inPhase_eq_decide_of_cons hcon, decide_eq_true hres]
        exact not_reversibleAtW_of_irreversibleAt hirr
          (draw_reversible_inphaseW hdpos hst hw hph)
  · intro hpr
    obtain ⟨s₁, hs₁⟩ := hly
    by_cases hst : st.stock = []
    · exfalso
      rw [show State.step st Move.draw = State.stepDraw st from rfl] at hs₁
      rw [State.stepDraw, recycle_allEmpty st hst hpr, dealStock_nil st hst] at hs₁
      exact absurd hs₁ (by simp)
    · exact draw_irreversible_pristine hdpos hst hpr