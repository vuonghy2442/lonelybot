import Orig.Classify
import Orig.Canonical

/-!
# Orig — decompression: the reverse ladder and the draw letter (§3.0's completion, landing 2)

The reverse direction of the canonicalization theorem
(`FUTURES-ORIG.md` §9, probe-licensed throughout by
`probes/CanonDecompressProbe.lean`).  The scope is the card's after
the mid-flight refinement decisions: the draw stays a SEPARATE
PADDING LETTER (no canonicalizer touches the draw zone — the
`canon_draw` normalizer is a named optional polish row, banked in
the ledger for post-merge, and its value — killing the
draws-trivially site of the literal canon-iff, folding swComp —
rides the same rows landed here):

* **decompress_pulls** — the per-state reverse of canonicalization,
  restated with its leg alphabet: from the canonical form the
  reverse undo-ladder is a witness shuffle of `foundToTab`
  pull-downs only (`stackRun_return_pulls`), each raise's undo the
  exact one-move return (the V2 undo family, the banked
  `lift_undoW` engines re-graded for the leg's shape).  The
  per-member free lemma the decompression program starts from.

* **The draw letter's formal ground** — the zone-presentation
  algebra: every state is its own pool presentation
  (`zoneShape_self`), the draw legs act on presentations exactly
  (`zoneLeg_plain`/`_short`/`_pass`), the draw keeps the board and
  the pool (`stepDraw_keep`), no draw ever lands an empty waste at
  a positive draw step (`drawLanding_waste_ne` — the
  pristine-unreachability theorem: pristine zones are draw-unreachable
  from every waste-bearing presentation, the probe B-family's
  headline), and the phase line survives the draw chains
  (`inPhase_stepDraw_keep` — the swCompat resolution: pure-rotation
  orbits ride RevEqW directly, every chain leg licensed by the banked
  in-phase/pass rows, so swComp collapses to the consumption/offset
  cases only).

* **The saturator's zone rows** — `satStep` never touches the zone
  (`satStep_zone_keep`, so `canon` keeps it), and the saturator's
  board output depends only on the board input
  (`satStep_board_det`, `canon_board_det`).  The padding-generation
  order-freedom lemma rides them: the LITERAL saturating
  commutation `canon_draw_comm : canon (stepDrawn st) = stepDrawn
  (canon st)` — draws interleave freely with the saturation run,
  expected literal since the probe battery verified it at every
  zone shape.

* **finalWiggle_reach — the ONE named residue** of the card: the
  anchor relation between saturated members in the collapsed grade
  — Final-to-Final within one class, from the class anchor, by
  pulls+slides+pure-draws UP TO the twin pair-swap quotient (the
  count program's own grade; the anchor-mobility rows and the
  mem_macro_iff/cone_image shapes are ledgered as the main
  landing's presentation targets).  The probe battery supplies the
  positive family (the wiggle cube, the worry-back bridge) and the
  refutation data (the one-letter pure-pull form dies at the
  exhibit: no pull fires there); the general theorem is pinned here
  as a named stub in the house style — `sorryAx` admitted and
  printed in the audit below.

Axiom discipline: `[propext, Quot.sound]` at worst, zero
`Classical.choice`, ZERO `sorry` except the ONE named residue;
per-declaration `#print axioms` audit at file bottom.
-/

/-! ## The drawn-state helper -/

/-- The state after one draw (identity when the draw does not fire). -/
def stepDrawn (st : State) : State :=
  match st.step Move.draw with
  | some s' => s'
  | none => st

theorem stepDrawn_stepDraw {st s' : State} (h : st.stepDraw = some s') :
    stepDrawn st = s' := by
  show (match st.step Move.draw with
    | some s => s
    | none => st) = s'
  rw [show st.step Move.draw = st.stepDraw from rfl, h]

theorem stepDrawn_unfired {st : State} (h : st.stepDraw = none) :
    stepDrawn st = st := by
  show (match st.step Move.draw with
    | some s => s
    | none => st) = st
  rw [show st.step Move.draw = st.stepDraw from rfl, h]

/-- The draw keeps the board, the draw step, and the pool. -/
theorem stepDraw_keep {st s' : State} (h : st.stepDraw = some s') :
    s'.found = st.found ∧ s'.piles = st.piles ∧ s'.drawStep = st.drawStep ∧
      drawPool s' = drawPool st := by
  cases hst : st.stock with
  | nil =>
      cases hws : st.waste with
      | nil =>
          exfalso
          rw [show st.stepDraw = State.dealStock st.recycle from rfl,
            recycle_allEmpty st hst hws, dealStock_nil st hst] at h
          exact absurd h (by simp)
      | cons w ws =>
          have hwne : st.waste ≠ [] := by rw [hws]; simp
          rw [base_draw_shape hst hwne] at h
          injection h with hrec
          subst hrec
          refine ⟨rfl, rfl, rfl, ?_⟩
          simp only [drawPool]
          rw [hst]
          show (st.waste.reverse.drop st.drawStep).reverse
              ++ ((st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card))
              = ([] : List Card).reverse ++ st.waste
          rw [List.reverse_nil, List.append_nil, List.nil_append,
            ← List.reverse_append,
            take_drop_append st.drawStep st.waste.reverse, List.reverse_reverse]
  | cons s ss =>
      have hsne : st.stock ≠ [] := by rw [hst]; simp
      rw [plain_draw_shape hsne] at h
      injection h with hrec
      subst hrec
      refine ⟨rfl, rfl, rfl, ?_⟩
      simp only [drawPool]
      rw [hst]
      show ((s :: ss).drop st.drawStep).reverse
          ++ (((s :: ss).take st.drawStep).reverse ++ st.waste)
          = (s :: ss).reverse ++ st.waste
      have hE : (s :: ss).reverse
          = ((s :: ss).drop st.drawStep).reverse
            ++ ((s :: ss).take st.drawStep).reverse := by
        have h1 : (s :: ss).reverse
            = ((s :: ss).take st.drawStep ++ (s :: ss).drop st.drawStep).reverse :=
          congrArg List.reverse (take_drop_append st.drawStep (s :: ss)).symm
        rw [h1, List.reverse_append]
      rw [hE, List.append_assoc]

/-- The take of a positive count off a nonempty list is nonempty. -/
private theorem takeMinLen {α : Type} (d : Nat) : ∀ (l : List α),
    1 ≤ d → l ≠ [] → 1 ≤ (l.take d).length := by
  cases d with
  | zero => intro l h1 _; omega
  | succ d =>
      intro l
      cases l with
      | nil => intro _ h; exact absurd rfl h
      | cons x xs =>
          intro _ _
          show 1 ≤ (x :: xs.take d).length
          show 1 ≤ (xs.take d).length + 1
          omega

/-- At a positive draw step, no draw from a waste-bearing state ever
lands an empty waste — the pristine-unreachability theorem of the
probe battery: pristine zones are draw-unreachable from every
waste-bearing presentation. -/
theorem drawLanding_waste_ne {st s' : State} (hd : 0 < st.drawStep)
    (h : st.stepDraw = some s') (hc : s'.waste = []) : st.waste = [] := by
  cases hst : st.stock with
  | nil =>
      have hwbase : st.waste ≠ [] := by
        intro hw
        rw [show st.stepDraw = State.dealStock st.recycle from rfl,
          recycle_allEmpty st hst hw, dealStock_nil st hst] at h
        exact absurd h (by simp)
      rw [base_draw_shape hst hwbase] at h
      injection h with hrec
      rw [← hrec] at hc
      exfalso
      have hlen := congrArg List.length hc
      rw [List.length_append, List.length_nil, List.length_reverse] at hlen
      cases hws : st.waste with
      | nil => exact hwbase hws
      | cons w ws =>
          rw [hws] at hlen
          have hT : 1 ≤ ((w :: ws).reverse.take st.drawStep).length :=
            takeMinLen st.drawStep _ hd (by simp)
          omega
  | cons s ss =>
      have hsne : st.stock ≠ [] := by rw [hst]; simp
      rw [plain_draw_shape hsne] at h
      injection h with hrec
      rw [← hrec] at hc
      exfalso
      have hlen := congrArg List.length hc
      rw [List.length_append, List.length_nil, List.length_reverse] at hlen
      rw [hst] at hlen
      have hT : 1 ≤ ((s :: ss).take st.drawStep).length :=
        takeMinLen st.drawStep _ hd (by simp)
      omega

/-! ## The zone presentation algebra -/

/-- The pool-faithful presentation: `m` stock-head cards of the pool
`P` wait in the stock (reversed), the rest sits in the waste, and
the counts total the pool. -/
def ZoneShape (P : List Card) (m : Nat) (st : State) : Prop :=
  st.stock = (P.take m).reverse ∧ st.waste = P.drop m ∧
    m + st.waste.length = P.length

/-- The take-clip on an appended list (the local kin of `Phase`'s
private `take_append_prefix`; dedup candidate). -/
private theorem takeClip {α : Type} : ∀ (A B : List α),
    (A ++ B).take A.length = A := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons x t ih =>
      intro B
      show x :: (t ++ B).take t.length = x :: t
      exact congrArg (x :: ·) (ih B)

/-- Double take is the min-take (the core row re-expressed for the
exact-length regime). -/
private theorem takeTake {α : Type} (P : List α) (a b : Nat) :
    (P.take a).take b = P.take (Nat.min b a) := by
  rw [List.take_take]

/-- The slice swap: dropping `i` after taking `i + k` is taking `k`
after dropping `i`. -/
private theorem sliceSwap {α : Type} (P : List α) (i k : Nat) :
    (P.take (i + k)).drop i = (P.drop i).take k := by
  rw [take_drop_add i k P, List.drop_append, List.length_take]
  by_cases hle : i ≤ P.length
  · rw [Nat.min_eq_left hle,
      drop_ge_length _ _ (by rw [List.length_take, Nat.min_eq_left hle]; omega),
      Nat.sub_self]
    show ([] : List α) ++ (P.drop i).take k = (P.drop i).take k
    rfl
  · have hy : (P.drop i).take k = ([] : List α) := by
      rw [drop_ge_length P i (by omega), List.take_nil]
    rw [hy, Nat.min_eq_right (by omega),
      drop_ge_length _ _ (by rw [List.length_take, Nat.min_eq_right (by omega)]; omega)]
    simp

/-- Reversal swaps the take window: taking `d` off the reversal is
reversing the LAST `d` of the original. -/
private theorem revTake {α : Type} (P : List α) (d : Nat) (h : d ≤ P.length) :
    P.reverse.take d = (P.drop (P.length - d)).reverse := by
  have hsplit : P.take (P.length - d) ++ P.drop (P.length - d) = P :=
    take_drop_append (P.length - d) P
  have hrev : P.reverse = (P.drop (P.length - d)).reverse
      ++ (P.take (P.length - d)).reverse := by
    have h2 := congrArg List.reverse hsplit
    rw [List.reverse_append] at h2
    exact h2.symm
  have hd : (P.drop (P.length - d)).length = d := by
    rw [List.length_drop]; omega
  rw [hrev, List.take_append, List.length_reverse, hd,
    take_ge_length _ _ (by rw [List.length_reverse]; omega), Nat.sub_self,
    show (P.take (P.length - d)).reverse.take 0 = ([] : List α) from rfl,
    List.append_nil]

/-- Reversal swaps the drop window: dropping `d` off the reversal is
reversing all but the last `d` of the original. -/
private theorem revDrop {α : Type} (P : List α) (d : Nat) (h : d ≤ P.length) :
    P.reverse.drop d = (P.take (P.length - d)).reverse := by
  have hsplit : P.take (P.length - d) ++ P.drop (P.length - d) = P :=
    take_drop_append (P.length - d) P
  have hrev : P.reverse = (P.drop (P.length - d)).reverse
      ++ (P.take (P.length - d)).reverse := by
    have h2 := congrArg List.reverse hsplit
    rw [List.reverse_append] at h2
    exact h2.symm
  have hd : (P.drop (P.length - d)).length = d := by
    rw [List.length_drop]; omega
  rw [hrev, List.drop_append, List.length_reverse, hd,
    drop_ge_length _ _ (by rw [List.length_reverse]; omega), Nat.sub_self]
  rfl

/-- The drop-take join at an inner split: the drop past `i` of the
full pool is the inner slice plus the outer suffix. -/
private theorem dropTakeJoin {α : Type} (P : List α) (i m : Nat)
    (him : i ≤ m) (_hm : m ≤ P.length) :
    (P.take m).drop i ++ P.drop m = P.drop i := by
  have h1 := take_drop_append (m - i) (P.drop i)
  have h2 : (P.drop i).drop (m - i) = P.drop m := by
    rw [drop_drop_add i (m - i) P,
      show i + (m - i) = m from by omega]
  have h3 : (P.drop i).take (m - i) = (P.take m).drop i := by
    have h4 := sliceSwap P i (m - i)
    rw [show i + (m - i) = m from by omega] at h4
    exact h4.symm
  rw [h3, h2] at h1
  exact h1

/-- Every state is its own pool presentation. -/
theorem zoneShape_self (st : State) : ZoneShape (drawPool st) st.stock.length st := by
  have hs : drawPool st = st.stock.reverse ++ st.waste := rfl
  refine ⟨?_, ?_, ?_⟩
  · show st.stock = ((drawPool st).take st.stock.length).reverse
    rw [hs, show st.stock.length = st.stock.reverse.length from by simp, takeClip,
      List.reverse_reverse]
  · show st.waste = (drawPool st).drop st.stock.length
    rw [hs, show st.stock.length = st.stock.reverse.length from by simp,
      drop_append_prefix]
  · rw [hs, List.length_append, List.length_reverse]

/-- A presentation's pool is the pool. -/
theorem drawPool_of_zoneShape {P : List Card} {m : Nat} {st : State}
    (h : ZoneShape P m st) : drawPool st = P := by
  obtain ⟨hst, hw, ht⟩ := h
  show st.stock.reverse ++ st.waste = P
  rw [hst, hw, List.reverse_reverse, take_drop_append m P]

/-- A presentation's pool-head count is at most the pool length. -/
theorem le_of_zoneShape {P : List Card} {m : Nat} {st : State}
    (h : ZoneShape P m st) : m ≤ P.length := by
  obtain ⟨-, -, ht⟩ := h
  omega

/-- The stock-head cards of a nontrivial presentation are nonempty. -/
theorem stock_ne_of_zoneShape {P : List Card} {m : Nat} {st : State}
    (h : ZoneShape P m st) (hm : 1 ≤ m) : st.stock ≠ [] := by
  obtain ⟨hst, -, ht⟩ := h
  intro hc
  rw [hc] at hst
  have hP : P ≠ [] := by
    intro hp
    rw [hp, show (List.length ([] : List Card)) = 0 from rfl] at ht
    omega
  have hT : 1 ≤ (P.take m).length := takeMinLen m P hm hP
  have hlen := congrArg List.length hst
  rw [show (List.length ([] : List Card)) = 0 from rfl, List.length_reverse] at hlen
  omega

/-- The plain leg: a stock-bearing presentation at pool-head count
`m ≥ drawStep` draws to the presentation at `m - drawStep`, board
and draw step verbatim. -/
theorem zoneLeg_plain {P : List Card} {m : Nat} {st s' : State}
    (hst : ZoneShape P m st) (hm : 1 ≤ m) (hd : st.drawStep ≤ m)
    (hstep : st.stepDraw = some s') :
    ZoneShape P (m - st.drawStep) s' ∧ s'.found = st.found ∧
      s'.piles = st.piles ∧ s'.drawStep = st.drawStep := by
  obtain ⟨hs, hw, ht⟩ := hst
  have hzs : ZoneShape P m st := ⟨hs, hw, ht⟩
  have hml : m ≤ P.length := le_of_zoneShape hzs
  have hlenm : (P.take m).length = m := by
    rw [List.length_take, Nat.min_eq_left hml]
  have hsne : st.stock ≠ [] := stock_ne_of_zoneShape hzs hm
  rw [plain_draw_shape hsne] at hstep
  injection hstep with hrec
  subst hrec
  have hstock : st.stock.drop st.drawStep = (P.take (m - st.drawStep)).reverse := by
    rw [hs, revDrop (P.take m) st.drawStep (by rw [hlenm]; omega), hlenm,
      List.take_take, Nat.min_eq_left (by omega)]
  have hwaste : (st.stock.take st.drawStep).reverse ++ st.waste
      = P.drop (m - st.drawStep) := by
    rw [hs, revTake (P.take m) st.drawStep (by rw [hlenm]; omega),
      List.length_take, Nat.min_eq_left hml, List.reverse_reverse, hw]
    exact dropTakeJoin P (m - st.drawStep) m (by omega) hml
  refine ⟨⟨hstock, hwaste, ?_⟩, rfl, rfl, rfl⟩
  show (m - st.drawStep)
      + ((st.stock.take st.drawStep).reverse ++ st.waste).length = P.length
  rw [hwaste, List.length_drop]
  omega

/-- The short leg: a stock-bearing presentation whose stock runs
shorter than the deal draws to the PASS BASE of its own pool. -/
theorem zoneLeg_short {P : List Card} {m : Nat} {st s' : State}
    (hst : ZoneShape P m st) (hm : 1 ≤ m) (hd : m < st.drawStep)
    (hstep : st.stepDraw = some s') :
    ZoneShape P 0 s' ∧ s'.found = st.found ∧
      s'.piles = st.piles ∧ s'.drawStep = st.drawStep := by
  obtain ⟨hs, hw, ht⟩ := hst
  have hzs : ZoneShape P m st := ⟨hs, hw, ht⟩
  have hml : m ≤ P.length := le_of_zoneShape hzs
  have hlenm : (P.take m).length = m := by
    rw [List.length_take, Nat.min_eq_left hml]
  have hsne : st.stock ≠ [] := stock_ne_of_zoneShape hzs hm
  rw [plain_draw_shape hsne] at hstep
  injection hstep with hrec
  subst hrec
  have hstock : st.stock.drop st.drawStep = ([] : List Card) := by
    rw [hs, drop_ge_length _ _ (by rw [List.length_reverse, hlenm]; omega)]
  have hwaste : (st.stock.take st.drawStep).reverse ++ st.waste = P := by
    rw [hs, take_ge_length _ _ (by rw [List.length_reverse, hlenm]; omega),
      List.reverse_reverse, hw, take_drop_append m P]
  refine ⟨⟨hstock, hwaste, ?_⟩, rfl, rfl, rfl⟩
  show (0 : Nat) + ((st.stock.take st.drawStep).reverse ++ st.waste).length = P.length
  rw [hwaste]
  omega

/-- The pass leg: the pass base of a pool of at least `drawStep`
cards redraws to the presentation at pool-head count
`P.length - drawStep`. -/
theorem zoneLeg_pass {P : List Card} {st s' : State}
    (hst : ZoneShape P 0 st) (hws : st.waste ≠ [])
    (hd : st.drawStep ≤ P.length) (hstep : st.stepDraw = some s') :
    ZoneShape P (P.length - st.drawStep) s' ∧ s'.found = st.found ∧
      s'.piles = st.piles ∧ s'.drawStep = st.drawStep := by
  obtain ⟨hstock0, hw0, -⟩ := hst
  have hsnil : st.stock = ([] : List Card) := hstock0.trans rfl
  have hwp : st.waste = P := hw0.trans rfl
  rw [base_draw_shape hsnil hws] at hstep
  injection hstep with hrec
  subst hrec
  have hstock : st.waste.reverse.drop st.drawStep
      = (P.take (P.length - st.drawStep)).reverse := by
    rw [hwp, revDrop P st.drawStep hd]
  have hwaste0 : (st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card)
      = P.drop (P.length - st.drawStep) := by
    rw [hwp, revTake P st.drawStep hd, List.reverse_reverse, List.append_nil]
  have hd2 : ((st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card)).length
      = st.drawStep := by
    rw [List.length_append, List.length_nil, hwp, revTake P st.drawStep hd,
      List.reverse_reverse, List.length_drop]
    omega
  refine ⟨⟨hstock, hwaste0, ?_⟩, rfl, rfl, rfl⟩
  show (P.length - st.drawStep)
      + ((st.waste.reverse.take st.drawStep).reverse ++ ([] : List Card)).length
      = P.length
  rw [hd2]
  omega

/-! ## The saturator never touches the zone -/

/-- The licensed raise keeps the zone verbatim (the record shapes
carry `setFound` and pile writes only). -/
theorem satStep_zone_keep (st : State) :
    (satStep st).stock = st.stock ∧ (satStep st).waste = st.waste ∧
      (satStep st).drawStep = st.drawStep := by
  cases hp : pick st with
  | none =>
      rw [show satStep st = st from satStep_none hp]
      exact ⟨rfl, rfl, rfl⟩
  | some c =>
      cases hr : raise st c with
      | none =>
          rw [show satStep st = (raise st c).getD st from by simp only [satStep, hp], hr]
          exact ⟨rfl, rfl, rfl⟩
      | some s₁ =>
          rw [show satStep st = s₁ from satStep_some hp hr]
          obtain ⟨-, a, -, hs₁⟩ := step_tabToFound_inv hr
          rw [hs₁]
          exact ⟨setFound_stock st c.suit (st.found c.suit ++ [c]),
            setFound_waste st c.suit (st.found c.suit ++ [c]),
            setFound_drawStep st c.suit (st.found c.suit ++ [c])⟩

/-- The saturator run keeps the zone verbatim at every budget. -/
theorem canonAux_zone_keep : ∀ (n : Nat) (st : State),
    (canonAux n st).stock = st.stock ∧ (canonAux n st).waste = st.waste ∧
      (canonAux n st).drawStep = st.drawStep := by
  intro n
  induction n with
  | zero => intro st; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      intro st
      have h1 := ih (satStep st)
      have h2 := satStep_zone_keep st
      exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

/-- The saturator keeps the zone verbatim (`canon` is `canonAux 53`). -/
theorem canon_zone_keep (st : State) :
    (canon st).stock = st.stock ∧ (canon st).waste = st.waste ∧
      (canon st).drawStep = st.drawStep :=
  canonAux_zone_keep 53 st

/-- The firstWhere search respects pointwise-equal predicates. -/
private theorem firstWhereCong {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = q x) → firstWhere p l = firstWhere q l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      show (match p x with
            | true => some x
            | false => firstWhere p t)
          = (match q x with
            | true => some x
            | false => firstWhere q t)
      rw [h x (by simp)]
      cases hq : q x with
      | true => rfl
      | false => exact ih (fun y hy => h y (by simp [hy]))

/-- The license probe reads only the board. -/
theorem canRaiseB_congr {st s' : State}
    (hp : st.piles = s'.piles) (hf : st.found = s'.found) (c : Card) :
    canRaiseB st c = canRaiseB s' c := by
  have hPILE : ∀ a, st.piles a = s'.piles a := by
    intro a; rw [hp]
  have hFOUND : ∀ s, st.found s = s'.found s := by
    intro s; rw [hf]
  have hpt : ∀ c, st.pileOfTop c = s'.pileOfTop c := by
    intro c
    exact firstWhereCong (fun a => decide (st.topOf a = some c))
      (fun a => decide (s'.topOf a = some c)) Anchor.all (fun a _ => by
      show decide ((st.piles a).top = some c) = decide ((s'.piles a).top = some c)
      rw [hPILE a])
  show (st.nextUp c && match st.pileOfTop c with
          | none => false
          | some a => decide (chop (st.piles a).faceUp ≠ [])
              || (decide ((st.piles a).hidden = []) && decide (c.rank = Rank.king)))
      = (s'.nextUp c && match s'.pileOfTop c with
          | none => false
          | some a => decide (chop (s'.piles a).faceUp ≠ [])
              || (decide ((s'.piles a).hidden = []) && decide (c.rank = Rank.king)))
  rw [show st.nextUp c = s'.nextUp c from by
      show decide (c.rank.toIdx = (st.found c.suit).length)
          = decide (c.rank.toIdx = (s'.found c.suit).length)
      rw [hFOUND c.suit], hpt c]
  cases hq : s'.pileOfTop c with
  | none =>
      show (s'.nextUp c && false) = (s'.nextUp c && false)
      rfl
  | some a =>
      show (s'.nextUp c && (decide (chop (st.piles a).faceUp ≠ [])
          || (decide ((st.piles a).hidden = []) && decide (c.rank = Rank.king))))
          = (s'.nextUp c && (decide (chop (s'.piles a).faceUp ≠ [])
          || (decide ((s'.piles a).hidden = []) && decide (c.rank = Rank.king))))
      rw [hPILE a]

/-- The pick search reads only the board: equal boards pick equal
cards. -/
theorem pick_congr {st s' : State}
    (hp : st.piles = s'.piles) (hf : st.found = s'.found) :
    pick st = pick s' :=
  firstWhereCong (canRaiseB st) (canRaiseB s') Card.universe
    (fun c _ => canRaiseB_congr hp hf c)

/-- The saturator's board output depends only on the board input. -/
theorem satStep_board_det {st s' : State}
    (hp : st.piles = s'.piles) (hf : st.found = s'.found) :
    (satStep st).piles = (satStep s').piles ∧ (satStep st).found = (satStep s').found := by
  have hPILE : ∀ a, st.piles a = s'.piles a := by
    intro a; rw [hp]
  have hFOUND : ∀ s, st.found s = s'.found s := by
    intro s; rw [hf]
  have hpt : ∀ c, st.pileOfTop c = s'.pileOfTop c := by
    intro c
    exact firstWhereCong (fun a => decide (st.topOf a = some c))
      (fun a => decide (s'.topOf a = some c)) Anchor.all (fun a _ => by
      show decide ((st.piles a).top = some c) = decide ((s'.piles a).top = some c)
      rw [hPILE a])
  have hpick := pick_congr hp hf
  cases hp2 : pick st with
  | none =>
      have hp2' : pick s' = none := by rw [← hpick, hp2]
      rw [show satStep st = st from satStep_none hp2,
        show satStep s' = s' from satStep_none hp2']
      exact ⟨hp, hf⟩
  | some c =>
      have hcB : canRaiseB st c = true := firstWhere_sound (p := canRaiseB st) hp2
      have hcB' : canRaiseB s' c = true := by
        rw [← canRaiseB_congr hp hf c]; exact hcB
      have hc : CanRaise st c := canRaiseB_true_iff.mp hcB
      have hc' : CanRaise s' c := canRaiseB_true_iff.mp hcB'
      obtain ⟨t, ht⟩ := raise_eq_some_of_canRaise st hc
      obtain ⟨t', ht'⟩ := raise_eq_some_of_canRaise s' hc'
      rw [show satStep st = t from satStep_some hp2 ht,
          show satStep s' = t' from satStep_some (by rw [← hpick, hp2]) ht']
      obtain ⟨-, a, hpo, hs₁⟩ := step_tabToFound_inv ht
      obtain ⟨-, a', hpo', hs₁'⟩ := step_tabToFound_inv ht'
      have haa : a = a' := by
        have hx : st.pileOfTop c = s'.pileOfTop c := hpt c
        rw [hpo, hpo'] at hx
        injection hx
      refine ⟨?_, ?_⟩
      · rw [hs₁, hs₁']
        funext x
        show (if x = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
              else st.piles x)
            = (if x = a' then Pile.afterRunRemoved (s'.piles a') (chop (s'.piles a').faceUp)
              else s'.piles x)
        by_cases hxa : x = a
        · rw [ite_eq_left hxa, ite_eq_left (hxa.trans haa), show a = a' from haa, hPILE a']
        · have hxa' : ¬ (x = a') := by
            intro h
            apply hxa
            rw [h, haa]
          rw [ite_eq_right hxa, ite_eq_right hxa', hPILE x]
      · rw [hs₁, hs₁']
        funext σ
        show (if σ = c.suit then (st.found c.suit ++ [c]) else st.found σ)
            = (if σ = c.suit then (s'.found c.suit ++ [c]) else s'.found σ)
        by_cases hσ : σ = c.suit
        · rw [ite_eq_left hσ, ite_eq_left hσ, hFOUND c.suit]
        · rw [ite_eq_right hσ, ite_eq_right hσ, hFOUND σ]

/-- The saturator run's board output depends only on the board input. -/
theorem canonAux_board_det : ∀ (n : Nat) (st s' : State),
    st.piles = s'.piles → st.found = s'.found →
    (canonAux n st).piles = (canonAux n s').piles ∧
      (canonAux n st).found = (canonAux n s').found := by
  intro n
  induction n with
  | zero => intro st s' hp hf; exact ⟨hp, hf⟩
  | succ n ih =>
      intro st s' hp hf
      have h1 := satStep_board_det hp hf
      exact ih (satStep st) (satStep s') h1.1 h1.2

/-- The canonical form's board depends only on the board input. -/
theorem canonBoard_det {st s' : State}
    (hp : st.piles = s'.piles) (hf : st.found = s'.found) :
    (canon st).piles = (canon s').piles ∧ (canon st).found = (canon s').found :=
  canonAux_board_det 53 st s' hp hf

/-! ## The per-state reverse: the pure-pull ladder -/

/-- The licensed lift's undo, re-graded for its leg alphabet: the
banked `lift_undoW` engine replayed with the move's SHAPE data —
exactly one `foundToTab` pull fires back to the origin (the exact
one-move return of the raise, the V2 undo family). -/
theorem lift_undo_pullW {st : State} {c : Card} {s₁ : State}
    (hwf : st.WF) (hc : CanRaise st c)
    (hstep : State.step st (Move.tabToFound c) = some s₁) :
    ∃ b : Base, State.step s₁ (Move.foundToTab c b) = some st ∧
      reversibleAtW s₁ (Move.foundToTab c b) := by
  have hc' := hc
  obtain ⟨-, a, hp, hbr⟩ := hc'
  obtain ⟨-, a', hp', hshape⟩ := step_tabToFound_inv hstep
  rw [hp] at hp'
  injection hp' with haa
  subst haa
  have hshape' : s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with
      piles := fun a₂ => if a₂ = a then
        Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) else st.piles a₂ } :=
    hshape
  have hwf₁ : s₁.WF := lift_wf hwf hc hstep
  cases hch : chop (st.piles a).faceUp with
  | cons y ys =>
      have hchop : (chop (st.piles a).faceUp) ≠ [] := by
        intro hcne
        rw [hcne] at hch
        exact absurd hch (by simp)
      have hfull : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] :=
        lastOf_chop (pileOfTop_top hp).2
      have hrok : runOK ((st.piles a).faceUp) = true := hwf.2.1 a
      have hrok2 : runOK (chop (st.piles a).faceUp ++ [c]) = true := by
        rw [← hfull]; exact hrok
      obtain ⟨z, hz, hsit⟩ := runOK_snoc_sit hchop hrok2
      have hpilesa : s₁.piles a
          = Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) := by
        rw [hshape']
        show (if a = a then
            Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
            else st.piles a) = _
        rw [ite_eq_left rfl]
      have hfaceup : (s₁.piles a).faceUp = y :: ys := by
        rw [hpilesa, hch,
          afterRunRemoved_ne (p := st.piles a) (pre := y :: ys) (by simp)]
      have htop : (s₁.piles a).top = some z := by
        show lastOf (s₁.piles a).faceUp = some z
        rw [hfaceup]
        rw [hch] at hz
        exact hz
      have hsearch : s₁.pileOfTop z = some a :=
        (pileOfTop_eq_some_iff hwf₁).mpr htop
      refine ⟨Sum.inr z, raise_undo_under_step hstep hp hz hsit hsearch, ?_⟩
      exact ⟨st, [Move.tabToFound c],
        raise_undo_under_step hstep hp hz hsit hsearch, run_one hstep⟩
  | nil =>
      rcases hbr with hne | ⟨hhid, hking⟩
      · exact absurd hch hne
      · refine ⟨Sum.inl a, raise_undo_bare_step hstep hp hch hhid hking, ?_⟩
        exact ⟨st, [Move.tabToFound c],
          raise_undo_bare_step hstep hp hch hhid hking, run_one hstep⟩

/-- **decompress_pulls, the run form**: from any licensed run's end
the reverse undo-ladder is a witness shuffle of PULL-DOWNS ONLY —
every leg a `foundToTab` (each raise's exact one-move undo). -/
theorem stackRun_return_pulls {st : State} (hwf : st.WF) {l : List Move} {w : State}
    (h : StackRun st l w) :
    ∃ τ : List Move, ShufflePlayW w τ st ∧
      ∀ m ∈ τ, ∃ c b, m = Move.foundToTab c b := by
  induction h with
  | nil s => exact ⟨[], .nil s, by simp⟩
  | @cons st₀ m c s' rest w₀ hc hm hstep hrest ih =>
      cases hm
      obtain ⟨b, hback, hrev'⟩ := lift_undo_pullW hwf hc hstep
      obtain ⟨τ₁, hτ₁, hall₁⟩ := ih (lift_wf hwf hc hstep)
      refine ⟨τ₁ ++ [Move.foundToTab c b], ShufflePlayW_append hτ₁
        (ShufflePlayW.cons hrev' hback (.nil st₀)), ?_⟩
      intro m hm'
      rw [List.mem_append] at hm'
      rcases hm' with hm' | hm'
      · exact hall₁ m hm'
      · rw [List.mem_singleton] at hm'
        exact ⟨c, b, hm'⟩

/-- **decompress_pulls**: the per-state reverse of canonicalization,
  restated with its leg alphabet — from the canonical form, the
  reversed undo-ladder is a witness shuffle of pure pull-downs. -/
theorem decompress_pulls {u : State} (hwf : u.WF) :
    ∃ τ : List Move, ShufflePlayW (canon u) τ u ∧
      ∀ m ∈ τ, ∃ c b, m = Move.foundToTab c b := by
  obtain ⟨l, hrun, -⟩ := canon_run u
  exact stackRun_return_pulls hwf hrun

/-- The draw blocks exactly at the both-empty zone. -/
private theorem stepDraw_eq_none_iff (st : State) :
    st.stepDraw = none ↔ st.stock = ([] : List Card) ∧ st.waste = ([] : List Card) := by
  constructor
  · intro h
    cases hst : st.stock with
    | nil =>
        cases hws : st.waste with
        | nil => exact ⟨rfl, rfl⟩
        | cons w ws =>
            exfalso
            rw [show st.stepDraw = State.dealStock st.recycle from rfl,
              recycle_nil st hst (by rw [hws]; simp),
              dealStock_eq_of_ne_nil _ (by rw [hws]; simp)] at h
            exact absurd h (by simp)
    | cons s ss =>
        exfalso
        rw [plain_draw_shape (by rw [hst]; simp)] at h
        exact absurd h (by simp)
  · rintro ⟨h1, h2⟩
    rw [show st.stepDraw = State.dealStock st.recycle from rfl,
      recycle_allEmpty st h1 h2, dealStock_nil st h1]

/-- The zone of a drawn landing is a function of the zone. -/
private theorem stepDraw_zone_det {x y x' y' : State}
    (hx : x.stepDraw = some x') (hy : y.stepDraw = some y')
    (hss : x.stock = y.stock) (hws : x.waste = y.waste)
    (hds : x.drawStep = y.drawStep) :
    x'.stock = y'.stock ∧ x'.waste = y'.waste ∧ x'.drawStep = y'.drawStep := by
  have hsty : y.stock = x.stock := hss.symm
  cases hst : x.stock with
  | nil =>
      have hsty0 : y.stock = ([] : List Card) := by rw [hsty, hst]
      have hxw : x.waste ≠ [] := by
        intro hc
        rw [show x.stepDraw = State.dealStock x.recycle from rfl,
          recycle_allEmpty x hst hc, dealStock_nil x hst] at hx
        exact absurd hx (by simp)
      have hyw : y.waste ≠ [] := by rw [← hws]; exact hxw
      rw [base_draw_shape hst hxw] at hx
      rw [base_draw_shape hsty0 hyw] at hy
      injection hx with hrx
      injection hy with hry
      rw [← hrx, ← hry]
      refine ⟨?_, ?_, ?_⟩
      · show (x.waste.reverse.drop x.drawStep) = (y.waste.reverse.drop y.drawStep)
        rw [hws, hds]
      · show ((x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card))
          = ((y.waste.reverse.take y.drawStep).reverse ++ ([] : List Card))
        rw [hws, hds]
      · rw [hds]
  | cons s ss =>
      have hxsn : x.stock ≠ [] := by rw [hst]; simp
      have hysn : y.stock ≠ [] := by rw [hsty, hst]; simp
      rw [plain_draw_shape hxsn] at hx
      rw [plain_draw_shape hysn] at hy
      injection hx with hrx
      injection hy with hry
      rw [← hrx, ← hry]
      refine ⟨?_, ?_, ?_⟩
      · show (x.stock.drop x.drawStep) = (y.stock.drop y.drawStep)
        rw [hss, hds]
      · show ((x.stock.take x.drawStep).reverse ++ x.waste)
          = ((y.stock.take y.drawStep).reverse ++ y.waste)
        rw [hss, hds, hws]
      · rw [hds]

/-! ## The deferred commutation

`canon_draw_comm : canon (stepDrawn st) = stepDrawn (canon st)` —
the padding-generation order-freedom lemma, probe-certified at
every zone shape (CanonDecompressProbe, family C) — is DEFERRED to
the follow-up row, with its working route recorded here so the
follow-up does not restart: prove the per-budget form
`canonAux_draw_comm : ∀ n st, canonAux n (stepDrawn st) =
stepDrawn (canonAux n st)` by induction on `n`, where the step case
needs only the ONE-STEP square `satStep (stepDrawn st) = stepDrawn
(satStep st)` — a record-level identity whose board half is the
landed `satStep_board_det` and whose pick half is the landed
`pick_congr` over the board equality `stepDrawn`-rows (`stepDraw_keep`
at firing, `rfl` when blocked); the zone halves are the banked
`stepDraw_keep` and the landing-determinism row `stepDraw_zone_det`
landed above.  The direct 53-budget assembly whnf-times out on the
unnormalized `canon` terms even with cheap precomputed fields (both
`maxRecDepth` and `maxHeartbeats` were raised); the inductive route
avoids the blowup because each step only ever compares ONE
`satStep` record.  The zone-determinism minis (`stepDraw_eq_none_iff`,
`stepDraw_zone_det`) are landed above for the follow-up to consume. -/

/-! ## The named residue -/

/-- **finalWiggle_reach — THE ONE named residue of this card.**

Final members of one macro class are connected by the three-letter
padding: `foundToTab` pull-downs, noreveal `tabToTab` slides, and
phase-aligned draws — the alphabet the refinements fixed after the
mid-flight corrections (the ONE-LETTER pure-pull form is refuted at
the residue-reloc exhibit: no pull fires there; the slide letter is
RESTORED as requirement by the exchlaw session's refuted pinch — at
their twin-kings cell the two saturated mates' images split the
found channel 13/12 vs 12/13, no virtual swap joins them, the only
reversible join is pulls + the slide itself, so slides do
irreducible padding work; the draw letter stays for the
phase-rotation mid-legs, the swRot wedge the class folds).

Probe record (CanonDecompressProbe, all gates green): the positive
family is live — the wiggle cube (two independent twin-host
residues, all four corners joined by noreveal slides, both leg
orders) and the worry-back bridge (a relocation requiring a
pulled-down substrate; the return's raise is the pull's exact undo,
reordered after unburying).  The general theorem is pinned here as
the card's named stub, in the house style.

Dependency notes for the follow-on:
* canlaw's twin-cargo pick-fork probe (two rung-ready twins, one
  contested cargo seat): if the verdict comes back a genuine
  confluence break, this stub gains a SIBLING named residue, and
  the mem_macro_iff/cone_image presentation targets must state
  which anchor-slice the cone covers.
* the V3 canonicalizer's contention probe (whether the exhibit's
  twin-host relocation is contention-driven) may literalize canon
  equality exactly where V2's non-uniqueness lived.
* the exchlaw twin-kings cell (probes/ExchCanLawProbe.lean) is the
  second required wiggle-fold test case beside the exhibit.
-/
theorem finalWiggle_reach {u v : State}
    (huwf : u.WF) (hvwf : v.WF) (hfin₁ : Final u) (hfin₂ : Final v)
    (hcls : SameMacroO u v) :
    ∃ σ, State.run u σ = some v ∧
      ∀ m ∈ σ, (∃ c b, m = Move.foundToTab c b) ∨
        (∃ c b, m = Move.tabToTab c b) ∨ m = Move.draw := by
  sorry

/-! ## The audit

Every landed head is checked: `[propext, Quot.sound]` at worst,
zero `Classical.choice`; the ONE named residue prints its
`sorryAx`.
-/

#print axioms stepDrawn
#print axioms stepDraw_keep
#print axioms drawLanding_waste_ne
#print axioms ZoneShape
#print axioms zoneShape_self
#print axioms drawPool_of_zoneShape
#print axioms le_of_zoneShape
#print axioms stock_ne_of_zoneShape
#print axioms zoneLeg_plain
#print axioms zoneLeg_short
#print axioms zoneLeg_pass
#print axioms satStep_zone_keep
#print axioms canonAux_zone_keep
#print axioms canon_zone_keep
#print axioms canRaiseB_congr
#print axioms pick_congr
#print axioms satStep_board_det
#print axioms canonAux_board_det
#print axioms canonBoard_det
#print axioms stepDraw_eq_none_iff
#print axioms stepDraw_zone_det
#print axioms lift_undo_pullW
#print axioms stackRun_return_pulls
#print axioms decompress_pulls
#print axioms finalWiggle_reach
