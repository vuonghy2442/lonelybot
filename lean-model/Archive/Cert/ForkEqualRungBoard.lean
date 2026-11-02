import Orig2.Fork.Local.ForkDirect
import Orig2.Substrate.CargoRaise

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# EqualRung_Board — the `F_t1_runshiftp2` equal-rung 13-move witness

READ-ONLY scratch card.  No source file is modified; nothing is committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery in
`Orig2/ForkEqualRungMin.lean`.

## What this card does

`Temp/Crack_Report.md` §4b records a probe-exact, unit-shortest witness play
of length **13** between two `SSaturated` states whose rung vectors are
**equal** `(4,0,3,2)`, containing a genuine same-card relocation (`5C` raised
off `6H`, later pulled onto `6D`).  The probe side is
`Temp/Crack_witness.py`; the board is `F_t1_runshiftp2`
(`Temp/SatDiffer_Second_analyze.py`), component 392 states.

This card transcribes the board and the play into the Lean model:

* the 14 states `s0 … s13` along the play (`s0 = u`, `s13 = v`);
* the 13 letters `m0 … m12`;
* `play : ShufflePlayW s0 rho s13`, every leg reversibility-certified;
* `s0_wf`, `s13_wf`, `s0_sat`, `s13_sat`;
* the equal rung vector (`rung_eq`), and `s0 ≠ s13`.

Minimality (no witness play of length `< 13`) is discharged in
`Orig2/ForkEqualRungDist.lean` (the 392-state distance certificate); the
`SplitHyp` instance and the unconditional refutation of `Direct.MountainAtSplits`
live in `Orig2/ForkEqualRungMain.lean`.

## The state-key `skey`

`State` has function fields, so it has no `DecidableEq`.  `skey` is a
19-field list-of-card-lists key (plus `drawStep`) that *is* injective
(`skey_inj`), which lets (a) every `State.step` equation be proved by
`decide` on keys, and (b) the bounded BFS of the next card dedup its
visited set soundly.
-/

namespace EqualRung

/-! ## §1. The board -/

/-- Card literal. -/
def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/-- The 30-card inert hidden deck sitting under `p6` in every state. -/
def deck : List Card :=
  [crd .diamond .ace, crd .diamond .three, crd .spade .four, crd .diamond .five,
   crd .spade .six, crd .heart .seven, crd .club .seven, crd .heart .eight,
   crd .club .eight, crd .heart .nine, crd .diamond .nine, crd .spade .nine,
   crd .club .nine, crd .heart .ten, crd .diamond .ten, crd .spade .ten,
   crd .club .ten, crd .heart .jack, crd .diamond .jack, crd .spade .jack,
   crd .club .jack, crd .heart .queen, crd .diamond .queen, crd .spade .queen,
   crd .club .queen, crd .heart .king, crd .diamond .king, crd .spade .king,
   crd .club .king]

/-- State builder: four foundations and the six live piles; `p6` is the inert
hidden deck and the stock/waste are empty (`drawStep = 1`). -/
def mkst (fh fd fs fc : List Card) (p0 p1 p2 p3 p4 p5 : List Card) : State :=
  { found := fun s => match s with
      | .heart => fh
      | .diamond => fd
      | .spade => fs
      | .club => fc
    piles := fun a => match a with
      | .p0 => { hidden := [], faceUp := p0 }
      | .p1 => { hidden := [], faceUp := p1 }
      | .p2 => { hidden := [], faceUp := p2 }
      | .p3 => { hidden := [], faceUp := p3 }
      | .p4 => { hidden := [], faceUp := p4 }
      | .p5 => { hidden := [], faceUp := p5 }
      | .p6 => { hidden := deck, faceUp := [] }
    stock := []
    waste := []
    drawStep := 1 }

/-! ### §1a. The fourteen states along the play -/

/-- **`u`** — hearts `A..4`, spades `A..3`, clubs `A,2` founded. -/
def s0 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four] []
  [crd .spade .ace, crd .spade .two, crd .spade .three]
  [crd .club .ace, crd .club .two]
  [crd .diamond .four, crd .club .three, crd .diamond .two]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .spade .five]
  [crd .heart .six, crd .club .five]
  [crd .club .six, crd .heart .five, crd .club .four]
  [crd .spade .eight, crd .diamond .seven]

def s1 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two, crd .spade .three]
  [crd .club .ace, crd .club .two]
  [crd .diamond .four, crd .club .three, crd .diamond .two]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .spade .five, crd .heart .four]
  [crd .heart .six, crd .club .five]
  [crd .club .six, crd .heart .five, crd .club .four]
  [crd .spade .eight, crd .diamond .seven]

def s2 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two] [crd .club .ace, crd .club .two]
  [crd .diamond .four, crd .club .three, crd .diamond .two]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .spade .five, crd .heart .four, crd .spade .three]
  [crd .heart .six, crd .club .five]
  [crd .club .six, crd .heart .five, crd .club .four]
  [crd .spade .eight, crd .diamond .seven]

def s3 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two] [crd .club .ace, crd .club .two]
  [crd .diamond .four, crd .club .three]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .spade .five, crd .heart .four, crd .spade .three,
   crd .diamond .two]
  [crd .heart .six, crd .club .five]
  [crd .club .six, crd .heart .five, crd .club .four]
  [crd .spade .eight, crd .diamond .seven]

def s4 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two]
  [crd .club .ace, crd .club .two, crd .club .three]
  [crd .diamond .four]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .spade .five, crd .heart .four, crd .spade .three,
   crd .diamond .two]
  [crd .heart .six, crd .club .five]
  [crd .club .six, crd .heart .five, crd .club .four]
  [crd .spade .eight, crd .diamond .seven]

def s5 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two]
  [crd .club .ace, crd .club .two, crd .club .three, crd .club .four]
  [crd .diamond .four]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .spade .five, crd .heart .four, crd .spade .three,
   crd .diamond .two]
  [crd .heart .six, crd .club .five]
  [crd .club .six, crd .heart .five]
  [crd .spade .eight, crd .diamond .seven]

def s6 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two]
  [crd .club .ace, crd .club .two, crd .club .three, crd .club .four,
   crd .club .five]
  [crd .diamond .four]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .spade .five, crd .heart .four, crd .spade .three,
   crd .diamond .two]
  [crd .heart .six]
  [crd .club .six, crd .heart .five]
  [crd .spade .eight, crd .diamond .seven]

def s7 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two]
  [crd .club .ace, crd .club .two, crd .club .three, crd .club .four,
   crd .club .five]
  [crd .diamond .four]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six]
  [crd .heart .six, crd .spade .five, crd .heart .four, crd .spade .three,
   crd .diamond .two]
  [crd .club .six, crd .heart .five]
  [crd .spade .eight, crd .diamond .seven]

def s8 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two]
  [crd .club .ace, crd .club .two, crd .club .three, crd .club .four]
  [crd .diamond .four]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .club .five]
  [crd .heart .six, crd .spade .five, crd .heart .four, crd .spade .three,
   crd .diamond .two]
  [crd .club .six, crd .heart .five]
  [crd .spade .eight, crd .diamond .seven]

def s9 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two]
  [crd .club .ace, crd .club .two, crd .club .three]
  [crd .diamond .four]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .club .five]
  [crd .heart .six, crd .spade .five, crd .heart .four, crd .spade .three,
   crd .diamond .two]
  [crd .club .six, crd .heart .five, crd .club .four]
  [crd .spade .eight, crd .diamond .seven]

def s10 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two] [crd .club .ace, crd .club .two]
  [crd .diamond .four, crd .club .three]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .club .five]
  [crd .heart .six, crd .spade .five, crd .heart .four, crd .spade .three,
   crd .diamond .two]
  [crd .club .six, crd .heart .five, crd .club .four]
  [crd .spade .eight, crd .diamond .seven]

def s11 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two] [crd .club .ace, crd .club .two]
  [crd .diamond .four, crd .club .three, crd .diamond .two]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .club .five]
  [crd .heart .six, crd .spade .five, crd .heart .four, crd .spade .three]
  [crd .club .six, crd .heart .five, crd .club .four]
  [crd .spade .eight, crd .diamond .seven]

def s12 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three] []
  [crd .spade .ace, crd .spade .two, crd .spade .three]
  [crd .club .ace, crd .club .two]
  [crd .diamond .four, crd .club .three, crd .diamond .two]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .club .five]
  [crd .heart .six, crd .spade .five, crd .heart .four]
  [crd .club .six, crd .heart .five, crd .club .four]
  [crd .spade .eight, crd .diamond .seven]

/-- **`v`** — the same foundations as `u`; `5S`/`5C` swapped between `p2`/`p3`. -/
def s13 : State := mkst
  [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four] []
  [crd .spade .ace, crd .spade .two, crd .spade .three]
  [crd .club .ace, crd .club .two]
  [crd .diamond .four, crd .club .three, crd .diamond .two]
  [crd .diamond .eight, crd .spade .seven]
  [crd .diamond .six, crd .club .five]
  [crd .heart .six, crd .spade .five]
  [crd .club .six, crd .heart .five, crd .club .four]
  [crd .spade .eight, crd .diamond .seven]

/-! ### §1b. The thirteen letters -/

def m0 : Move := Move.foundToTab (crd .heart .four) (Sum.inr (crd .spade .five))
def m1 : Move := Move.foundToTab (crd .spade .three) (Sum.inr (crd .heart .four))
def m2 : Move := Move.tabToTab (crd .diamond .two) (Sum.inr (crd .spade .three))
def m3 : Move := Move.tabToFound (crd .club .three)
def m4 : Move := Move.tabToFound (crd .club .four)
def m5 : Move := Move.tabToFound (crd .club .five)
def m6 : Move := Move.tabToTab (crd .spade .five) (Sum.inr (crd .heart .six))
def m7 : Move := Move.foundToTab (crd .club .five) (Sum.inr (crd .diamond .six))
def m8 : Move := Move.foundToTab (crd .club .four) (Sum.inr (crd .heart .five))
def m9 : Move := Move.foundToTab (crd .club .three) (Sum.inr (crd .diamond .four))
def m10 : Move := Move.tabToTab (crd .diamond .two) (Sum.inr (crd .club .three))
def m11 : Move := Move.tabToFound (crd .spade .three)
def m12 : Move := Move.tabToFound (crd .heart .four)

/-- **The witness play.** -/
def rho : List Move :=
  [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12]

/-! ## §2. The state key -/

/-- Nineteen card-list fields plus `drawStep`: injective on `State`. -/
def skey (st : State) : List (List Card) × Nat :=
  ([st.found .heart, st.found .diamond, st.found .spade, st.found .club,
    (st.piles .p0).hidden, (st.piles .p0).faceUp,
    (st.piles .p1).hidden, (st.piles .p1).faceUp,
    (st.piles .p2).hidden, (st.piles .p2).faceUp,
    (st.piles .p3).hidden, (st.piles .p3).faceUp,
    (st.piles .p4).hidden, (st.piles .p4).faceUp,
    (st.piles .p5).hidden, (st.piles .p5).faceUp,
    (st.piles .p6).hidden, (st.piles .p6).faceUp,
    st.stock, st.waste], st.drawStep)

/-- **`skey` IS INJECTIVE.** -/
theorem skey_inj {x y : State} (h : skey x = skey y) : x = y := by
  simp only [skey, Prod.mk.injEq] at h
  obtain ⟨hk, hD⟩ := h
  have g : ∀ i : Nat, ((skey x).1.drop i).head? = ((skey y).1.drop i).head? :=
    fun i => congrArg (fun l => (l.drop i).head?) hk
  have h1 : x.found .heart = y.found .heart := by simpa [skey] using g 0
  have h2 : x.found .diamond = y.found .diamond := by simpa [skey] using g 1
  have h3 : x.found .spade = y.found .spade := by simpa [skey] using g 2
  have h4 : x.found .club = y.found .club := by simpa [skey] using g 3
  have h5 : (x.piles .p0).hidden = (y.piles .p0).hidden := by simpa [skey] using g 4
  have h6 : (x.piles .p0).faceUp = (y.piles .p0).faceUp := by simpa [skey] using g 5
  have h7 : (x.piles .p1).hidden = (y.piles .p1).hidden := by simpa [skey] using g 6
  have h8 : (x.piles .p1).faceUp = (y.piles .p1).faceUp := by simpa [skey] using g 7
  have h9 : (x.piles .p2).hidden = (y.piles .p2).hidden := by simpa [skey] using g 8
  have h10 : (x.piles .p2).faceUp = (y.piles .p2).faceUp := by simpa [skey] using g 9
  have h11 : (x.piles .p3).hidden = (y.piles .p3).hidden := by simpa [skey] using g 10
  have h12 : (x.piles .p3).faceUp = (y.piles .p3).faceUp := by simpa [skey] using g 11
  have h13 : (x.piles .p4).hidden = (y.piles .p4).hidden := by simpa [skey] using g 12
  have h14 : (x.piles .p4).faceUp = (y.piles .p4).faceUp := by simpa [skey] using g 13
  have h15 : (x.piles .p5).hidden = (y.piles .p5).hidden := by simpa [skey] using g 14
  have h16 : (x.piles .p5).faceUp = (y.piles .p5).faceUp := by simpa [skey] using g 15
  have h17 : (x.piles .p6).hidden = (y.piles .p6).hidden := by simpa [skey] using g 16
  have h18 : (x.piles .p6).faceUp = (y.piles .p6).faceUp := by simpa [skey] using g 17
  have h19 : x.stock = y.stock := by simpa [skey] using g 18
  have h20 : x.waste = y.waste := by simpa [skey] using g 19
  refine State.ext ?_ ?_ h19 h20 hD
  · funext s
    cases s with
    | heart => exact h1
    | diamond => exact h2
    | spade => exact h3
    | club => exact h4
  · funext a
    cases a with
    | p0 => exact Pile.ext h5 h6
    | p1 => exact Pile.ext h7 h8
    | p2 => exact Pile.ext h9 h10
    | p3 => exact Pile.ext h11 h12
    | p4 => exact Pile.ext h13 h14
    | p5 => exact Pile.ext h15 h16
    | p6 => exact Pile.ext h17 h18

/-- A `decide`-able step equation at the key level. -/
def stepKey (st : State) (m : Move) (t : State) : Bool :=
  decide (Option.map skey (State.step st m) = some (skey t))

theorem eq_of_stepKey {st t : State} {m : Move} (h : stepKey st m t = true) :
    State.step st m = some t := by
  have hh : Option.map skey (State.step st m) = some (skey t) := of_decide_eq_true h
  cases hs : State.step st m with
  | none => rw [hs] at hh; exact absurd hh (by simp)
  | some u =>
      rw [hs] at hh
      have hu : skey u = skey t := by
        simpa using Option.some.inj hh
      rw [skey_inj hu]

/-! ## §3. The thirteen steps -/

theorem step0 : State.step s0 m0 = some s1 := eq_of_stepKey (by decide)
theorem step1 : State.step s1 m1 = some s2 := eq_of_stepKey (by decide)
theorem step2 : State.step s2 m2 = some s3 := eq_of_stepKey (by decide)
theorem step3 : State.step s3 m3 = some s4 := eq_of_stepKey (by decide)
theorem step4 : State.step s4 m4 = some s5 := eq_of_stepKey (by decide)
theorem step5 : State.step s5 m5 = some s6 := eq_of_stepKey (by decide)
theorem step6 : State.step s6 m6 = some s7 := eq_of_stepKey (by decide)
theorem step7 : State.step s7 m7 = some s8 := eq_of_stepKey (by decide)
theorem step8 : State.step s8 m8 = some s9 := eq_of_stepKey (by decide)
theorem step9 : State.step s9 m9 = some s10 := eq_of_stepKey (by decide)
theorem step10 : State.step s10 m10 = some s11 := eq_of_stepKey (by decide)
theorem step11 : State.step s11 m11 = some s12 := eq_of_stepKey (by decide)
theorem step12 : State.step s12 m12 = some s13 := eq_of_stepKey (by decide)

/-! ## §4. Well-formedness and reversibility -/

theorem s0_wf : s0.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨4, by decide⟩
    | diamond => exact ⟨0, by decide⟩
    | spade => exact ⟨3, by decide⟩
    | club => exact ⟨2, by decide⟩
  · intro a; cases a <;> decide
  · intro c _; rcases c with ⟨s, r⟩; cases s <;> cases r <;> decide

theorem wf1 : s1.WF := step_wf s0_wf step0
theorem wf2 : s2.WF := step_wf wf1 step1
theorem wf3 : s3.WF := step_wf wf2 step2
theorem wf4 : s4.WF := step_wf wf3 step3
theorem wf5 : s5.WF := step_wf wf4 step4
theorem wf6 : s6.WF := step_wf wf5 step5
theorem wf7 : s7.WF := step_wf wf6 step6
theorem wf8 : s8.WF := step_wf wf7 step7
theorem wf9 : s9.WF := step_wf wf8 step8
theorem wf10 : s10.WF := step_wf wf9 step9
theorem wf11 : s11.WF := step_wf wf10 step10
theorem wf12 : s12.WF := step_wf wf11 step11
theorem s13_wf : s13.WF := step_wf wf12 step12

theorem rev0 : reversibleAtW s0 m0 :=
  (reversibleOf_iff_reversibleAtW s0_wf m0).mp (by decide)
theorem rev1 : reversibleAtW s1 m1 :=
  (reversibleOf_iff_reversibleAtW wf1 m1).mp (by decide)
theorem rev2 : reversibleAtW s2 m2 :=
  (reversibleOf_iff_reversibleAtW wf2 m2).mp (by decide)
theorem rev3 : reversibleAtW s3 m3 :=
  (reversibleOf_iff_reversibleAtW wf3 m3).mp (by decide)
theorem rev4 : reversibleAtW s4 m4 :=
  (reversibleOf_iff_reversibleAtW wf4 m4).mp (by decide)
theorem rev5 : reversibleAtW s5 m5 :=
  (reversibleOf_iff_reversibleAtW wf5 m5).mp (by decide)
theorem rev6 : reversibleAtW s6 m6 :=
  (reversibleOf_iff_reversibleAtW wf6 m6).mp (by decide)
theorem rev7 : reversibleAtW s7 m7 :=
  (reversibleOf_iff_reversibleAtW wf7 m7).mp (by decide)
theorem rev8 : reversibleAtW s8 m8 :=
  (reversibleOf_iff_reversibleAtW wf8 m8).mp (by decide)
theorem rev9 : reversibleAtW s9 m9 :=
  (reversibleOf_iff_reversibleAtW wf9 m9).mp (by decide)
theorem rev10 : reversibleAtW s10 m10 :=
  (reversibleOf_iff_reversibleAtW wf10 m10).mp (by decide)
theorem rev11 : reversibleAtW s11 m11 :=
  (reversibleOf_iff_reversibleAtW wf11 m11).mp (by decide)
theorem rev12 : reversibleAtW s12 m12 :=
  (reversibleOf_iff_reversibleAtW wf12 m12).mp (by decide)

/-! ## §5. The split data and the witness plays -/

/-- The pull card of the split (`3C`, raised at move 3, pulled at move 9). -/
def cpc : Card := crd .club .three
/-- Its landing base at move 9 (`4D`). -/
def cb : Base := Sum.inr (crd .diamond .four)
/-- The raise card of the right leg (`3S`, move 11). -/
def drc : Card := crd .spade .three

theorem cpc_eq_m9 : Move.foundToTab cpc cb = m9 := rfl
theorem drc_eq_m11 : Move.tabToFound drc = m11 := rfl

def pre : List Move := [m0, m1, m2, m3, m4, m5, m6, m7, m8]
def post : List Move := [m10]
def tail : List Move := [m12]
def left : List Move := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10]
def right : List Move := [m11, m12]

theorem rho_eq : rho = left ++ right := rfl
theorem left_eq : left = pre ++ Move.foundToTab cpc cb :: post := rfl
theorem right_eq : right = Move.tabToFound drc :: tail := rfl

theorem post_free : ∀ m ∈ post, ValleyElim.FreeMove m := by
  intro m hm
  have hm' : m = m10 := by
    have : post = [m10] := rfl
    rw [this] at hm
    simpa using hm
  subst hm'
  exact ValleyElim.free_slide (crd .diamond .two) (Sum.inr (crd .club .three))

theorem play_left : ShufflePlayW s0 left s11 := by
  refine Walk.cons rev0 step0 ?_
  refine Walk.cons rev1 step1 ?_
  refine Walk.cons rev2 step2 ?_
  refine Walk.cons rev3 step3 ?_
  refine Walk.cons rev4 step4 ?_
  refine Walk.cons rev5 step5 ?_
  refine Walk.cons rev6 step6 ?_
  refine Walk.cons rev7 step7 ?_
  refine Walk.cons rev8 step8 ?_
  refine Walk.cons rev9 step9 ?_
  exact Walk.cons rev10 step10 (Walk.nil s11)

theorem play_right : ShufflePlayW s11 right s13 := by
  refine Walk.cons rev11 step11 ?_
  exact Walk.cons rev12 step12 (Walk.nil s13)

/-- **THE 13-LETTER WITNESS PLAY `u → v`.** -/
theorem play : ShufflePlayW s0 rho s13 := by
  have h := ShufflePlayW_append play_left play_right
  rwa [show left ++ right = rho from rho_eq.symm] at h

/-! ## §6. Saturation and the equal rung vector -/

theorem s0_sat : SSaturated s0 := by
  intro c hc
  have hb : canRaiseSB s0 c = true := (canRaiseSB_iff s0_wf).mpr hc
  have hall : (Card.universe.all (fun c => !(canRaiseSB s0 c))) = true := by decide
  have hfalse : (!(canRaiseSB s0 c)) = true :=
    (List.all_eq_true.mp hall) c (Card.mem_universe c)
  rw [hb] at hfalse
  exact absurd hfalse (by simp)

theorem s13_sat : SSaturated s13 := by
  intro c hc
  have hb : canRaiseSB s13 c = true := (canRaiseSB_iff s13_wf).mpr hc
  have hall : (Card.universe.all (fun c => !(canRaiseSB s13 c))) = true := by decide
  have hfalse : (!(canRaiseSB s13 c)) = true :=
    (List.all_eq_true.mp hall) c (Card.mem_universe c)
  rw [hb] at hfalse
  exact absurd hfalse (by simp)

theorem rung_u_heart : rungAt s0 .heart = 4 := rfl
theorem rung_u_diamond : rungAt s0 .diamond = 0 := rfl
theorem rung_u_spade : rungAt s0 .spade = 3 := rfl
theorem rung_u_club : rungAt s0 .club = 2 := rfl
theorem rung_v_heart : rungAt s13 .heart = 4 := rfl
theorem rung_v_diamond : rungAt s13 .diamond = 0 := rfl
theorem rung_v_spade : rungAt s13 .spade = 3 := rfl
theorem rung_v_club : rungAt s13 .club = 2 := rfl

/-- **THE ENDPOINTS HAVE THE SAME RUNG VECTOR `(4,0,3,2)`.** -/
theorem rung_eq : ∀ σ : Suit, rungAt s0 σ = rungAt s13 σ := by
  intro σ; cases σ <;> rfl

theorem s0_ne_s13 : s0 ≠ s13 := by
  intro h
  have h1 : (s0.piles .p2).faceUp = (s13.piles .p2).faceUp := by rw [h]
  have h2 : (s0.piles .p2).faceUp = [crd .diamond .six, crd .spade .five] := rfl
  have h3 : (s13.piles .p2).faceUp = [crd .diamond .six, crd .club .five] := rfl
  rw [h2, h3] at h1
  exact absurd h1 (by decide)

end EqualRung
