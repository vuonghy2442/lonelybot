import Orig2.Fork.ForkCrossSuit
import Orig2.ForkEqualRungMin

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Cert_CrossSuit_Board - the 17-letter cross-suit counterexample, transcribed

READ-ONLY scratch card (`Temp/`).  No source edit, no commit.  Zero `sorry`,
zero `Classical.choice`, zero `nativeDecide`.

`Temp/Search_Report.md` §2-§3 records a shortest witness play of length 17
between two `SSaturated`, equal-rung `(11,10,12,0)` states, carrying 8
cross-suit raise-before-pull pairs.  The pair `raise QD ... raise KS ;
slide KH -> empty 6 ; pull KS (inl 5)` is `CorridorClean` and `PullFree`.

This card transcribes the board and the play into the Lean model and refutes
`CrossSuit.CrossSuitCorridorResidual`, `CrossSuit.CrossSuitPureCorridorResidual`
and the exact target proposition, **given the minimality hypothesis**
`hmin : ∀ ρ', ShufflePlayW u ρ' v → 17 ≤ ρ'.length`.  The hypothesis is
discharged in `Temp/Cert_CrossSuit_Dist.lean` (the 2308-state distance
certificate) and consumed in `Orig2/ForkCertMain.lean`.

## The hidden bits are load-bearing

Piles 1 and 3 are HIDDEN-NONEMPTY (`KC`, `KD`, never revealed by a witness
letter).  `EqualRung.mkst` fixes piles 0-5 hidden-empty, so it cannot spell
these states; `mkstH` below carries the seven `(hidden, faceUp)` pairs.
-/

namespace Cert

open EqualRung (skey skey_inj eq_of_stepKey stepKey allMoves step_mem_allMoves)

/-! ## §1. The board -/

/-- Card literal. -/
def crd (s : Suit) (r : Rank) : Card := ⟨s, r⟩

/-- Hidden-aware state builder: four foundations, the seven `(hidden, faceUp)`
pairs, stock and waste (`drawStep = 1`). -/
def mkstH (fh fd fs fc : List Card) (h0 h1 h2 h3 h4 h5 h6 : List Card)
    (u0 u1 u2 u3 u4 u5 u6 : List Card) (stk wst : List Card) : State :=
  { found := fun s => match s with
      | .heart => fh
      | .diamond => fd
      | .spade => fs
      | .club => fc
    piles := fun a => match a with
      | .p0 => ⟨h0, u0⟩
      | .p1 => ⟨h1, u1⟩
      | .p2 => ⟨h2, u2⟩
      | .p3 => ⟨h3, u3⟩
      | .p4 => ⟨h4, u4⟩
      | .p5 => ⟨h5, u5⟩
      | .p6 => ⟨h6, u6⟩
    stock := stk
    waste := wst
    drawStep := 1 }

def s0 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten, crd .heart .jack] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack, crd .spade .queen] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .diamond .jack, crd .club .ten] [] [crd .club .five] [crd .heart .king] [crd .spade .king, crd .diamond .queen] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s1 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten, crd .heart .jack] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .diamond .jack, crd .club .ten] [] [crd .club .five] [crd .heart .king, crd .spade .queen] [crd .spade .king, crd .diamond .queen] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s2 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten, crd .heart .jack] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen] [] [crd .club .five] [crd .heart .king, crd .spade .queen, crd .diamond .jack, crd .club .ten] [crd .spade .king, crd .diamond .queen] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s3 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .heart .jack] [] [crd .club .five] [crd .heart .king, crd .spade .queen, crd .diamond .jack, crd .club .ten] [crd .spade .king, crd .diamond .queen] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s4 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .heart .jack, crd .club .ten] [] [crd .club .five] [crd .heart .king, crd .spade .queen, crd .diamond .jack] [crd .spade .king, crd .diamond .queen] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s5 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten, crd .diamond .jack] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .heart .jack, crd .club .ten] [] [crd .club .five] [crd .heart .king, crd .spade .queen] [crd .spade .king, crd .diamond .queen] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s6 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten, crd .diamond .jack] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack, crd .spade .queen] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .heart .jack, crd .club .ten] [] [crd .club .five] [crd .heart .king] [crd .spade .king, crd .diamond .queen] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s7 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten, crd .diamond .jack, crd .diamond .queen] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack, crd .spade .queen] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .heart .jack, crd .club .ten] [] [crd .club .five] [crd .heart .king] [crd .spade .king] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s8 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten, crd .diamond .jack, crd .diamond .queen] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack, crd .spade .queen, crd .spade .king] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .heart .jack, crd .club .ten] [] [crd .club .five] [crd .heart .king] [] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s9 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten, crd .diamond .jack, crd .diamond .queen] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack, crd .spade .queen, crd .spade .king] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .heart .jack, crd .club .ten] [] [crd .club .five] [] [crd .heart .king] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s10 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten, crd .diamond .jack, crd .diamond .queen] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack, crd .spade .queen] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .heart .jack, crd .club .ten] [] [crd .club .five] [crd .spade .king] [crd .heart .king] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s11 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten, crd .diamond .jack, crd .diamond .queen] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .heart .jack, crd .club .ten] [] [crd .club .five] [crd .spade .king] [crd .heart .king, crd .spade .queen] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s12 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten, crd .diamond .jack, crd .diamond .queen] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen] [] [crd .club .five] [crd .spade .king] [crd .heart .king, crd .spade .queen, crd .heart .jack, crd .club .ten] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s13 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten, crd .diamond .jack] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen] [] [crd .club .five] [crd .spade .king, crd .diamond .queen] [crd .heart .king, crd .spade .queen, crd .heart .jack, crd .club .ten] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s14 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .diamond .jack] [] [crd .club .five] [crd .spade .king, crd .diamond .queen] [crd .heart .king, crd .spade .queen, crd .heart .jack, crd .club .ten] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s15 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .diamond .jack, crd .club .ten] [] [crd .club .five] [crd .spade .king, crd .diamond .queen] [crd .heart .king, crd .spade .queen, crd .heart .jack] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s16 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten, crd .heart .jack] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .diamond .jack, crd .club .ten] [] [crd .club .five] [crd .spade .king, crd .diamond .queen] [crd .heart .king, crd .spade .queen] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

def s17 : State :=
  mkstH [crd .heart .ace, crd .heart .two, crd .heart .three, crd .heart .four, crd .heart .five, crd .heart .six, crd .heart .seven, crd .heart .eight, crd .heart .nine, crd .heart .ten, crd .heart .jack] [crd .diamond .ace, crd .diamond .two, crd .diamond .three, crd .diamond .four, crd .diamond .five, crd .diamond .six, crd .diamond .seven, crd .diamond .eight, crd .diamond .nine, crd .diamond .ten] [crd .spade .ace, crd .spade .two, crd .spade .three, crd .spade .four, crd .spade .five, crd .spade .six, crd .spade .seven, crd .spade .eight, crd .spade .nine, crd .spade .ten, crd .spade .jack, crd .spade .queen] [] [] [crd .club .king] [] [crd .diamond .king] [] [] [] [crd .club .seven] [] [crd .club .queen, crd .diamond .jack, crd .club .ten] [] [crd .club .five] [crd .spade .king, crd .diamond .queen] [crd .heart .king] [crd .club .ace, crd .club .two, crd .club .three, crd .club .four, crd .club .six, crd .club .eight, crd .club .nine, crd .club .jack, crd .heart .queen] []

/-- **`u`** - the start state. -/
def u : State := s0

/-- **`v`** - the end state (`p5`/`p6` exchanged). -/
def v : State := s17

/-! ### §1a. The seventeen letters -/

def m0 : Move := Move.foundToTab (crd .spade .queen) ((Sum.inr (crd .heart .king)))

def m1 : Move := Move.tabToTab (crd .diamond .jack) ((Sum.inr (crd .spade .queen)))

def m2 : Move := Move.foundToTab (crd .heart .jack) ((Sum.inr (crd .club .queen)))

def m3 : Move := Move.tabToTab (crd .club .ten) ((Sum.inr (crd .heart .jack)))

def m4 : Move := Move.tabToFound (crd .diamond .jack)

def m5 : Move := Move.tabToFound (crd .spade .queen)

def m6 : Move := Move.tabToFound (crd .diamond .queen)

def m7 : Move := Move.tabToFound (crd .spade .king)

def m8 : Move := Move.tabToTab (crd .heart .king) ((Sum.inl Anchor.p6))

def m9 : Move := Move.foundToTab (crd .spade .king) ((Sum.inl Anchor.p5))

def m10 : Move := Move.foundToTab (crd .spade .queen) ((Sum.inr (crd .heart .king)))

def m11 : Move := Move.tabToTab (crd .heart .jack) ((Sum.inr (crd .spade .queen)))

def m12 : Move := Move.foundToTab (crd .diamond .queen) ((Sum.inr (crd .spade .king)))

def m13 : Move := Move.foundToTab (crd .diamond .jack) ((Sum.inr (crd .club .queen)))

def m14 : Move := Move.tabToTab (crd .club .ten) ((Sum.inr (crd .diamond .jack)))

def m15 : Move := Move.tabToFound (crd .heart .jack)

def m16 : Move := Move.tabToFound (crd .spade .queen)


/-- **The witness play.** -/
def rho : List Move :=
  [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16]


/-! ### §1b. The seventeen steps -/


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

theorem step13 : State.step s13 m13 = some s14 := eq_of_stepKey (by decide)

theorem step14 : State.step s14 m14 = some s15 := eq_of_stepKey (by decide)

theorem step15 : State.step s15 m15 = some s16 := eq_of_stepKey (by decide)

theorem step16 : State.step s16 m16 = some s17 := eq_of_stepKey (by decide)


/-! ## §2. Well-formedness -/

theorem s0_wf : s0.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro s
    cases s with
    | heart => exact ⟨11, by decide⟩
    | diamond => exact ⟨10, by decide⟩
    | spade => exact ⟨12, by decide⟩
    | club => exact ⟨0, by decide⟩
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

theorem wf13 : s13.WF := step_wf wf12 step12

theorem wf14 : s14.WF := step_wf wf13 step13

theorem wf15 : s15.WF := step_wf wf14 step14

theorem wf16 : s16.WF := step_wf wf15 step15

theorem wf17 : s17.WF := step_wf wf16 step16


theorem u_wf : u.WF := s0_wf
theorem v_wf : v.WF := wf17


/-! ## §3. Saturation (both cargo fibres are singletons) -/


theorem s0_sat : SSaturated s0 := by
  intro c hc
  have hb : canRaiseSB s0 c = true := (canRaiseSB_iff s0_wf).mpr hc
  have hall : (Card.universe.all (fun c => !(canRaiseSB s0 c))) = true := by decide
  have hfalse : (!(canRaiseSB s0 c)) = true :=
    (List.all_eq_true.mp hall) c (Card.mem_universe c)
  rw [hb] at hfalse
  exact absurd hfalse (by simp)


theorem s17_sat : SSaturated s17 := by
  intro c hc
  have hb : canRaiseSB s17 c = true := (canRaiseSB_iff wf17).mpr hc
  have hall : (Card.universe.all (fun c => !(canRaiseSB s17 c))) = true := by decide
  have hfalse : (!(canRaiseSB s17 c)) = true :=
    (List.all_eq_true.mp hall) c (Card.mem_universe c)
  rw [hb] at hfalse
  exact absurd hfalse (by simp)


theorem u_sat : SSaturated u := s0_sat
theorem v_sat : SSaturated v := s17_sat


/-! ## §4. The reversibility of every letter and the play -/


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

theorem rev13 : reversibleAtW s13 m13 :=
  (reversibleOf_iff_reversibleAtW wf13 m13).mp (by decide)

theorem rev14 : reversibleAtW s14 m14 :=
  (reversibleOf_iff_reversibleAtW wf14 m14).mp (by decide)

theorem rev15 : reversibleAtW s15 m15 :=
  (reversibleOf_iff_reversibleAtW wf15 m15).mp (by decide)

theorem rev16 : reversibleAtW s16 m16 :=
  (reversibleOf_iff_reversibleAtW wf16 m16).mp (by decide)


/-- **THE SEVENTEEN-LETTER WITNESS PLAY `u → v`.** -/
theorem play : ShufflePlayW u rho v := by
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

  refine Walk.cons rev10 step10 ?_

  refine Walk.cons rev11 step11 ?_

  refine Walk.cons rev12 step12 ?_

  refine Walk.cons rev13 step13 ?_

  refine Walk.cons rev14 step14 ?_

  refine Walk.cons rev15 step15 ?_

  refine Walk.cons rev16 step16 ?_

  exact Walk.nil s17


theorem rho_length : rho.length = 17 := by decide


/-! ## §5. The clean cross-suit corridor -/

/-- The raised card of the corridor (`raise QD`, letter 6). -/
def QD : Card := crd .diamond .queen
/-- The pulled card of the corridor (`pull KS`, letter 9). -/
def KS : Card := crd .spade .king
/-- The landing base of the pull (`inl p5` - the window empties pile 5). -/
def p5b : Base := Sum.inl Anchor.p5

def pre : List Move := [m0, m1, m2, m3, m4, m5]
/-- The corridor: `raise KS ; slide KH -> empty 6`. -/
def gam : List Move := [m7, m8]
def tail : List Move := [m10, m11, m12, m13, m14, m15, m16]

/-- **THE SPLIT.** -/
theorem rho_eq_split :
    rho = pre ++ Move.tabToFound QD :: gam ++ Move.foundToTab KS p5b :: tail := rfl

theorem QD_KS_suits : QD.suit ≠ KS.suit := by decide

/-- **THE CORRIDOR IS CLEAN** (its only raise is of the pull's suit `S`, and it
carries no pull at all). -/
theorem clean_gam : CrossSuit.CorridorClean gam QD KS := by
  constructor
  · intro e he
    have h1 : Move.tabToFound e = m7 ∨ Move.tabToFound e = m8 := by
      simpa [gam] using he
    rcases h1 with h | h
    · have h2 : Move.tabToFound e = Move.tabToFound KS := by
        simpa [m7, KS] using h
      injection h2 with heq
      subst heq
      rfl
    · exact absurd h (by simp [m8])
  · intro e b he
    have h1 : Move.foundToTab e b = m7 ∨ Move.foundToTab e b = m8 := by
      simpa [gam] using he
    rcases h1 with h | h
    · exact absurd h (by simp [m7])
    · exact absurd h (by simp [m8])

/-- **THE CORRIDOR PULLS NOTHING.** -/
theorem pullFree_gam : CrossSuit.PullFree gam := by
  intro e b he
  have h1 : Move.foundToTab e b = m7 ∨ Move.foundToTab e b = m8 := by
    simpa [gam] using he
  rcases h1 with h | h
  · exact absurd h (by simp [m7])
  · exact absurd h (by simp [m8])

/-! ## §6. The target proposition, and the refutations from minimality -/

/-- **THE EXACT TARGET** (the conclusion of `CrossSuit.crossSuitVacuity`,
without the residual hypothesis). -/
def CrossSuitVacuityTarget : Prop :=
  ∀ (u v : State) (ρ : List Move),
    u.WF → SSaturated u → SSaturated v → ShufflePlayW u ρ v →
    (∀ ρ' : List Move, ShufflePlayW u ρ' v → ρ.length ≤ ρ'.length) →
    ∀ (i j : Nat) (c d : Card) (b : Base), i < j →
      ρ[i]? = some (Move.tabToFound c) →
      ρ[j]? = some (Move.foundToTab d b) → c.suit ≠ d.suit → False

theorem rho6 : rho[6]? = some (Move.tabToFound QD) := by decide
theorem rho9 : rho[9]? = some (Move.foundToTab KS p5b) := by decide

/-- **`CrossSuitCorridorResidual` IS FALSE** (given the distance bound). -/
theorem corridorResidual_false_of_min
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → 17 ≤ ρ'.length) :
    ¬ CrossSuit.CrossSuitCorridorResidual := by
  intro hres
  have hlen : ∀ ρ' : List Move, ShufflePlayW u ρ' v → rho.length ≤ ρ'.length := by
    intro ρ' h'
    rw [rho_length]
    exact hmin ρ' h'
  exact hres u v rho pre gam tail QD KS p5b u_wf u_sat v_sat play hlen
    rho_eq_split QD_KS_suits clean_gam

/-- **`CrossSuitPureCorridorResidual` IS FALSE** (given the distance bound). -/
theorem pureResidual_false_of_min
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → 17 ≤ ρ'.length) :
    ¬ CrossSuit.CrossSuitPureCorridorResidual := by
  intro hres
  have hlen : ∀ ρ' : List Move, ShufflePlayW u ρ' v → rho.length ≤ ρ'.length := by
    intro ρ' h'
    rw [rho_length]
    exact hmin ρ' h'
  exact hres u v rho pre gam tail QD KS p5b u_wf u_sat v_sat play hlen
    rho_eq_split QD_KS_suits clean_gam pullFree_gam

/-- **THE TARGET PROPOSITION IS FALSE** (given the distance bound). -/
theorem vacuityTarget_false_of_min
    (hmin : ∀ ρ' : List Move, ShufflePlayW u ρ' v → 17 ≤ ρ'.length) :
    ¬ CrossSuitVacuityTarget := by
  intro hT
  have hlen : ∀ ρ' : List Move, ShufflePlayW u ρ' v → rho.length ≤ ρ'.length := by
    intro ρ' h'
    rw [rho_length]
    exact hmin ρ' h'
  exact hT u v rho u_wf u_sat v_sat play hlen 6 9 QD KS p5b
    (by decide) rho6 rho9 QD_KS_suits

end Cert
