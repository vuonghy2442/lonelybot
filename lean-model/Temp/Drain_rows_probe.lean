import Orig2.Fork.Split.ForkDrainClose
import Orig2.Fork.Class.ForkPairRung

set_option autoImplicit false

def fndOf (n : Suit → Nat) : Suit → List Card := fun s => (Suit.upCards s).take (n s)

def stockOf (n : Suit → Nat) (tab : List Card) : List Card :=
  Card.universe.filter (fun c =>
    !(decide (c ∈ tab)) && Suit.all.all (fun s => !(decide (c ∈ (Suit.upCards s).take (n s)))))

def fd : Suit → Nat := fun s =>
  match s with | .spade => 11 | .heart => 11 | .diamond => 0 | .club => 11

def qS : Card := ⟨.spade, .queen⟩
def qC : Card := ⟨.club, .queen⟩
def kH : Card := ⟨.heart, .king⟩
def jD : Card := ⟨.diamond, .jack⟩
def kD : Card := ⟨.diamond, .king⟩

def tabD : List Card := [kH, qC, jD, kD, qS]

def sD : State where
  found := fndOf fd
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [kH, qC, jD]⟩
    | .p1 => ⟨[], [kD, qS]⟩
    | _ => ⟨[], []⟩
  stock := stockOf fd tabD
  waste := []
  drawStep := 1

#eval ("nextUp qS", sD.nextUp qS)
#eval ("nextUp qC", sD.nextUp qC)
#eval ("pileOfTop qS", sD.pileOfTop qS)
#eval ("pileHolding qS", sD.pileHolding qS)
#eval ("canRaiseSB qS", canRaiseSB sD qS)
#eval ("tabToFoundR qS", tabToFoundR sD qS)
#eval ("canRaiseSB qC", canRaiseSB sD qC)
#eval ("freeCard qC", freeCardS sD qC)
#eval ("pileHolding qC", sD.pileHolding qC)
#eval ("pileOfTop qC", sD.pileOfTop qC)
#eval ("drainLiveB", Drain.drainLiveB sD qS)
