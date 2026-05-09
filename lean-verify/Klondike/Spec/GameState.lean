import Klondike.Spec.Basic

namespace Klondike.Spec

abbrev Pile := List Card
abbrev HiddenCards := List Card

structure TableauPile where
  hidden : HiddenCards
  visible : Pile
  deriving DecidableEq, Repr

abbrev Foundation := Suit → Fin 14

structure Deck where
  stock : List Card
  waste : List Card
  drawStep : Fin 14
  deriving DecidableEq, Repr

structure GameState where
  piles : Fin 7 → TableauPile
  foundation : Foundation
  deck : Deck

namespace GameState

def pileTop (s : GameState) (i : Fin 7) : Option Card :=
  (s.piles i).visible.head?

def pileIsEmpty (s : GameState) (i : Fin 7) : Bool :=
  (s.piles i).visible.isEmpty

def foundationRank (s : GameState) (suit : Suit) : Option Rank :=
  let r := s.foundation suit
  if r = 0 then none else some ⟨r - 1, by omega⟩

def canMoveToFoundation (s : GameState) (c : Card) : Bool :=
  match s.foundationRank c.suit with
  | some r => c.rank = r.val + 1
  | none => c.rank = 0

def canMoveToPile (s : GameState) (i : Fin 7) (c : Card) : Prop :=
  match s.pileTop i with
  | some top => c.goesOnTopOf top
  | none => c.isKing

def isWin (s : GameState) : Prop := ∀ suit : Suit, s.foundation suit = 13

def applyMove (s : GameState) (m : Move) : Option GameState := sorry

end GameState

end Klondike.Spec
